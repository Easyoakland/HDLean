import Lean
import Lean.Meta
import Hdlean.Basic
import Compiler
import Std

open Std (HashMap HashSet)

open Lean hiding Module
open Meta
open Hdlean.ToData
open Compiler
open Data.SystemVerilog
open BitShape

namespace Hdlean.Compiler

structure CompileContext where
  env : HashMap FVarId ValueExpr := {}
  deriving Repr

structure CompileState where
  cache : NameMap Module := {}
  items : Array ModuleItem := #[]
  /-- Modules required to be emitted. Might contain modules that aren't in the `cache` -/
  modules : Array Module := {}
  deriving Repr

abbrev CompilerM := ReaderT CompileContext (StateT CompileState MetaM)

def CompilerM.run' (x: CompilerM α): MetaM α :=
  x.run {} |>.run' {}

def addItem (item : ModuleItem) : CompilerM Unit :=
  modify fun s => { s with items := s.items.push item }

def getHWType (type : Expr) : CompilerM HWType := do
  let .some shape ← bitShape? type | throwError "TODO unsized 3"
  return { width := shape.totalWidth }
-- TODO delete getHWType: take `BitShape` not `Expr` to avoid doubling work when caller already has the shape.
def getHWType' (shape : BitShape) : CompilerM HWType := do
  return { width := shape.totalWidth }

/-- HWType representing the tag for the given `type`  -/
def tagHWType (type : Expr) : CompilerM HWType := do
  let .some shape ← bitShape? type | throwError "TODO unsized 4"
  let .some tagBits := shape.tagBits? | throwError "TODO unsized 4"
  return { width := tagBits }

def denylist: NameSet := (NameSet.empty
  |>.insert ``BitVec.add
  |>.insert ``BitVec.mul
  |>.insert ``Fin.mk
  |>.insert ``BitVec.ofFin
)
def whnf := @whnfWithDenylist' (inlineMatchers:=true) denylist
-- abbrev binderTelescope {α} e k (reducing:=true) (maxVars?:=Option.none) (cleanupAnnotations:=false) := @Meta.binderTelescope (α:=α) e k (reducing:=reducing) (denylist:=denylist) maxVars? cleanupAnnotations

/-- A function is synthesizable if all arguments and the return type are synthesizable. This means that they either can be erased (`Sort _`) or have a known unboxed size. This also works for a function with 0 args (a type). -/
def forallIsSynthesizable (type:Expr): MetaM Bool := forallTelescope type fun args body => do
  let is_synthesizable (type:Expr): MetaM Bool := do
    -- Types and Prop are synthesizable (to nothing).
    if (← isTypeFormerType type) then return true
    -- If has unboxed size then it can be represented with that size in synthesis.
    if (←(bitShape? type)).isSome then return true
    -- Otherwise, is not synthesizable
    return false
  (← args.mapM (·.fvarId!.getType)).push body
    |>.allM (is_synthesizable .)

/-- Get return type given the type of a function substituting the given args  -/
def Meta.returnTypeT (type:Expr) (args:Array Expr): MetaM Expr := do forallTelescope type fun args' body => return body.replaceFVars args' args
/-- Get return type of a function substituting the given args  -/
def Meta.returnTypeV (e:Expr) (args:Array Expr): MetaM Expr := do forallTelescope (← inferType e) fun args' body => return body.replaceFVars args' args

mutual
/-- Compiles a recursor.
- Tags are stored in the low bits and fields are ordered first at lowest idx and last at highest index.
- `args` should (given correct usage of recursor) be `#[params, motives, minors, indices, major, other...]`.
 -/
partial def compileRecursor (recursor : RecursorVal) (args : Array Expr) : CompilerM ValueExpr := do
  dbg!' args
  if recursor.numMotives != 1 then throwError "Number of motives != 1 for {recursor.name}"
  if args.size < recursor.getMajorIdx+1 then throwError "Recursor {recursor.name} underapplied"
  if args.size > recursor.getMajorIdx+1 then throwError s!"TODO: extra args: {args[recursor.getMajorIdx+1:]}"
  let otherArgs := args[recursor.getMajorIdx+1:].toArray
  dbg!' otherArgs
  let motive ← reduce args[recursor.numParams]!
  let major := args[recursor.getMajorIdx]!
  -- Return type is found by applying indices and major premise to motive.
  -- If the type depends on the major premise's values this will fail, otherwise whnf will simplify to the monomorphic type. The `+1` is for the major argument.
  let retType ← whnf <| mkAppN motive args[recursor.getFirstIndexIdx:recursor.getFirstIndexIdx+recursor.numIndices+1]
  dbg!' retType
  let params := args[0:recursor.numParams].toArray
  let minors := args[recursor.getFirstMinorIdx:recursor.getFirstIndexIdx].toArray
  if !(← forallIsSynthesizable retType) then throwError "Return type of motive not synthesizable: {retType}"
  let majorVal ← compileValue major
  let majorType ← inferType major
  let majorInductVal ← Lean.getConstInfoInduct recursor.getMajorInduct
  dbg!' majorType
  let some shape ← bitShape? majorType | throwError "Major type not synthesizable: {majorType}"
  let majorTag ← mkFreshUserName (recursor.getMajorInduct ++ `tag)
  addItem <| .var { name := majorTag, type := ← tagHWType majorType }
  addItem <| .assignment .blocking (.bitSelect (.identifier majorTag) [0:shape.tagBits?.get!]) majorVal
  dbg!' "before cases"
  let cases ← minors.mapIdxM fun idx minor => do
    let ctorVal ← Lean.getConstInfoCtor majorInductVal.ctors[idx]!
    -- dbg!' ← whnf <| mkAppN recursor.rules[idx]!.rhs args[0:recursor.getFirstIndexIdx]
    let tagVal ← compileValue ((mkAppN (.const ``Fin.mk []) #[(.lit <| .natVal minors.size), .lit <| .natVal idx, .const ``lcProof []]))

    -- Extract/slice each field of the `idx`th ctor to a new `.var` declaration with a corresponding free variable. Apply each new free variable to the minor premise and compile the `minor` function call with the new free variables in context.
    let .struct ctorFieldShapes ← bitShape! <| mkAppN (.const ctorVal.name []) params | throwError "HDLean Internal Error: ctor shape is not a struct"
    let mut fieldNames : Array Name := #[]
    let mut fieldStart := shape.tagBits?.get! -- First field after tag
    let mut fieldTypes : Array Expr := #[]
    for fieldIdx in [0:ctorVal.numFields] do
      let name ← mkFreshUserName (.num (recursor.getMajorInduct ++ `field) fieldIdx)
      let width := ctorFieldShapes[fieldIdx]!.totalWidth
      addItem <| .var {name, type := {width}}
      addItem <| .assignment .blocking (.identifier name) (.bitSelect majorVal [fieldStart:fieldStart+width])
      fieldNames := fieldNames.push name
      fieldTypes := fieldTypes.push (← lambdaTelescope minor fun args _body => inferType args[fieldIdx]!)
      fieldStart := fieldStart + width -- Next field after current field
    -- Compile with the free variables associated with each field added to context.
    let result ← withLocalDeclsDND (fieldNames.zip fieldTypes) fun fieldFVarIds =>
      let fieldFVarIds' := fieldFVarIds.map (·.fvarId!)
      withReader (fun ctx => {ctx with env := ctx.env.insertMany <| fieldFVarIds'.zip (fieldNames.map .identifier)})
      <| compileValue (dbg! mkAppN minor fieldFVarIds)
    return dbg! (tagVal, result)
  dbg!' "after cases"
  let recRes ← mkFreshUserName (recursor.getMajorInduct ++ `recRes)
  let retHWType ← getHWType retType
  addItem <| .var { name := recRes, type := retHWType }
  addItem <| .alwaysComb [.conditionalAssignment .blocking (.identifier recRes) retHWType (.identifier majorTag) (← getHWType majorType) cases.toList (.some undefinedValue)]
  return .identifier recRes

partial def compileValue (e : Expr) : CompilerM ValueExpr := do
  let e ← whnf (dbg! e)
  let e := (dbg! e).eta
  -- dbg!' Repr.reprPrec e 0
  match dbg! e with
  | .fvar fvarId => do
    match (← read).env.get? fvarId with
    | .some value => pure value
    | .none => throwError "Unknown free variable: {fvarId}"
  | .app .. =>
    let (fn, args) := e.getAppFnArgs
    if fn.isAnonymous then throwError "non-constant application {e}"
    dbg!' fn
    let info ← Lean.getConstInfo fn

    if ← isTypeFormerType (← Meta.returnTypeT info.type args) then return ValueExpr.literal "/*ZST*/"

    match fn with
    | ``BitVec.ofFin =>
      let #[_w, toFin] := args | throwError "Invalid number of arguments ({args.size}) for BitVec.ofFin"
      let val ← compileValue toFin
      return val
    | ``Fin.mk =>
      let #[n, val, _isLt] := args | throwError "Invalid number of arguments ({args.size}) for Fin.mk"
      let val ← compileValue val
      let n ← unsafe Meta.evalExpr Nat (.const ``Nat {}) n
      let lit := match val.emit with |.none => "" |.some val => s!"{n.ceilLog2}'{val}"
      return .literal lit -- Add width annotation
    | ``BitVec.mul =>
      let #[_n, x, y] := args | throwError "Invalid number of arguments ({args.size}) for BitVec.mul"
      let x ← compileValue x
      let y ← compileValue y
      return .binaryOp .mul x y
    | ``BitVec.add =>
      let #[_n, x, y] := args | throwError "Invalid number of arguments ({args.size}) for BitVec.add"
      let x ← compileValue x
      let y ← compileValue y
      return .binaryOp .add x y
    | fn =>
      match ← Lean.getConstInfo fn with
      | .recInfo val => compileRecursor val args
      | .ctorInfo val => throwError "TODO ctor with arguments: {e}; val={val}"
      | _ => throwError "Unsupported function application: {e}"
  | .const name _ =>
    if let .ctorInfo val ← Lean.getConstInfo name then
      if val.numFields != 0 then throwError "Underapplied ctor: {name}"
      let tag := val.cidx
      compileValue (.lit <| .natVal tag)
    else
      throwError "Unsupported constant which is not unfoldable: {name} := {e}"
  | .lit e => return .literal <| match e with |.natVal n => s!"{n}" |.strVal s => s
  | _ => throwError "Unsupported expression: {e}"
end

partial def compileAssignment (space : SpaceExpr) (e : Expr) : CompilerM Unit := do
  match e with
  | .mdata _ body => compileAssignment space body
  | .letE _ _ value body _ => do
      let valueType ← inferType value
      dbg!' ""
      let valueHWType ← getHWType valueType
      let tmpName ← mkFreshUserName `let
      addItem <| .var {
        name := tmpName,
        type := valueHWType
      }
      let valueVal ← compileValue value
      dbg!' valueVal
      addItem <| .assignment .blocking (.identifier tmpName) valueVal
      let letFVar ← mkFreshFVarId
      withReader (fun ctx => { ctx with env := ctx.env.insert letFVar (.identifier tmpName) }) do
        compileAssignment space (body.instantiate1 (.fvar letFVar))
  | .app .. | .const .. =>
      let value ← compileValue e
      addItem <| .assignment .blocking space value
  | .proj typeName idx s => throwError "TODO projection: type={typeName},idx={idx},s={s};{e}"
  | e => throwError "Unsupported statement expression: {e}"

/-- Add module(s) corresponding to a function to the back of the list to be emitted as well as returning it. `fun x y z => body` becomes
  ```
  module(
    input x
    ,input y
    ,input z
    ,ouput o
  )
    assign o = body
  endmodule
  ```
-/
partial def compileFun (fn: Expr): CompilerM Module := do
  dbg!' fn
  lambdaTelescope (dbg! ← etaExpand fn) fun args body => do
  -- If doesn't unfold is probably an irreducible constant which should be handled correctly by `compileAssignment`
  let body := (← delta? body) |>.getD body
  dbg!' (args, body, ← delta? body)
  -- If body isn't synthesizable then unfold until it is. Since the top-level function is required to be monomorphic at some point the unfolding will expose a synthesizable signature (worst case by unfolding everything to primitives).
  if !(← forallIsSynthesizable (← inferType body)) then
    let .some body' ← delta? body | throwError "Unsynthesizable body is not unfoldable: {body}, args={args}"
    dbg!' body'
    if body' == body then throwError "Unsynthesizable body could not be unfolded: {body}, args={args}"
    return ← compileFun (dbg! ← mkLambdaFVars args body')
  let .some retShape ← bitShape? (← Meta.returnTypeV body args) | throwError dbg! "TODO"

  let mut parameters := #[]
  let mut ports := #[]

  for arg in args do
    let argType ← inferType arg
    let .some argShape ← bitShape? argType | throwError "TODO unsized 2"
    ports := ports.push {
      name := ← arg.fvarId!.getUserName,
      type := { width := argShape.totalWidth },
      direction := .input
    }

  ports := ports.push {
    name := `o,
    type := { width := retShape.totalWidth },
    direction := .output
  }

  let ctx : CompileContext := {
    env := ← args.foldlM (init := (← read).env) fun map arg => do
      let name := ← arg.fvarId!.getUserName
      return map.insert arg.fvarId! (.identifier name)
  }

  withReader (fun _ => ctx) <| compileAssignment (.identifier `o) body

  let name ← mkFreshUserName `mod
  let mod := {
    name,
    parameters := parameters,
    ports := ports,
    items := (←get).items
  }
  modify fun x => {x with items:=#[], modules:=x.modules.push mod}
  return mod

def constToSystemVerilog (name : Name) : CompilerM Module := do
  if let .some mod := (← get).cache.find? name then return mod

  let info ← Lean.getConstInfo name
  let e := info.value!

  let mod ← compileFun e
  assert! mod == (← get).modules.back!
  let compiledMod := {mod with name}

  -- Fix the name of the module removing the old version, and cache the new module.
  modify fun x => {x with cache := x.cache.insert name compiledMod, modules := x.modules.pop.push compiledMod}

  return compiledMod

def emit (name : Name) : MetaM String := do
  let mod ← withTransparency .all <| constToSystemVerilog name |>.run'
  return ToString.toString mod.emit

section Testing
def f: Bool:= .true
#eval do println! ← emit (``f)

def g: BitVec 3 := 68#3
#eval do println! ← emit (``g)
def add_mul (x y z: BitVec w) := x + y * z
def add_mul_mono := add_mul (w:=4)
#eval do println! ← emit (``add_mul_mono)
#eval do println! ← constToSystemVerilog (``add_mul_mono) |>.run'
def add (x y: BitVec w) := x + y
def add_mono := add (w:=4)
#eval do println! ← emit (``add_mono)
def add_mul' (x y z: BitVec w) := (add x y) * z
def add_mul_mono' := add_mul' (w:=4)

def tmp : (BitVec 4) → (BitVec 4) → (BitVec 4) := (inferInstanceAs (Add (BitVec 4))).1
#eval do println! (← delta? (.const ``tmp [])).get!

#eval do println! ← emit (``add_mul_mono')

#eval show MetaM _ from do
 let expr := (← delta? (.const ``add_mul_mono [])).get!
 println! ToString.toString <| (← compileFun expr |>.run').emit

def mynot (x: Bool): Bool := match x with
  | false => true
  | true => false
def mynotL (x: LBool): LBool := match x with
  | .true => .false
  | .false => .true
  | .undef => .undef
private inductive Either (α β) where | left (a:α) | right (b:β)
def mynotE (x: Either Bool Bool): Bool := match x with
  | .left v => mynot v
  | .right v => mynot v
def mynotE' (x: Either LBool LBool): LBool := match x with
  | .left v => mynotL v
  | .right v => mynotL v
def mynotE'' (x: Either Bool LBool): Either LBool Bool := match x with
  | .left v => .right <| mynot v
  | .right v => .left <| mynotL v
#eval do println! ← emit (``mynot)
#eval do println! ← emit (``mynotL)
#eval do println! ← emit (``mynotE)
#eval do println! ← emit (``mynotE')
#eval do println! ← emit (``mynotE'')
inductive EvenOddList (α : Type u) : Bool → Type u where
  | nil : EvenOddList α true
  | cons : α → EvenOddList α isEven → EvenOddList α (not isEven)
def test1 (x y:BitVec 3):= x + y * 3
structure MyS where
  a: Fin 2
  b: Fin 3
  c: BitVec 4
def MyS.test1 : MyS:= {a:=1,b:=2,c:=3:MyS}
def MyS.test2 : Fin 2:= {a:=1,b:=2,c:=3:MyS}.a
#eval do println! ← emit (``MyS.test1)
#eval do println! ← emit (``MyS.test2)

def sorryP {p:Prop}: p := sorry
def len_manual (x: Vector α n): Fin (n+1) := x.elimAsList fun l hl => match l with
  | .nil => ⟨0, by omega⟩
  | .cons a b =>
    have : n - 1 + 1 + 1 = n + 1 := by
      have : n > 0 := by exact?
      omega
    1 + (len_manual (n:=n-1) (.mk b.toArray (by exact?)) |>.castSucc |> cast (by rw [this]))
#eval len_manual (α:=Nat) #v[1,2,3]
def len_manual_mono : Fin 3 := len_manual #v[0,1]

#check Acc.rec
#eval do println! ← emit (``len_manual_mono)
#eval show MetaM _ from do println! (← Lean.getConstInfoRec ``Bool.rec)

#eval do return ToString.toString (← (withTransparency .all <| binderTelescope (.const ``mynot []) fun _args body =>  Meta.unfoldDefinition? (dbg! body)))
#eval do ((← (withTransparency .all <| binderTelescope (.const ``mynot []) fun _args body => do return Meta.unfoldDefinition? (dbg! (← Lean.Compiler.LCNF.inlineMatchers (dbg! body))))))
#eval do ( (binderTelescope (.const ``mynot []) fun _args body => do return (dbg! ← delta? body)))
#eval do ( (Lean.Compiler.LCNF.inlineMatchers (.const ``mynot [])))

-- TODO
-- How does inlineMatchers work in LCNF, how is Cases made, and how does bindCases work?
-- #check Core.transform
-- #check Meta.traverseChildren

#eval do
  let res ← Meta.unfoldDefinition? (.const ``mynot.match_1 [1]);
  println! "---";
  println! res
#eval do
  let res ← Meta.withTransparency .all <| Meta.unfoldDefinition? (.app (.const ``mynot.match_1 [1]) (.fvar (← mkFreshFVarId)) )
  println! "---"
  println! res
#eval do
  let mynot := Expr.const ``mynot []
  let x ← mkFreshExprMVar (Expr.const ``Bool [])
  let applied := mkApp mynot x
  whnfImp applied  -- Still stuck, but now with metavariable instead of free var

-- #check Meta.caseValues
#eval (binderTelescope (.const ``mynot []) fun args body => do
  dbg_trace args
  dbg_trace body
  let x ← mkFreshExprMVar (Expr.const ``Bool [])
  let cases ← withLocalDecl `x .default (.const ``Bool []) fun x => do
    let body := mkApp (.const ``mynot []) x
    let cases ← x.mvarId!.cases (dbg! args[0]!.fvarId!) #[AltVarNames.mk .false [dbg! ← args[0]!.fvarId!.getUserName]]
    pure cases
    -- pure (cases.map fun (case, _) => case.fields[0]!)
  -- `cases` now contains [false, true] for each branch
  -- whnfImp body
)


/-
deriving instance Repr for
  LCNF.Arg,
  LCNF.LitValue,
  LCNF.LetValue,
  LCNF.LetDecl,
  LCNF.LitValue,
  LCNF.LetValue,
  LCNF.Param,
  LCNF.Code
#eval do println! ← Lean.Compiler.LCNF.ToLCNF.toLCNF (mkAppN (.const ``mynot []) #[.const ``Bool.true []]) |>.run
 -/
end Testing

end Hdlean.Compiler
