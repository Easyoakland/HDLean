import Lean
import Std

import Hdlean.Basic
import Compiler

open Std (HashMap HashSet)
open Lean hiding Module
open Meta

open Hdlean.Meta
open Hdlean.BitShape hiding struct union
open Hdlean.Compiler
open Netlist.SystemVerilog

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
  return { width := shape.tagBits }

def denylist: NameSet := (NameSet.empty
  |>.insert ``Fin.mk
  |>.insert ``BitVec.ofFin
  |>.insert ``BitVec.add
  |>.insert ``BitVec.mul
  |>.insert ``BitVec.ult
  |>.insert ``BitVec.ule
  -- |>.insert ``instLTBitVec
  -- |>.insert ``instLEBitVec
  -- |>.insert ``instDecidableLtBitVec
  -- |>.insert ``instDecidableLeBitVec
)
def whnf := @whnfWithDenylist' (inlineMatchers:=true) denylist
-- abbrev binderTelescope {α} e k (reducing:=true) (maxVars?:=Option.none) (cleanupAnnotations:=false) := @Meta.binderTelescope (α:=α) e k (reducing:=reducing) (denylist:=denylist) maxVars? cleanupAnnotations

/-- A function is synthesizable if all arguments and the return type are synthesizable. This means that they either can be erased (`Sort _`) or have a known unboxed size. This also works for a function with 0 args (a type). -/
def forallIsSynthesizable (type:Expr): MetaM Bool := forallTelescope type fun args body => do
  let is_synthesizable (type:Expr): MetaM Bool := do
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

/-- Compiles the projection of a single field of a constructor given a `ValueExpr`.

- `constructedVal`: The compiled value to extract the field from.
- `constructedValType`: Type of `constructedVal`
- `ctorVal`: The ctor used to make `constructedVal`
- `fieldIdx`: Which field to extract
- `fieldType`: The type of the field to extract

For example, extracting `num1` and `num2` (one call for each) from the `ValueExpr` of `v` in
```
inductive OneOrTwo where
  | one BitVec 1
  | two (BitVec 1, BitVec 2)
let v := OneOrTwo.two (1, 2)
let .two (num1, num2) := v | panic! ""
```
Or extracting `y` from the `ValueExpr` of `v` in
```
structure MyStruct where
  x : BitVec 1
  y : BitVec 2
  z : BitVec 3
let v := {x:=1,y:=2,z:=3}
v.y
```
-/
def compileFieldProj (constructedVal:ValueExpr) (constructedValType: Expr) (ctorVal : ConstructorVal) (fieldIdx:Nat) (fieldType:Expr) : CompilerM ValueExpr := do
  let shape ← bitShape! constructedValType
  if let .union #[] := shape then return ValueExpr.literal "/*ZST*/"
  let (tagWidth, fieldShapes) ← do
    match shape with
    | .union variants =>
      let .some variant := variants[ctorVal.cidx]? | throwError "ctorVal is invalid variant: {ctorVal} of {variants}"
      let .struct fieldShapes := variant | throwError "HDLean Internal Error: ctor variant shape not struct: {ctorVal} is {variants[ctorVal.cidx]!}"
      pure (shape.tagBits, fieldShapes)
    | .struct fieldShapes =>
      assert! ctorVal.cidx = 0
      pure (0, fieldShapes)

  if fieldIdx >= fieldShapes.size then
    throwError "Projection index out of bounds: {fieldIdx} for {ctorVal.induct} with {fieldShapes.size} fields"

  let mut start := tagWidth
  for i in [0:fieldIdx] do
    start := start + fieldShapes[i]!.totalWidth
  let width := fieldShapes[fieldIdx]!.totalWidth
  let name ← mkFreshUserName (.num (ctorVal.name ++ `field) fieldIdx)
  addItem <| .var {name, type := ← getHWType fieldType}
  addItem <| .assignment .blocking (.identifier name) (.bitSelect constructedVal [start:start+width])
  return .identifier name

-- Substitute < notation on BitVec with this, which is the same but easier to detect and block during compilation.
-- @[inline, reducible] def _root_.BitVec.lt (x y: BitVec n) := x < y
-- @[inline, reducible] def _root_.BitVec.ble (x y: BitVec n): Bool := x ≤ y
-- @[inline, reducible] def _root_.BitVec.blt (x y: BitVec n): Bool := x < y
-- Substitute < notation on BitVec with this, which is the same but easier to detect and block during compilation.
-- @[inline, reducible] def instLTBitVecHW: LT (BitVec w) where
--   lt := BitVec.lt
-- @[inline, reducible] def instLEBitVecHW: LE (BitVec w) where
--   le := BitVec.le
@[inline, reducible] instance instDecidableLtBitVecHW (x y : BitVec w) : Decidable (LT.lt x y) :=
  if h: x.ult y then .isTrue (by bv_decide)
    -- .isTrue (by exact BitVec.ult_iff_lt.mp h)
  else .isFalse (by bv_decide)
    -- .isFalse (Std.Tactic.BVDecide.Normalize.BitVec.lt_ult x y ▸ h)

mutual
/-- Compiles a projection expression `Expr.proj` (e.g., `a.1`) for structures and single-ctor inductives -/
partial def compileExprProj (typeName:Name) (idx:Nat) (struct:Expr) : CompilerM ValueExpr := do
  compileFieldProj
    (constructedVal:=← compileValue struct)
    (constructedValType:=← inferType struct)
    (ctorVal:=Lean.getStructureCtor (← getEnv) typeName)
    (fieldIdx:=idx)
    (fieldType:=← inferType (.proj typeName idx struct))

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
  if retType.isProp then return ValueExpr.literal "/*ZST: rec eliminates to Prop */"
  let minors := args[recursor.getFirstMinorIdx:recursor.getFirstIndexIdx].toArray
  if !(← forallIsSynthesizable retType) then throwError "Return type of motive not synthesizable: {retType}"
  let majorVal ← compileValue major
  let majorType ← inferType major
  let majorInductVal ← Lean.getConstInfoInduct recursor.getMajorInduct
  dbg!' majorType
  let some shape ← bitShape? majorType | throwError "Major type not synthesizable: {majorType}"
  let majorTag ← mkFreshUserName (recursor.getMajorInduct ++ `tag)
  addItem <| .var { name := majorTag, type := ← tagHWType majorType }
  addItem <| .assignment .blocking (.identifier majorTag) (.bitSelect majorVal [0:shape.tagBits])
  dbg!' "before cases"
  let cases ← minors.mapIdxM fun idx minor => do
    let ctorVal ← Lean.getConstInfoCtor majorInductVal.ctors[idx]!
    let tagVal ← compileValue <| mkAppN (.const ``Fin.mk []) #[
      .lit <| .natVal (dbg! minors.size),
      .lit <| .natVal idx,
      .const ``lcProof []
    ]
    -- Infer field types from minor premise's argument types
    let fieldTypes ← (Array.range ctorVal.numFields).mapM fun fieldIdx => lambdaTelescope minor fun args _body => inferType args[fieldIdx]!
    -- Extract fields with `compileFieldProj`.
    let fieldVals ← (Array.range ctorVal.numFields).mapM fun fieldIdx => compileFieldProj majorVal majorType ctorVal fieldIdx fieldTypes[fieldIdx]!
    let binderNames ← (Array.range ctorVal.numFields).mapM fun fieldIdx => mkFreshUserName (.num (ctorVal.name ++ `field) fieldIdx)
    -- Apply minor premise to extracted fields.
    let result ← withLocalDeclsDND (binderNames.zip fieldTypes) fun fieldFVarIds => do
      let mapping := fieldFVarIds.mapIdx (fun i fvarId => (fvarId.fvarId!, fieldVals[i]!))
      withReader (fun ctx => {ctx with env := ctx.env.insertMany mapping})
        <| compileValue (mkAppN minor fieldFVarIds)
    return dbg! (tagVal, result)
  dbg!' "after cases"
  let recRes ← mkFreshUserName (recursor.getMajorInduct ++ `recRes |>.str ((ToString.toString retType).takeWhile fun c => !c.isWhitespace))
  let retHWType ← getHWType retType
  addItem <| .var { name := recRes, type := retHWType }
  match minors.size with
  | 0 => addItem <| ModuleItem.assignment .blocking (.identifier recRes) undefinedValue
  | 1 => addItem <| ModuleItem.assignment .blocking (.identifier recRes) cases[0]!.snd
  | _ => addItem <| .alwaysComb [.conditionalAssignment .blocking (.identifier recRes) retHWType (.identifier majorTag) (← getHWType majorType) cases.toList (.some undefinedValue)]
  return .identifier recRes

/-- Compile a constructor in the opposite way that a FieldProjection is compiled.  -/
partial def compileCtor (ctor : ConstructorVal) (levels: List Level) (args : Array Expr) : CompilerM ValueExpr := do
  let params := args.extract 0 ctor.numParams
  let fields := args.extract ctor.numParams (ctor.numParams+ctor.numFields)
  dbg!' (params, fields)
  let inductType := dbg! mkAppN (.const ctor.induct levels) params
  let shape ← bitShape! inductType
  let tagWidth := shape.tagBits
  let fieldShapes ← match shape with
    | .union variants =>
      let .some variant := variants[ctor.cidx]? | throwError "ctor idx invalid: {ctor.cidx} / {variants.size}"
      let .struct fieldShapes := variant | throwError "HDLean Internal Error: variant shape for constructor {ctor.cidx} of {ctor.induct} is not struct "
      pure fieldShapes
    | .struct fieldShapes => pure fieldShapes
  if fieldShapes.size != fields.size then throwError "HDLean Internal Error: field count mismatch for {ctor.name} (expected {fieldShapes.size}, got {fields.size})"
  let fieldVals ← fields.mapM (fun field => compileValue (dbg! field))
  let tagVal ← if tagWidth == 0 then pure #[] else
    let tagVal ← compileValue <| mkAppN (.const ``BitVec.ofNat []) #[
      .lit <| .natVal tagWidth,
      .lit <| .natVal ctor.cidx,
    ]
    pure #[tagVal]
  dbg!' (fieldVals, tagVal)
  return .concatenation <| Array.toList <| fieldVals ++ tagVal


/-- Returns a substituted `Expr` if implemented by something else for hardware synthesis -/
partial def HWImplementedBy? (e:Expr): MetaM (Option Name) := do
  pure <| match e with
  -- | (.proj ``LT 0 (.app (.const ``instLTBitVec []) _)) => .some ``BitVec.lt
  | (.const ``instDecidableLtBitVec []) => .some ``instDecidableLtBitVecHW
  | _ => .none

partial def compileValue (e : Expr) : CompilerM ValueExpr := do
  let e ← whnf (dbg! e)
  let e := (dbg! e).eta
  if let .some (.union #[]) := ← bitShape? (← inferType e) then
    return ValueExpr.literal "/*ZST*/"

  match dbg! e with
  | .fvar fvarId => do
    match (← read).env.get? fvarId with
    | .some value => pure value
    | .none => throwError "Unknown free variable: {fvarId}"
  | .app .. =>
    let (fn, args) := e.getAppFnArgs
    let fn := if let .some fn := dbg! ← HWImplementedBy? (dbg! e.getAppFn) then fn else fn
    if fn.isAnonymous then throwError "non-constant application {e}"
    dbg!' fn

    match fn with
    | ``BitVec.ofFin =>
      let #[_w, toFin] := args | throwError "Invalid number of arguments ({args.size}) for BitVec.ofFin"
      let val ← compileValue toFin
      return val
    | ``Fin.mk =>
      let #[n, val, _isLt] := args | throwError "Invalid number of arguments ({args.size}) for Fin.mk"
      let val ← compileValue val
      let n ← unsafe Meta.evalExpr Nat (.const ``Nat {}) n
      let lit := match val.emit with |.none => "" |.some val => s!"{n.ceilLog2}'{val}" -- Add width annotation
      return .literal lit
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
    | ``BitVec.ult =>
      let #[_n, x, y] := args | throwError "Invalid number of arguments ({args.size}) for BitVec.ult"
      let x ← compileValue x
      let y ← compileValue y
      return .binaryOp .lt x y
    | ``BitVec.ule =>
      let #[_n, x, y] := args | throwError "Invalid number of arguments ({args.size}) for BitVec.ule"
      let x ← compileValue x
      let y ← compileValue y
      return .binaryOp .le x y
    -- | ``instLTBitVec =>
    --   compileValue (.const ``instLTBitVecHW [])
    -- | ``instLEBitVec =>
    --   compileValue (.const ``instLEBitVecHW [])
    | fn =>
      match ← Lean.getConstInfo fn with
      | .recInfo val => compileRecursor val args
      | .ctorInfo val => compileCtor (dbg! val) e.getAppFn.constLevels! (dbg! args)
      | _ => throwError "Unsupported function application: {e}"
  | .const name _ =>
    if let .ctorInfo val ← Lean.getConstInfo name then
      if val.numFields != 0 then throwError "Underapplied ctor: {name}"
      let tag := val.cidx
      compileValue (.lit <| .natVal tag)
    else
      throwError "Unsupported constant which is not unfoldable: {name} := {e}"
  | .lit e => return .literal <| match e with |.natVal n => s!"{n}" |.strVal s => s
  | .proj typeName idx s => compileExprProj typeName idx s
  | _ => throwError "Unsupported expression: {e}"
end

partial def compileAssignment (space : SpaceExpr) (e : Expr) : CompilerM Unit := do
  match e with
  | .mdata _ body => compileAssignment space body
  | .letE _ _ value body _ => do
      let valueVal ← compileValue value
      let valueType ← inferType value
      let name ← mkFreshUserName `let
      addItem <| .var { name, type := ← getHWType valueType }
      addItem <| .assignment .blocking (.identifier name) valueVal
      let letFVar ← mkFreshFVarId
      withReader (fun ctx => { ctx with env := ctx.env.insert letFVar (.identifier name) }) do
        compileAssignment space (body.instantiate1 (.fvar letFVar))
  | .app .. | .const .. | .proj .. =>
      let value ← compileValue e
      addItem <| .assignment .blocking space value
  | e => throwError "Unsupported statement expression: {e}"

/-- Add module(s) corresponding to a function to the back of the list to be emitted as well as returning it. `fun x y z => body` becomes
  ```
  module(
    input x
    ,input y
    ,input z
    ,output o
  )
    assign o = body
  endmodule
  ```
-/
partial def compileFun (fn: Expr): CompilerM Module := do
  lambdaTelescope (← etaExpand fn) fun args body => do
  -- If doesn't unfold is probably an irreducible constant which should be handled correctly by `compileAssignment`
  let body := (← delta? body) |>.getD body
  -- If body isn't synthesizable then unfold until it is. Since the top-level function is required to be monomorphic at some point the unfolding will expose a synthesizable signature (worst case by unfolding everything to primitives).
  if !(← forallIsSynthesizable (← inferType body)) then
    let .some body' ← delta? body | throwError "Unsynthesizable body is not unfoldable: {body}, args={args}"
    dbg!' body'
    if body' == body then throwError "Unsynthesizable body could not be unfolded: {body}, args={args}"
    return ← compileFun (← mkLambdaFVars args body')
  let .some retShape ← bitShape? (← Meta.returnTypeV body args) | throwError dbg! "TODO"

  let mut parameters := #[]
  let mut ports := #[]

  for arg in args do
    let argType ← inferType arg
    let .some argShape ← bitShape? argType | throwError "Argument `{arg}:{argType}` is unsynthesizable"
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
def mynotEIf (x: Either LBool LBool): Fin 3 :=
  if let .left _ := x then 0
  else if let .right _ := x then 1
  else 2
def mynotEIf' (x: Bool): Fin 2 :=
  if h:x then 0
  else if h2:!x then 1
  else suffices False from this.elim
    by cases x <;> contradiction

#eval do println! ← emit (``mynot)
#eval do println! ← emit (``mynotL)
#eval do println! ← emit (``mynotE)
#eval do println! ← emit (``mynotE')
#eval do println! ← emit (``mynotE'')
#eval do println! ← emit (``mynotEIf)
#eval do println! ← emit (``mynotEIf')

inductive EvenOddList (α : Type u) : Bool → Type u where
  | nil : EvenOddList α true
  | cons : α → EvenOddList α isEven → EvenOddList α (not isEven)
def test1 (x y:BitVec 3):= x + y * 3
structure MyS where
  a: Fin 2
  b: Fin 3
  c: BitVec 4
#eval Lean.getProjectionFnInfo? ``MyS.a
#eval do return Lean.getProjFnInfoForField? (← getEnv) ``MyS `a
#eval do return Lean.getProjFnForField? (← getEnv) ``MyS `a
#eval do return Lean.getStructureFields (← getEnv) ``MyS
#eval do return Lean.getFieldInfo? (← getEnv) ``MyS `a
#eval do return Lean.getStructureInfo (← getEnv) ``MyS |>.getProjFn? 0
#check Hdlean.Compiler.MyS.a
def MyS.test1 : MyS:= {a:=1,b:=2,c:=3:MyS}
def MyS.test2 : Fin 2:= {a:=1,b:=2,c:=3:MyS}.a
def MyS.test3 (a: Fin 2): Fin 2:= {a,b:=2,c:=3:MyS}.a
def MyS.test4 (s: MyS): Fin 2:= s.a
def MyS.test5 (s: MyS): Fin 3:= s.b
#eval do println! ← emit (``MyS.test1)
#eval do return ToString.toString <| ← whnf <| .app (.const ``MyS.a []) (.const ``MyS.test1 [])
#eval do println! ← emit (``MyS.test2)
#eval do println! ← emit (``MyS.test3)
#eval do println! ← emit (``MyS.test4)
#eval do println! ← emit (``MyS.test5)
structure DependentStructure where
  n : Nat
  d : Vector Bool n
def DependentStructure.test1 (s: DependentStructure) := s.d
def DependentStructure.test2 (s: DependentStructure)(h:s.n=3) : Vector Bool 3 := h ▸ s.d
#eval try do println! ← emit (``DependentStructure.test1); panic! "should error" catch _ => pure ()
#eval try do println! ← emit (``DependentStructure.test2); panic! "should error" catch _ => pure ()
structure DependentStructure' (n:Nat) where
  d : Vector Bool n
  g : Vector Bool (2 * n)
def DependentStructure'.test1 (s: DependentStructure' 4) := s.d
def DependentStructure'.test2 (s: DependentStructure' 3) := s.g
#eval do println! ← emit (``DependentStructure'.test1)
#eval do println! ← emit (``DependentStructure'.test2)
section
local instance : OfNat Bool 0 := ⟨false⟩
local instance : OfNat Bool 1 := ⟨true⟩
def DependentStructure'.t: DependentStructure' 3 := {d:=#v[1,0,1],g:=#v[0,0,1,0,0,1]}
end

#eval do return Lean.getStructureInfo (← getEnv) ``DependentStructure |>.getProjFn? 1 |>.get!
#check Hdlean.Compiler.DependentStructure.d

def len_manual (x: Vector α n): Fin (n+1) := x.elimAsList fun l hl => match l with
  | .nil => ⟨0, by omega⟩
  | .cons a b =>
    have : n - 1 + 1 + 1 = n + 1 := by
      have : n > 0 := by exact?
      omega
    1 + (len_manual (n:=n-1) (.mk b.toArray (by exact?)) |>.castSucc |> cast (by rw [this]))
#eval len_manual (α:=Nat) #v[1,2,3]
def len_manual_mono : Fin 3 := len_manual #v[0,1]

#check PSigma.mk
#check (@PSigma.mk Nat (fun n => Vector Nat n) 2 #v[0,1]).1

#check Acc.rec
#eval show Bool from @Acc.rec (r:=Eq) (motive:=fun x y => Bool) _ (fun x y z => x) .true (@lcProof (Acc _ _))
#reduce fun (n:Nat) => (Nat.rec (motive := fun _ => List Nat) ([]) (fun x y => y.cons x) (n+2) : List Nat)
#reduce True.rec (motive:=fun _ => String) "start" .intro
noncomputable def testSubsingletonElim := True.rec (motive:=fun _ => String) "start" .intro
#eval whnf (.const ``testSubsingletonElim [])
#eval Meta.whnf (.const ``testSubsingletonElim [])
-- TODO I think this is working weird because the major type is Prop. But maybe not because True.rec and Nat.rec etc reduces fine.
-- TODO alternatively, it's because there's Eq.rec and reduce doesn't seem to handle that well.
-- TODO ah! is Acc.rec similar to Eq.rec in that it blocks reduction?! When does a recursor block reduction? What would be the intended method of reducing one of these recursors which block reduction? I'm guessing I'm going to need some kind of intermediate between whnf which is blocked on .rec and #eval which fully evaluates an expression.
#eval do println! ← emit (``len_manual_mono) -- TODO variants = [], yet it is trying to synthesize in hardware.
#check Acc.rec
#check Eq.rec
#eval do println! ← withTransparency .all <| whnf (.const ``len_manual_mono [])
#eval do println! ← (
    Meta.transform
    (← withTransparency .all <| reduce (explicitOnly:=false) (.const ``len_manual_mono []))
    (pre:=fun e => do
    let type ← inferType e
    let typeType ← inferType type
    if (← Meta.isPropFormerType type) then
      dbg!' s!"replace, {e} with lcProof"
      return TransformStep.done (Expr.const `lcErased [])
    else if (← Meta.isPropFormerType (dbg! typeType)) then
      dbg!' s!"replace, {e} with lcErased"
      -- return TransformStep.done (.app (Expr.const `lcProof []) type)
      return TransformStep.done (Expr.const `lcProof [])
    else
      return TransformStep.continue .none)
  )
#eval do
  let a := ← (
    Meta.transform
    (← withTransparency .all <| reduce (explicitOnly:=false) (.const ``len_manual_mono []))
    (pre:=fun e => do
    let type ← inferType e
    let typeType ← inferType type
    if (← Meta.isPropFormerType type) then
      dbg!' s!"replace, {e} with lcProof"
      return TransformStep.done (Expr.const `lcErased [])
    else if (← Meta.isPropFormerType (dbg! typeType)) then
      dbg!' s!"replace, {e} with lcErased"
      -- return TransformStep.done (.app (Expr.const `lcProof []) type)
      return TransformStep.done (Expr.const `lcProof [])
    else
      return TransformStep.continue .none)
  )
  ToString.toString <$> (reduce a)
#eval len_manual_mono
#reduce len_manual_mono
#reduce show Bool from Acc.rec (motive:=fun x y => Bool) (fun x y z => x) (lcProof)

#eval do (Lean.Compiler.LCNF.inlineMatchers (.const ``mynot []))

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

def _root_.BitVec.natMax {w:Nat}: BitVec w := -1 -- since -1 is all `1`s it is also the largest unsigned value

def wouldOverflow (n m : BitVec w): Bool :=
  if n + m < n then true
  else if n + m < m then true
  else false

def saturatingAdd (n m : BitVec w): BitVec w :=
  if wouldOverflow n m then BitVec.natMax else
  n + m
def t := fun (x y : BitVec 3) => (x < y: Bool)
def t2 := fun (x y : BitVec 3) => x.ult y
def t3 := fun (x y : BitVec 3) => x.ule y
#print t

example: saturatingAdd 0#2 3#2 = 3#2 := rfl
example: saturatingAdd 1#2 3#2 = 3#2 := rfl
example: saturatingAdd 2#2 3#2 = 3#2 := rfl
example: saturatingAdd 2#2 2#2 = 3#2 := rfl
example: saturatingAdd 3#2 3#2 = 3#2 := rfl
open scoped BitVec in
#eval
  let a: BitVec 2 := 3#'(by omega)
  a

def saturatingAddMono := saturatingAdd (w:=2)
#eval do println! ← emit (``t)
#eval do println! ← emit (``t2)
#eval do println! ← emit (``t3)
#eval do println! ← emit (``saturatingAddMono)

end Testing

end Hdlean.Compiler
