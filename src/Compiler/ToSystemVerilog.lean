import Lean
import Std

import Hdlean.Basic
import Hdlean.SigmaMealy
import Compiler.BitShape
import Compiler.Netlist
import Compiler.WHNF
import Compiler.Trace

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

/-- HWType representing the given type in its entirety (both tag and payload). -/
def getHWType (shape : BitShape) : CompilerM HWType := do
  return { width := shape.totalWidth }

/-- HWType representing the tag for the given `type`  -/
def tagHWType (shape : BitShape) : CompilerM HWType := do
  return { width := shape.tagBits }

section Primitives
def BitVec.shiftLeftHW {m n : Nat} (x : BitVec m) (s : BitVec n) : BitVec m := BitVec.instHShiftLeft.hShiftLeft x s

def BitVec.shiftRightHW {m n : Nat} (x : BitVec m) (s : BitVec n) : BitVec m := BitVec.instHShiftRight.hShiftRight x s

instance (priority:=low) BitVec.instHShiftLeftHW : HShiftLeft  (BitVec m) (BitVec n) (BitVec m) := ⟨BitVec.shiftLeftHW⟩

instance (priority:=low) BitVec.instHShiftRightHW : HShiftRight (BitVec m) (BitVec n) (BitVec m) := ⟨BitVec.shiftRightHW⟩

instance (priority:=low) instDecidableLtBitVecHW (x y : BitVec w) : Decidable (LT.lt x y) :=
  if h: x.ult y then .isTrue (by bv_decide)
    -- .isTrue (by exact BitVec.ult_iff_lt.mp h)
  else .isFalse (by bv_decide)
    -- .isFalse (Std.Tactic.BVDecide.Normalize.BitVec.lt_ult x y ▸ h)

instance (priority:=low) instDecidableLeBitVecHW (x y : BitVec w) : Decidable (LE.le x y) :=
  if h: x.ule y then .isTrue (by bv_decide)
  else .isFalse (by bv_decide)

attribute [implemented_by_hw BitVec.instHShiftLeftHW] BitVec.instHShiftLeft
attribute [implemented_by_hw BitVec.instHShiftRightHW] BitVec.instHShiftRight
attribute [implemented_by_hw instDecidableLtBitVecHW] instDecidableLtBitVec
attribute [implemented_by_hw instDecidableLeBitVecHW] instDecidableLeBitVec

def denylist: NameSet := (NameSet.empty
  |>.insert ``BitVec.add
  |>.insert ``BitVec.sub
  |>.insert ``BitVec.mul
  |>.insert ``BitVec.ult
  |>.insert ``BitVec.slt
  |>.insert ``BitVec.ule
  |>.insert ``BitVec.sle
  |>.insert ``BitVec.decEq
  |>.insert ``BitVec.and
  |>.insert ``BitVec.or
  |>.insert ``BitVec.xor
  |>.insert ``BitVec.shiftLeftHW
  |>.insert ``BitVec.shiftRightHW
  |>.insert ``BitVec.sshiftRight'
  |>.insert ``Vector.get
  |>.insert ``Vector.extract
  |>.insert ``Mealy.pure
  |>.insert ``Mealy.scan
)
end Primitives

-- TODO, denylist (or new list) which is used to only prevent unfolding if at least one argument to the function is unknown (contains meta or free variable), otherwise should reduce like regular since the result is guaranteed not to contain a free or meta var if it doesn't have any to start with. This way we can do more compile-time computation without getting blocked when we don't need to be.
-- Note, if the function is over-applied and there's meta/free vars in the overapplied arguments, that doesn't matter for the purpose of unfolding the function.
def whnfEvalEta (e:Expr): MetaM Expr := @Hdlean.Meta.whnfEvalEta denylist e

def unfoldDefinitionEval? := fun body => withDenylist denylist (Hdlean.Meta.unfoldDefinitionEval? body)

/-- A function is synthesizable if all arguments and the return type are synthesizable. This means that they either can be erased (`Sort _`) or have a known unboxed size. This also works for a function with 0 args (a type). -/
-- TODO, this should take a flag for if unwrapping Mealy when checking synthesizable. Then we have `synthesizable α (mealy:=false) → synthesizable (Mealy α) (mealy:=true)`. This enables saying `α → Mealy β` is synthesizable (if `α` and `β` are), but `α → Mealy (Mealy β)` is not. Maybe call it `time_dim` where `time_dim` starts at `1` since we have `1` dimension of time and then inside a `Mealy` the time_dim goes to `0`, since we have no time dimension left? Then everything is implicitly constant across remaining unspecified time dimensions.
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
  trace[hdlean.compiler.compileFieldProj] "compiling field projection:{Format.line}\
of: {constructedVal}{Format.line}\
field: {fieldIdx}"
  let .some shape ← bitShape? constructedValType | throwError "HDLean Internal Error: field projection of type without bitShape: {constructedValType}"
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
  let .some fieldShape ← bitShape? fieldType | throwError "field type has unknown bit shape: {fieldType}"
  addItem <| .var {name, type := ← getHWType fieldShape}
  addItem <| .assignment (.identifier name) (.bitSelect constructedVal [start:start+width])
  return .identifier name

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
  trace[hdlean.compiler.compileRecursor] "compiling recursor {recursor.name}
params = {args[:recursor.numParams]}
motive = {args[recursor.numParams:recursor.numParams+recursor.numMotives]}
minors = {args[recursor.getFirstMinorIdx:recursor.getFirstIndexIdx]}
indices = {args[recursor.getFirstIndexIdx:recursor.getMajorIdx]}
major = {args[recursor.getMajorIdx]!}
extra args = {args[recursor.getMajorIdx+1:]}"
  if recursor.numMotives != 1 then throwError "Number of motives != 1 for {recursor.name}"
  if args.size < recursor.getMajorIdx+1 then throwError "Recursor {recursor.name} underapplied"
  if args.size > recursor.getMajorIdx+1 then throwError "TODO: extra args: {args[recursor.getMajorIdx+1:]}"
  let motive ← reduce args[recursor.numParams]!
  let major := args[recursor.getMajorIdx]!
  -- Return type is found by applying indices and major premise to motive.
  -- If the type depends on the major premise's values this will fail, otherwise whnf will simplify to the monomorphic type. The `+1` is for the major argument.
  let retType ← whnfEvalEta <| mkAppN motive args[recursor.getFirstIndexIdx:recursor.getFirstIndexIdx+recursor.numIndices+1]
  trace[hdlean.compiler.compileRecursor] "retType = {retType}"
  if retType.isProp then return ValueExpr.literal "/*ZST: rec eliminates to Prop */"
  let minors := args[recursor.getFirstMinorIdx:recursor.getFirstIndexIdx].toArray
  if !(← forallIsSynthesizable retType) then throwError "Return type of motive not synthesizable: {retType}"
  trace[hdlean.compiler.compileRecursor] "compiling major val"
  let majorVal ← compileValue major
  let majorType ← inferType major
  let majorInductVal ← Lean.getConstInfoInduct recursor.getMajorInduct
  trace[hdlean.compiler.compileRecursor] "compiling {minors.size} ctor cases"
  let cases ← minors.mapIdxM fun idx minor => do
    trace[hdlean.compiler.compileRecursor] "compiling minor for ctor {idx}"
    let ctorVal ← Lean.getConstInfoCtor majorInductVal.ctors[idx]!
    let tagVal ← compileValue <| mkAppN (.const ``Fin.mk []) #[
      .lit <| .natVal (minors.size),
      .lit <| .natVal idx,
      .const ``lcProof []
    ]
    -- Infer field types from minor premise's argument types
    let fieldTypes ← (Array.range ctorVal.numFields).mapM fun fieldIdx => lambdaTelescope minor fun args _body => inferType args[fieldIdx]!
    -- Extract fields with `compileFieldProj`.
    let fieldVals ← (Array.range ctorVal.numFields).mapM fun fieldIdx => compileFieldProj majorVal majorType ctorVal fieldIdx fieldTypes[fieldIdx]!
    let binderNames ← (Array.range ctorVal.numFields).mapM fun fieldIdx => mkFreshUserName (.num (ctorVal.name ++ `field) fieldIdx)
    -- Apply minor premise to extracted fields.
    -- TODO apply inductive hypothesis or check it exists and fail.
    let result ← withLocalDeclsDND (binderNames.zip fieldTypes) fun fieldFVarIds => do
      let mapping := fieldFVarIds.mapIdx (fun i fvarId => (fvarId.fvarId!, fieldVals[i]!))
      withReader (fun ctx => {ctx with env := ctx.env.insertMany mapping})
        <| compileValue (mkAppN minor fieldFVarIds)
    return (tagVal, result)
  trace[hdlean.compiler.compileRecursor] "compiled {minors.size} ctor cases"
  let recRes ← mkFreshUserName (recursor.getMajorInduct ++ `recRes |>.str ((ToString.toString retType).takeWhile fun c => !c.isWhitespace))
  let .some retType ← bitShape? retType | throwError "return type unknown bit shape: {retType}"
  let retHWType ← getHWType retType
  addItem <| .var { name := recRes, type := retHWType }
  match minors.size with
  | 0 => addItem <| ModuleItem.assignment (.identifier recRes) undefinedValue
  | 1 => addItem <| ModuleItem.assignment (.identifier recRes) cases[0]!.snd
  | _ =>
    let some majorShape ← bitShape? majorType | throwError "Major type not synthesizable:
major = {major}
majorVal = {majorVal}
majorType = {majorType}"
    let majorTag ← mkFreshUserName (recursor.getMajorInduct ++ `tag)
    addItem <| .var { name := majorTag, type := ← tagHWType majorShape }
    addItem <| .assignment (.identifier majorTag) (.bitSelect majorVal [0:majorShape.tagBits])
    addItem <| .alwaysComb [.conditionalAssignment .blocking (.identifier recRes) retHWType (.identifier majorTag) (← getHWType majorShape) cases.toList (.some undefinedValue)]
  return .identifier recRes

partial def compileList (list: Expr) : CompilerM (List ValueExpr) := do
  let (fn, args) := (← whnfEvalEta list).getAppFnArgs
  match fn with
  | ``List.cons =>
    let #[_α, head, tail] := args | throwError invalidNumArgs args fn
    return .cons (← compileValue head) (← compileList tail)
  | ``List.nil => return []
  | fn => throwError "HDLean Internal Error: {fn} not a List constructor"

/-- Compile a constructor.

By default this is done in the opposite way that a FieldProjection is compiled, but there are some special cases.
 -/
partial def compileCtor (ctor : ConstructorVal) (levels: List Level) (args : Array Expr) : CompilerM ValueExpr := do
  trace[hdlean.compiler.compileCtor] "compiling ctor: {ctor.name}"
  match ctor.name with
  | ``Vector.mk =>
    let #[_α, _n, toArray, _h] := args | throwError invalidNumArgs args ctor.name
    let (fn, args) := (← whnfEvalEta toArray).getAppFnArgs
    assert! fn == ``Array.mk
    let #[_α, toList] := args | throwError invalidNumArgs args ``Array.mk
    let vals ← compileList toList
    return .concatenation vals
  | _ =>
  let params := args.extract 0 ctor.numParams
  let fields := args.extract ctor.numParams (ctor.numParams+ctor.numFields)
  if args.size > ctor.numParams+ctor.numFields then throwError "TODO: extra ctor args"
  trace[hdlean.compiler.compileCtor] "params = {params}"
  trace[hdlean.compiler.compileCtor] "fields = {fields}"
  let inductType := mkAppN (.const ctor.induct levels) params
  let .some shape ← bitShape? inductType | throwError "inductive type has unknown bit shape: {inductType}"
  let tagWidth := shape.tagBits
  let fieldShapes ← match shape with
    | .union variants =>
      let .some variant := variants[ctor.cidx]? | throwError "ctor idx invalid: {ctor.cidx} / {variants.size}"
      let .struct fieldShapes := variant | throwError "HDLean Internal Error: variant shape for constructor {ctor.cidx} of {ctor.induct} is not struct "
      pure fieldShapes
    | .struct fieldShapes => pure fieldShapes
  if fieldShapes.size != fields.size then throwError "HDLean Internal Error: field count mismatch for {ctor.name} (expected {fieldShapes.size}, got {fields.size})"
  let fieldVals ← fields.mapM (fun field => do
    trace[hdlean.compiler.compileCtor] "compiling field value"
    compileValue field
  )
  trace[hdlean.compiler.compileCtor] "compiling tag value"
  let tagVal ← if tagWidth == 0 then pure #[] else
    let tagVal ← compileValue <| mkAppN (.const ``BitVec.ofNat []) #[
      .lit <| .natVal tagWidth,
      .lit <| .natVal ctor.cidx,
    ]
    pure #[tagVal]
  return .concatenation <| Array.toList <| fieldVals ++ tagVal

partial def resetName := `rst
partial def clockName := `clk
partial def activeLowResetValue := compileValue (mkNatLit 0)
partial def activeHighResetValue := compileValue (mkNatLit 1)

partial def invalidNumArgs (args: Array α) (fn: Name): MessageData := m!"Invalid number of arguments ({args.size}) for {fn}"

/-- Given a type of `Mealy α`, return `α` -/
partial def unwrapMealyType (e:Expr): CompilerM Expr := do
  let (fn, args) := e.getAppFnArgs
  let #[α] := args | throwError invalidNumArgs args fn
  return α

/-- Given an expression `Mealy.scan s f reset` which represents a registered state element,
return the output `ValueExpr` and `HWType` corresponding to `o` in the following (where <<>> indicates lean and the rest is SystemVerilog):
```systemverilog
logic var /*space for σ*/ state = <<compileValue reset>>
logic var /*space for σ*/ new_state
logic var /*space for β*/ o
assign {o, new_state} = <<compileValue f s state>>
always_ff @(posedge clk)
  state <= new_state
```
-/
partial def compileMealyScan (e:Expr) : CompilerM (ValueExpr × HWType) := do
  let (fn, args) := e.getAppFnArgs
  if fn != ``Mealy.scan then throwError "HDLean Internal Error: fn not Mealy.scan"
  let invalidNumArgs := fun () => invalidNumArgs args fn
  let #[α,β,σ,s,f,reset] := args | throwError invalidNumArgs ()
  trace[hdlean.compiler.compileMealyScan] "compiling mealy scan{Format.line}α={α},{Format.line}β={β},{Format.line}σ={σ},{Format.line}s={s},{Format.line}f={f},{Format.line}reset={reset}"
  trace[debug] "s={s},f={f},reset={reset}"
  let stateName ← mkFreshUserName `registerState
  let newStateName ← mkFreshUserName `newRegisterState
  let outputName ← mkFreshUserName `registerOutput
  let .some σShape ← bitShape? σ | throwError "σ has unknown bit shape: {σ}"
  let .some βShape ← bitShape? β | throwError "β has unknown bit shape: {β}"
  let σHWType ← getHWType σShape
  let βHWType ← getHWType βShape
  addItem <| .var { name := stateName, type := σHWType }
  addItem <| .var { name := newStateName, type := σHWType }
  addItem <| .var { name := outputName, type := βHWType }
  trace[hdlean.compiler.compileMealyScan] "compiling reset value"
  let resetValue ← compileValue reset
  trace[hdlean.compiler.compileMealyScan] "compiling scan input"
  let sValue ← compileValue s
  -- TODO use reset value in initial block.
  -- TODO combine `withLocalDeclD` with modifying `CompileContext` instead of manually doing both.
  withLocalDeclD `s (← unwrapMealyType <| ← inferType s) fun sFVar => do
  withLocalDeclD `state (← inferType reset) fun stateFVar => do
  withReader (fun ctx => {ctx with env := (
    ctx.env
      |>.insert sFVar.fvarId! sValue
      |>.insert stateFVar.fvarId! (.identifier stateName)
  )}) do
    trace[hdlean.compiler.compileMealyScan] "compiling scan function"
    let appliedF ← compileValue (mkApp2 f sFVar stateFVar)
    addItem <| .assignment
      (.concatenation [.identifier outputName, .identifier newStateName])
      (appliedF)
    addItem <| .alwaysClocked .posedge clockName [
      Stmt.conditionalAssignment .nonblocking
        (.identifier stateName) σHWType
        (.identifier resetName) ResetHWType
        [(← activeLowResetValue, resetValue)] -- TODO this is only active low, haven't yet implemented customization change based on domain.
        (.some (.identifier newStateName))
    ]
  return (.identifier outputName, βHWType)

-- TODO: Return `BitShape` or `HWType` of returned `ValueExpr` and use that instead of doing `inferType` since `inferType` is the wrong thing to use when encountering `Mealy α`. Alternative (maybe uglier?) solution is to write custom `HWInferType` or `HWBitShape?`.
partial def compileValue (e : Expr) : CompilerM ValueExpr := do
  trace[hdlean.compiler.compileValue] "compiling value: {e}"
  let e ← whnfEvalEta e
  trace[hdlean.compiler.compileValue] "whnfEvalEta: {e}"
  if let .some (.union #[]) := ← bitShape? (← inferType e) then
    trace[hdlean.compiler.compileValue] "value is a zst"
    return ValueExpr.literal "/*ZST*/"
  match e with
  | .fvar fvarId => do
    match (← read).env.get? fvarId with
    | .some value => pure value
    | .none => throwError "Unknown free variable: {fvarId}"
  | .app .. | .const .. =>
    let (fn, args) := e.getAppFnArgs
    let invalidNumArgs := fun () => invalidNumArgs args fn
    if fn.isAnonymous then throwError "HDLean Internal Error: non-constant application {e}"
    match fn with
    | ``BitVec.ofFin =>
      let #[_w, toFin] := args | throwError invalidNumArgs ()
      let val ← compileValue toFin
      return val
    | ``Fin.mk =>
      let #[n, val, _isLt] := args | throwError invalidNumArgs ()
      let val ← compileValue val
      let n ← try unsafe Meta.evalExpr Nat (.const ``Nat {}) n
        catch e => throwError "Can't compile Fin.mk: can't evaluate upper bound = '{n}': {e.toMessageData}"
      let lit := match val.emit with |.none => "" |.some val => s!"{n.ceilLog2}'{val}" -- Add width annotation
      return .literal lit
    | ``BitVec.mul =>
      let #[_n, x, y] := args | throwError invalidNumArgs  ()
      let x ← compileValue x
      let y ← compileValue y
      return .binaryOp .mul x y
    | ``BitVec.add =>
      let #[_n, x, y] := args | throwError invalidNumArgs ()
      let x ← compileValue x
      let y ← compileValue y
      return .binaryOp .add x y
    | ``BitVec.sub =>
      let #[_n, x, y] := args | throwError invalidNumArgs ()
      let x ← compileValue x
      let y ← compileValue y
      return .binaryOp .sub x y
    | ``BitVec.ult =>
      let #[_n, x, y] := args | throwError invalidNumArgs ()
      let x ← compileValue x
      let y ← compileValue y
      return .binaryOp .lt x y
    | ``BitVec.slt =>
      let #[_n, x, y] := args | throwError invalidNumArgs ()
      let x ← compileValue x
      let y ← compileValue y
      return .binaryOp .lt (.castOp .signed x) (.castOp .signed y)
    | ``BitVec.ule =>
      let #[_n, x, y] := args | throwError invalidNumArgs ()
      let x ← compileValue x
      let y ← compileValue y
      return .binaryOp .le x y
    | ``BitVec.sle =>
      let #[_n, x, y] := args | throwError invalidNumArgs ()
      let x ← compileValue x
      let y ← compileValue y
      return .binaryOp .le (.castOp .signed x) (.castOp .signed y)
    | ``BitVec.decEq =>
      let #[_w, x, y] := args | throwError invalidNumArgs ()
      let x ← compileValue x
      let y ← compileValue y
      return .binaryOp .eq x y
    | ``BitVec.and =>
      let #[_w, x, y] := args | throwError invalidNumArgs ()
      let x ← compileValue x
      let y ← compileValue y
      return .binaryOp .and x y
    | ``BitVec.or =>
      let #[_w, x, y] := args | throwError invalidNumArgs ()
      let x ← compileValue x
      let y ← compileValue y
      return .binaryOp .or x y
    | ``BitVec.xor =>
      let #[_w, x, y] := args | throwError invalidNumArgs ()
      let x ← compileValue x
      let y ← compileValue y
      return .binaryOp .xor x y
    | ``BitVec.shiftLeftHW =>
      let #[_m, _n, x, s] := args | throwError invalidNumArgs ()
      let x ← compileValue x
      let s ← compileValue s
      return .binaryOp .sll x s
    | ``BitVec.shiftRightHW =>
      let #[_m, _n, x, s] := args | throwError invalidNumArgs ()
      let x ← compileValue x
      let s ← compileValue s
      return .binaryOp .srl x s
    | ``BitVec.sshiftRight' =>
      let #[_n, _m, a, s] := args | throwError invalidNumArgs ()
      let a ← compileValue a
      let s ← compileValue s
      return .binaryOp .sra a s
    | ``Vector.get =>
      let #[α, _n, xs, i] := args | throwError invalidNumArgs ()
      let xs ← compileValue xs
      let i ← compileValue i
      let .some αShape ← bitShape? α | throwError "Vector type has unknown bit shape: {α}"
      let αWidth := αShape.totalWidth
      return .dynamicBitSelect xs (.slice (start:=i) (len:=1) (scale:=αWidth))
    | ``Vector.extract =>
      let #[α, n, xs, start, stop] := args | throwError invalidNumArgs ()
      let n ← try unsafe Meta.evalExpr Nat (.const ``Nat {}) n
        catch e => throwError "Can't compile Vector.extract: can't evaluate vector length = '{n}': {e.toMessageData}"
      let start ← try unsafe Meta.evalExpr Nat (.const ``Nat {}) start
        catch e => throwError "Can't compile Vector.extract: can't evaluate argument 'start' = '{start}': {e.toMessageData}"
      let stop ← try pure <| (← unsafe Meta.evalExpr Nat (.const ``Nat {}) stop).min n
        catch e => throwError "Can't compile Vector.extract: can't evaluate argument 'stop' = '{stop}': {e.toMessageData}"
      if start ≥ stop then return .zst
      let .some αShape ← bitShape? α | throwError "Vector type has unknown bit shape: {α}"
      let αWidth := αShape.totalWidth
      return .bitSelect (← compileValue xs) [start*αWidth:stop*αWidth]
    | ``Mealy.pure =>
      let #[_α, a] := args | throwError invalidNumArgs ()
      -- `Mealy.pure` is treated transparently.
      compileValue a
    | ``Mealy.scan =>
      Prod.fst <$> compileMealyScan e
    | fn =>
      match ← Lean.getConstInfo fn with
      | .recInfo val => compileRecursor val args
      | .ctorInfo val => compileCtor val e.getAppFn.constLevels! args
      | _ => throwError "Unsupported function application: {e}"
  | .lit e => return .literal <| match e with |.natVal n => s!"{n}" |.strVal s => s
  | .proj typeName idx s =>
    match typeName, idx with
    | ``Fin, 0 => compileValue s
    | _, _ => compileExprProj typeName idx s
  | _ => throwError "Unsupported expression: {e}"
end

partial def compileAssignment (space : SpaceExpr) (e : Expr) : CompilerM Unit := do
  match e with
  | .mdata _ body => compileAssignment space body
  -- TODO, does this letE case make any sense?
  | .letE _ _ value body _ => do
      let valueVal ← compileValue value
      let valueType ← inferType value
      let .some valueShape ← bitShape? valueType | throwError "value has unknown bit shape: {valueType}"
      let name ← mkFreshUserName `let
      addItem <| .var { name, type := ← getHWType valueShape }
      addItem <| .assignment (.identifier name) valueVal
      let letFVar ← mkFreshFVarId
      withReader (fun ctx => { ctx with env := ctx.env.insert letFVar (.identifier name) }) do
        compileAssignment space (body.instantiate1 (.fvar letFVar))
  | .app .. | .const .. | .proj .. =>
      let value ← compileValue e
      addItem <| .assignment space value
  | e => throwError "Unsupported statement expression: {e}"

/-- Add module(s) corresponding to a function to the back of the list to be emitted as well as returning it. `fun x y z => body` becomes
  ```systemverilog
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
  lambdaTelescope (← etaExpand <| ← whnfEvalEta fn) fun args body => do
  trace[hdlean.compiler.compileFun] "compiling {fn}
args = {args}
body = {body}"
  -- If body isn't synthesizable then unfold until it is. Since the top-level function is required to be monomorphic at some point the unfolding will expose a synthesizable signature (worst case by unfolding everything to primitives).
  let (hasClkRst, compiledBody?) ← if !(← forallIsSynthesizable (← inferType body)) then
    let err := fun () body => m!"Function has an unsynthesizable interface (unsynthesizable argument or return type) and this can't be resolved by unfolding the function body:"
      ++ MessageData.nestD m!"{Std.Format.line}body={body},{Std.Format.line}args={args}"
    let body' ← whnfEvalEta body
    match ← withDenylist denylist (unfoldDefinitionEval? body') with
    | .some body' =>
      if body' == body then throwError err () body'
      return ← compileFun (← mkLambdaFVars args body')
    | .none =>
      -- TODO this is probably wrong. e.g. `Mealy (Mealy BitVec 3)`, should not be synthesizable.
      -- Probably need a flag in `CompileM` keeping track of currently compiling in time or space, or if currently compiling inside a context with a clock, or compiling inside a scan statement, etc...
      if body.getAppFn.constName? == ``Mealy.pure then
        let .some body ← Hdlean.Meta.unfoldDefinitionEval? body | throwError "Can't unfold Mealy.pure"
        return ← compileFun <| ← whnfEvalEta <| ← mkAppM ``Mealy.value #[body]
      else if body.getAppFn.constName? == ``Mealy.scan then
        let compiledBody ← compileMealyScan body
        pure <| (true, Option.some compiledBody)
      else
        throwError err () body'
    else pure (false, Option.none)
  let retHWType ← match compiledBody? with
  | .none =>
    let retTy ← Meta.returnTypeV body args
    let .some shape ← bitShape? retTy | throwError "return type unknown bit shape {retTy}"
    getHWType shape
  | .some (_, compiledBodyHWType) => pure compiledBodyHWType
  let mut parameters := #[]
  let mut ports := #[]
  -- Add clock and reset signals if needed.
  if hasClkRst then
    ports := ports.push {
      name := clockName
      type := ClockHWType
      direction := .input
    } |>.push {
      name := resetName
      type := ResetHWType
      direction := .input
    }
  -- Convert function arguments to module ports.
  for arg in args do
    let argType ← inferType arg
    let .some argShape ← bitShape? argType | throwError "Argument is unsynthesizable: {arg}"
    ports := ports.push {
      name := ← arg.fvarId!.getUserName,
      type := ← getHWType argShape,
      direction := .input
    }
  ports := ports.push {
    name := `o,
    type := retHWType,
    direction := .output
  }
  -- Intantiate the function and assign the result of the function call to the output port.
  let ctx : CompileContext := {
    env := ← args.foldlM (init := (← read).env) fun map arg => do
      let name := ← arg.fvarId!.getUserName
      return map.insert arg.fvarId! (.identifier name)
  }
  -- Assign to output (if type has nonzero size).
  if retHWType.width != 0 then
    match compiledBody? with
    | .none => withReader (fun _ => ctx) <| compileAssignment (.identifier `o) body
    | .some (compiledBodyValue, _) => addItem <| .assignment (.identifier `o) compiledBodyValue
  else
    addItem <| .assignment (.identifier `o) (.zst)
  -- Save the module to the CompileM state of modules to emit and return it.
  let name ← mkFreshUserName `mod
  let mod := { name, parameters, ports, items := (←get).items }
  modify fun x => {x with items:=#[], modules:=x.modules.push mod}
  return mod

def compileDecl (name : Name) : CompilerM Module := do
  if let .some mod := (← get).cache.find? name then return mod
  let mod ← compileFun (.const name [])
  assert! mod == (← get).modules.back!
  let compiledMod := {mod with name}
  -- Fix the name of the module removing the old version, and cache the new module.
  -- TODO: the name of the current stack should be in `CompilerM` to make error messages nicer and so that modules are named correctly on creation instead of needing this fixup step.
  modify fun x => {x with cache := x.cache.insert name compiledMod, modules := x.modules.pop.push compiledMod}
  return compiledMod

/-- Emit `Std.Format` of the final SystemVerilog code for the given constant. -/
def emit (name : Name) : MetaM Std.Format := do
  let mod ← withTransparency .all <| compileDecl name |>.run'
  return mod.emit

/- Below is effectively a REPL of random tests. -/
-- TODO use an actual unit testing framework
-- TODO delete.
section Testing
/- def f: Bool:= .true
#eval do println! ← emit (``f)
#check Nat.add._sunfold
#print Nat.add._sunfold
#print Nat.add
def g: BitVec 3 := 68#3
#eval do println! ← emit (``g)
def add_mul (x y z: BitVec w) := x + y * z
def add_mul_mono := add_mul (w:=4)
#eval do println! ← emit (``add_mul_mono)
def add (x y: BitVec w) := x + y
def add_mono := add (w:=4)
#eval do println! ← emit (``add_mono)
def add_mul' (x y z: BitVec w) := (add x y) * z
def add_mul_mono' := add_mul' (w:=4)

def tmp : (BitVec 4) → (BitVec 4) → (BitVec 4) := (inferInstanceAs (Add (BitVec 4))).1
#eval do println! (← delta? (.const ``tmp [])).get!

#eval do println! ← emit (``add_mul_mono')

def mynot (x: Bool): Bool := match x with
  | false => true
  | true => false
def mynotL (x: LBool): LBool := match x with
  | .true => .false
  | .false => .true
  | .undef => .undef
def mynotE (x: PSum Bool Bool): Bool := match x with
  | .inl v => mynot v
  | .inr v => mynot v
def mynotE' (x: Sum LBool LBool): LBool := match x with
  | .inl v => mynotL v
  | .inr v => mynotL v
def mynotE'' (x: Sum Bool LBool): Sum LBool Bool := match x with
  | .inl v => .inr <| mynot v
  | .inr v => .inl <| mynotL v
def mynotEIf (x: PSum LBool LBool): Fin 3 :=
  if let .inl _ := x then 0
  else if let .inr _ := x then 1
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
def MyS.test1 : MyS:= {a:=1,b:=2,c:=3:MyS}
def MyS.test2 : Fin 2:= {a:=1,b:=2,c:=3:MyS}.a
def MyS.test3 (a: Fin 2): Fin 2:= {a,b:=2,c:=3:MyS}.a
def MyS.test4 (s: MyS): Fin 2:= s.a
def MyS.test5 (s: MyS): Fin 3:= s.b
def MyS.test6 (s: MyS) := s.c
#eval do println! ← emit (``MyS.test1)
#eval do println! ← emit (``MyS.test2)
#eval do println! ← emit (``MyS.test3)
#eval do println! ← emit (``MyS.test4)
#eval do println! ← emit (``MyS.test5)
#eval do println! ← emit (``MyS.test6)
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
def len_manual_mono : Fin 3 := len_manual #v[0,1]
#eval len_manual #v[1,2,3]
#reduce len_manual._unsafe_rec #v[1,2,3]


#check PSigma.mk
#check (@PSigma.mk Nat (fun n => Vector Nat n) 2 #v[0,1]).1

inductive MyTypeWithIndices: Bool → Type where
  | mk1 : MyTypeWithIndices .true
  | mk2 : MyTypeWithIndices .false
#check MyTypeWithIndices.rec

set_option pp.proofs true in
#check Acc.rec
#check PSum.rec
-- #eval show Bool from @Acc.rec (r:=Eq) (motive:=fun x y => Bool) _ (fun x y z => x) .true (@lcProof (Acc _ _))
#reduce fun (n:Nat) => (Nat.rec (motive := fun _ => List Nat) ([]) (fun x y => y.cons x) (n+2) : List Nat)
#reduce True.rec (motive:=fun _ => String) "start" .intro
noncomputable def testSubsingletonElim := True.rec (motive:=fun _ => String) "start" .intro
#eval whnfEvalEta (.const ``testSubsingletonElim [])
#eval Lean.Meta.whnf (.const ``testSubsingletonElim [])
#check WellFounded.rec
set_option trace.hdlean.compiler true
#eval do println! ← emit (``len_manual_mono)
partial def len_manual' (x: Vector α n): Fin (n+1) := x.elimAsList fun l hl => match l with
  | .nil => ⟨0, by omega⟩
  | .cons a b =>
    have : n - 1 + 1 + 1 = n + 1 := by
      have : n > 0 := by exact?
      omega
    1 + (len_manual' (n:=n-1) (.mk b.toArray (by exact?)) |>.castSucc |> cast (by rw [this]))
unsafe def len_manual_mono' : Fin 3 := len_manual' #v[0,1]
set_option trace.hdlean.compiler.compileRecursor true
set_option trace.hdlean.compiler.compileValue true
set_option trace.Meta.whnf true in
#eval do println! ← emit (``len_manual_mono')
#eval withTransparency .all <| Meta.unfoldDefinitionEval? (.const ``len_manual' [])
#eval delta? (.const ``len_manual' [])
#eval do return ← Lean.getConstInfo ``len_manual_mono'
set_option trace.debug true in
#eval do return Compiler.implementedByAttr.getParam? (← getEnv) ``len_manual'
#check len_manual'._unsafe_rec
#print len_manual'._unsafe_rec
#print len_manual._unsafe_rec
def a.imp: Fin 8 := 4
@[implemented_by a.imp]
opaque a: Fin 8 := 3
#eval Lean.Compiler.LCNF.toDecl (``a) |>.run
#eval do println! ← emit (``a)
#eval do println! ←whnfEvalEta (.const ``a [])
def b.imp : BitVec 8 → BitVec 8 := fun n => n + 2
set_option trace.hdlean.compiler true in
@[implemented_by b.imp]
opaque b (n:BitVec 8): BitVec 8
#eval do println! ← emit (``b)

#eval do withTransparency .all <| monadLift (n:=MetaM) <| delta? (.const ``a [])
#eval do return ← Lean.getConstInfo ``a
set_option trace.debug true in
#eval do trace[debug] (← Lean.getConstInfo ``len_manual').value! true
#eval do return Compiler.implementedByAttr.getParam? (← getEnv) ``len_manual'
#print a
#eval do println! ← emit ``a
#eval a
#print len_manual'
#print len_manual._unary
#eval Lean.Compiler.LCNF.toDecl (``len_manual) |>.run
#check Lean.Compiler.LCNF.LetValue.fvar
#eval len_manual_mono'

def wf_fake._size: Bool → Nat
  | .false => 0
  | .true => 1
def wf_fake (b _b2:Bool): Unit := if b then wf_fake false false else ()
  termination_by wf_fake._size b
  decreasing_by
    rename_i h
    simp [wf_fake._size, h]
#print wf_fake
#print wf_fake._unary
#eval do println! ← withTransparency .all <| Lean.Meta.whnf (Expr.const ``wf_fake [])
#eval do println! ← withTransparency .all <| whnfEvalEta (Expr.const ``wf_fake [])
set_option trace.debug true in
#eval do trace[debug] Expr.eta <| ← withTransparency .all <| Lean.Meta.whnf (Expr.const ``wf_fake._unary [])
set_option trace.debug true in
#eval do trace[debug] Expr.eta <| ← withTransparency .all <| whnf (mkAppN (Expr.const ``wf_fake []) #[(.const ``Bool.false []), (.const ``Bool.false [])])
#check WellFounded.fix_eq
#eval Lean.Compiler.LCNF.toDecl (``wf_fake._unary) |>.run
#eval Lean.Compiler.LCNF.toDecl (``WellFounded.fix) |>.run
#check List.rec
def _root_.Nat.isEven: Nat → Bool
  | 0 => .true
  | n+1 => not n.isEven
#print Nat.isEven
#eval withTransparency .all <| whnfEvalEta <| (Expr.const ``Nat.isEven []).app (mkRawNatLit 1)
#check Nat.rec


#eval do
  let e := (Expr.const ``len_manual_mono [])
  let e ← withTransparency .all <| reduce e
  dbg!' ← reduceRecMatcher? e
  return ToString.toString e
#eval Lean.getConstInfoRec ``Acc.rec
#check Acc.rec
#check Eq.rec
#eval do println! ← withTransparency .all <| whnfEvalEta (.const ``len_manual_mono [])
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
def saturatingAddMono := saturatingAdd (w:=2)
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
#eval BitVec.ofInt 2 (-1)
#eval BitVec.ofInt 2 (-1) |>.toInt

#eval do println! ← emit (``t)
#eval do println! ← emit (``t2)
#eval do println! ← emit (``t3)
#eval do println! ← emit (``saturatingAddMono) -/

end Testing

section TestingMealy
def use_mealy_pure : Mealy (BitVec 3) := Mealy.pure 1

#eval do println! ← emit (``use_mealy_pure)

def use_mealy_scan : Mealy (BitVec 3) := Mealy.scan (use_mealy_pure) fun v (st:BitVec 4) => (v, st)
#eval do println! ← emit (``use_mealy_scan)
def use_mealy_scan' : Mealy (BitVec 3) := Mealy.scan (id use_mealy_pure) fun v (st:BitVec 3) => (v+st, st)
#eval do println! ← emit (``use_mealy_scan')
def use_mealy_scan'' : Mealy (BitVec 3) := Mealy.scan (use_mealy_scan') fun v (st:BitVec 3) => (v+2*st, st+1)
#eval do println! ← emit (``use_mealy_scan'')
end TestingMealy

def cyclic_fibonacci_series : Mealy (BitVec n) :=
  (Mealy.pure ()).scan (reset:=(0,1))
    (fun () ((prev2: BitVec n), (prev1: BitVec n)) =>
      let next := prev2+prev1
      (prev2, (prev1,next)))

open NotSynthesizable in
#eval simulate (cyclic_fibonacci_series (n:=16)) (Array.replicate 20 ()) |>.take 20 |>.map fun x => x.fst.value
open NotSynthesizable in
#eval simulate (cyclic_fibonacci_series (n:=16)) (Array.replicate 20 ()) |>.take 20 |>.map fun x => x.fst.repr' 0 (inst:=by rw [x.snd.left]; reduceAll; exact inferInstance) |> ToString.toString

def cyclic_fibonacci_series_mono := cyclic_fibonacci_series (n:=18)
#eval do println! ← emit (``cyclic_fibonacci_series_mono)

/-
TODO, need feedback/mutual recursion to do something like this?
def cyclic_fibonacci_series' : Mealy (BitVec n) :=
  let prev2 := register 0 prev1
  let prev1 := register 1 prev2+prev1
-/

def delay1 [reset:Inhabited α] (s:Mealy α): Mealy α := s.scan (fun v st => (st,v))

-- Ok, this is cool and It Just Works™.
def delayN (n:Nat) [reset:Inhabited α] (s:Mealy α): Mealy α := Id.run do
  let mut s := s
  for _ in [0:n] do
    s := delay1 s
  pure s

def delay1_mono := delay1 (α:=BitVec 3) (cyclic_fibonacci_series)

def delay4 [reset:Inhabited α] (s:Mealy α): Mealy α := delayN 4 s

def delay4_mono := delay4 (α:=BitVec 3) (cyclic_fibonacci_series)

#eval do println! ← emit (``delay1_mono)
#eval do println! ← emit (``delay4_mono)

open NotSynthesizable in
#eval! simulate (delayN 3 (α:=BitVec 14) cyclic_fibonacci_series) (Array.replicate 20 (cast sorry ())) |>.take 20 |>.map fun x => x.fst.value |> ToString.toString
-- TODO, make a `reduce` function using `Hdlean.Meta.whnfEvalEta` so it uses `._unsafe.rec` in order to get stuff like `delay4_mono.σ` to actually evaluate instead of getting stuck in `Acc.rec` madness.

#check Mealy.scan
def feedback (s:Mealy (σ → β × σ)) (reset:σ) : Mealy β :=
  s.scan (reset:=reset) fun f st => f st

def feedback' (f:Mealy (α → σ → β × σ)) (i: Mealy α) (reset:σ) : Mealy β :=
  (.,.)<$>i<*>f|>.scan (reset:=reset) fun (i,f) st => f i st

unsafe def lut_mealy (vals: Array α) [Inhabited α]: Mealy α :=
  Mealy.pure () |>.scan fun () (st:BitVec vals.size) =>
    let rec lookup (w: Nat) (n:BitVec w) (vals:Array α) (h: n < vals.size): α :=
      if h: n = 0 then match vals.back? with
        | .none => vals.back!
        | .some x => x
      else
        have : n ≠ 0 := h
        have : 0 < vals.size := by sorry
        have : 1 ≤ n := by sorry --bv_omega
        let n' := n-1
        have : n' < n := by sorry --bv_omega
        have := by calc
          0 < n := by bv_decide
          n < vals.size := by bv_decide
        lookup w n' vals.pop (by subst n'; simp [*]; admit)
    let v := lookup vals.size 3 vals sorry
    (v, st+1)

#eval 1#3 < 2#3
#eval (1#3-1) < (2#3-1)
#eval (0#3-1) < (1#3-1)

open NotSynthesizable in
#eval! simulate (lut_mealy #[1,2,3,4]) (Array.replicate 20 ()) |>.map fun x => x.fst.value
unsafe def lut_mealy_mono := lut_mealy #[(1:BitVec 3),2,3,4]
-- This won't work until BitVec arithmetic like functions (in this case sub and eq) reduce when fully-applied without free/meta vars even if in the denylist. Because they aren't unfolded this compiles both halves of the if statement forever when it should actually simplify to the recursive half repeatedly with the non-recursive half at the end. It should be able to unfold at compile time since `n` is known at compile time and `n-1` and `n=0` control if the function recurses at all.
-- set_option trace.hdlean.compiler true in
-- set_option trace.Meta.whnf true in
-- set_option maxHeartbeats 1000 in
-- #eval do println! ← emit (``lut_mealy_mono)

def mealy_match (lut: Array (BitVec 3)): Mealy (BitVec 3) :=
  Mealy.pure () |>.scan fun
    | s, Bool.false => if h:s = () then (lut.back!, true) else by contradiction
    | (), b@Bool.true => (lut[0]!, not b)
def mealy_match_mono := mealy_match #[1,2,3,4]
#eval do println! ← emit (``mealy_match_mono)

def mkVec : Vector (BitVec 3) 3 := #v[1,2].push 3
#check Vector.mk
#eval do println! ← emit (``mkVec)
def mkVec' (last: BitVec 3): Vector (BitVec 3) 3 := #v[1,2].push last
#eval do println! ← emit (``mkVec')
def mkVec'' (el: BitVec 3): Vector (BitVec 3 ⊕ BitVec 10) 2 := #v[.inl 1,.inr 2].set 0 (.inl el)
#eval do println! ← emit (``mkVec'')

def indexVec (vec: Vector (BitVec 4) 3): BitVec 4 :=
  vec[1]
def indexVec' (vec: Vector (BitVec 4) 3) (idx: Fin 3): BitVec 4 :=
  vec[idx]
def indexVec'' (vec: Vector (BitVec 4) 3) (fake_idx: Fin 3) (fake_idx2: Fin 3) :=
  vec.extract 1 3
#eval do println! ← emit (``indexVec)
#print indexVec'
#eval do println! ← emit (``indexVec')
#eval do println! ← emit (``indexVec'')
#eval indexVec'' #v[1,2,3] 1 2

def func_on_mealy (s:Mealy Bool): (Mealy Bool):= s.scan fun i st => (i, ())
def use_func_on_mealy : (Mealy Bool):= func_on_mealy (Mealy.pure true |>.scan fun i (st:Bool) => if st then (i,not st) else (not i, not st))

-- For this to work have to finish implement synthesis of functions which take `Mealy` as argument or return.
-- #eval do println! ← emit (``func_on_mealy)
#eval do println! ← emit (``use_func_on_mealy)

def conditional_func (b:Bool): Bool → Bool:= match b with
| .true => id
| .false => not
#print conditional_func
#print conditional_func.match_1

def use_conditional_func (s:Mealy Bool): Mealy (Bool) := s.scan fun i (st:Bool) => match st with
| .false => (conditional_func false i, not st)
| .true => (conditional_func true i, not st)

-- #eval do println! ← emit (``conditional_func)
-- #eval do println! ← emit (``use_conditional_func)
def conditional_func' (_b:Bool) (_i: Bool): Bool := true
def use_conditional_func' (s:Mealy Bool): Mealy (Bool) := s.scan fun i (st:Bool) => match st with
| .false => (conditional_func' false i, not st)
| .true => (conditional_func' true i, not st)
-- set_option trace.hdlean.compiler true in
-- #eval do println! ← emit (``use_conditional_func')

end Hdlean.Compiler
