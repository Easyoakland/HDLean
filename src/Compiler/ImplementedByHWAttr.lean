import Lean.Meta
import Hdlean.Basic
open Lean

namespace Hdlean.Compiler

structure ImplementedByHw where
  name : Name
  deriving Repr, BEq

-- Adapted from `lean/Lean/Compiler/ImplementedByAttr.lean` and `ReducibilityAttrs`
/-- Extension which tracks information for the `implemented_by_hw` attribute. -/
-- TODO compare this to implementedByAttr. I think it does some extra checks such as making sure the types are equal, the universes are equal, the type isn't implemented as itself...
initialize implementedByHwExt : PersistentEnvExtension (Name × ImplementedByHw) (Name × ImplementedByHw) (NameMap ImplementedByHw) ← registerPersistentEnvExtension {
  name := `implementedByHwCore
  mkInitial := pure {}
  addImportedFn := fun imports _ctx => do
    let mut out := ({}:NameMap ImplementedByHw)
    -- Merge imports' implemented_by_hw state with this environment.
    for imp in imports do
      for (name, val) in imp do
        if let .some x := out.get? name then
          if x != val then
            IO.throwServerError (← m!"conflicting import: {name} already has an implemented_by_hw attribute of {x} but another import has an implemented_by_hw attribute of {val}".toString)
        out := out.insert name val
    pure out
  addEntryFn := fun (s : NameMap ImplementedByHw) (p : Name × ImplementedByHw) => s.insert p.1 p.2
  exportEntriesFn := fun m =>
    let r : Array (Name × ImplementedByHw) := m.foldl (fun a n p => a.push (n, p)) #[]
    r.qsort (fun a b => Name.quickLt a.1 b.1)
  statsFn := fun s => "implemented by hw core extension" ++ Format.line ++ "number of local entries: " ++ format s.size
  -- TODO: what should this be?
  -- asyncMode := .async .asyncEnv
}

-- Instead of Attribute.Bu iltin.getIdent, might also be able to use this:
-- let name ← Attribute.Builtin.getId stx
-- if name == Name.anonymous then throwError "missing argument for implementation provided to implemented_by_hw attribute"
def addAttr (declName : Name) (stx : Syntax) (kind : AttributeKind) : AttrM Unit := do
  let fnNameStx ← Attribute.Builtin.getIdent stx
  let fnName ← Elab.realizeGlobalConstNoOverloadWithInfo fnNameStx
  let impl := .mk fnName
  unless kind == AttributeKind.global do throwAttrMustBeGlobal impl.name kind
  let currentState := implementedByHwExt.getState (← getEnv)
  if let .some x := currentState.get? declName then
    throwError "{declName} already has an implemented_by_hw attribute of {x}"
  modifyEnv fun env => implementedByHwExt.addEntry env (declName, impl)

/-- When compiling to hardware the provided constant is used as an implementation instead of the annotated constant. -/
initialize registerBuiltinAttribute {
    ref             := by exact decl_name%
    name            := `implemented_by_hw
    descr           := "name of the Lean constant that is used to implement the annotated constant when hdlean compiles to hardware"
    add             := addAttr
    applicationTime := .afterTypeChecking
 }

def getImplementedByHw? (env : Environment) (declName : Name) :=
  let state := implementedByHwExt.getState env
  state.find? declName |>.map (·.name)
