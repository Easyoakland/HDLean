import Lean
import Lean.Meta
import Hdlean.Basic
import Compiler.Data

open Lean Lean.Compiler Lean.Compiler.LCNF


section
  def Nat.ceilLog2:Nat → Nat
  | 0 => 0
  | 1 => 0
  | n+2 => (n+1).log2 + 1

  example : Nat.ceilLog2 0 = 0 := rfl
  example : Nat.ceilLog2 1 = 0 := rfl
  example : Nat.ceilLog2 2 = 1 := by simp [Nat.ceilLog2, Nat.log2]
  example : Nat.ceilLog2 3 = 2 := by simp [Nat.ceilLog2, Nat.log2]
  example : Nat.ceilLog2 4 = 2 := by simp [Nat.ceilLog2, Nat.log2]
  example : Nat.ceilLog2 5 = 3 := by simp [Nat.ceilLog2, Nat.log2]
  example : Nat.ceilLog2 6 = 3 := by simp [Nat.ceilLog2, Nat.log2]
  example : Nat.ceilLog2 7 = 3 := by simp [Nat.ceilLog2, Nat.log2]
  example : Nat.ceilLog2 8 = 3 := by simp [Nat.ceilLog2, Nat.log2]
  example : Nat.ceilLog2 9 = 4 := by simp [Nat.ceilLog2, Nat.log2]
  example : Nat.ceilLog2 10 = 4 := by simp [Nat.ceilLog2, Nat.log2]
  example : Nat.ceilLog2 16 = 4 := by simp [Nat.ceilLog2, Nat.log2]
  example : Nat.ceilLog2 17 = 5 := by simp [Nat.ceilLog2, Nat.log2]
end

namespace Hdlean.ToData

namespace BitShape
structure State where
  -- /-- Whether getting the BitWidth of a constructor (true → sum of args) or not (false → size of result) -/
  -- fn_ctor : Bool := true
  cache : Std.HashMap Expr Nat := {}

-- abbrev M := StateRefT' Unit State Id
-- abbrev M := StateRefT State Lean.Compiler.LCNF.ToLCNF.M
abbrev M := StateRefT State MetaM

-- #check LCNF.ToLCNF.run

def M.runToMetaM (x : M α) (state: State := {}) : MetaM α :=
  x |>.run' state

def M.run (x : M α) (state: State := {}) : CompilerM α :=
  x |>.run' state |>.run' {}

def M.run' (self : M α) (env: Environment) : IO (Except Exception α) :=
  let self := self.run
  let self := self.run {}
  let self := self.run {fileMap:=default, fileName:=default} {env}
  do
  let self ← self.toIO'
  pure <| Prod.fst <$> self

instance : Inhabited Core.Context where
  default := {fileName:=default, fileMap:=default}

def runMeta (f: MetaM α) (context : Core.Context := default) : M ((α × Meta.State) × Core.State) := do
  let res ← f.run |>.run context {env:=← getEnv}
  pure res
def runMeta' (f: MetaM α) (context : Core.Context := default) : M α := do
  let res ← runMeta f context
  pure res.fst.fst

mutual
  /-- Helper function to compute the size of a constructor of a fully applied inductive type.  -/
  partial def ctorBitWidth (val : ConstructorVal) (params : Array Expr): M Nat := do
    if val.numFields + val.numParams = 0 then return 0

    Lean.Meta.forallTelescope val.type (fun ctorArgs _ => do
      if ctorArgs.size < val.numParams then throwError "Constructor {val.name} has has fewer applied arguments than the inductive's parameter count."

      -- Inductive ctors take, in order, the inductive parameters, then the field parameters.
      let paramFVars := ctorArgs.extract 0 val.numParams
      let fieldFVars := ctorArgs.extract val.numParams ctorArgs.size
      assert! val.numParams + val.numFields = ctorArgs.size

      let rec getFVarDecl (fvarId : FVarId) : MetaM Expr := do
        match (← getLCtx).find? fvarId with
        | some d => return d.type
        | none   => fvarId.throwUnknown

      -- Fields are stored and take space, while parameters must be applied.
      fieldFVars.foldlM (init:=0) fun acc fieldFVar => do
        let fieldType ← Lean.Meta.inferType fieldFVar
         -- The field's type may depend on the inductive's parameters (e.g., `α` in `List α`).
        -- We must replace the formal parameter variables with the concrete `params` provided.
        let instantiatedType := fieldType.replaceFVars paramFVars params
        let fieldSize ← bitWidth instantiatedType
        return acc + fieldSize
    )

  /-- Helper function to compute the size of a fully applied inductive type.  -/
  partial def inductiveBitWidth (val : InductiveVal) (params : Array Expr): M Nat := do
    if val.isRec || val.isReflexive then throwError "{val.name} doesn't have a unboxed size because it is recursive or reflexive"

    let discriminant := val.ctors.length.ceilLog2
    let payload ← val.ctors.foldlM (init:=0) (fun (acc:Nat) (name : Name) => do
      (acc.max .) <$> ctorBitWidth (← Lean.getConstInfoCtor name) params
    )
    return discriminant + payload

  /--
  Calculates the unboxed bit width of a given type expression.

  This function handles primitive types, inductive types (including structures), and type aliases.
  It implements a cache to avoid re-computation and to correctly handle recursive types.
  -/
  partial def bitWidth (type:Expr) : M Nat := Meta.withTransparency .all do
    if let some saved := (←get).cache[type]? then return saved
    let width ← match type with
      | .mdata _ e => bitWidth e -- Ignore metadata
      | .app .. | .const .. =>
        let (fn, args) := type.getAppFnArgs
        if ← Lean.isInductive fn then
          let val ← Lean.getConstInfoInduct fn
          if args.size < val.numParams then throwError "`{type}` is not fully instantiated"

          -- Special handle some types.
          -- TODO: use a generic `.hdlean.shape (fn, args) → Shape` function in the namespace of the type instead. This will enable users to use dependant types to synthesize more dynamically sized objects by defining this function themselves. Possibly use an attribute like `[shape f]` to let user control which function to use for the shape info.
          if fn = ``BitVec then
            let length := args[0]!
            unsafe Meta.evalExpr Nat (.const ``Nat []) length
          else if fn = ``Fin then
            let upper_bound := args[0]!
            let upper_bound ← unsafe Meta.evalExpr Nat (.const ``Nat []) upper_bound
            pure upper_bound.ceilLog2
          else if fn = ``Vector then
            let size_of_element ← bitWidth args[0]!
            let length ← unsafe Meta.evalExpr Nat (.const ``Nat []) args[1]!
            pure <| length * size_of_element
          else
            inductiveBitWidth val args
        else
          let unfoldedType ← Meta.whnf type
          if unfoldedType != type then -- whnf made progress
            bitWidth unfoldedType
          else
            throwError "{fn} isn't an inductive"
      | _ => throwError "Expr has no width: {type}"
    modify (fun s => {s with cache := s.cache.insert type width})
    pure width
end

end BitShape
