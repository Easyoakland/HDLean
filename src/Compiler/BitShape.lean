import Lean
import Lean.Meta
import Hdlean.Basic
import Compiler.Netlist

open Lean Lean.Compiler Lean.Compiler.LCNF


namespace Nat
  def ceilLog2:Nat → Nat
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
end Nat

namespace Lean
def isCtorCore (env : Environment) (declName : Name) : Bool :=
  env.findAsync? declName matches some { kind := .ctor, .. }

def isCtor [Monad m] [MonadEnv m] (declName : Name) : m Bool :=
  return isCtorCore (← getEnv) declName
end Lean

namespace Hdlean

inductive BitShape where
  | struct (fields: Array BitShape)
  | union (alternatives: Array BitShape)
  deriving Repr, BEq, Hashable

namespace BitShape

def tagBits : BitShape → Nat
| .union alts => alts.size.ceilLog2
| _ => 0

def totalWidth : BitShape → Nat
  | .struct fields => fields.foldl (init := 0) (fun acc s => acc + s.totalWidth)
  | .union alts => alts.size.ceilLog2 + (alts.foldl (init := 0) (fun acc alt => acc.max alt.totalWidth))

instance : Inhabited BitShape where
  default := .union #[]

structure State where
  cache : Std.HashMap Expr (Option BitShape) := {}

abbrev M := StateRefT State MetaM

def M.run (x : M α) (state: State := {}) : MetaM α :=
  x |>.run' state

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
  partial def ctorBitShape (val : ConstructorVal) (params : Array Expr): M (Option BitShape) := do
    if val.numFields + val.numParams = 0 then return BitShape.struct #[]

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
      let fieldShapes ← fieldFVars.mapM fun fieldFVar => do
        let fieldType ← Lean.Meta.inferType fieldFVar
         -- The field's type may depend on the inductive's parameters (e.g., `α` in `List α`).
        -- We must replace the formal parameter variables with the concrete `params` provided.
        let instantiatedType := fieldType.replaceFVars paramFVars params
        bitShape instantiatedType
      let .some fieldShapes := fieldShapes.mapM fun fieldFVar => fieldFVar | return .none
      return BitShape.struct fieldShapes
    )

  /-- Helper function to compute the size of a fully applied inductive type.  -/
  partial def inductiveBitShape (val : InductiveVal) (params : Array Expr): M (Option BitShape) := do
    -- At this point, if the type is recursive or reflexive then it doesn't have an unboxed representation.
    if val.isRec || val.isReflexive then return .none

    let altShapes ← val.ctors.mapM (fun (name : Name) => do
      ctorBitShape (← Lean.getConstInfoCtor name) params
    )
    let .some altShapes := altShapes.mapM id | return .none
    return BitShape.union altShapes.toArray

  /--
  Calculates the unboxed bit width of a given type expression. Or `.none` if the type doesn't have one.

  Note that propositions and type formers (`type_of% type` = `Sort u` or `... -> Sort u` where `u≠1`) return the same shape as `Empty`, that is, a 0 bit shape.

  This function handles primitive types, inductive types (including structures), constructors, and type aliases.
  It implements a cache to avoid re-computation and to correctly handle recursive types.
  -/
  partial def bitShape (type:Expr) : M (Option BitShape) := Meta.withTransparency .all do
    if (← Lean.Meta.isTypeFormerType type) || (← Lean.Meta.isProp type) then return Option.some default
    if let some saved := (←get).cache[type]? then return saved
    let shape ← match type with
      | .mdata _ e => bitShape e -- Ignore metadata
      | .app .. | .const .. =>
        let (fn, args) := type.getAppFnArgs
        if ← Lean.isInductive fn then
          let val ← Lean.getConstInfoInduct fn
          if args.size < val.numParams then throwError "`{type}` is not fully instantiated"

          -- Special handle some types.
          -- `catch` kernel panics on `Meta.evalExpr`
          -- TODO: use a generic `.hdlean.shape (fn, args) → Shape` function in the namespace of the type instead. This will enable users to use dependant types to synthesize more dynamically sized objects by defining this function themselves. Possibly use an attribute like `[shape f]` to let user control which function to use for the shape info.
          try
            if fn = ``BitVec then
              let length := args[0]!
              let length ← unsafe Meta.evalExpr Nat (.const ``Nat []) length
              return some <| BitShape.struct <| Array.replicate length (← bitShape (.const ``Bool [])).get!
            else if fn = ``Fin then
              let upper_bound := args[0]!
              let upper_bound ← unsafe Meta.evalExpr Nat (.const ``Nat []) upper_bound
              let upper_bound := upper_bound.ceilLog2
              return some <| BitShape.struct <| Array.replicate upper_bound (← bitShape (.const ``Bool [])).get!
            else if fn = ``Vector then
              let .some shape_of_element ← bitShape args[0]! | return .none
              let length ← unsafe Meta.evalExpr Nat (.const ``Nat []) args[1]!
              return some <| BitShape.struct <| Array.replicate length (shape_of_element)
          catch _ex => return none

          inductiveBitShape val args
        else if ← Lean.isCtor fn then
          let val ← Lean.getConstInfoCtor fn
          if args.size < val.numParams then throwError "ctor parameters for `{type}` not fully instantiated"

          ctorBitShape val args
        else
          let unfoldedType ← Meta.whnf type
          if unfoldedType != type then -- whnf made progress
            bitShape unfoldedType
          else
            let .some info := (← getEnv).findAsync? fn | throwError "{fn} isn't a constant"
            throwError "{fn} isn't an inductive or constructor, it is {info.kind} with args: {args}"
      | _ => pure none
    modify (fun s => {s with cache := s.cache.insert type shape})
    pure shape
end

/-- ≈ `bitShape.run` -/
def bitShape? := fun e => (bitShape e).run

end BitShape
