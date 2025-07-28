import Lean.Meta
import Hdlean.Basic

namespace HDLean.WHNF

open Lean Meta

/-- Follows regular unfold rules based on transparency but unconditionally prevents unfolding if the constant is in the provided denylist -/
def canUnfoldDenylist (denylist : NameSet) (cfg : Config) (info : ConstantInfo) : CoreM Bool := do
  if denylist.contains info.name then
    return false -- Block unfolding for denylisted constants
  else
    let env ← getEnv
    match cfg.transparency with
    | .all => return true
    | .default => return !(← isIrreducible info.name)
    | _ => return (← isReducible info.name) || isGlobalInstance env info.name

/--
Weak Head Normal Form (WHNF) reduction that skips unfolding denylisted constants.
- `denylist`: Set of constant names (e.g., `NameSet.empty.insert ``BitVec.add`)
- `e`: Expression to reduce

Note: still unfolds/reduces fully applied primitive applications like `Nat.add` even if they are in the denylist.
-/
def whnfWithDenylist (denylist : NameSet) (e : Expr) : MetaM Expr :=
  withTheReader Meta.Context (fun ctx =>
    { ctx with canUnfold? := some (canUnfoldDenylist denylist) }
  ) (whnf e)

/-
def _root_.Nat.myAdd := Nat.add

#eval show MetaM Expr from do
  let e := mkAppN (mkConst ``Nat.add) #[toExpr 3, toExpr 3]
  let denylist := NameSet.empty
  whnfWithDenylist denylist e -- Returns `Lean.Expr.lit (Lean.Literal.natVal 6)`

-- Denylist Nat.add and reduce Nat.add 3 3
#eval show MetaM Expr from do
  let e := mkAppN (mkConst ``Nat.add) #[toExpr 3, toExpr 3]
  let denylist := NameSet.empty.insert `Nat.add
  whnfWithDenylist denylist e -- Returns `Lean.Expr.lit (Lean.Literal.natVal 6)`

-- Denylist Nat.myAdd and reduce Nat.myAdd 3 3
#eval show MetaM Expr from do
  let e := mkAppN (mkConst ``Nat.myAdd) #[toExpr 3]
  let denylist := NameSet.empty.insert `Nat.add |>.insert `Nat.myAdd
  whnfWithDenylist denylist e -- Returns equivalent of `Nat.myAdd 3 3`
-/

/-- Like `whnfImp`, but checks `canUnfold?` before doing primitive reductions so the denylist can prevent primitive reductions even when fully applied. In other words, primitives like `Nat.add` are considered to be unfolded to get reduced. Doesn't cache, so it's slower than `whnfImp`. -/
partial def whnfImp' (e : Expr) (inlineMatchers:=false) : MetaM Expr :=
  withIncRecDepth <| whnfEasyCases e fun e => do
      withTraceNode `Meta.whnf (fun _ => return m!"Non-easy whnf: {e}") do
        checkSystem "whnf"
        let e' ← whnfCore e
        let some canUnfold := Context.canUnfold? (← read) | throwError "no `canUnfold` in `whnfImp'`"
        let env ← getEnv
        let canUnfold ← match do env.find? (← e.getAppFn'.const?).fst with
          | some info => do canUnfold (← getConfig) (info)
          | none => pure Bool.true -- If not a name can't unfold anyway, so reduce like regular.
        if canUnfold then
          match (← reduceNat? e') with
          | some v => pure v
          | none   =>
            match (← reduceNative? e') with
            | some v => pure v
            | none   =>
              match (← unfoldDefinition? e') with
              | some e'' => whnfImp' e'' inlineMatchers
              | none =>
                if !inlineMatchers || (← match (e'.getAppFn).constName? with
                  | .none => pure .none
                  | .some name => getMatcherInfo? name).isNone then pure e'
                else whnfImp' (inlineMatchers:=inlineMatchers) <| ← Compiler.LCNF.inlineMatchers e'
                -- match (← delta? e') with
                -- | .some e'' => pure (← whnfImp' e'')
                -- | none => pure e'
        else pure e

/-- Like `whnfWithDenylist` but using `whnfImp'` so the denylist can include primitive reductions like `Nat.add`. Slower than `whnfWithDenylist` because it uses `whnfImp` which doesn't Cache. -/
def whnfWithDenylist' (denylist : NameSet) (e : Expr) (inlineMatchers:=false)  : MetaM Expr :=
  withTheReader Meta.Context (fun ctx =>
    { ctx with canUnfold? := some (canUnfoldDenylist denylist) }
  ) (whnfImp' e inlineMatchers)

/- -- Denylist Nat.add and reduce Nat.add 3 3
#eval show MetaM Expr from do
  let e := mkAppN (mkConst ``Nat.add) #[toExpr 3,toExpr 3]
  let denylist := NameSet.empty
  whnfWithDenylist' denylist e -- Returns `Lean.Expr.lit (Lean.Literal.natVal 6)`

#eval show MetaM Expr from do
  let e := mkAppN (mkConst ``Nat.add) #[toExpr 3,toExpr 3]
  let denylist := NameSet.empty.insert `Nat.add
  whnfWithDenylist' denylist e -- Returns equivalent of `Nat.add 3 3`
 -/

/-
/-- Like whnfHeadPred but expands matchers  -/
def whnfDeltaHeadPred' (e : Expr) (pred : Expr → MetaM Bool) : MetaM Expr := whnfHeadPred
-/
