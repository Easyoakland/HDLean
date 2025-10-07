import Lean.Meta
import Hdlean.Basic
import Compiler.ImplementedByHWAttr

namespace Hdlean.Meta

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

def canUnfold (e:Expr): MetaM Bool := do
  let env ← getEnv
  let some canUnfold := Context.canUnfold? (← read) | return Bool.true
  match do env.find? (← e.getAppFn'.const?).fst with
  | some info => canUnfold (← getConfig) (info)
  | none => pure Bool.true -- If not a name can't unfold anyway, so reduce like regular.

set_option linter.unusedVariables false in
/-- Like `unfoldDefinition?` but unfolds using (in order of priority) `implemented_by_hw`, `implemented_by`, auxiliary `._unsafe_rec`, or actual value of constant (even if constant is `opaque`)
-/
def unfoldDefinitionEval? (e : Expr) : MetaM (Option Expr) := do
  if !(← canUnfold e) then return .none
  let fn := e.getAppFn'
  let args := e.getAppArgs
  let .const fn lvls := fn | return .none
  -- -- Try `implemented_by_hw`
  if let .some fn' := Compiler.getImplementedByHw? (← getEnv) fn then
    return mkAppN (.const fn' lvls) args
  -- Try `implemented_by`
  if let .some fn := Compiler.getImplementedBy? (← getEnv) fn then
    return mkAppN (.const fn lvls) args
 -- Prioritize `._unsafe_rec`
  let .some info ← Compiler.LCNF.getDeclInfo? fn | return .none
  -- Unfold even if opaque.
  if let .some fn := info.value? (allowOpaque := true) then
    return fn.beta args
  else return .none
  /-
  -- Regular `unfoldDefinition?`
  if let .some e ← unfoldDefinition? e ignoreTransparency then trace[debug] "1: instead return: {e}" return e
  -- Try to unfold matchers
  if !inlineMatchers then trace[debug] "2: instead return: .none" return .none
  let e' ← Compiler.LCNF.inlineMatchers e
  if e' == e then trace[debug] "3: instead return: .none" return .none
  trace[debug] "4: instead return: {e'}"
  return e' -/

mutual
/-- `whnfAtMostI` but using `whnfEvalImp`. -/
partial def whnfEvalAtMostI (e : Expr) : MetaM Expr := do
  match (← getTransparency) with
  | .all | .default => withTransparency TransparencyMode.instances <| whnfEvalImp e
  | _ => whnfEvalImp e

/-- Wraps `whnfCore` so that its internal calls to `whnf` instead go through `whnfEvalImp`.  -/
partial def whnfEvalCore (e : Expr) : MetaM Expr := do
  match e with
  | .app f ..       =>
    let f := f.getAppFn
    let f' ← whnfEvalCore f
    let e' := mkAppN f' e.getAppArgs
    -- If we reduced the head then try again and maybe reduce more. If we didn't then we're safe to run `whnfCore` without it having to deal with reducible `.proj` and therefore without it running a `whnf` which isn't `whnfEval`.
    if f' != f then whnfEvalCore e' else whnfCore e'
  | .proj _ i c =>
    let k (c : Expr) := do
      match (← projectCore? c i) with
      | some e => whnfEvalCore e
      | none => return e
    -- `whnfCore` calls `whnf` when this setting is set above `.yes`, so we use our `whnfEval` versions here instead.
    match (← getConfig).proj with
    | .no => return e
    | .yes => k (← whnfEvalCore c)
    | .yesWithDelta => k (← whnfEvalImp c)
    -- Remark: If the current transparency setting is `reducible`, we should not increase it to `instances`
    | .yesWithDeltaI => k (← whnfEvalAtMostI c)
  | e =>
    -- `whnfCore` uses `whnf` to handle projections if this setting is above `.yes`. To use `whnfEval` instead, we set this to `.no` so instead `whnfCore` will return the value unchanged and we can handle the `.proj` with `whnfEval` if needed.
    let e ← withConfig (fun config => {config with proj := .no}) <| whnfCore e
    -- Check if `e` became a `.proj`. If it did we should loop to use our Eval version to handle `.proj`. If it didn't then this return is a regular `whnfCore` return.
    if let .proj .. := e then whnfEvalCore e else pure e

/-- A hybrid of `Lean.Meta.whnfImp` and eval. Different from `Lean.Meta.whnfImp` in that:
- Checks `canUnfold?` before doing primitive reductions so the denylist can prevent primitive reductions even when fully applied. In other words, primitives like `Nat.add` are considered to be unfolded to get reduced.
  - TODO(fix): Doesn't cache, so it's slower than `whnfImp`.
- Unfolds using unfoldDefinitionEval? (in order of priority) `implemented_by`, auxiliary `._unsafe_rec`, or actual value of constant (even if constant is `opaque`).
-/
partial def whnfEvalImp (e : Expr) : MetaM Expr :=
  withIncRecDepth <| whnfEasyCases e fun e => do
      withTraceNode `Meta.whnf (fun _ => return m!"Non-easy whnfEval: {e}") do
        checkSystem "whnf"
        if ← canUnfold e then
          let e' ← whnfEvalCore e
          match (← reduceNat? e') with
          | some v => pure v
          | none   =>
            match (← reduceNative? e') with
            | some v => pure v
            | none   =>
              match ← unfoldDefinitionEval? e' with
              | some e' => whnfEvalImp e'
              | none => pure e'
        else pure e
end

/-- Run `MetaM α` with `canUnfold?` set such that it respects `denylist` -/
def withDenylist (denylist : NameSet) (a:MetaM α) : MetaM α := do
  let prevCanUnfold := (← read).canUnfold? |>.getD (fun _ _ => pure true)
  withReader (fun ctx =>
    {ctx with canUnfold? := some (fun cfg info => do return (← prevCanUnfold cfg info)
      && (←  canUnfoldDenylist denylist cfg info))}
  ) a

/-- Like `whnf` but using `whnfEvalImp` and a denylist of definitions to not unfold. -/
def whnfEval (denylist : NameSet) (e : Expr): MetaM Expr :=
  withDenylist denylist <|
    whnfEvalImp e

partial def whnfEvalEta (denylist : NameSet) (e : Expr) : MetaM Expr := do
  let res ← @whnfEval denylist e
  let resEta := res.eta
  if res != resEta then
    @whnfEvalEta denylist resEta
  else
    return res
