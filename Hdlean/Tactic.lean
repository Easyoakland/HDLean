import Lean
open Lean Lean.Tactic Lean.Elab.Tactic Lean.Elab.Tactic.Conv Lean.Meta

/-- Puts term in normal form. -/
syntax (name := reduceAll) "reduceAll" : conv
/-- Puts term in normal form. -/
syntax (name := reduceAll') "reduceAll" : tactic

@[tactic reduceAll]
def Tactic.evalReduceAll : Tactic := fun _ =>
   withMainContext do
     changeLhs (← Meta.reduceAll (← getLhs))

macro_rules
  | `(tactic|reduceAll) => `(tactic|conv => reduceAll)

/- elab "reduce" "(" "skipTypes" ":=" skipTypes:term ")" : conv => do
   withMainContext do
     changeLhs (← Meta.reduce (skipTypes:=← unsafe Meta.evalExpr (α:=Bool) (.const ``Bool []) (← Lean.Elab.Term.elabTerm skipTypes .none)) (← getLhs)) -/
