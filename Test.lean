import Lean
import Hdlean

inductive Either (α β:Type u) where
  | left (a:α)
  | right (b:β)
  deriving Repr, BEq

inductive MyType (n:Nat) where
| A : BitVec n → MyType n
| B : Option UInt16 → MyType n

structure A where
  suba : Bool
  subb : Bool
  subc : Bool
inductive B where
  | a (val:A)
  | b (val:A)
  | c (val:A)
inductive C (n:Nat): Type where
  | p (val:(Bool×Bool))
  | p2 (val:(Bool×Bool)) (v: Vector A n)

def Test.t1 := UInt8
def Test.t2 := BitVec 7
def Test.t3 := Either Bool B
def Test.t4 := MyType 2
def Test.t5 := Either Nat Bool

open Test Lean Lean.Compiler.LCNF Hdlean.BitShape in
def main : IO Unit := do
  let bitWidthAsserts: Lean.Meta.MetaM (List Bool) := do pure [
    (← bitShape! (.const ``t1 [])).totalWidth == 8,
    (← bitShape! (.const ``t2 [])).totalWidth == 7,
    (← bitShape! (.const ``A [])).totalWidth == 3,
    (← bitShape! (.const ``B [])).totalWidth == 2+3,
    (← bitShape! (.const ``B [])).totalWidth == 2+3,
    (← bitShape! (.const ``t3 [])).totalWidth == 1+(max 1 (2+3)),
    (← bitShape! (.const ``Unit [])).totalWidth == 0,
    (← bitShape! (.const ``Empty [])).totalWidth == 0,
    (← bitShape! (.const ``t4 [])).totalWidth == 1+(max 2 (1 + 16)),
    (← bitShape? (.const ``Nat [])) == .none,
    (← bitShape? (.const ``t5 [])) == .none,
  ]
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Test}] {} (trustLevel := 0)
  match ← (bitWidthAsserts.run' {} |>.run' default {env}).toIO' with
  | .ok testResults =>
    let failingTests := testResults.zipIdx.filterMap (fun x => if !x.1 then .some x.2 else .none)
    if failingTests.length != 0 then
    panic! s!"some tests failed: {failingTests}"
  | .error e => panic! s!"error: {← e.toMessageData.toString}"

inductive thisisastruct : (ty:Type) → Type where
  | mk (thisisafunction: ty → thisisastruct ty): thisisastruct ty
