import Hdlean.Arrow
import Hdlean.Tactic
import Lean

namespace Hdlean

/-- Mealy machine with inputs of `Mealy.I` and outputs of `O` with state `Mealy.σ` -/
structure Mealy (O : Type u) where
  σ : Type u
  I : Type u
  /-- The current output value of the machine.
  When defining new `Mealy` machines this should be the reset value. -/
  value : O
  /-- The current state of the machine.
  When defining new `Mealy` machines this should be the reset value. -/
  state : σ
  transition : I → σ → O × σ

attribute [inline] Mealy.transition -- TODO I don't think this does anything

open Std.Format in
/-- Format the `Mealy` without formatting its internal state. -/
protected def Mealy.repr (self: Mealy α) [Repr α]: Nat → Std.Format := fun p =>
  bracket "{ " (Std.Format.joinSep [
    group ("value" ++ " " ++ ":="  ++ " " ++ Repr.reprPrec self.value p),
    group ".."
  ] ("," ++ " ") ) " }"

open Std.Format in
/-- Format the `Mealy` including its internal state.
    There's a good change you will have to manually pass `inst` to format the state.
-/
/- TODO tactic to unfold to get the σ type for auto-synthesizing? -/
protected def Mealy.repr' (self: Mealy α) [inst: Repr self.σ] [Repr α]: Nat → Std.Format := fun p =>
  bracket "{ " (Std.Format.joinSep [
    group ("value" ++ " " ++ ":="  ++ " " ++ Repr.reprPrec self.value p),
    group ("state" ++ " " ++ ":="  ++ " " ++ Repr.reprPrec self.state p),
    group ".."
  ] ("," ++ " ") ) " }"


end Hdlean
namespace NotSynthesizable
open NotSynthesizable
open Hdlean -- Have to open top level Hdlean namespace before the `namespace Hdlean` command for things to resolve properly.

-- The following Mealy... functions are in `NotSynthesizable.Hdlean`, so that they can be called like methods after opening the `NotSynthesizable` namespace. Unfortunately, this doesn't work if their full names are `Hdlean.NotSynthesizable.Mealy.blah` and only if it is `NotSynthesizable.Hdlean.Mealy.blah`

namespace Hdlean

@[specialize m] def Mealy.next (m : Mealy α) (i: m.I) : Mealy α :=
  let p := m.transition i m.state
  ⟨m.σ, m.I, p.1, p.2, m.transition⟩
#check Hdlean.Mealy.next

/- /-- This has "failed to generate equational theorem" issues -/
def Mealy.get (n:Nat) (s : Mealy α) (inputs: Vector s.I n) : Mealy α := let inputs' := inputs.toList; match h: n, h2: inputs' with
| 0, .nil => s
| p+1, .cons i rest => by
  have : (i::rest).length = p+1 := by rw [← h2, Vector.length_toList, h]
  have : (rest).length = p := by exact Nat.succ_inj.mp this
  exact get p (s.next i) (.mk (Array.mk rest) (by assumption))
| 0, .cons .. => s
| n+1, .nil => s
-/

@[specialize n m] def Mealy.get (n:Nat) (m : Mealy α) (inputs: Vector m.I n) : Mealy α := let inputs' := inputs.toList; match h: n with
| 0 => match h2:inputs' with
  | .nil => m
  | .cons i is => nomatch show False by
    have : (i::is).length = 0 := by rw [← h2, Vector.length_toList, h]
    contradiction
| p+1 => match h2:inputs' with
  | .nil => nomatch show False by
    have : inputs'.length = p+1 := by rw [Vector.length_toList, h]
    rw [h2] at this
    contradiction
  | .cons i rest =>
    have : (i::rest).length = p+1 := by rw [← h2, Vector.length_toList, h]
    have : (rest).length = p := by exact Nat.succ_inj.mp this
    get p (m.next i) (.mk (Array.mk rest) (by assumption))

@[simp] theorem Mealy.next_σ (s : Mealy α) (i: s.I): (s.next i).σ = s.σ  := rfl
@[simp] theorem Mealy.get_σ (s : Mealy α): ∀ n i, (s.get n i).σ = s.σ
  | 0, i => by
    rw [Mealy.get]
    split
    . rfl
    . split
  | n+1, i => by
    rw [Mealy.get]
    split
    . split
    . rw [get_σ, next_σ]

@[simp] theorem Mealy.next_I (s : Mealy α) (i: s.I): (s.next i).I = s.I := rfl

end Hdlean -- The rest of the `NotSynthesizable` functions here aren't meant to be used like methods. If they were defined above then every usage would have to `open NotSynthesizable.Hdlean` to use them in addition to `open NotSynthesizable`.

@[specialize machine] def simulate (machine: Mealy O) (inputs: Array machine.I) : Array (Σ' (m : Mealy O), m.σ = machine.σ ∧ m.I = machine.I) :=
  have : machine.σ = (machine.σ) := rfl
  let p: (Mealy O) := machine
  let machine_acc: {p: Mealy O // p.σ = (machine.σ) ∧ machine.I = p.I } := ⟨p, And.intro rfl rfl⟩
  Id.run do
  let a := Id.run do ForIn'.forIn' [0:inputs.size] (#[], machine_acc) (fun i _ (acc, m) => ForInStep.yield <|
    let m' := m.val.next <| cast m.property.right inputs[i]
    have : m'.σ = (machine.σ) := by unfold m'; simp; rw [m.property.left]
    let p: Mealy O := m'

  (
    acc.push m
    , ⟨p, by
        unfold p m'
        simp
        rw [m.property.left, ← m.property.right]
        constructor <;> rfl
      ⟩
  ))
  a.fst.map fun x => PSigma.mk x.val (by rw [x.property.left, ← x.property.right]; constructor <;> rfl)
  -- let c := b.map fun x => x.fst.repr' (inst:=x.snd) 0
  -- c.map fun x => ToString.toString x


end NotSynthesizable
namespace Hdlean -- re-open the top-level Hdlean namespace now that we're done with NotSynthesizable.

@[inline] def Mealy.pure (a : α) : Mealy α where
  σ := PUnit
  I := PUnit
  value := a
  state := ()
  transition _ _ := (a, .unit)

@[inline] instance : Applicative (Mealy) where
  pure := Mealy.pure
  seq f a := let a := a (); {
    σ := (f.σ× a.σ)
    I := (f.I× a.I)
    value := f.value a.value
    state := (f.state, a.state)
    transition i s :=
      let (f, fs) := f.transition i.fst s.fst
      let (a, as) := a.transition i.snd s.snd
      (f a, (fs, as))
  }

@[inline] instance [HMul α β γ] : HMul (Mealy α) (Mealy β) (Mealy γ) where
  hMul a b := (.*.) <$> a <*> b
@[inline] instance [HAdd α β γ] : HAdd (Mealy α) (Mealy β) (Mealy γ) where
  hAdd a b := (.+.) <$> a <*> b

/-- Make a mealy machine which takes no input from its transition function and initial state. -/
def Mealy.corec {α σ :Type _} (f : σ → α × σ) (st : σ) : Mealy α where
  σ := σ
  I := Unit
  value := f st |>.fst
  state := st
  transition _ s := f s

/-- In hardware this corresponds to a new Mealy machine made with a new registered state `σ` which merges the output of machine `s` and the previous `σ` state of the new machine, using `f`.

If `s` outputs values `[1,2,3,4,...]`

Then this machine outputs `[reset, f 1 reset, f 2 (f 1 reset), f 3 (f 2 (f 1 reset)), ...]`

`reset` uses `Inhabited` by default, but can be manually specified like so:
- `m.scan (reset:=0) f`
- `m.scan f 0`
-/
-- `by exact` is used because tactic defaults are executed in the context of the calling site, and this enables passing a custom reset either positional or nominal without having to wrap the value in `⟨⟩`.
def Mealy.scan {α β σ: Type u} (s : Mealy α) (f : α → σ → (β×σ)) (reset : σ := by exact inferInstanceAs (Inhabited _) |>.default) : Mealy β where
  σ := (σ × s.σ)
  I := s.I
  value := (f s.value reset).fst
  state := ((f s.value reset).snd, s.state)
  transition i st :=
    let (a, st_snd') := s.transition i st.snd
    let (b, st_fst') := f a st.fst
    (b, (st_fst', st_snd'))

@[inline] def Mealy.compose (m1: Mealy O1) (m2: Mealy O) (h:O1=m2.I := by trivial): Mealy O where
  σ := m1.σ × m2.σ
  I := m1.I
  value := m2.value
  state := (m1.state, m2.state)
  transition i s :=
    let (o1, m1s) := m1.transition i s.fst
    let (o, m2s) := m2.transition (cast h o1) s.snd
    (o, (m1s, m2s))

notation:50 a:50 " >>>' " b:50 => Mealy.compose a b

def delay1 [reset: Inhabited α] (s:Mealy α): Mealy α := {
  σ := (α× s.σ)
  I := s.I
  state := (s.value, s.state)
  value := default
  transition i st :=
    let (out0, s_st) := st
    let (out1, s_st') := s.transition i s_st
    (out0, (out1, s_st'))
}

def increasing: Mealy Nat where
  σ := Nat
  I := Unit
  value := default
  state := default
  transition _ s := (s+1,s+1)

def multiplyAccumulate (x y : Mealy Nat) : Mealy Nat where
  σ := (Nat×x.σ× y.σ)
  I := (x.I× y.I)
  value := default
  state := (0, x.state, y.state)
  transition i s :=
    let (x, xs) := x.transition i.fst s.snd.fst
    let (y, ys) := y.transition i.snd s.snd.snd
    let v := s.fst + x * y
    (v, (v,xs,ys))

def multiplyAccumulate' (x y : Mealy Nat): Mealy Nat := let mul := x * y; {
  value := default
  state := (mul.state, 0)
  transition i s :=
    let (v, vs) := mul.transition i s.fst
    (v, (vs, v))
  , ..
}

def multiplyAccumulate'' (x y : Mealy Nat): Mealy Nat := (x*y).scan fun i st => (st+i,st+i)
def multiplyAccumulate''' (x y : Mealy Nat): Mealy Nat := ((.,.)<$>x<*>y).scan fun (x,y) st => (st+x*y,st+x*y)


def accAdder [Inhabited α] [Add α]: Mealy α := {
  value := default
  state := default
  transition i s := let v :=  i + s
    (v, v)
  , ..
}

section
open NotSynthesizable

#eval by exact increasing.next () |>.repr' (inst:=inferInstanceAs (Repr Nat)) 0
#eval by exact multiplyAccumulate (pure 2) (pure 2) |>.next ((), ()) |>.repr  0
#eval by exact multiplyAccumulate' (pure 2) (pure 2) |>.get 1 (by
    reduceAll; exact default
  ) |>.repr' 0 (inst := by
    reduceAll; exact inferInstance
  )
#eval simulate (multiplyAccumulate'' (increasing) (pure 2)) (Array.replicate 10 (by reduceAll; exact default)) |>.map fun x => x.fst.repr 0
#eval simulate (multiplyAccumulate''' (increasing) (pure 2)) (Array.replicate 10 (by reduceAll; exact default)) |>.map fun x => x.fst.repr 0

#eval
  let n := 1000
  by exact increasing >>>' accAdder |>.get n (by
    unfold accAdder; simp; exact ⟨Array.replicate n (), by simp⟩
  ) |>.repr' 0 (inst := by
    simp
    reduceAll
    exact inferInstance
  )

end

structure MealyA (I O : Type u) where
  σ : Type u
  value : O
  state : σ
  transition : I → σ → O × σ

attribute [inline] MealyA.transition

namespace MealyA
instance : CoeDep (Mealy O) m (MealyA m.I O) where
  coe := {
    σ := m.σ
    value := m.value
    state := m.state
    transition := m.transition
  }

instance : CoeDep (MealyA I O) m (Mealy O) where
  coe := {
    σ := m.σ
    I := I
    value := m.value
    state := m.state
    transition := m.transition
  }
end MealyA

def Mealy.A (m: Mealy α): MealyA m.I α := m

def test': Mealy Nat := Mealy.A (Mealy.pure 0)
#check increasing
#eval test'.repr 0
#eval ((Mealy.pure 0).A : Mealy Nat).repr 0

/-- Same as `Mealy` but at the same universe as its type arguments. -/
structure MealyExplicit (σ I O : Type u) where
  value : O
  state : σ
  transition : I → σ → O × σ
def Mealy.Explicit (m: Mealy O) : MealyExplicit m.σ m.I O where
  value := m.value
  state := m.state
  transition := m.transition

open NotSynthesizable in
#eval
  let m := increasing >>>' accAdder
  have : m.σ = (Nat × Nat) := rfl
  let p: ((m:Mealy Nat) × Repr (m.σ)) := Sigma.mk m <| this ▸ inferInstanceAs (Repr (Nat×Nat))
  let machine: {p: ((m:Mealy Nat) × Repr (m.σ)) // p.fst.σ = (Nat×Nat) ∧ Unit = p.fst.I } := ⟨p, And.intro rfl rfl⟩
  Id.run do
  let a := Id.run do ForIn.forIn [0:10] (#[], machine) (fun _ (acc, m) => ForInStep.yield <|
    let m' := m.val.fst.next <| cast m.property.right ()
    have : m'.σ = (Nat × Nat) := by unfold m'; simp [m.property]
    let p: ((m:Mealy Nat) × Repr (m.σ)) := Sigma.mk m' <| this ▸ inferInstanceAs (Repr (Nat×Nat))

  (
    acc.push m
    , ⟨p, by
        unfold p m'
        simp [m.property]
      ⟩
  ))
  let b := a.fst.map fun x => x.val
  let c := b.map fun x => x.fst.repr' (inst:=x.snd) 0
  c.map fun x => ToString.toString x

/-- A Mealy machine with explicit inputs and outputs implementing the `Arrow` and related classes. This is marked as `irreducible` so that the various `Arrow` notations work with `MealyA'`. Internally, this is represented with a `reset → MealyA`. This reset/initial value is needed to define `Arrow`.
-/
@[irreducible] def MealyA' (I O : Type u) := [Inhabited I] → MealyA I O

section UnsealedMealyA'
unseal MealyA'

instance [Inhabited I]: Coe (MealyA' I O) (MealyA I O) where
  coe x := x
instance : Coe (MealyA I O) (MealyA' I O) where
  coe x := x
instance [Inhabited I]: CoeDep (MealyA' I O) m (Mealy O) where
  coe := m
instance : CoeDep (Mealy O) m (MealyA' m.I O) where
  coe := m
def Mealy.A' (m: Mealy α): MealyA' m.I α := m

-- Since MealyA' enables assuming a default value, can implement `Arrow`
instance: Arrow (MealyA') where
  id := {
    σ := Unit
    value := default
    state := ()
    transition i s := (i, s)
  }
  compose bc ab :=
  let inst := (Inhabited.mk (ab.transition default ab.state).fst)
  -- Get and apply inhabited proofs first
  let ab := ab
  let bc := @bc inst
  {
    σ := bc.σ × ab.σ
    value := bc.transition default bc.state |>.fst
    state := (bc.state, ab.state)
    transition i s :=
      let (abo, ab') := ab.transition i s.snd
      let (bco, bc') := bc.transition abo s.fst
      (bco, bc', ab')
  }
  arr f := {
    σ := Unit
    value := f default
    state := ()
    transition i s := (f i, s)
  }
  first f inst :=
  -- Get and apply inhabited proofs first
  let _ := Inhabited.mk <| inst.default.fst
  let _ := Inhabited.mk <| inst.default.snd
  let _ := Inhabited.mk <| f.transition default f.state |>.fst
  {
    σ := f.σ
    value := default
    state := f.state
    transition i s :=
      let (fo, f') := f.transition i.fst s
      ((fo,i.snd), f')
  }

namespace Mealy.Test
def test: MealyA Nat Nat := inferInstanceAs (Arrow MealyA') |>.id
def test2: Mealy Nat :=
  have : increasing.I = Unit := rfl
  let _: Inhabited increasing.I := Inhabited.mk ()
  let _: Inhabited accAdder.I := Inhabited.mk (0:Nat)
  let a: MealyA' Unit Nat := increasing.A'
  let b: MealyA' Nat Nat  := @accAdder _ instInhabitedNat instAddNat |>.A'
  let b: MealyA' Unit Nat := instArrowMealyA'.compose b a
  ↑b

def adderA [Inhabited α] [Add α]: MealyA α α := accAdder.A

-- TODO, why does regular ↑ notation not work, but this does?
notation:max "↑" a => Coe.coe a

seal MealyA' in
def test3: MealyA Unit Nat :=
  let c: MealyA' Unit Nat := (↑adderA (α:=Nat)) <<< (increasing.A')
  ↑c

seal MealyA' in
def test4: MealyA Unit Nat :=
  let c: MealyA' Unit Nat := (increasing.A') >>> (↑adderA (α:=Nat))
  ↑c

-- #eval test.instCoeDepMealy.coe.repr' 0 (inst:=by unfold test Category.id CoeDep.coe MealyA.instCoeDepMealy instArrowMealyA' Arrow.toCategory; simp; exact inferInstance)
#eval test.instCoeDepMealy.coe.repr' 0 (inst:=by reduceAll; exact inferInstance)

-- #eval test2.repr' 0 (inst:=by unfold test2 increasing accAdder Category.compose Arrow.toCategory instArrowMealyA' Mealy.A'; simp; exact inferInstance)
#eval test2.repr' 0 (inst:=by with_unfolding_all reduceAll; exact inferInstance)

-- #eval (↑test3: Mealy Nat).repr' 0 (inst:=by unfold test3 Coe.coe increasing adderA accAdder Category.compose Arrow.toCategory instArrowMealyA' instCoeMealyA'MealyAOfInhabited instCoeMealyAMealyA' Mealy.A' Mealy.A; simp; exact inferInstance)
#eval (↑test3: Mealy Nat).repr' 0 (inst:=by reduceAll; exact inferInstance)

-- #eval (↑test4: Mealy Nat).repr' 0 (inst:=by unfold test4 Coe.coe increasing adderA accAdder Category.compose Arrow.toCategory instArrowMealyA' instCoeMealyA'MealyAOfInhabited instCoeMealyAMealyA' Mealy.A' Mealy.A; simp; exact inferInstance)
#eval (↑test4: Mealy Nat).repr' 0 (inst:=by reduceAll; exact inferInstance)
end Mealy.Test

/-- If `d` and `c` are uninhabited but `b` is inhabited, then `Arrow.loop` (also called `trace`) is unsound as defined in Haskell.
`f` is what the definition in Haskell looks like, and it implies `False`, which is why it is unsound.
So, the correct definition must be able to prove one of the following with additional assumptions on `f`:
- `Inhabited d`.
- `(Inhabited d → False) → Inhabited (b → c)` i.e. `(¬Inhabited b) ∨ Inhabited c`.
While this could be an `Either` of both, the second condition would not work well with class synthesis and the first is almost certainly what will be used in practice anyway. The second would mean the assumptions of `f` provides no information because the original function takes `False`.
 -/
private theorem haskell_arrowLoop_unsound (f: ∀ b d c, ((b× d) → (c× d)) → b → c): False :=
  let f := f PUnit PEmpty PEmpty
  let input := fun (_, d) => nomatch d
  nomatch f input PUnit.unit

class ArrowLoop (a) extends Arrow a where
  loop [Inhabited d]: a (b×d) (c×d) -> a b c

-- Not lawful because of σ permuting in isomorphic but unequal ways. Doesn't really matter. Could maybe make it lawful by quotienting over all σ, but that sounds like more work than needed.
instance : ArrowLoop MealyA' where
  loop {d _ _} inst m := {
    σ := m.σ×d
    value := m.value.fst
    state := (m.state, inst.default)
    transition i s :=
      let ((c_o, d_o), state) := m.transition (i, s.snd) s.fst
      (c_o, (state, d_o))
  }
end UnsealedMealyA'

def adder: MealyA' (Nat × Nat) Nat := Arrow.arr ((.+.).uncurry)

open Category Arrow ArrowLoop in
def accAdder': MealyA' Nat Nat :=
  loop <| adder >>> ((arr id) &&& (arr id))


open NotSynthesizable in
unseal MealyA' in
#eval simulate (accAdder'.instCoeDepMealy.coe) (#[1,2,3,4,5,6,7,8]: Array Nat) |>.map (fun x =>
  x.fst.repr' 0 (inst:= by
    rw [x.snd.left]
    unfold CoeDep.coe MealyA.instCoeDepMealy accAdder' adder
     Arrow.split Arrow.arr Category.compose ArrowLoop.loop instArrowMealyA' instArrowLoopMealyA'
    simp only
    exact inferInstance
  )
)

section

open Arrow ArrowLoop NotSynthesizable in
#eval
  let m := loop (first accAdder' >>> Category.id (cat:=MealyA') (a:=(Nat× Nat)))
  simulate (O:=Nat) (CoeDep.coe m) (#[1,2,3,4,5,6]: Array Nat) |>.map fun x => x.fst.repr 0
open Arrow ArrowLoop NotSynthesizable in
#eval
  let m := accAdder' >>> (loop (Category.id (cat:=MealyA') (a:=(Nat× Nat))))
  simulate (O:=Nat) (CoeDep.coe m) (#[1,2,3,4,5,6]: Array Nat) |>.map fun x => x.fst.repr 0

open Arrow ArrowLoop NotSynthesizable in
#eval
  let m: MealyA' Nat Nat := loop (first accAdder' >>> Category.id (cat:=MealyA') (a:=(Nat× Nat)))
  simulate (O:=Nat) (CoeDep.coe m: Mealy Nat) (#[1,2,3,4,5,6]: Array Nat)
  |>.map fun x => x.fst.repr' 0 (inst:=by
    rw [x.snd.left]
    -- unfold m CoeDep.coe accAdder' adder instCoeDepMealyA'Mealy MealyA'
    -- simp only
    -- unfold instArrowMealyA' instArrowLoopMealyA' MealyA'
    -- simp only
    -- change Repr ((Unit × (((((Unit × Unit) × Unit) × Unit) × Unit) × Unit) × Nat) × Nat)
    reduceAll
    exact inferInstance
  )

-- open Arrow ArrowLoop NotSynthesizable in
-- set_option pp.raw true in
-- #reduce
--   let m := accAdder' >>> (loop (Category.id (cat:=MealyA') (a:=(Nat× Nat))))
--   (↑m:Mealy Nat).σ

open Arrow ArrowLoop NotSynthesizable in
#eval
  let m := accAdder' >>> (loop (Category.id (cat:=MealyA') (a:=(Nat× Nat))))
  simulate (O:=Nat) (CoeDep.coe m : Mealy Nat) (#[1,2,3,4,5,6]: Array Nat)
  |>.map fun x => x.fst.repr' 0 (inst:=by
    rw [x.snd.left]
    -- unfold m CoeDep.coe accAdder' adder instCoeDepMealyA'Mealy MealyA'
    -- simp only
    -- unfold instArrowMealyA' instArrowLoopMealyA' MealyA'
    -- simp only
    -- change Repr ((Unit × Nat) × (((((Unit × Unit) × Unit) × Unit) × Unit) × Unit) × Nat)
    reduceAll
    exact inferInstance
  )
-- variable {h: MealyA' b c} {f: MealyA' (c× d) (c× d)}
-- open Arrow ArrowLoop in
-- theorem instArrowLoopMealyA'.left_tightening  [Inhabited b] [Inhabited d] : loop (first h >>> f) = h >>> loop f := by
--   simp only
--   unfold loop instArrowLoopMealyA' instArrowMealyA' Category.compose MealyA'
--   simp

open NotSynthesizable in
#eval simulate (O:=Nat) (delay1 (reset:=⟨42⟩) increasing) (#[(),(),(),(),()]) |>.map fun x => x.fst.repr 0
open NotSynthesizable in
#eval simulate (O:=Nat) (increasing.scan (reset:=42) fun a s => (s,a)) (Array.replicate 5 ()) |>.map fun x => x.fst.repr 0
open NotSynthesizable in
#eval simulate (O:=Nat) (increasing.scan (fun a s => (s,a)) 42 ) (Array.replicate 5 ()) |>.map fun x => x.fst.repr 0

end

#reduce (types:=true) ((↑adder:MealyA (Nat×Nat) Nat).σ)
#eval do println! ← Lean.Meta.reduce (skipTypes := false) <| ←Lean.Elab.Term.elabTerm (←`((↑adder:MealyA (Nat×Nat) Nat).σ)) .none
