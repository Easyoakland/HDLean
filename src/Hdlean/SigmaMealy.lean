import Hdlean.Arrow
import Hdlean.Tactic
import Lean

namespace Hdlean

inductive ActiveEdge where
  | rising
  | falling
  deriving Inhabited

inductive ResetEdge where
  /-- async assert sync de-assert -/
  | asynchronous
  /-- sync assert sync de-assert -/
  | synchronous
  deriving Inhabited

inductive InitBehavior where
  | unknown
  | defined
  deriving Inhabited

inductive ResetPolarity where
  | activeHigh
  | activeLow
  deriving Inhabited

structure Domain where
  freq : {n:Nat//n≠0}
  activeEdge : ActiveEdge
  resetEdge : ResetEdge
  initBehavior : InitBehavior
  resetPolarity : ResetPolarity

instance : Inhabited Domain where
  default := {
    freq := ⟨10_000_000, Ne.symm (Nat.zero_ne_add_one _)⟩,
    activeEdge:=default,
    resetEdge:=default,
    initBehavior:=default,
    resetPolarity:=default
  }

/- - This might be more performant when running `simulate` in `Lean` if Lean has trouble optimizing `dom` parameters away.
section IndirectDomain

class HasDomain (t:Type u) where
  dom : Domain
structure System
instance : HasDomain System where
  dom := {
    freq := ⟨100_000_000, by omega⟩,
    activeEdge := .rising,
    resetEdge := .asynchronous,
    initBehavior := .defined,
    resetPolarity := .activeHigh
  }
structure Signal' (dom : Type u) (O : Type u)
def freq (dom) [HasDomain dom]: Nat := HasDomain.dom dom |>.freq
#eval freq System

set_option trace.compiler.ir true in
def signal_freq [HasDomain dom] (s:Signal' dom O): Nat := HasDomain.dom dom |>.freq
#eval (signal_freq .mk (dom:=System) (O:=BitVec 3))
end IndirectDomain -/

/-- Mealy/Moore hybrid machine with outputs of `O` with state `Mealy.σ` -/
-- While not currently enforced, it is assumed that `σ` and `transition` don't change.
structure Mealy (O : Type u) where
  σ : Type u
  /-- The current state of the machine.
  When defining new `Mealy` machines this should be the reset value. -/
  state : σ
  /-- Function which returns the current output and the next state. -/
  transition : σ → O × σ

attribute [inline] Mealy.transition -- TODO I don't think this does anything

/-- The current output value at the current clock cycle -/
@[simp] abbrev Mealy.output (m:Mealy O) : O := m.transition m.state |>.fst

@[inherit_doc Mealy.output, simp]
abbrev Mealy.value := @Mealy.output

@[inline, reducible]
def Mealy.transitionOutput (m : Mealy O) : (m.σ → O) := fun st => m.transition st |>.fst

@[inline, reducible]
def Mealy.transitionState (m : Mealy O) : (m.σ → m.σ) := fun st => m.transition st |>.snd

set_option linter.unusedVariables false in
def Signal (dom : Domain) O := Mealy O

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

def Mealy.next (m : Mealy α) : (α× Mealy α) :=
  let (o, st) := m.transition m.state
  ⟨o, m.σ, st, m.transition⟩

@[simp] def Mealy.get (n:Nat) (m : Mealy α) : (α× Mealy α) := match n with
  | 0 => (m.value, m)
  | p+1 => get p m.next.snd

@[simp] theorem Mealy.next_σ (s : Mealy α) : (s.next).snd.σ = s.σ  := rfl
@[simp] theorem Mealy.get_σ (s : Mealy α): ∀ n, (s.get n).snd.σ = s.σ
  | 0 => by
    rw [Mealy.get]
  | n+1 => by
    rw [Mealy.get]
    rw [get_σ, next_σ]

end Hdlean -- The rest of the `NotSynthesizable` functions here aren't meant to be used like methods. If they were defined above then every usage would have to `open NotSynthesizable.Hdlean` to use them in addition to `open NotSynthesizable`.

/- @[specialize machine] def simulate (machine: Mealy O) (cycles : Nat) : Array (Σ' (m : O × Mealy O), m.2.σ = machine.σ) :=
  have : machine.σ = (machine.σ) := rfl
  let p: Mealy O := machine
  let machine_acc: {p: (O×Mealy O) // p.2.σ = (machine.σ)  } := ⟨(p.value,p), rfl⟩
  Id.run do
  let a := Id.run do ForIn'.forIn' [0:cycles] (#[], machine_acc) (fun i _ (acc, m) => ForInStep.yield <|
    let next := m.val.2.next --<| cast m.property.right
    let o := next.1
    let m' := next.2
    have : m'.σ = (machine.σ) := by unfold m'; simp [next]; rw [m.property]
    let p: Mealy O := m'
    (
      acc.push m
      , ⟨(o,p), by
          unfold p m'
          subst next; subst m'
          simp
          rw [m.property]
        ⟩
    )
  )
  a.fst.map fun x => PSigma.mk x.val (by rw [x.property]) -/

@[specialize machine] def simulate (machine: Mealy O) (cycles : Nat) : Array (Σ' (m : Mealy O), m.σ = machine.σ) :=
  have : machine.σ = (machine.σ) := rfl
  let p: Mealy O := machine
  let machine_acc: {p: (Mealy O) // p.σ = (machine.σ)  } := ⟨p, rfl⟩
  Id.run do
  let a := Id.run do ForIn'.forIn' [0:cycles] (#[], machine_acc) (fun i _ (acc, m) => ForInStep.yield <|
    let next := m.val.next --<| cast m.property.right
    let m' := next.2
    have : m'.σ = (machine.σ) := by unfold m'; simp [next]; rw [m.property]
    let p: Mealy O := m'
    (
      acc.push m
      , ⟨p, by
          unfold p m'
          subst next; subst m'
          simp
          rw [m.property]
        ⟩
    )
  )
  a.fst.map fun x => PSigma.mk x.val (by rw [x.property])

@[specialize machine] def simulate' (machine: Mealy O) (cycles : Nat) : Array <| O × machine.σ := Id.run do
  let mut state := machine.state
  let mut out := #[]
  for _ in [0:cycles] do
    let (o, state') := machine.transition state
    out := out.push (o, state)
    state := state'
  out


end NotSynthesizable
namespace Hdlean -- re-open the top-level Hdlean namespace now that we're done with NotSynthesizable.

section Primitive
@[inline] protected def Mealy.pure (a : α) : Mealy α where
  σ := Unit
  state := ()
  transition _ := (a, ())

/-- In hardware this corresponds to a new Mealy machine made with a new registered state `σ` which merges the output of machine `s` and the previous `σ` state of the new machine, using `f`.

```txt
┌────────────────┐
│        ┌───┐   │
│       ┌│ σ │<┐ │
│       │└───┘ │ │
│┌───┐  └>┌───┐┘ │
││ s │--->│ f │--│->
│└───┘    └───┘  │
└────────────────┘
```

If `s` outputs values `[1,2,3,4,...]`

Then this machine outputs `[reset, f 1 reset, f 2 (f 1 reset), f 3 (f 2 (f 1 reset)), ...]`

`reset` uses `Inhabited` by default, but can be manually specified like so:
- `m.scan (reset:=0) f`
- `m.scan f 0`
-/
-- `by exact` is used because tactic defaults are executed in the context of the calling site, and this enables passing a custom reset either positional or nominal without having to wrap the value in `⟨⟩`.
def Mealy.scan {α β σ: Type u} (s : Mealy α) (f : α → σ → (β×σ)) (reset : σ := by exact inferInstanceAs (Inhabited _) |>.default) : Mealy β where
  σ := (σ × s.σ)
  state := (reset, s.state)
  transition st :=
    let (a, st_snd') := s.transition st.2
    let (b, st_fst') := f a st.fst
    (b, (st_fst', st_snd'))

/-- Combine two separate `Mealy` into one tuple.


```txt
┌─────────┐
│┌───┐    │
││ a │──┐ │
│└───┘  │ │
│       ╞═│═>
│┌───┐  │ │
││ b │──┘ │
│└───┘    │
└─────────┘
```
-/
def Mealy.merge (a : Mealy α) (b : Mealy β): Mealy (α × β) where
  σ := a.σ × b.σ
  state := (a.state, b.state)
  transition st :=
    let (a', aSt') := a.transition st.fst
    let (b', bSt') := b.transition st.snd
    ((a', b'), (aSt', bSt'))
end Primitive

/-- Separate a `Mealy` of a tuple into a tuple of `Mealy`.

Note: In software simulation this runs `m` twice, once for the `fst` projection, and once for the `snd` projection, so it is more efficient to `map` if possible.

```txt
┌────────┐
│┌───┐ ┌─│─>
││ m │═╡ │
│└───┘ └─│─>
└────────┘
```
-/
def Mealy.unmerge (m : Mealy (α × β)) : Mealy α × Mealy β :=
  (m.scan fun m () => (m.1,()),
    m.scan fun m () => (m.2,()))

/-- Map a `Mealy` with a function.

In hardware this corresponds to appending the circuit corresponding to the function after the given `s`.

```txt
┌─────────────┐
│┌───┐  ┌───┐ │
││ s │->│ f │-│->
│└───┘  └───┘ │
└─────────────┘
```
 -/
def Mealy.map (f : α → β) (s : Mealy α) : Mealy β := s.scan fun m () => (f m, ())

/- def Mealy.scan2 {α α2 β σ: Type u} (s : Mealy α) (s2 : Mealy α2) (f : α → α2 → σ → (β×σ)) (reset : σ := by exact inferInstanceAs (Inhabited _) |>.default) : Mealy β where
  σ := (σ × s.σ × s2.σ)
  state := (reset, (s.state, s2.state))
  transition st :=
    let (a, st_snd') := s.transition st.snd.fst
    let (a2, st_snd2') := s2.transition st.snd.snd
    let (b, st_fst') := f a a2 st.fst
    (b, (st_fst', (st_snd', st_snd2'))) -/

-- By defining this in terms of `pure`, `merge`, and `scan` it is synthesizable.
@[inline] instance : Applicative Mealy where
  pure := Mealy.pure
  seq f a := f.merge (a ()) |>.map (fun (f, a) => f a)
  -- Using `scan` instead of default of `seq ∘ pure` to decrease number of `()` in the state.
  -- TODO: There is still an extra `()` per `map` call with this formulation, maybe `Mealy.map` should be a primitive to avoid lots of `()` in state.
  map := Mealy.map

@[inline] instance [HMul α β γ] : HMul (Mealy α) (Mealy β) (Mealy γ) where
  hMul a b := (.*.) <$> a <*> b
@[inline] instance [HDiv α β γ] : HDiv (Mealy α) (Mealy β) (Mealy γ) where
  hDiv a b := (./.) <$> a <*> b
@[inline] instance [HMod α β γ] : HMod (Mealy α) (Mealy β) (Mealy γ) where
  hMod a b := (.%.) <$> a <*> b
@[inline] instance [HPow α β γ] : HPow (Mealy α) (Mealy β) (Mealy γ) where
  hPow a b := (HPow.hPow) <$> a <*> b
@[inline] instance [HAdd α β γ] : HAdd (Mealy α) (Mealy β) (Mealy γ) where
  hAdd a b := (.+.) <$> a <*> b
@[inline] instance [HSub α β γ] : HSub (Mealy α) (Mealy β) (Mealy γ) where
  hSub a b := (.-.) <$> a <*> b
@[inline] instance [HShiftLeft α β γ] : HShiftLeft (Mealy α) (Mealy β) (Mealy γ) where
  hShiftLeft a b := (.<<<.) <$> a <*> b
@[inline] instance [HShiftRight α β γ] : HShiftRight (Mealy α) (Mealy β) (Mealy γ) where
  hShiftRight a b := (.>>>.) <$> a <*> b
@[inline] instance [HAnd α β γ] : HAnd (Mealy α) (Mealy β) (Mealy γ) where
  hAnd a b := (.&&&.) <$> a <*> b
@[inline] instance [HOr α β γ] : HOr (Mealy α) (Mealy β) (Mealy γ) where
  hOr a b := (.|||.) <$> a <*> b
@[inline] instance [HXor α β γ] : HXor (Mealy α) (Mealy β) (Mealy γ) where
  hXor a b := (.^^^.) <$> a <*> b
@[inline] instance [Neg α]: Neg (Mealy α) where
  neg a := (-.) <$> a

end Hdlean
namespace NotSynthesizable.Hdlean
open _root_.Hdlean
/-- Make a mealy machine from its transition function and an initial state.

```txt
┌────────┐
│ ┌───┐  │
│┌│ σ │<┐│
││└───┘ ││
│└>┌───┐┘│
│  │ f |-│->
│  └───┘ │
└────────┘
```
-/
def Mealy.corec {α σ :Type _} (f : σ → α × σ) (st : σ) : Mealy α where
  σ := σ
  state := st
  transition := f

def Mealy.destruct (s : Mealy β) : β × Mealy β :=
  let (o,st') := s.transition s.state
  (o, ⟨s.σ,st',s.transition⟩)

def Mealy.cons {α : Type u} (a : α) (s : Mealy α) : Mealy α := Mealy.corec (fun
  | (true, sSt) => (a, (false, sSt))
  | (false, sSt) => let (o, sSt') := s.transition sSt; (o, (false, sSt'))
) (true, s.state)

open NotSynthesizable Mealy in
#eval simulate' (Mealy.cons 42 (corec (fun st => (st,st+1)) 0)) 10 |>.map (·.fst)

-- def Mealy.corec.scan {α β σ: Type u} (s : Mealy α) (f : α → σ → (β×σ)) (reset : σ := by exact inferInstanceAs (Inhabited _) |>.default) : Mealy β :=

end NotSynthesizable.Hdlean

namespace Hdlean
section Thms
open NotSynthesizable Hdlean

@[simp] theorem next_eq_destruct : @Mealy.next = @Mealy.destruct := rfl

@[simp] theorem output_eq_destruct_fst (m : Mealy O): m.output = m.destruct.fst := by simp [Mealy.destruct]

@[simp] theorem scan_destruct (a : Mealy O) (f : O → σ → (β×σ)) (reset : σ) : (a.scan f reset).destruct = let (o,st) := f a.destruct.fst (reset); (o, (a.destruct.snd).scan f st) := by
  simp only [Mealy.destruct, Mealy.scan]
/-
@[simp] theorem scan_destruct.fst (a : Mealy O) (f : O → σ → (β×σ)) (reset : σ) : (a.scan f reset).destruct.fst = (f a.destruct.fst (reset)).fst := by
  simp only [Mealy.destruct, Mealy.scan] -/

@[simp] theorem get_succ_eq_get_destruct (a : Mealy O) (i:Nat) : a.get (i+1) = let ith := (a.get i |>.snd); (ith.destruct.snd.destruct.fst, ith.destruct.snd) := by
  induction i generalizing a
  case zero => simp
  case succ i ih =>
    simp
    simp at ih
    rw [ih]

@[simp] theorem get_succ_eq_get_destruct_destruct.fst (a : Mealy O) (i:Nat) : (a.get (i+1)).fst = (a.get i).snd.destruct.snd.destruct.fst := by
  induction i generalizing a
  case zero => simp
  case succ i ih =>
    simp
    simp at ih
    rw [ih]

@[simp] theorem get_destruct_eq_get_succ (m : Mealy O) (i:Nat) : ((m.destruct.snd).get i).fst = (m.get (i+1)).fst := rfl

theorem scan_get (a b : Mealy O) (f : O → σ → (β×σ)) (reset : σ) (h:∀ i, a.get i = b.get i): ∀ i, (a.scan f reset).get i = (b.scan f reset).get i := fun i => by
  induction i
  case zero =>
    have : a = b := congrArg Prod.snd (h 0)
    rw [this]
  case succ i ih =>
    rw [get_succ_eq_get_destruct]
    rw [ih]
    rw [← get_succ_eq_get_destruct]

theorem scan_get' (a b : Mealy O) (f : O → σ → (β×σ)) (reset : σ) (h:∀ i, (a.get i).fst = (b.get i).fst): ∀ i, ((a.scan f reset).get i).fst = ((b.scan f reset).get i).fst := fun i => by
  induction i generalizing a b reset <;> simp
  case zero =>
    have : a.destruct.fst = b.destruct.fst := h 0
    rw [this]
  case succ i ih =>
    have : a.destruct.fst = b.destruct.fst := h 0
    rw [this]
    apply ih
    simp
    intro i'
    exact h (i' + 1)

open Mealy in
@[simp] theorem destruct_corec (f : α → β × α) (a : α) :
  (corec f a).destruct = let (b, a) := f a; (b, corec f a) := by
    simp [corec, destruct]

open Mealy in
@[simp] theorem pure_eq_corec_const (a:α): (Mealy.pure a) = Mealy.corec (a,.) () := by rfl

end Thms

@[inline] def Mealy.compose {α β γ : Type} (m1: Mealy (α → β)) (m2: Mealy (β → γ)) : Mealy (α → γ) := m1.merge m2 |>.map (fun (m1,m2) => m2 ∘ m1)
/-  where
  σ := m1.σ × m2.σ
  state := (m1.state, m2.state)
  transition s :=
    let (o1, m1s) := m1.transition s.fst
    let (o2, m2s) := m2.transition s.snd
    (o2 ∘ o1, (m1s, m2s)) -/

def delay1 [reset: Inhabited α] (s:Mealy α): Mealy α := {
  σ := (α× s.σ)
  state := (reset.default, s.state)
  transition st :=
    let (out0, s_st) := st
    let (out1, s_st') := s.transition s_st
    (out0, (out1, s_st'))
}

def increasing: Mealy Nat where
  σ := Nat
  state := default
  transition s := (s,s+1)

def multiplyAccumulate (x y : Mealy Nat) : Mealy Nat where
  σ := (Nat×x.σ× y.σ)
  state := (0, x.state, y.state)
  transition s :=
    let (x, xs) := x.transition s.snd.fst
    let (y, ys) := y.transition s.snd.snd
    let v := s.fst + x * y
    (v, (v,xs,ys))

def multiplyAccumulate' (x y : Mealy Nat): Mealy Nat := let mul := x * y; {
  state := (mul.state, 0)
  transition s :=
    let (v, vs) := mul.transition s.fst
    (v, (vs, v))
  , ..
}

def multiplyAccumulate'' (x y : Mealy Nat): Mealy Nat := (x*y).scan fun i st => (st+i,st+i)
def multiplyAccumulate''' (x y : Mealy Nat): Mealy Nat := ((.,.)<$>x<*>y).scan fun (x,y) st => (st+x*y,st+x*y)


def accAdder [Inhabited α] [Add α] (i: Mealy α): Mealy α := i.scan fun i st =>
  let v :=  i + st
  (st, v)

section
open NotSynthesizable

#eval by exact increasing |>.repr' (inst:=inferInstanceAs (Repr Nat)) 0
#eval simulate' increasing 10
#eval by exact (delay1 increasing) |>.repr' (inst:=by reduceAll; exact inferInstance) 0
#eval by exact (delay1 increasing).next.1
#eval by exact (delay1 increasing).next.2 |>.repr' (inst:=by reduceAll; exact inferInstance) 0
#eval by exact increasing.next.1
#eval simulate increasing 10 |>.map fun x => x.fst.repr' 0 (inst:=by rw [x.snd]; reduceAll; exact inferInstance)
#eval simulate (delay1 (reset:=.mk 42) increasing) 10 |>.map fun x => x.fst.repr' 0 (inst:=by rw [x.snd]; reduceAll; exact inferInstance)
#eval by exact increasing.next.snd |>.repr' (inst:=inferInstanceAs (Repr Nat)) 0
#eval by exact multiplyAccumulate (pure 2) (pure 2) |>.next.1
#eval by exact multiplyAccumulate (pure 2) (pure 2) |>.next.2 |>.repr 0
#eval by exact multiplyAccumulate' (pure 2) (pure 2) |>.get 1 |>.2 |>.repr' 0 (inst := by
    reduceAll; exact inferInstance
  )
#eval simulate (multiplyAccumulate'' (increasing) (pure 2)) 10 |>.map fun x => x.fst.repr 0
#eval simulate (multiplyAccumulate''' (increasing) (pure 2)) 10 |>.map fun x => x.fst.repr 0

#eval
  let n := 1000000
  by exact (accAdder increasing) |>.get n |>.1

end

def MealyA (I O : Type u) := Mealy I → Mealy O

namespace MealyA

/-- Instance of `Arrow` for `MealyA`. This turns out to be somewhat inefficient because it must re-calculate several times to do `Prod` projections. -/
instance: Arrow MealyA where
  id := instArrowForall.id
  compose := instArrowForall.compose
  arr := Functor.map
  first bc bxd :=
    let (b,d) := bxd.unmerge
    bc b |>.merge d

namespace Mealy.Test

def adderA [Inhabited α] [Add α]: MealyA α α := accAdder

def test3: MealyA Unit Nat := (adderA (α:=Nat)) <<< (fun _ => increasing)

def test4: MealyA Unit Nat := (fun _ => increasing) >>> (adderA (α:=Nat))

#eval (test3 (Mealy.pure ())).repr' 0 (inst:=by reduceAll; exact inferInstance)

#eval (test4 (Mealy.pure ())).repr' 0 (inst:=by reduceAll; exact inferInstance)
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
instance : ArrowLoop MealyA where
  loop {_ _ _} inst m := fun a =>
    Prod.fst <$> (m <| a.scan (reset:=inst.default) fun a b => ((a,b),b))

def adder: MealyA (Nat × Nat) Nat := Arrow.arr ((.+.).uncurry)

open Category Arrow ArrowLoop in
def accAdder': MealyA Nat Nat :=
  loop <| adder >>> ((arr id) &&& (arr id))

section

open Arrow ArrowLoop NotSynthesizable in
#eval
  let m := loop (first accAdder' >>> Category.id (cat:=MealyA) (a:=(Nat× Nat)))
  simulate' (O:=Nat) (m <| (fun i => #[1,2,3,4,5,6][i]!) <$> increasing) 6 |>.map id
open Arrow ArrowLoop NotSynthesizable in
#eval
  let m := accAdder' >>> (loop (Category.id (a:=(Nat× Nat))))
  simulate (O:=Nat) (m <| (let v := #[1,2,3,4,5,6][.]!; dbg_trace v; v) <$> increasing) 1 |>.map fun x => x.fst.repr 0

open NotSynthesizable in
#eval
  simulate' (accAdder' ((let v := #[0,1,2,3,4,5][.]!; dbg_trace v; v) <$> increasing)) 6
open NotSynthesizable in

open Arrow ArrowLoop NotSynthesizable in
#eval
  let m: MealyA Nat Nat := loop (first accAdder' >>> Category.id (a:=(Nat× Nat)))
  simulate (O:=Nat) (m ((#[1,2,3,4,5,6][.]!) <$> increasing)) 6
  |>.map fun x => x.fst.repr' 0 (inst:=by
    rw [x.snd]
    reduceAll
    exact inferInstance
  )

open Arrow ArrowLoop NotSynthesizable in
#eval
  let m := accAdder' >>> (loop (Category.id (a:=(Nat× Nat))))
  simulate (O:=Nat) (m ((#[1,2,3,4,5,6][.]!)<$>increasing)) 6
  |>.map fun x => x.fst.repr' 0 (inst:=by
    rw [x.snd]
    reduceAll
    exact inferInstance
  )

end

open NotSynthesizable in
/--
Mealy machines s₁ and s₂ are defined to be bisimulations if their current values are equal and tails are bisimulations.

See <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Stream/Init.html#Stream'.IsBisimulation>
-/
def Mealy.IsBisimulation (a b : Mealy α) (R : (a:Mealy α) → (b:Mealy α) → Prop) : Prop :=
  a.value = b.value
    ∧ R (a.next.2) (b.next.2)

def Mealy.EqualNow (a b : Mealy α) : Prop := a.value = b.value
