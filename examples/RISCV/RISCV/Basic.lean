import Hdlean

@[simp] instance : Coe Bool (BitVec n) where
  coe
    | .true => 1
    | .false => 0
instance : OfNat Bool 0 := ⟨false⟩
instance : OfNat Bool 1 := ⟨true⟩

/-- Vectors of length 0 are always inhabited even if α is not. -/
instance : Inhabited (Vector α 0) := ⟨#v[]⟩
example : Vector Empty 0 := default

instance : HAppend (α) (Vector α n) (Vector α (1+n)) where
  hAppend a b := #v[a] ++ b
instance : HAppend (Vector α n) (α) (Vector α (n+1)) where
  hAppend a b := a ++ #v[b]

/-- A subvector with the provided bounds.

Unmentioned bounds use `Vector.extract`'s default of extending to extremes.
-/
syntax:max (name:=vec_slice) term noWs "[" withoutPosition((term)? ":" (term)?) "]" : term
macro_rules (kind:=vec_slice)
  | `($a[$start : $stop]) => `(Vector.extract $a $start $stop)
  | `($a[$start : ])      => `(let a := $a; Vector.extract a $start a.size)
  | `($a[ : $stop])       => `(Vector.extract $a 0 $stop)
  | `($a[ : ])            => `(Vector.extract $a)

def Vector.dfoldl.tail {β : Nat → Type u} (f : ∀ (i : Nat), β i → α → β (i+1)) (init : β 0): ∀ {n}, (v : Vector α n) → β n := fun {n} v =>
  let rec go (i : Nat) (h : i ≤ n) (acc : β i) : β n :=
    if hlt : i < n then
      let elem := v.get ⟨i, hlt⟩
      go (i+1) (by omega) (f i acc elem)
    else
      have : i = n := by omega
      this ▸ acc
  go 0 (by omega) init

def Vector.dfoldl.tail' {β : Nat → Type u} (f : ∀ (i : Nat), β i → α → β (i+1))
    (init : β 0) : ∀ {n}, Vector α n → β n := fun v =>
  cast (by simp only [Nat.zero_add]) <| dfoldl_aux f 0 init v
where
  dfoldl_aux {β : Nat → Type u} (f : ∀ (i : Nat), β i → α → β (i+1))
      : ∀ (start : Nat) (acc : β start) {n}, Vector α n → β (start + n)
    | start, acc, 0, _ => acc
    | start, acc, n+1, v =>
      let hd := v.head
      let tl := v.tail
      have : start + (n + 1) = (start + 1) + n := by omega
      this ▸ dfoldl_aux f (start + 1) (f start acc hd) tl

/-- Dependent `Vector.foldl`  -/
def Vector.dfoldl {β : Nat → Type u} (f : ∀ (i : Nat), β i → α → β (i+1)) (init : β 0) : ∀ {n}, Vector α n → β n
  | 0,   _ => init
  | n+1, v => f n (Vector.dfoldl f init v.pop) v.back

@[simp] theorem Vector.dfoldl_succ {β : Nat → Type u} (f : ∀ (i : Nat), β i → α → β (i+1)) (init : β 0) (v : Vector α (n+1)):
  dfoldl f init v = f (n) (dfoldl f init v.pop) v.back
:= rfl

theorem Vector.get_pop {α : Type _} {n : Nat} (v : Vector α (n+1)) (i : Nat) (h : i < n) :
    (v.pop).get ⟨i, h⟩ = v.get ⟨i, Nat.lt_trans h (Nat.lt_succ_self n)⟩ := by
  simp [Vector.get]

theorem Vector.get_last {α : Type _} {n : Nat} (v : Vector α (n+1)) :
    v.get ⟨n, Nat.lt_succ_self n⟩ = v.back := by
  simp [Vector.back, Vector.get]

-- Key idea: fold over n elements is equivalent to fold over first n-1 elements then apply f
theorem Vector.dfoldl_tail_go_pop {α : Type _} {β : Nat → Type u}
    (f : ∀ i, β i → α → β (i+1))
    (v : Vector α (n+1)) (i : Nat) (hi : i ≤ n) (acc : β i) :
    f n (Vector.dfoldl.tail.go f v.pop i hi acc) v.back =
    Vector.dfoldl.tail.go f v i (Nat.le_trans hi (Nat.le_succ n)) acc := by
  induction h : n - i generalizing i acc
  case zero =>
    have : i = n := by omega
    subst i
    -- Both sides unfold to acc since i = n means we don't enter the loop
    unfold Vector.dfoldl.tail.go
    unfold Vector.dfoldl.tail.go
    rw [Vector.back_eq_getElem]
    simp only [Nat.add_one_sub_one, Nat.lt_irrefl, ↓reduceDIte, Nat.lt_add_one]
    rfl
  case succ m ih =>
    have hlt : i < n := by omega
    have hlt' : i < n + 1 := by omega
    unfold Vector.dfoldl.tail.go
    have get_eq : v.pop.get ⟨i, hlt⟩ = v.get ⟨i, Nat.lt_trans hlt (Nat.lt_succ_self n)⟩ :=
      Vector.get_pop v i hlt
    simp only [↓reduceDIte, hlt, get_eq, hlt']
    rw [← ih (i + 1) (_) (f i acc (v.get ⟨i, _⟩))]
    omega

theorem Vector.dfoldl_tail_key {α : Type _} {β : Nat → Type u}
    (f : ∀ i, β i → α → β (i+1)) (init : β 0) (v : Vector α (n+1)) :
    dfoldl.tail f init v = f n (dfoldl.tail f init v.pop) v.back := by
  unfold dfoldl.tail
  rw [dfoldl_tail_go_pop f]

theorem Vector.dfoldl_eq_tail : @Vector.dfoldl = @Vector.dfoldl.tail := by
  funext α β f init n v
  induction n -- note v already generalized since it depends on n
  . unfold Vector.dfoldl Vector.dfoldl.tail dfoldl.tail.go dfoldl.tail.go
    simp only [Nat.lt_irrefl, ↓reduceDIte]
  case _ n ih =>
    have := ih v.pop
    unfold Vector.dfoldl
    rw [this, dfoldl_tail_key]

attribute [csimp] Vector.dfoldl_eq_tail

/-- `Vector.foldl` but for `BitVec` interpreted as a `Vector Bool`  -/
def BitVec.dfoldl {β : Nat → Type u} (f : ∀ (i : Nat), β i → Bool → β (i+1)) (init : β 0) (v : BitVec n) : β n :=
  let rec go (i : Nat) (h : i ≤ n) (acc : β i) : β n :=
    if hlt : i < n then
      let elem := v.getLsb ⟨i, hlt⟩
      go (i+1) (by omega) (f i acc elem)
    else
      have : i = n := by omega
      this ▸ acc
  go 0 (by omega) init

def BitVec.dfoldl' {β : Nat → Type u} (f : ∀ (i : Nat), β i → Bool → β (i+1)) (init : β 0) : ∀ {n}, BitVec n → β n
  | 0,   _ => init
  | n+1, v => f n (dfoldl' f init (v.extractLsb' 0 n)) v.msb

theorem List.mem_of_mem_dropLast {l:List α} (hmem:x ∈ l.dropLast): x ∈ l := by
  unfold List.dropLast at hmem
  split at hmem
  . exact hmem
  . contradiction
  case _ _ l _ =>
    simp only [mem_cons] at hmem
    simp only [mem_cons]
    exact match hmem with
    | .inl h => .inl h
    | .inr h => .inr <| List.mem_of_mem_dropLast h


theorem Vector.mem_of_mem_pop {v : Vector α n} (h : a ∈ v.pop): a ∈ v := by
  simp only [Vector.pop, Array.pop, mem_mk, List.mem_toArray] at h
  have := List.mem_of_mem_dropLast h
  rw [← Vector.toList] at this
  exact mem_toList_iff.mp this

set_option linter.unusedVariables false in -- keep hinduct and hbase names
/-- Like  List.foldlRecOn, but for `Vector`s.
  Possible (but inefficient) to use for actual computation.
-/
def Vector.dfoldlRecOn {β : Nat → Sort _} {motive : (n:Nat) → β n → Sort _}
    : ∀ {n : Nat} (v : Vector α n) (op : ∀ (i : Nat), β i → α → β (i+1))
      {b : β 0} (hbase : motive 0 b)
      (hinduct : ∀ (i : Fin n) (b : β i) (_ : motive i b) (a : α) (_ : a = v[i]), motive (i+1) (op i b a)),
      motive n (Vector.dfoldl op b v) := by
  intro n
  induction n with
  | zero =>
    intro v op b hbase hinduct
    simp [Vector.dfoldl]
    exact hbase
  | succ n ih =>
    intro v op b hbase hinduct
    simp [Vector.dfoldl]
    -- Get the last element and the rest
    let last := v.back
    let init := v.pop
    -- Apply IH to get motive for the recursive call
    have ih_result := ih init op hbase  fun i b' hb' a ha =>
      have : init[i] = v[i.castSucc] := Vector.getElem_pop _
      let ret := hinduct i.castSucc b' hb' a (Eq.trans ha this)
      ret
    -- Apply hinduct for the last element
    exact hinduct ⟨n, Nat.lt_add_one n⟩ (Vector.dfoldl op b init) ih_result last Vector.back_eq_getElem

def Vector.toBitVec (v: Vector Bool n): BitVec n :=
  v.dfoldl (β:=BitVec) (init:=0) fun _ b bit =>
    b.append (Coe.coe bit)

def Vector.toBitVec' (v: Vector Bool n): BitVec n :=
  v.dfoldl (β:=BitVec) (init:=0) fun _ b bit =>
    BitVec.cast (by grind only) <| (Coe.coe bit : BitVec 1).append b

example : #v[].toBitVec = 0#0 := by native_decide
example : #v[].toBitVec = 1#0 := by native_decide
example : #v[0].toBitVec = 0 := by native_decide
example : #v[1].toBitVec = 1 := by native_decide
example : #v[0,0,0].toBitVec = 0#3 := by native_decide
example : #v[1,1,1].toBitVec = 7#3 := by native_decide
example : #v[0,0,0,1].toBitVec = 1#4 := by native_decide
example : #v[0,1,0,1].toBitVec = 5#4 := by native_decide

def BitVec.toVector (b: BitVec n): Vector Bool n :=
  b.dfoldl' (β := Vector Bool) (init:=#v[]) fun n v bit =>
    Nat.add_comm n 1 ▸ (#v[bit] ++ v)

def BitVec.toVector' (b: BitVec n): Vector Bool n :=
  b.dfoldl' (β := Vector Bool) (init:=#v[]) fun _ v bit => v.push bit

example :  (0#0 : BitVec _).toVector = #v[]:= by native_decide
example :  (1#0 : BitVec _).toVector = #v[]:= by native_decide
example :  (0 : BitVec _).toVector = #v[0]:= by native_decide
example :  (1 : BitVec _).toVector = #v[1]:= by native_decide
example :  (0#3 : BitVec _).toVector = #v[0,0,0]:= by native_decide
example :  (7#3 : BitVec _).toVector = #v[1,1,1]:= by native_decide
example :  (1#4 : BitVec _).toVector = #v[0,0,0,1]:= by native_decide
example : (1#4).toVector = #v[0,0,0,1] := rfl
example :  (5#4 : BitVec _).toVector = #v[0,1,0,1]:= by native_decide
example : (8#3).toVector.toBitVec = 8#3 := rfl

@[simp] theorem BitVec.toVector_idx_eq (b: BitVec n) (i : Fin n): b.toVector'[i] = b[i] := by
  simp [BitVec.toVector']
  induction n
  case zero => grind only
  case succ n ih =>
    unfold dfoldl'
    have ih := ih (extractLsb' 0 n b)
    if h : i = n then
      simp [h]
      grind
    else
      let i' := i.castLT (by
        change i < n
        omega
      )
      have ih' := ih i'
      rw [Vector.getElem_push_lt]
      conv =>
        enter [1,2]
        change i'.val
      conv =>
        enter [2,2]
        change i'.val
      rw [ih']
      simp
      . grind
      . omega

@[simp] theorem Vector.toBitVec_idx_eq (v: Vector Bool n) (i : Fin n): v.toBitVec'[i] = v[i] := by
  simp [Vector.toBitVec']
  apply Vector.dfoldlRecOn v _
    (motive := fun n' (bv : BitVec n') =>
      ∀ (i' : Fin n'), (i'_lt_n:i' < n) → bv[i'] = v[i'])
    (hbase := fun i _ => i.elim0)
  case i'_lt_n => simp
  case hinduct =>
    intros n' bv hi a a_getElem_v i' i'_lt_n
    simp only [Fin.getElem_fin, BitVec.getElem_cast]
    rw [BitVec.getElem_append]
    -- Either the index extracts a bit from before appending
    if h: i' < n'.val then
      let i' := i'.castLT h
      simp [h]
      exact hi i' _
    -- Or the new bit
    else
      have : i'.val = n'.val := by omega
      have : v[i'.val] = v[n'.val] := by simp only [this]
      rw [a_getElem_v, this]
      simp [h]
      cases v[n'] <;> simp only [BitVec.getElem_zero, BitVec.getElem_one, decide_eq_true_eq]
      omega

-- #check BitVec.eq_of_getElem_eq
-- #check Vector.ext
@[simp] theorem toBitVecToVector (v : Vector Bool n) : v.toBitVec'.toVector' = v := by
  suffices ∀ (i : Fin n), v.toBitVec'.toVector'[i] = v[i] by
    apply Vector.ext
    intro i i_lt_n
    exact this ⟨i, i_lt_n⟩
  intro i
  rw [BitVec.toVector_idx_eq, Vector.toBitVec_idx_eq]

theorem toVectorToBitVec (bv : BitVec n) : bv.toVector'.toBitVec' = bv := by
  suffices ∀ (i : Fin n), bv.toVector'.toBitVec'[i] = bv[i] by
    apply BitVec.eq_of_getElem_eq
    intro i i_lt_n
    exact this ⟨i, i_lt_n⟩
  intro i
  rw [Vector.toBitVec_idx_eq, BitVec.toVector_idx_eq]

instance : Coe (Vector Bool n) (BitVec n) := ⟨Vector.toBitVec⟩
instance : Coe (BitVec n) (Vector Bool n) := ⟨BitVec.toVector⟩

def Vector.modifyM [Monad m] (xs : Vector α n) (i : Fin n) (f : α → m α) : m (Vector α n) := do
  let v   := xs[i]
  let v ← f v
  pure <| xs.set i v
def Vector.modify (xs : Vector α n) (i : Fin n) (f : α → α) : Vector α n :=
  Id.run <| Vector.modifyM xs i (pure <| f ·)
def Vector.modifyOp (xs : Vector α n) (idx : Fin n) (f : α → α) : Vector α n :=
  xs.modify idx f
