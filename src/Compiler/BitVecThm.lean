instance (n:Nat): Trans (α:=BitVec n) (β:=BitVec n) (γ:=BitVec n) (. < .) (. < .) (. < .) where
  trans := by
    intro a b c a_lt_b b_lt_c
    unfold instLTBitVec BitVec.toNat BitVec.toFin Fin.val at *
    simp only at *
    omega

#synth Trans (α:=BitVec 3) (β:=BitVec 3) (γ:=BitVec 3) (. < .) (. < .) (. < .)

theorem BitVec.lt_imp_nonnil.aux (a b : BitVec n) (h: a < b): 0 < n := by
  false_or_by_contra
  rename_i h2
  simp at h2
  subst h2
  rw [BitVec.eq_nil a, BitVec.eq_nil b] at h
  exact Nat.not_succ_le_zero BitVec.nil.toNat h
@[simp] theorem BitVec.lt_imp_nonnil (a b : BitVec n) (h: a < b): n ≠ 0 := by
  apply Nat.ne_zero_of_lt
  apply BitVec.lt_imp_nonnil.aux
  exact h

theorem BitVec.sub_nonequal_of_lt (a b: BitVec n) (b_lt_a: b < a): a ≠ b := by exact?

theorem BitVec.sub_nonzero_of_lt (a b: BitVec n) (b_lt_a: b < a): a - b ≠ 0 := by
  -- have : ∀ (n:Nat), 0 < n → n ≠ 0 := by exact fun n a => Nat.ne_zero_of_lt a
  -- have : n ≠ 0 := lt_imp_nonzero_size b a b_lt_a
  -- have : a ≠ b := by exact Ne.symm (BitVec.ne_of_lt b_lt_a)
  -- intro h
  -- have : ∀ a b, b ≤ a → a - b = 0 → a = b := by omega
  bv_omega

theorem BitVec.sub_lt_of_lt_of_le (a b : BitVec n) (a_lt_b: a < b) (ha: m ≤ a): (a - m < b - m) := by
  have := BitVec.lt_imp_nonnil a b a_lt_b
  have : 2^n ≠ 0 := by simp [this]
  unfold instHSub Sub.sub BitVec.instSub BitVec.sub
  simp
  have h1 := Nat.mod_eq_iff_lt (m:=2 ^ n - m.toNat + a.toNat) this |>.mpr
  have h2 := Nat.mod_eq_iff_lt (m:=2 ^ n - m.toNat + b.toNat) this |>.mpr
  rw [h1,h2]
  bv_omega
  . bv_omega
  . bv_omega

#synth Trans (α:=BitVec 3) (β:=BitVec 3) (γ:=BitVec 3) (. < .) (. < .) (. < .)
