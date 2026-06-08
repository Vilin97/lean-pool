/-
Copyright (c) 2026 Joseph McKinsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph McKinsey
-/
import LeanPool.Flean.FloatCfg
import LeanPool.Flean.LogRules
import LeanPool.Flean.IntRounding

/-!
# Subnormal Floating-Point Representations

This module defines `SubnormRep`, the sign/mantissa representation of subnormal
floating-point numbers, its rational interpretation, rounding to subnormals, and
the validity and error properties of subnormal rounding.
-/

variable {C : FloatCfg}

/-- A sign/mantissa representation of a subnormal floating-point number. -/
structure SubnormRep (C : FloatCfg) where
  /-- The sign bit (`true` for negative). -/
  s : Bool
  /-- The subnormal mantissa. -/
  m : ℕ

/-- Negate a subnormal representation by flipping its sign bit. -/
def SubnormRep.neg (f : SubnormRep C) : SubnormRep C :=
  ⟨¬f.s, f.m⟩

lemma neg_subnorm_involutive : Function.Involutive (@SubnormRep.neg C) := by
  unfold Function.Involutive
  simp [SubnormRep.neg]

/-- A subnormal representation is nonzero when its mantissa is nonzero. -/
def SubnormRep.nonzero (f : SubnormRep C) : Prop := f.m ≠ 0

lemma subnorm_neg_nonzero {f : SubnormRep C} (h : f.nonzero) :
  (f.neg).nonzero := by
  simp only [SubnormRep.nonzero, ne_eq, SubnormRep.neg, Bool.not_eq_true, Bool.decide_eq_false] at *
  exact h

/-- The rational value represented by a subnormal representation. -/
def subnormalToQ : SubnormRep C →  ℚ
| ⟨b, m⟩ =>
  let s := if b then -1 else 1
  s * (m / C.prec) * 2^C.emin

lemma subnormal_to_q_neg (s : SubnormRep C) :
  subnormalToQ s.neg = -subnormalToQ s := by
  rw [subnormalToQ, subnormalToQ, SubnormRep.neg]
  cases s.s <;> simp

lemma subnormal_to_q_nonzero (s : SubnormRep C) :
  subnormalToQ s ≠ 0 ↔ s.nonzero := by
  rw [not_iff_comm]
  simp only [SubnormRep.nonzero, ne_eq, Decidable.not_not]
  constructor
  · intro h
    rw [subnormalToQ, h]
    simp
  intro h
  rw [subnormalToQ] at h
  rcases s with ⟨b, m⟩
  cases b <;>
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, mul_eq_zero, div_eq_zero_iff,
      Nat.cast_eq_zero, neg_mul, neg_eq_zero] at h <;> dsimp <;> {
    rcases h with (h | h) | h
    · exact h
    · linarith [C.prec_pos]
    linarith [zpow_pos (a := (2 : ℚ)) rfl C.emin]
  }


/-- Round a rational to a subnormal representation using the rounder `r`. -/
def subnormalRound (r : IntRounder) (q : ℚ) : SubnormRep C :=
  ⟨q < 0, r (q < 0) (|q| * 2^(-C.emin) * C.prec)⟩

lemma neg_subnormal_round (r : IntRounder) {q : ℚ} (h : q ≠ 0) :
  subnormalRound (C := C) (r.neg) (-q) = SubnormRep.neg (subnormalRound r q) := by
  rw [subnormalRound, subnormalRound, SubnormRep.neg, IntRounder.neg]
  simp only [Left.neg_neg_iff, abs_neg, zpow_neg, decide_eq_true_eq, not_lt, SubnormRep.mk.injEq,
    decide_eq_decide]
  have not_to_ge : 0 < q ↔ 0 ≤ q := by
    exact Iff.symm (Ne.le_iff_lt (id (Ne.symm h)))
  have lt_to_lt : 0 < q ↔ ¬(q < 0) := by
    rw [not_to_ge]
    exact Iff.symm not_lt
  refine ⟨not_to_ge, ?_⟩
  simp_rw [lt_to_lt]
  rw [decide_not]
  simp

/-- Round a rational down to a subnormal representation. -/
def subnormalRoundDown (q : ℚ) : SubnormRep C :=
  subnormalRound round0 q

lemma subnormal_round_coe (r : IntRounder) [rh : ValidRounder r]
  {s : SubnormRep C} (h : s.nonzero) :
  subnormalRound r (subnormalToQ s) = s := by
  --rw [subnormalRound, subnormalToQ]
  wlog h' : s.s = false generalizing r s
  · have t1 := this (r := r.neg) (rh := (neg_valid_rounder r).2 rh) (subnorm_neg_nonzero h)
    have t2 : s.neg.s = false := by simp [SubnormRep.neg, h']
    replace t1 := t1 t2
    rw [subnormal_to_q_neg, neg_subnormal_round] at t1
    · apply neg_subnorm_involutive.injective t1
    rw [subnormal_to_q_nonzero]
    exact h
  rcases s with ⟨b, m⟩
  dsimp at h'
  rw [h'] at h ⊢
  rw [subnormalRound, subnormalToQ]
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul, zpow_neg, SubnormRep.mk.injEq,
    decide_eq_false_iff_not, not_lt]
  have : 0 ≤ ↑m / ↑C.prec * (2 : ℚ) ^ C.emin := by positivity
  constructor
  · exact this
  nth_rw 4 [show m = r false m by symm; apply ValidRounder.leftInverse]
  congr
  · apply decide_eq_false
    exact not_lt_of_ge this
  have hprec : (C.prec : ℚ) ≠ 0 := by
    norm_cast; linarith [C.prec_pos]
  rw [abs_of_nonneg (by positivity), mul_assoc, mul_assoc, <-mul_assoc (2 ^ _),
    mul_inv_cancel₀ (by positivity), one_mul]
  rw [div_mul_cancel₀ _ hprec]


lemma subnormal_round_down_coe (s : SubnormRep C) (h : s.nonzero) :
  subnormalRoundDown (subnormalToQ s) = s :=
  subnormal_round_coe round0 h

lemma subnormal_round_le_of_le (r : IntRounder) [rh : ValidRounder r] (q1 q2 : ℚ)
  (h : q1 ≤ q2) :
  subnormalToQ (C := C) (subnormalRound r q1)
      ≤ subnormalToQ (C := C) (subnormalRound r q2) := by
  by_cases h1 : q1 = 0
  · rw [h1, subnormalRound]
    simp only [lt_self_iff_false, decide_false, abs_zero, zero_mul]
    nth_rw 1 [show (0 : ℚ) = ↑(0 : ℕ) by rfl]
    rw [rh.leftInverse false]
    rw [subnormalToQ]
    simp only [Bool.false_eq_true, ↓reduceIte, CharP.cast_eq_zero, zero_div, mul_zero, zero_mul]
    have : decide (q2 < 0) = false := by simp; linarith
    rw [subnormalToQ, subnormalRound, this]
    dsimp
    positivity
  by_cases h2 : q2 = 0
  · rw [h2]
    nth_rw 2 [subnormalRound]
    simp only [lt_self_iff_false, decide_false, abs_zero, zpow_neg, zero_mul]
    rw [show (0 : ℚ) = ↑(0 : ℕ) by rfl, rh.leftInverse false]
    rw [subnormalToQ, subnormalToQ, subnormalRound]
    simp only [CharP.cast_eq_zero, zero_div, mul_zero, zero_mul]
    have : decide (q1 < 0) = true := by
      apply decide_eq_true
      apply lt_of_le_of_ne ?_ h1
      exact h2 ▸ h
    rw [this]
    simp only [↓reduceIte, neg_mul, one_mul, Left.neg_nonpos_iff, ge_iff_le]
    positivity
  revert h r
  apply casesQPlane (q1 := q1) (q2 := q2)
  · intro q1 q1pos q2 q2pos r rh h
    rw [subnormalRound, subnormalRound]
    rw [subnormalToQ, subnormalToQ]
    rw [decide_eq_false (by linarith), decide_eq_false (by linarith)]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    gcongr
    apply rh.le_iff_le
    · positivity
    gcongr
  · intro q1 q1neg q2 q2pos r rh h
    rw [subnormalRound, subnormalRound]
    rw [subnormalToQ, subnormalToQ]
    rw [decide_eq_true (by linarith), decide_eq_false (by linarith)]
    simp only [↓reduceIte, zpow_neg, neg_mul, one_mul, Bool.false_eq_true]
    have : ∀a b, (0 : ℚ) ≤ a → 0 ≤ b → -a ≤ b := by
      intros a b ha hb
      linarith
    apply this
    · positivity
    positivity
  · intro q1 q1pos q2 q2neg r rh h
    exfalso
    linarith
  · intro q1 q1neg q2 q2neg ih r rh h
    have : -q1 ≤ -q2 := by linarith
    replace ih := ih (r.neg) (rh := rh.neg) this
    rw [neg_subnormal_round, neg_subnormal_round,
      subnormal_to_q_neg, subnormal_to_q_neg] at ih
    · linarith
    · exact Ne.symm (ne_of_gt q2neg)
    exact Ne.symm (ne_of_gt q1neg)
  · exact h1
  exact h2

lemma subnormal_exp_small {q : ℚ} (q_nonneg : q ≠ 0)
  (h : Int.log 2 |q| < C.emin) : |q| * 2 ^ (-C.emin) < 1 := by
  set e := Int.log 2 |q|
  have q_term_small : |q| * 2^(-e) < 2 := by
    rw [zpow_neg]
    exact (mantissa_size_aux q q_nonneg).2
  have emin_smaller_than_e : (2: ℚ)^(-C.emin) ≤ 2^(-e - 1) := by
    rw [zpow_le_zpow_iff_right₀ (by norm_num)]
    linarith
  calc
    |q| * 2 ^ (-C.emin) ≤ |q| * 2^(-e - 1) := by
      exact mul_le_mul_of_nonneg_left emin_smaller_than_e (abs_nonneg _)
    _ = |q| * 2^(-e) / 2 := by
      rw [zpow_sub₀ (by norm_num)]
      ring
    _ < 1 := by linarith

/-- A subnormal rounding map is valid if it never overflows the precision on
inputs below the smallest normal magnitude. -/
def ValidSubnormalRounding (f : ℚ → SubnormRep C) : Prop :=
  ∀ q : ℚ, q ≠ 0 → Int.log 2 |q| < C.emin → (f q).2 ≤ C.prec

lemma subnormal_round_valid (r : IntRounder) [rh : ValidRounder r] :
  ValidSubnormalRounding (subnormalRound r : ℚ → SubnormRep C) := by
  simp only [ValidSubnormalRounding, subnormalRound]
  intro q q_nonneg h
  nth_rw 2 [show C.prec = r (decide (q < 0)) C.prec by symm; apply ValidRounder.leftInverse]
  apply ValidRounder.le_iff_le
  · positivity
  nth_rw 2 [<-one_mul (C.prec : ℚ)]
  apply mul_le_mul_of_nonneg_right
  · apply le_of_lt
    apply subnormal_exp_small q_nonneg h
  linarith [C.prec_pos]

lemma subnorm_zero {s : Bool} :
  subnormalToQ (⟨s, 0⟩ : SubnormRep C) = 0 := by
  simp [subnormalToQ]

lemma roundsub_zero (r : IntRounder) [rh : ValidRounder r] :
  subnormalToQ (subnormalRound r (C := C) 0) = 0 := by
  rw [subnormalToQ, subnormalRound]
  simp only [lt_self_iff_false, decide_false, Bool.false_eq_true, ↓reduceIte, abs_zero, zpow_neg,
    zero_mul, one_mul, mul_eq_zero, div_eq_zero_iff, Nat.cast_eq_zero]
  left
  left
  apply ValidRounder.leftInverse

lemma rounddownsub_le (q : ℚ) :
  subnormalToQ (subnormalRound rounddown (C := C) q) ≤ q := by
  rw [subnormalToQ, subnormalRound, rounddown]
  have t1 : 0 < (C.prec : ℚ) := by norm_cast; exact C.prec_pos
  have t2 : 0 < (2 : ℚ)^C.emin := by positivity
  have t3 := div_pos t1 t2
  by_cases h : q < 0
  · simp only [h, decide_true, ↓reduceIte, zpow_neg, neg_mul, one_mul]
    rw [roundinf_apply, neg_le]
    rw [<-abs_of_pos (a := -q) (Left.neg_pos_iff.mpr h)]
    rw [abs_neg]
    rw [Nat.cast_natAbs]
    simp only [Int.cast_abs]
    rw [abs_of_neg, abs_of_pos]
    · rw [<-div_eq_mul_inv]
      rw [div_mul]--, <-div_le_div_iff_of_pos_right t3]
      rw [le_div_iff₀ t3]
      rw [mul_div, mul_div_right_comm]
      apply Int.le_ceil
    · norm_cast
      apply Int.lt_ceil.mpr
      apply mul_pos ?_ t1
      apply mul_pos ?_ (inv_pos.mpr t2)
      exact Left.neg_pos_iff.mpr h
    exact h
  simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, zpow_neg, one_mul]
  replace h := le_of_not_gt h
  rw [round0_apply, abs_of_nonneg h, Nat.cast_natAbs]
  rw [abs_of_nonneg]
  · rw [<-div_eq_mul_inv]
    rw [div_mul]
    rw [div_le_iff₀ t3]
    rw [mul_div, mul_div_right_comm]
    apply Int.floor_le
  positivity

lemma le_roundupsub (q : ℚ) :
  q ≤ subnormalToQ (subnormalRound roundup (C := C) q) := by
  rw [subnormalToQ, subnormalRound]
  have t1 : 0 < (C.prec : ℚ) := by norm_cast; exact C.prec_pos
  by_cases h : q < 0
  · rw [roundup]
    simp only [h, decide_true, ↓reduceIte, zpow_neg, neg_mul, one_mul]
    rw [le_neg]
    rw [abs_of_neg h, round0_apply, Nat.cast_natAbs]
    rw [Int.cast_abs]
    rw [abs_of_nonneg]
    · rw [<-div_eq_mul_inv]
      rw [div_mul]--, <-div_le_div_iff_of_pos_right t3]
      rw [div_le_iff₀ (div_pos t1 (by positivity))]
      rw [mul_div, mul_div_right_comm]
      apply Int.floor_le
    norm_cast
    apply Int.le_floor.mpr
    apply mul_nonneg ?_ ?_
    · apply mul_nonneg
      · apply le_neg.mpr
        exact le_of_lt h
      positivity
    apply le_of_lt
    exact_mod_cast C.prec_pos
  rw [roundup]
  simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, zpow_neg, one_mul, ge_iff_le]
  replace h := le_of_not_gt h
  rw [roundinf_apply, abs_of_nonneg h, Nat.cast_natAbs]
  rw [abs_of_nonneg]
  · rw [<-div_eq_mul_inv]
    rw [div_mul]--, <-div_le_div_iff_of_pos_right t3]
    rw [le_div_iff₀ (div_pos t1 (by positivity))]
    rw [mul_div, mul_div_right_comm]
    apply Int.le_ceil
  positivity

lemma subnormal_up_minus_down (q : ℚ) :
  subnormalToQ (subnormalRound (C := C) roundup q) -
    subnormalToQ (subnormalRound (C := C) rounddown q) ≤ 2^C.emin * (↑C.prec)⁻¹ := by
  simp_rw [subnormalToQ, subnormalRound, roundup, rounddown]
  simp_rw [round0_apply, roundinf_apply]
  wlog h : q ≥ 0 generalizing q
  · simp at h
    replace this := this (q := -q) (by linarith)
    have h' : ¬(-q < 0) := by linarith
    simp only [h, decide_true, ↓reduceIte, zpow_neg, Nat.cast_natAbs, Int.cast_abs, neg_mul,
      one_mul, sub_neg_eq_add, neg_add_le_iff_le_add, ge_iff_le]
    simp only [h', decide_false, Bool.false_eq_true, ↓reduceIte, abs_neg, zpow_neg, Nat.cast_natAbs,
      Int.cast_abs, one_mul, tsub_le_iff_right] at this
    rw [add_comm]
    exact this
  have h' : ¬(q < 0) := by linarith
  simp only [h', decide_false, Bool.false_eq_true, ↓reduceIte, zpow_neg, one_mul, tsub_le_iff_right,
    ge_iff_le]
  rw [Nat.cast_natAbs, Nat.cast_natAbs]
  rw [abs_of_nonneg (by positivity)]
  nth_rw 2 [abs_of_nonneg (by positivity)]
  have := Int.ceil_le_floor_add_one (|q| * ((2 : ℚ)^C.emin)⁻¹ * C.prec)
  have h : StrictMono (fun x => x / C.prec * (2 : ℚ)^C.emin) := by
    apply StrictMono.mul_const _ (by positivity)
    apply StrictMono.div_const
    · exact fun ⦃a b⦄ a ↦ a
    · exact_mod_cast C.prec_pos
  qify at this
  apply h.monotone at this
  -- This is especially brittle
  simp at this
  field_simp at this
  field_simp
  rw [add_comm] at this
  exact this

lemma subnormal_round_neg (r : IntRounder) {q : ℚ} (h : q ≠ 0) :
  subnormalRound r.neg (-q) = (subnormalRound (C := C) r q).neg := by
  simp only [subnormalRound, SubnormRep.neg, IntRounder.neg]
  congr 2
  · simp [h.symm.le_iff_lt]
  · simp [<-decide_not, h.le_iff_lt]
  simp

lemma subnormal_round_eq_up_down (r : IntRounder) [rh : ValidRounder r] (q : ℚ) :
  subnormalRound r q = subnormalRound (C := C) rounddown q ∨
  subnormalRound r q = subnormalRound (C := C) roundup q := by
  unfold subnormalRound
  set x := |q| * 2^(-C.emin) * C.prec
  have := round_eq_or' (r := r) (b := q < 0)
      (q := x) (h := by positivity)
  rcases this with this | this
  · simp [this]
  simp [this]

lemma subnormal_round_close (r : IntRounder) [rh : ValidRounder r] (q : ℚ) :
  |q - subnormalToQ (subnormalRound (C := C) r q)| ≤ 2^C.emin / C.prec := by
  apply le_trans (b := subnormalToQ (subnormalRound (C := C) roundup q)
    - subnormalToQ (subnormalRound (C := C) rounddown q))
  · rcases subnormal_round_eq_up_down r q with h | h
    · rw [h, abs_of_nonneg (by rw [sub_nonneg]; exact rounddownsub_le q)]
      rw [sub_le_sub_iff_right]
      exact le_roundupsub q
    · rw [h, abs_sub_comm,
        abs_of_nonneg (by rw [sub_nonneg]; exact le_roundupsub q)]
      rw [sub_le_sub_iff_left]
      exact rounddownsub_le q
  · exact subnormal_up_minus_down q

lemma subnormal_near_close (q : ℚ) :
  |q - subnormalToQ (subnormalRound (C := C) roundnearest q)| ≤ 2^(C.emin - 1) / C.prec := by
  by_cases h : q = 0
  · rw [h]
    simp only [subnormalToQ, subnormalRound, lt_self_iff_false, decide_false, roundnearest_apply,
      roundNearInt, abs_zero, zpow_neg, zero_mul, Int.fract_zero, one_div, inv_pos, Nat.ofNat_pos,
      ↓reduceIte, Int.floor_zero, Int.natAbs_zero, Bool.false_eq_true, CharP.cast_eq_zero, zero_div,
      mul_zero, sub_self]
    positivity
  wlog h' : 0 < q generalizing q
  · have negq : 0 < -q := by
      apply lt_of_le_of_ne (by linarith)
      exact (neg_ne_zero.mpr h).symm
    replace this := this (q := -q) (by linarith) negq
    rw [<-roundnearest_neg] at this
    rw [subnormal_round_neg (h := h), subnormal_to_q_neg] at this
    rw [neg_sub_neg, abs_sub_comm] at this
    exact this
  rw [subnormalRound, roundnearest_apply]
  have : ¬(q < 0) := by linarith
  simp only [this, decide_false, ge_iff_le, subnormalToQ, Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [Nat.cast_natAbs]
  rw [abs_of_pos h']
  nth_rw 2 [abs_of_nonneg (by positivity)]
  calc
    |q - (roundNearInt (q * 2 ^ (-C.emin) * ↑C.prec)) / ↑C.prec * 2 ^ C.emin| =
      |q * 2^(-C.emin) * C.prec / C.prec * 2^C.emin
        - (roundNearInt (q * 2 ^ (-C.emin) * ↑C.prec)) / ↑C.prec * 2 ^ C.emin| := by
      rw [mul_div_cancel_right₀]
      · rw [mul_assoc (c := 2^_)]
        rw [zpow_neg, inv_mul_cancel₀ (by positivity), mul_one]
      exact_mod_cast ne_of_gt C.prec_pos
    _ = |q * 2^(-C.emin) * C.prec - (roundNearInt (q * 2 ^ (-C.emin) * ↑C.prec))|
          / C.prec * 2^C.emin := by
      rw [<-sub_mul, <-sub_div, abs_mul, abs_div,
        abs_of_pos (a := 2^C.emin) (by positivity),
        abs_of_pos (a := (C.prec : ℚ))]
      exact_mod_cast C.prec_pos
    _ ≤ 1 / 2 / C.prec * 2^C.emin := by
      apply mul_le_mul_of_nonneg_right ?_ (by positivity)
      apply div_le_div_of_nonneg_right
      · rw [abs_sub_comm]
        exact round_near_int_le (q * 2^(-C.emin) * C.prec)
      exact_mod_cast le_of_lt C.prec_pos
    _ = 2^(C.emin - 1) / C.prec := by
      rw [zpow_sub₀ (by linarith)]
      field_simp
