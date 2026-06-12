/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import LeanPool.ComputableReal.SpecialFunctions.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Verified rational bounds for pi

Rational lower and upper bounds for `Real.pi` are derived from the
`Real.sqrtTwoAddSeries` approximation, shown to converge, and packaged into a
`ComputableℝSeq.Pi`, giving an `IsComputable` instance for `Real.pi`. The bounds
go through the `noncomputable` square-root sequences, so `Pi` and the derived
bounds `piLb`/`piUb` are `noncomputable` Lean terms.
-/

open scoped QInterval

namespace ComputableℝSeq

section Pi

private theorem mul_le_of_le_of_le_one_of_nonneg {a b c : ℝ} (hac : a ≤ c) (hb : b ≤ 1)
    (ha : 0 ≤ a) : a * b ≤ c :=
  (mul_le_of_le_one_right ha hb).trans hac

noncomputable instance instComputableSqrtTwoAddSeries (x : ℝ) [hx : IsComputable x] (n : ℕ) :
    IsComputable (Real.sqrtTwoAddSeries x n) :=
  n.rec hx (fun _ _ ↦ IsComputable.instComputableSqrt _)

/-- Definition of `sqrtTwoAddSeriesN`. -/
noncomputable def sqrtTwoAddSeriesN : ℕ → ComputableℝSeq :=
  fun n ↦ (instComputableSqrtTwoAddSeries 0 n).seq

theorem sqrtTwoAddSeriesN_lb_le (n k : ℕ) : (sqrtTwoAddSeriesN n).lb k ≤ Real.sqrtTwoAddSeries 0
  n := by
  rw [← IsComputable.prop (x := Real.sqrtTwoAddSeries 0 n)]
  exact ComputableℝSeq.hlb _ _

theorem sqrtTwoAddSeriesN_ub_ge (n k : ℕ) : Real.sqrtTwoAddSeries 0 n ≤ (sqrtTwoAddSeriesN n).ub
  k := by
  rw [← IsComputable.prop (x := Real.sqrtTwoAddSeries 0 n)]
  exact ComputableℝSeq.hub _ _

theorem sqrtTwoAddSeriesN_ub_pos (n k : ℕ) : (0 : ℝ) ≤ (sqrtTwoAddSeriesN n).ub k := by
   exact le_trans (Real.sqrtTwoAddSeries_zero_nonneg n) (sqrtTwoAddSeriesN_ub_ge n k)

theorem sqrtTwoAddSeriesN_lb_lt_two (n k : ℕ) : (sqrtTwoAddSeriesN n).lb k < 2 := by
  rify
  refine lt_of_le_of_lt ?_ (Real.sqrtTwoAddSeries_lt_two n)
  convert ComputableℝSeq.hlb _ _
  symm
  exact IsComputable.prop

theorem sqrtTwoAddSeriesN_succ_lb (n k : ℕ) :
    (sqrtTwoAddSeriesN (n + 1)).lb k = (Sqrt.sqrtq (2 + (sqrtTwoAddSeriesN n).lub k) k).fst := by
  rfl

theorem sqrtTwoAddSeriesN_succ_ub (n k : ℕ) :
    (sqrtTwoAddSeriesN (n + 1)).ub k = (Sqrt.sqrtq (2 + (sqrtTwoAddSeriesN n).lub k) k).snd := by
  rfl

theorem sqrtTwoAddSeriesN_lb_nonneg (n k : ℕ) : 0 ≤ (sqrtTwoAddSeriesN n).lb k := by
  cases n
  · rfl
  · apply Sqrt.sqrtq_nonneg

theorem sqrtTwoAddSeriesN_lb_gt_one (n k : ℕ) (hk : 3 ≤ k) : 1 ≤ (sqrtTwoAddSeriesN (n + 1)).lb k
  := by
  have h₀ : (0 : ℝ) ≤ ((sqrtTwoAddSeriesN n).lub k).snd := sqrtTwoAddSeriesN_ub_pos n k
  rw [sqrtTwoAddSeriesN_succ_lb, Sqrt.sqrt_lb_def,
    if_neg (by push Not; change 0 < 2 + _; rify; positivity)]
  clear h₀
  have h₁ := sqrtTwoAddSeriesN_lb_nonneg n k
  rify at h₁ ⊢
  rw [show (2 + (sqrtTwoAddSeriesN n).lub k).toProd.1 = 2 + (sqrtTwoAddSeriesN n).lb k by rfl]
  set x : ℚ := (sqrtTwoAddSeriesN n).lb k
  have h₂ := Sqrt.sqrt_le_mkRat_add (2 + x) k
  generalize ↑(mkRat (Int.sqrt ((2 + x).num * 4 ^ k)) (((2 + x).den * 4 ^ k).sqrt + 1))=y at h₂ ⊢
  replace h₂ : √↑(2 + x) * (1 - 2 / 2^k) ≤ y := by
    ring_nf at h₂ ⊢
    linarith
  refine le_trans ?_ (le_trans (a := √↑(2 + x) * 3 / 4) ?_ h₂)
  · suffices 4 / 3 ≤ √↑(2 + x) by linarith
    apply Real.le_sqrt_of_sq_le
    push_cast
    linarith
  · rw [← mul_div]
    apply mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    rw [show (3 / 4 : ℝ) = 1 - 2 / 8 by norm_num]
    apply sub_le_sub_left
    apply div_le_div₀ zero_le_two le_rfl Nat.ofNat_pos'
    rw [show 8 = (2 : ℝ) ^ 3 by norm_num]
    exact_mod_cast Nat.pow_le_pow_right (by norm_num) hk

theorem sqrtTwoAddSeriesN_bounds (n k : ℕ) (hk : 3 ≤ k) :
    (sqrtTwoAddSeriesN n).ub k ≤ (sqrtTwoAddSeriesN n).lb k + 18 * n / 2^k
    := by
  induction n
  · simp only [CharP.cast_eq_zero, zero_div, mul_zero, add_zero]
    rfl
  rename_i n ih
  dsimp [lb, ub] at ih
  rify at ih ⊢
  rw [sqrtTwoAddSeriesN_succ_lb, sqrtTwoAddSeriesN_succ_ub]
  set x := ((sqrtTwoAddSeriesN n).lub k)
  have hl : (2 + x).fst ≤ 2 + Real.sqrtTwoAddSeries 0 n := by
    change ((2 + _ : ℚ) : ℝ) ≤ _
    rw [Rat.cast_add, Rat.cast_ofNat, add_le_add_iff_left]
    convert ComputableℝSeq.hlb _ _
    symm
    exact IsComputable.prop
  have hu : 2 + Real.sqrtTwoAddSeries 0 n ≤ (2 + x).snd := by
    change _ ≤ ((2 + _ : ℚ) : ℝ)
    rw [Rat.cast_add, Rat.cast_ofNat, add_le_add_iff_left]
    rw [← ge_iff_le]
    convert ComputableℝSeq.hub _ _
    symm
    exact IsComputable.prop
  have hm : 0 < (2 + x).fst := by
    change 0 < 2 + _
    suffices 0 ≤ x.fst by linarith
    apply sqrtTwoAddSeriesN_lb_nonneg n k
  have h₁ := Sqrt.sqrt_le_sqrtq_add (2 + Real.sqrtTwoAddSeries 0 n) (2 + x) k ⟨hl, hu⟩ hm
  have h₂ := Sqrt.sqrtq_sub_le_sqrt (2 + Real.sqrtTwoAddSeries 0 n) (2 + x) k ⟨hl, hu⟩ hm hk
  simp only [show (2 + x).snd = 2 + x.snd by rfl, show (2 + x).fst = 2 + x.fst by rfl] at h₁ h₂
  simp only [Rat.cast_add, Rat.cast_ofNat, add_sub_add_left_eq_sub, tsub_le_iff_right] at h₁ h₂
  set y := √(2 + Real.sqrtTwoAddSeries 0 n)
  set z := (Sqrt.sqrtq (2 + x) k).fst
  set w := (Sqrt.sqrtq (2 + x) k).snd
  set x₁ := x.fst
  set x₂ := x.snd
  have hgap : w - z ≤ (3 / 2) * ((↑x₂ - ↑x₁) / (√(2 + ↑x₁))) + 9 * y / 2^k := by
    rw [← mul_div] at h₁ h₂ ⊢
    conv at h₁ =>
      enter [2,2,2]
      rw [_root_.mul_comm]
    rw [← div_div] at h₁
    linarith
  have hxdiv : 3 / 2 * ((↑x₂ - ↑x₁) / √(2 + ↑x₁)) ≤ 18 * ↑n / 2 ^ k := by
    rcases n with _|n
    · simp [show x₁ = 0 by rfl, show x₂ = 0 by rfl]
    suffices (3 / 2) / √(2 + ↑x₁) ≤ 1 by
      rw [mul_div, _root_.mul_comm, ← mul_div]
      apply mul_le_of_le_of_le_one_of_nonneg
      · linarith
      · exact this
      · have : (x.fst : ℝ) ≤ x.snd := by exact_mod_cast x.fst_le_snd
        linarith [x.fst_le_snd]
    have hx₂ : 1 ≤ x₁ :=
      sqrtTwoAddSeriesN_lb_gt_one _ _ hk
    rify at hx₂
    rw [div_le_one₀ (by positivity), Real.le_sqrt' (by positivity)]
    linarith
  have hydiv : 9 * y / 2^k ≤ 18 / 2^k := by
    rw [div_le_div_iff_of_pos_right]
    · have hy2 : y < 2 := Real.sqrtTwoAddSeries_lt_two (n.succ)
      linarith
    · exact_mod_cast Nat.two_pow_pos k
  rw [mul_add, add_div]
  linarith

/-- Definition of `sqrtTwoSubSqrtTwoAddSeriesN`. -/
noncomputable def sqrtTwoSubSqrtTwoAddSeriesN : ℕ → ComputableℝSeq :=
  fun n ↦ (inferInstance : IsComputable (Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n))).seq

theorem sqrtTwoSubSqrtTwoAddSeries_eq (n k : ℕ) :
    (sqrtTwoSubSqrtTwoAddSeriesN n).lub k = Sqrt.sqrtq ((2 - sqrtTwoAddSeriesN n).lub k) k := by
  rfl

theorem real_sqrtTwoAddSeries_lb (n : ℕ) : 1 / 2 ^ n < √(2 - Real.sqrtTwoAddSeries 0 n) := by
  have h : 2 ≤ Real.pi - 1 / 4 ^ n := by
    have : 1 / 4 ^ n ≤ (1 : ℝ) := by
      rw [one_div]
      apply inv_le_one_of_one_le₀
      exact_mod_cast Nat.one_le_pow' n 3
    linarith [Real.pi_gt_three]
  have h₂ := lt_of_le_of_lt h (sub_right_lt_of_lt_add (Real.pi_lt_sqrtTwoAddSeries n))
  ring_nf at h₂
  rwa [lt_mul_iff_one_lt_left zero_lt_two, ← div_lt_iff₀ (by positivity)] at h₂

theorem sqrtTwoSubSqrtTwoAddSeries_lb (n k : ℕ) (hk : 3 ≤ k) :
    √(2 - Real.sqrtTwoAddSeries 0 n) ≤ (sqrtTwoSubSqrtTwoAddSeriesN n).lb k +
    (18 * n * 2 ^ n + 4) / 2 ^ k
     := by
  dsimp [lb]
  rw [sqrtTwoSubSqrtTwoAddSeries_eq]
  have h₁ := Sqrt.sqrt_le_sqrtq_add' (2 - Real.sqrtTwoAddSeries 0 n) ((2 - sqrtTwoAddSeriesN
    n).lub k) k
    ⟨?_, ?_⟩ ?_; rotate_left
  · change ((2 + -_ : ℚ) : ℝ) ≤ _
    rw [Rat.cast_add, Rat.cast_ofNat, Rat.cast_neg]
    apply tsub_le_tsub_left
    rw [← ge_iff_le]
    convert ComputableℝSeq.hub _ _
    symm
    exact IsComputable.prop
  · change _ ≤ ((2 + -_ : ℚ) : ℝ)
    rw [Rat.cast_add, Rat.cast_ofNat, Rat.cast_neg]
    apply tsub_le_tsub_left
    convert ComputableℝSeq.hlb _ _
    symm
    exact IsComputable.prop
  · linarith [Real.sqrtTwoAddSeries_lt_two n]
  have hx : ((2 - sqrtTwoAddSeriesN n).lub k).fst = 2 - (sqrtTwoAddSeriesN n).ub k := by
    change (2 +- _) = _
    rw [sub_eq_add_neg]
    rfl
  have hy : ((2 - sqrtTwoAddSeriesN n).lub k).snd = 2 - (sqrtTwoAddSeriesN n).lb k := by
    change (2 +- _) = _
    rw [sub_eq_add_neg]
    rfl
  simp only [hx, hy, Rat.cast_sub, Rat.cast_ofNat, sub_sub_sub_cancel_left] at h₁
  clear hx hy
  have h₄ := Real.sqrtTwoAddSeries_zero_nonneg n
  have h₅ := Real.sqrtTwoAddSeries_lt_two n
  have h₆ := sqrtTwoAddSeriesN_bounds n k hk
  have h₇ := (real_sqrtTwoAddSeries_lb n).le
  generalize
    (Sqrt.sqrtq ((2 - sqrtTwoAddSeriesN n).lub k) k).fst=w,
    (sqrtTwoAddSeriesN n).lb k=x,
    (sqrtTwoAddSeriesN n).ub k=y,
    Real.sqrtTwoAddSeries 0 n=z at *
  have h₈ : (↑y - ↑x) / √(2 - z) ≤ 18 * ↑n / 2 ^ k * 2 ^ n := by
    rw [div_eq_mul_inv]
    apply mul_le_mul
    · rify at h₆
      linarith
    · rw [← inv_inv (2^n),
        inv_le_inv₀ (by (have : 0 < 2 - z := by linarith); positivity) (by positivity),
        ← one_div]
      exact h₇
    · positivity
    · positivity
  have h₉ : 2 * √(2 - z) / 2 ^ k ≤ 4 / 2 ^ k := by
    apply div_le_div₀ zero_le_four ?_ (by positivity) le_rfl
    suffices √(2 - z) ≤ 2 by linarith
    rw [Real.sqrt_le_left zero_le_two]
    linarith
  have h₁₀ : ((18 * n * 2 ^ n + 4) / 2 ^ k : ℝ) = 18 * ↑n / 2 ^ k * 2 ^ n + 4 / 2 ^ k := by
    ring_nf
  linarith

theorem sqrtTwoSubSqrtTwoAddSeries_ub (n k : ℕ) (hk : 3 ≤ k) :
    (sqrtTwoSubSqrtTwoAddSeriesN n).ub k - (18 * n * 2 ^ n + 14) / 2 ^ k ≤ √(2 -
      Real.sqrtTwoAddSeries 0 n) := by
  dsimp [ub]
  rw [sqrtTwoSubSqrtTwoAddSeries_eq]
  have h₁ := Sqrt.sqrtq_sub_le_sqrt' (2 - Real.sqrtTwoAddSeries 0 n) ((2 - sqrtTwoAddSeriesN
    n).lub k) k
    ⟨?_, ?_⟩ ?_ hk; rotate_left
  · change ((2 + -_ : ℚ) : ℝ) ≤ _
    rw [Rat.cast_add, Rat.cast_ofNat, Rat.cast_neg]
    apply tsub_le_tsub_left
    rw [← ge_iff_le]
    convert ComputableℝSeq.hub _ _
    symm
    exact IsComputable.prop
  · change _ ≤ ((2 + -_ : ℚ) : ℝ)
    rw [Rat.cast_add, Rat.cast_ofNat, Rat.cast_neg]
    apply tsub_le_tsub_left
    convert ComputableℝSeq.hlb _ _
    symm
    exact IsComputable.prop
  · linarith [Real.sqrtTwoAddSeries_lt_two n]
  have hx : ((2 - sqrtTwoAddSeriesN n).lub k).fst = 2 - (sqrtTwoAddSeriesN n).ub k := by
    change (2 +- _) = _
    rw [sub_eq_add_neg]
    rfl
  have hy : ((2 - sqrtTwoAddSeriesN n).lub k).snd = 2 - (sqrtTwoAddSeriesN n).lb k := by
    change (2 +- _) = _
    rw [sub_eq_add_neg]
    rfl
  simp only [hx, hy, Rat.cast_sub, Rat.cast_ofNat, sub_sub_sub_cancel_left] at h₁
  clear hx hy
  have h₄ := Real.sqrtTwoAddSeries_zero_nonneg n
  have h₅ := Real.sqrtTwoAddSeries_lt_two n
  have h₆ := sqrtTwoAddSeriesN_bounds n k hk
  have h₇ := (real_sqrtTwoAddSeries_lb n).le
  generalize
    (Sqrt.sqrtq ((2 - sqrtTwoAddSeriesN n).lub k) k).fst=w,
    (sqrtTwoAddSeriesN n).lb k=x,
    (sqrtTwoAddSeriesN n).ub k=y,
    Real.sqrtTwoAddSeries 0 n=z at *
  have h₈ : (↑y - ↑x) / √(2 - z) ≤ 18 * ↑n / 2 ^ k * 2 ^ n := by
    rw [div_eq_mul_inv]
    apply mul_le_mul
    · rify at h₆
      linarith
    · rw [← inv_inv (2^n),
        inv_le_inv₀ (by (have : 0 < 2 - z := by linarith); positivity) (by positivity),
        ← one_div]
      exact h₇
    · positivity
    · positivity
  have h₉ : 7 * √(2 - z) / 2 ^ k ≤ 14 / 2 ^ k := by
    apply div_le_div₀ (by norm_num) ?_ (by positivity) le_rfl
    suffices √(2 - z) ≤ 2 by linarith
    rw [Real.sqrt_le_left zero_le_two]
    linarith
  have h₁₀ : ((18 * n * 2 ^ n + 14) / 2 ^ k : ℝ) = 18 * ↑n / 2 ^ k * 2 ^ n + 14 / 2 ^ k := by
    ring_nf
  linarith

/-- See theorem Real.pi_lt_sqrtTwoAddSeries in Mathlib -/
noncomputable def piLb (n : ℕ) : ℚ :=
  2 ^ (n + 1) * (sqrtTwoSubSqrtTwoAddSeriesN n).lb (3 * n)

/-- See theorem Real.pi_gt_sqrtTwoAddSeries in Mathlib -/
noncomputable def piUb (n : ℕ) : ℚ :=
  2 ^ (n + 1) * (sqrtTwoSubSqrtTwoAddSeriesN n).ub (3 * n) + 1 / 4 ^ n

theorem piLb_le_pi (n : ℕ) : piLb n ≤ Real.pi := by
  refine le_trans ?_ (Real.pi_gt_sqrtTwoAddSeries n).le
  simp only [piLb, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
  rw [mul_le_mul_iff_of_pos_left (by positivity)]
  have hval : (sqrtTwoSubSqrtTwoAddSeriesN n).val = Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) :=
    IsComputable.prop (x := Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n))
  rw [← hval]
  exact ComputableℝSeq.hlb _ _

theorem piUb_ge_pi (n : ℕ) : Real.pi ≤ piUb n := by
  refine le_trans (Real.pi_lt_sqrtTwoAddSeries n).le ?_
  simp only [one_div, piUb, Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_inv,
    add_le_add_iff_right]
  rw [mul_le_mul_iff_of_pos_left (by positivity)]
  have hval : (sqrtTwoSubSqrtTwoAddSeriesN n).val = Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) :=
    IsComputable.prop (x := Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n))
  rw [← hval]
  exact ComputableℝSeq.hub _ _

theorem piLb_ge_pi_sub_pow (n : ℕ) (hn : 0 < n) : Real.pi - 41 * n / 2 ^ n ≤ piLb n := by
  suffices 2 ^ (n + 1) * ((18 * n * 2 ^ n + 4) / 2 ^ (3 * n)) + 1 / 4 ^ n ≤ (41 * n / 2 ^ n : ℚ) by
    rify at this
    rw [piLb]
    have h₁ := sqrtTwoSubSqrtTwoAddSeries_lb n (3 * n) (by omega)
    replace h₁ := mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 2 ^ (n + 1) by positivity)
    rw [mul_add] at h₁
    have h₂ := Real.pi_lt_sqrtTwoAddSeries n
    push_cast
    linarith
  by_cases hn' : n < 2
  · interval_cases n
    norm_num
  clear hn
  push Not at hn'
  qify at hn'
  have h₁ : (2 ^ (n + 1) * ((18 * n * 2 ^ n + 4) / 2 ^ (3 * n)) + 1 / 4 ^ n : ℚ)
      = 36 * n / 2 ^ n + 9 / 4 ^ n := by
    rw [show (4 : ℚ) ^ n = (2 ^ 2) ^ n by rfl, ← pow_mul]
    field_simp
    ring_nf
  rw [h₁]; clear h₁
  suffices (9 / 4 ^ n : ℚ) ≤ 5 * n / 2 ^ n by
    simp only [← mul_div] at this ⊢
    linarith
  exact div_le_div₀ (by positivity) (by linarith) (by positivity) (pow_le_pow_left₀ rfl rfl n)

theorem piUb_le_pi_add_pow (n : ℕ) (hn : 0 < n) : piUb n ≤ Real.pi + 51 * n / 2 ^ n := by
  suffices 2 ^ (n + 1) * ((18 * n * 2 ^ n + 14) / 2 ^ (3 * n)) + 1 / 4 ^ n ≤ (51 * n / 2 ^ n : ℚ) by
    rify at this
    rw [piUb]
    have h₁ := sqrtTwoSubSqrtTwoAddSeries_ub n (3 * n) (by omega)
    replace h₁ := mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 2 ^ (n + 1) by positivity)
    rw [mul_sub] at h₁
    have h₂ := Real.pi_gt_sqrtTwoAddSeries n
    push_cast
    linarith
  by_cases hn' : n < 2
  · interval_cases n
    norm_num
  clear hn
  push Not at hn'
  qify at hn'
  have h₁ : (2 ^ (n + 1) * ((18 * n * 2 ^ n + 14) / 2 ^ (3 * n)) + 1 / 4 ^ n : ℚ)
      = 36 * n / 2 ^ n + 29 / 4 ^ n := by
    rw [show (4 : ℚ) ^ n = (2 ^ 2) ^ n by rfl, ← pow_mul]
    field_simp
    ring_nf
  rw [h₁]; clear h₁
  suffices (29 / 4 ^ n : ℚ) ≤ 15 * n / 2 ^ n by
    simp only [← mul_div] at this ⊢
    linarith
  exact div_le_div₀ (by positivity) (by linarith) (by positivity) (pow_le_pow_left₀ rfl rfl n)

theorem piLb_causeq : ∃ (h' : IsCauSeq abs piLb), Real.mk ⟨piLb, h'⟩ = Real.pi := by
  refine Real.of_near piLb Real.pi ?_
  intro ε hε
  have h₁ := Filter.Tendsto.const_mul 41 (tendsto_pow_const_div_const_pow_of_one_lt 1 one_lt_two)
  simp only [pow_one, mul_zero] at h₁
  replace h₁ := h₁.eventually_mem (Ioo_mem_nhds (neg_neg_iff_pos.mpr hε) hε)
  simp only [Set.mem_Ioo, Filter.eventually_atTop, ge_iff_le] at h₁
  obtain ⟨i, hi⟩ := h₁
  use max i 1
  intro j hj
  specialize hi j (le_of_max_le_left hj)
  rw [abs_lt]
  have h₂ := piLb_ge_pi_sub_pow j (le_of_max_le_right hj)
  rw [← mul_div] at h₂
  constructor
  · linarith
  · linarith [piLb_le_pi j]

theorem piUb_causeq : ∃ (h' : IsCauSeq abs piUb), Real.mk ⟨piUb, h'⟩ = Real.pi := by
  refine Real.of_near piUb Real.pi ?_
  intro ε hε
  have h₁ := Filter.Tendsto.const_mul 51 (tendsto_pow_const_div_const_pow_of_one_lt 1 one_lt_two)
  simp only [pow_one, mul_zero] at h₁
  replace h₁ := h₁.eventually_mem (Ioo_mem_nhds (neg_neg_iff_pos.mpr hε) hε)
  simp only [Set.mem_Ioo, Filter.eventually_atTop, ge_iff_le] at h₁
  obtain ⟨i, hi⟩ := h₁
  use max i 1
  intro j hj
  specialize hi j (le_of_max_le_left hj)
  rw [abs_lt]
  have h₂ := piUb_le_pi_add_pow j (le_of_max_le_right hj)
  rw [← mul_div] at h₂
  constructor
  · linarith  [piUb_ge_pi j]
  · linarith

/-- Definition of `Pi`. -/
noncomputable def Pi : ComputableℝSeq :=
  mk Real.pi
  (lub := fun n ↦ ⟨⟨piLb n, piUb n⟩,
    Rat.cast_le.mp <| (piLb_le_pi n).trans (piUb_ge_pi n)⟩)
  (hlb := piLb_le_pi)
  (hub := piUb_ge_pi)
  (hcl := piLb_causeq.rec (fun w _ ↦ w))
  (hcu := piUb_causeq.rec (fun w _ ↦ w))
  (heq := by
    obtain ⟨_, h₁⟩ := piLb_causeq
    obtain ⟨_, h₂⟩ := piUb_causeq
    rw [← Real.mk_eq, h₁, h₂]
  )

end Pi

end ComputableℝSeq

namespace IsComputable

noncomputable instance instComputablePi : IsComputable (Real.pi) where
  seq := ComputableℝSeq.Pi
  prop := ComputableℝSeq.mk_val_eq_val

end IsComputable
