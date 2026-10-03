/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.ArcsineAtoms
public import LeanPool.Zeta5Irrational.Potential
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.RingNF

/-! # The arcsine potential (A.1) and its modulus of continuity

* `arc_potential_real` : for real `t`, `∫₀^{2π} log ‖t - y(θ)‖ dθ = 2π Uω a b t`;
* `Gpot_sub_le` : the Hölder-`1/2` estimate for `log⁺ ‖ζ + s‖ + log⁺ ‖ζ - s‖` used for the circle
  regularisation error.
-/

public section

open MeasureTheory Set Real intervalIntegral Filter Topology

namespace Zeta5Irrational

/-- A square root of `ζ² - 1` for real `ζ`. -/
noncomputable def sqR (ζ : ℝ) : ℂ :=
  if 1 ≤ ζ ^ 2 then ((Real.sqrt (ζ ^ 2 - 1) : ℝ) : ℂ)
  else ((Real.sqrt (1 - ζ ^ 2) : ℝ) : ℂ) * Complex.I

lemma sqR_sq (ζ : ℝ) : sqR ζ ^ 2 = (ζ : ℂ) ^ 2 - 1 := by
  unfold sqR
  split_ifs with h
  · rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]; push_cast; ring
  · rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]; push_cast; ring

/-- The value `log⁺ ‖ζ + s‖ + log⁺ ‖ζ - s‖` for real `ζ`. -/
lemma posLog_sum_real (ζ : ℝ) :
    log⁺ ‖(ζ : ℂ) + sqR ζ‖ + log⁺ ‖(ζ : ℂ) - sqR ζ‖ =
      if 1 ≤ |ζ| then Real.log (|ζ| + Real.sqrt (ζ ^ 2 - 1)) else 0 := by
  unfold sqR
  by_cases h : 1 ≤ ζ ^ 2
  · rw [ite_eq_left h]
    have h1 : 1 ≤ |ζ| := by nlinarith [abs_nonneg ζ, sq_abs ζ]
    rw [ite_eq_left h1]
    have hs0 : 0 ≤ Real.sqrt (ζ ^ 2 - 1) := Real.sqrt_nonneg _
    have hs2 : Real.sqrt (ζ ^ 2 - 1) ^ 2 = ζ ^ 2 - 1 := Real.sq_sqrt (by linarith)
    rw [← Complex.ofReal_add, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    rcases le_or_gt 0 ζ with hζ | hζ
    · rw [abs_of_nonneg hζ] at h1 ⊢
      set s := Real.sqrt (ζ ^ 2 - 1) with hs
      have h2 : s ≤ ζ := Real.sqrt_le_iff.mpr ⟨hζ, by nlinarith⟩
      have h3 : 0 < ζ - s := by
        refine sub_pos.mpr (lt_of_le_of_ne h2 fun h => ?_)
        rw [h] at hs2; linarith
      have h4 : ζ - 1 ≤ s := (Real.le_sqrt (by linarith) (by nlinarith)).mpr (by nlinarith)
      have hA : 0 < ζ + s := by linarith
      rw [abs_of_pos hA, abs_of_pos h3, posLog_eq_log (by rw [abs_of_pos hA]; linarith),
        (posLog_eq_zero_iff _).mpr (by rw [abs_of_pos h3]; linarith), add_zero]
    · rw [abs_of_neg hζ] at h1 ⊢
      set s := Real.sqrt (ζ ^ 2 - 1) with hs
      have h2 : s ≤ -ζ := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
      have hA' : -1 - ζ ≤ s := (Real.le_sqrt (by linarith) (by nlinarith)).mpr (by nlinarith)
      have hA : ζ + s ≤ 0 := by linarith
      have hB : ζ - s < 0 := by linarith
      have hB1 : 1 ≤ -(ζ - s) := by linarith
      rw [abs_of_nonpos hA, abs_of_neg hB,
        (posLog_eq_zero_iff _).mpr (by rw [abs_of_nonneg (by linarith)]; linarith),
        posLog_eq_log (by rw [abs_of_nonneg (by linarith)]; exact hB1), zero_add]
      ring_nf
  · rw [ite_eq_right h]
    have h1 : ¬1 ≤ |ζ| := by intro h1; apply h; nlinarith [abs_nonneg ζ, sq_abs ζ]
    rw [ite_eq_right h1]
    have hs2 : Real.sqrt (1 - ζ ^ 2) ^ 2 = 1 - ζ ^ 2 := Real.sq_sqrt (by linarith)
    have e1 :
      (ζ : ℂ) + ((Real.sqrt (1 - ζ ^ 2) : ℝ) : ℂ) * Complex.I =
        (ζ : ℝ) + ((Real.sqrt (1 - ζ ^ 2) : ℝ) : ℂ) * Complex.I :=
      rfl
    have e2 :
      (ζ : ℂ) - ((Real.sqrt (1 - ζ ^ 2) : ℝ) : ℂ) * Complex.I =
        (ζ : ℝ) + ((-Real.sqrt (1 - ζ ^ 2) : ℝ) : ℂ) * Complex.I :=
      by push_cast; ring
    rw [e1, e2, Complex.norm_add_mul_I, Complex.norm_add_mul_I, neg_sq, hs2,
      show ζ ^ 2 + (1 - ζ ^ 2) = 1 by ring, Real.sqrt_one]
    simp

/-- The closed form `Uω` in terms of `ζ = (t - m)/r`. -/
lemma Uω_eq_log_add {a b t : ℝ} (hab : a < b) :
    Uω a b t =
      Real.log ((b - a) / 4) +
        (if 1 ≤ |(t - (a + b) / 2) / ((b - a) / 2)| then
          Real.log
            (|(t - (a + b) / 2) / ((b - a) / 2)| +
              Real.sqrt (((t - (a + b) / 2) / ((b - a) / 2)) ^ 2 - 1))
        else 0) := by
  set r := (b - a) / 2 with hr
  set m := (a + b) / 2 with hm
  have hr0 : 0 < r := by rw [hr]; linarith
  have hζ : |(t - m) / r| = |t - m| / r := by rw [abs_div, abs_of_pos hr0]
  by_cases h : a ≤ t ∧ t ≤ b
  · rw [Uω_of_mem h.1 h.2]
    have h1 : |t - m| ≤ r := by rw [abs_le]; constructor <;> linarith
    have h2 : |(t - m) / r| ≤ 1 := by rw [hζ, div_le_one hr0]; exact h1
    split_ifs with h3
    · have h4 : |(t - m) / r| = 1 := le_antisymm h2 h3
      rw [← sq_abs ((t - m) / r), h4, one_pow, sub_self, Real.sqrt_zero, add_zero, Real.log_one,
        add_zero]
    · ring
  · have h1 : 1 < |(t - m) / r| := by
      rw [hζ, one_lt_div hr0, lt_abs]
      rcases not_and_or.mp h with h | h
      · right; linarith [not_le.mp h]
      · left; linarith [not_le.mp h]
    rw [ite_eq_left h1.le]
    unfold Uω
    rw [ite_eq_right h]
    have hpos : 0 < |t - m| / r + Real.sqrt (((t - m) / r) ^ 2 - 1) := by
      have := Real.sqrt_nonneg (((t - m) / r) ^ 2 - 1)
      rw [hζ] at h1; linarith
    rw [hζ, ← Real.log_mul (by positivity) hpos.ne']
    congr 1
    have e : (t - a) * (t - b) = r ^ 2 * (((t - m) / r) ^ 2 - 1) := by
      have hba : b - a ≠ 0 := by linarith
      rw [hr, hm]; field_simp; ring
    rw [e, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr0.le]
    rw [show (b - a) / 4 = r / 2 by rw [hr]; ring, ← hm]
    field_simp

/-- **(A.1)**: the arcsine potential at a real point. -/
lemma arc_potential_real {a b : ℝ} (hab : a < b) (t : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π, Real.log ‖(t : ℂ) - arcCurve ((a + b) / 2) ((b - a) / 2) θ‖ =
      2 * π * Uω a b t := by
  have hr0 : 0 < (b - a) / 2 := by linarith
  have hsq :
    sqR ((t - (a + b) / 2) / ((b - a) / 2)) ^ 2 =
      (((t : ℂ) - ((a + b) / 2 : ℝ)) / ((b - a) / 2 : ℝ)) ^ 2 - 1 :=
    by rw [sqR_sq]; push_cast; ring
  rw [arc_log_integral hr0 hsq, Uω_eq_log_add hab]
  congr 1
  have e :
    ((t : ℂ) - ((a + b) / 2 : ℝ)) / ((b - a) / 2 : ℝ) =
      (((t - (a + b) / 2) / ((b - a) / 2) : ℝ) : ℂ) :=
    by push_cast; ring
  rw [e, add_assoc, posLog_sum_real, show (b - a) / 2 / 2 = (b - a) / 4 by ring]

/-! ### Hölder continuity of the potential -/

lemma norm_mul_roots {ζ sq : ℂ} (hsq : sq ^ 2 = ζ ^ 2 - 1) : ‖ζ + sq‖ * ‖ζ - sq‖ = 1 := by
  rw [← norm_mul, show (ζ + sq) * (ζ - sq) = ζ ^ 2 - sq ^ 2 by ring, hsq]; simp

/-- `log⁺ ‖ζ + s‖ + log⁺ ‖ζ - s‖ = log (max ‖ζ + s‖ ‖ζ - s‖)`. -/
lemma posLog_sum_eq_log_max {ζ sq : ℂ} (hsq : sq ^ 2 = ζ ^ 2 - 1) :
    log⁺ ‖ζ + sq‖ + log⁺ ‖ζ - sq‖ = Real.log (max ‖ζ + sq‖ ‖ζ - sq‖) := by
  have h := norm_mul_roots hsq
  have h1 := norm_nonneg (ζ + sq)
  have h2 := norm_nonneg (ζ - sq)
  rcases le_total 1 ‖ζ + sq‖ with hle | hle
  · have h3 : ‖ζ - sq‖ ≤ 1 := by nlinarith
    rw [max_eq_left (h3.trans hle),
      posLog_eq_log (x := ‖ζ + sq‖) (by rw [abs_of_nonneg h1]; exact hle),
      (posLog_eq_zero_iff ‖ζ - sq‖).mpr (by rw [abs_of_nonneg h2]; exact h3), add_zero]
  · have h3 : 1 ≤ ‖ζ - sq‖ := by by_contra hc; rw [not_le] at hc; nlinarith
    rw [max_eq_right (hle.trans h3),
      posLog_eq_log (x := ‖ζ - sq‖) (by rw [abs_of_nonneg h2]; exact h3),
      (posLog_eq_zero_iff ‖ζ + sq‖).mpr (by rw [abs_of_nonneg h1]; exact hle), zero_add]

lemma one_le_max_roots {ζ sq : ℂ} (hsq : sq ^ 2 = ζ ^ 2 - 1) : 1 ≤ max ‖ζ + sq‖ ‖ζ - sq‖ := by
  have h := norm_mul_roots hsq
  have h1 := norm_nonneg (ζ + sq)
  have h2 := norm_nonneg (ζ - sq)
  by_contra hc
  rw [not_le, max_lt_iff] at hc
  nlinarith

lemma log_sub_log_le_of_one_le {M M' : ℝ} (hM : 1 ≤ M) (hM' : 1 ≤ M') :
    Real.log M - Real.log M' ≤ |M - M'| := by
  rcases le_total M' M with h | h
  · rw [abs_of_nonneg (by linarith), ← Real.log_div (by linarith) (by linarith)]
    have := Real.log_le_sub_one_of_pos (show 0 < M / M' by positivity)
    have h2 : M / M' - 1 = (M - M') / M' := by field_simp
    have h3 : (M - M') / M' ≤ M - M' := by rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  · have := Real.log_le_log (by linarith) h
    linarith [abs_nonneg (M - M')]

lemma abs_log_max_sub_le {M M' : ℝ} (hM : 1 ≤ M) (hM' : 1 ≤ M') :
    |Real.log M - Real.log M'| ≤ |M - M'| := by
  rw [abs_le]
  constructor
  · have := log_sub_log_le_of_one_le hM' hM; rw [abs_sub_comm] at this; linarith
  · exact log_sub_log_le_of_one_le hM hM'

lemma max_roots_sub_le_aux (ζ ζ' s s' : ℂ) :
    |max ‖ζ + s‖ ‖ζ - s‖ - max ‖ζ' + s'‖ ‖ζ' - s'‖| ≤ ‖ζ - ζ'‖ + ‖s - s'‖ := by
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
  · calc
      |‖ζ + s‖ - ‖ζ' + s'‖| ≤ ‖(ζ + s) - (ζ' + s')‖ := abs_norm_sub_norm_le _ _
      _ = ‖(ζ - ζ') + (s - s')‖ := by ring_nf
      _ ≤ ‖ζ - ζ'‖ + ‖s - s'‖ := norm_add_le _ _
  · calc
      |‖ζ - s‖ - ‖ζ' - s'‖| ≤ ‖(ζ - s) - (ζ' - s')‖ := abs_norm_sub_norm_le _ _
      _ = ‖(ζ - ζ') - (s - s')‖ := by ring_nf
      _ ≤ ‖ζ - ζ'‖ + ‖s - s'‖ := norm_sub_le _ _

lemma max_roots_sub_le (ζ ζ' s s' : ℂ) :
    |max ‖ζ + s‖ ‖ζ - s‖ - max ‖ζ' + s'‖ ‖ζ' - s'‖| ≤ ‖ζ - ζ'‖ + min ‖s - s'‖ ‖s + s'‖ := by
  rcases le_total ‖s - s'‖ ‖s + s'‖ with h | h
  · rw [min_eq_left h]; exact max_roots_sub_le_aux ζ ζ' s s'
  · rw [min_eq_right h]
    have := max_roots_sub_le_aux ζ ζ' s (-s')
    rw [sub_neg_eq_add, sub_neg_eq_add, max_comm ‖ζ' + -s'‖,
      show ζ' + -s' = ζ' - s' by ring] at this
    exact this

lemma min_roots_le_sqrt (s s' : ℂ) : min ‖s - s'‖ ‖s + s'‖ ≤ Real.sqrt ‖s ^ 2 - s' ^ 2‖ := by
  rw [Real.le_sqrt (le_min (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)]
  have e : s ^ 2 - s' ^ 2 = (s - s') * (s + s') := by ring
  rw [e, norm_mul, sq]
  exact
    mul_le_mul (min_le_left _ _) (min_le_right _ _) (le_min (norm_nonneg _) (norm_nonneg _))
      (norm_nonneg _)

/-- The Hölder-`1/2` estimate for `G(ζ) = log⁺ ‖ζ + s‖ + log⁺ ‖ζ - s‖`. -/
lemma Gpot_sub_le {ζ ζ' s s' : ℂ} (hs : s ^ 2 = ζ ^ 2 - 1) (hs' : s' ^ 2 = ζ' ^ 2 - 1) :
    (log⁺ ‖ζ + s‖ + log⁺ ‖ζ - s‖) - (log⁺ ‖ζ' + s'‖ + log⁺ ‖ζ' - s'‖) ≤
      ‖ζ - ζ'‖ + Real.sqrt (‖ζ - ζ'‖ * ‖ζ + ζ'‖) := by
  rw [posLog_sum_eq_log_max hs, posLog_sum_eq_log_max hs']
  have h1 := abs_log_max_sub_le (one_le_max_roots hs) (one_le_max_roots hs')
  have h2 := max_roots_sub_le ζ ζ' s s'
  have h3 := min_roots_le_sqrt s s'
  rw [hs, hs', show ζ ^ 2 - 1 - (ζ' ^ 2 - 1) = (ζ - ζ') * (ζ + ζ') by ring, norm_mul] at h3
  linarith [le_abs_self (Real.log (max ‖ζ + s‖ ‖ζ - s‖) - Real.log (max ‖ζ' + s'‖ ‖ζ' - s'‖))]

end Zeta5Irrational
