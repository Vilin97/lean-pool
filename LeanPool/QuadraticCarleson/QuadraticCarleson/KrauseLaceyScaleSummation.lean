/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceySparseInterface
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Numerical summation in the nonstandard scale parameter

The nonstandard argument produces a geometric loss in the scale parameter.
This file contains only the numerical step used after interpolation: a finite
or infinite geometric tail with ratio `r` costs at most a constant multiple of
the Holder conjugate `q`. The analytic estimate supplying the ratio is kept
separate (and is not postulated here).
-/

@[expose] public section

open scoped BigOperators

namespace QuadraticCarleson


noncomputable
section

/-- The geometric decay ratio used to sum the scale estimates. -/
def scaleDecayRatio (q : ℝ) : ℝ := (2 : ℝ) ^ (-1 / (5 * q))

theorem scaleDecayRatio_nonneg {q : ℝ} :
    0 ≤ scaleDecayRatio q := by
  exact (Real.rpow_nonneg (by norm_num) _)

theorem scaleDecayRatio_lt_one {q : ℝ} (hq : 0 < q) :
    scaleDecayRatio q < 1 := by
  unfold scaleDecayRatio
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · norm_num
  · have h : 0 < (1 : ℝ) / (5 * q) := by positivity
    convert neg_lt_zero.mpr h using 1; ring

theorem finite_scale_decay_sum_le_of_gap {r δ : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hδ : 0 < δ) (hgap : δ ≤ 1 - r) (N : ℕ) :
    (Finset.sum (Finset.range N) (fun s ↦ r ^ s)) ≤ 1 / δ := by
  have hsum : (Finset.sum (Finset.range N) (fun s ↦ r ^ s)) ≤ ∑' s : ℕ, r ^ s := by
    exact (summable_geometric_of_norm_lt_one (by
      simpa [Real.norm_eq_abs, abs_of_nonneg hr] using hr1)).sum_le_tsum
      (Finset.range N) (fun s hs ↦ pow_nonneg hr s)
  rw [tsum_geometric_of_lt_one hr hr1] at hsum
  have hden : δ ≤ 1 - r := hgap
  have hδ' : 0 < 1 - r := sub_pos.mpr hr1
  calc
    _ ≤ (1 - r)⁻¹ := hsum
    _ ≤ δ⁻¹ := (inv_le_inv₀ hδ' hδ).mpr hden
    _ = 1 / δ := by rw [one_div]

theorem scale_decay_sum_le_of_gap {r δ : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hδ : 0 < δ) (hgap : δ ≤ 1 - r) :
    (∑' s : ℕ, r ^ s) ≤ 1 / δ := by
  rw [tsum_geometric_of_lt_one hr hr1]
  have hδ' : 0 < 1 - r := sub_pos.mpr hr1
  simpa only [one_div] using (inv_le_inv₀ hδ' hδ).mpr hgap

theorem finite_scale_decay_sum_le_twenty_mul_q {q r : ℝ} (hq : 2 ≤ q)
    (hr : 0 ≤ r) (hr1 : r < 1) (hgap : 1 / (20 * q) ≤ 1 - r) (N : ℕ) :
    (Finset.sum (Finset.range N) (fun s ↦ r ^ s)) ≤ 20 * q := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hδ : 0 < (1 : ℝ) / (20 * q) := by positivity
  have h := finite_scale_decay_sum_le_of_gap hr hr1 hδ hgap N
  calc
    _ ≤ 1 / (1 / (20 * q)) := h
    _ = 20 * q := by field_simp

theorem scale_decay_sum_le_twenty_mul_q {q r : ℝ} (hq : 2 ≤ q)
    (hr : 0 ≤ r) (hr1 : r < 1) (hgap : 1 / (20 * q) ≤ 1 - r) :
    (∑' s : ℕ, r ^ s) ≤ 20 * q := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hδ : 0 < (1 : ℝ) / (20 * q) := by positivity
  have h := scale_decay_sum_le_of_gap hr hr1 hδ hgap
  calc
    _ ≤ 1 / (1 / (20 * q)) := h
    _ = 20 * q := by field_simp

theorem holderConjugate_ge_two {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    2 ≤ holderConjugate p := by
  rw [holderConjugate]
  apply (le_div_iff₀ (sub_pos.mpr hp)).2
  nlinarith

theorem scale_decay_sum_le_twenty_mul_holderConjugate {p r : ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) (hr : 0 ≤ r) (hr1 : r < 1)
    (hgap : 1 / (20 * holderConjugate p) ≤ 1 - r) :
    (∑' s : ℕ, r ^ s) ≤ 20 * holderConjugate p := by
  exact scale_decay_sum_le_twenty_mul_q (holderConjugate_ge_two hp hp2)
    hr hr1 hgap

theorem scaleDecayRatio_sum_le_twenty_mul_q_of_gap {q : ℝ} (hq : 2 ≤ q)
    (hgap : 1 / (20 * q) ≤ 1 - scaleDecayRatio q) :
    (∑' s : ℕ, (scaleDecayRatio q) ^ s) ≤ 20 * q := by
  exact scale_decay_sum_le_twenty_mul_q hq (scaleDecayRatio_nonneg)
    (scaleDecayRatio_lt_one (by linarith)) hgap

theorem finite_scaleDecayRatio_sum_le_twenty_mul_q_of_gap {q : ℝ} (hq : 2 ≤ q)
    (hgap : 1 / (20 * q) ≤ 1 - scaleDecayRatio q) (N : ℕ) :
    (Finset.sum (Finset.range N) (fun s ↦ (scaleDecayRatio q) ^ s)) ≤ 20 * q := by
  exact finite_scale_decay_sum_le_twenty_mul_q hq
    (scaleDecayRatio_nonneg) (scaleDecayRatio_lt_one (by linarith)) hgap N

theorem scaleDecayRatio_gap {q : ℝ} (hq : 2 ≤ q) :
    1 / (20 * q) ≤ 1 - scaleDecayRatio q := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hq10 : 0 < 5 * q := by positivity
  have hx : 0 < Real.log 2 / (5 * q) := by
    positivity
  have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by
    exact le_trans (by norm_num) (le_of_lt Real.log_two_gt_d9)
  have hlog1 : Real.log 2 ≤ 1 := by
    exact le_of_lt (lt_trans Real.log_two_lt_d9 (by norm_num))
  have hxle : Real.log 2 / (5 * q) ≤ 1 / 2 := by
    apply (div_le_iff₀ hq10).2
    nlinarith
  have hxge : 1 / (10 * q) ≤ Real.log 2 / (5 * q) := by
    calc
      1 / (10 * q) = (1 / 2 : ℝ) / (5 * q) := by field_simp; ring
      _ ≤ Real.log 2 / (5 * q) :=
        div_le_div_of_nonneg_right hlog (le_of_lt hq10)
  have hxsmall : |-(Real.log 2 / (5 * q))| ≤ 1 := by
    rw [abs_neg, abs_of_pos hx]
    linarith
  have ht := Real.norm_exp_sub_one_sub_id_le hxsmall
  have ht' : Real.exp (-(Real.log 2 / (5 * q))) ≤
      1 - (Real.log 2 / (5 * q)) + (Real.log 2 / (5 * q)) ^ 2 := by
    have habs : |Real.exp (-(Real.log 2 / (5 * q)))-1+Real.log 2 / (5*q)| ≤
        (Real.log 2 / (5*q))^2 := by
      simpa [abs_neg, abs_of_pos hx, abs_of_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)),
        abs_of_pos hq0, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using ht
    linarith [le_trans (le_abs_self _) habs]
  have hquad : (Real.log 2 / (5 * q)) ^ 2 ≤
      (Real.log 2 / (5 * q)) / 2 := by
    nlinarith [sq_nonneg (Real.log 2 / (5 * q))]
  have hexp : Real.exp (-(Real.log 2 / (5 * q))) ≤ 1 - 1 / (20 * q) := by
    calc
      _ ≤ 1 - (Real.log 2 / (5 * q)) / 2 := by linarith [ht', hquad]
      _ ≤ 1 - 1 / (20 * q) := by
        have hh := mul_le_mul_of_nonneg_right hxge (by norm_num : (0 : ℝ) ≤ 1 / 2)
        have hh' : 1 / (20 * q) ≤ (Real.log 2 / (5 * q)) / 2 := by
          calc
            1 / (20 * q) = (1 / (10 * q)) / 2 := by field_simp; ring
            _ ≤ _ := by simpa [div_eq_mul_inv] using hh
        linarith
  rw [scaleDecayRatio, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have he : Real.log 2 * (-1 / (5 * q)) = -(Real.log 2 / (5 * q)) := by
    field_simp
  rw [he]
  linarith [hexp]

theorem scaleDecayRatio_sum_le_twenty_mul_q {q : ℝ} (hq : 2 ≤ q) :
    (∑' s : ℕ, (scaleDecayRatio q) ^ s) ≤ 20 * q :=
  scaleDecayRatio_sum_le_twenty_mul_q_of_gap hq (scaleDecayRatio_gap hq)

theorem finite_scaleDecayRatio_sum_le_twenty_mul_q {q : ℝ} (hq : 2 ≤ q) (N : ℕ) :
    (Finset.sum (Finset.range N) (fun s ↦ (scaleDecayRatio q) ^ s)) ≤ 20 * q :=
  finite_scaleDecayRatio_sum_le_twenty_mul_q_of_gap hq (scaleDecayRatio_gap hq) N

theorem scaleDecayRatio_sum_le_twenty_mul_holderConjugate {p : ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) :
    (∑' s : ℕ, (scaleDecayRatio (holderConjugate p)) ^ s) ≤
      20 * holderConjugate p :=
  scaleDecayRatio_sum_le_twenty_mul_q
    (holderConjugate_ge_two hp hp2)


end
end QuadraticCarleson
