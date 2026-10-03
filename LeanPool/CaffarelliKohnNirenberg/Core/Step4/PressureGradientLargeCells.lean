/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Basic

/-! # Large-cell normalization for pressure gradients

For the Morrey quantities in `prop:bootstrap`, a cell of radius `r ≥ r₀ > 0`
has normalization at most `r₀ ^ (-(5 * (1 - p / q) / p))` when `0 < p ≤ q`.
Its power integral is bounded by the whole-carrier integral. For `p = 6/5`,
the resulting factor is `r₀ ^ (5 / q - 25 / 6)` and the integral has power
`5/6`. The constant is one; the carrier radius enters only through its domain.

The indicator versions hold for every cell centre, including cells crossing
the carrier boundary. Both the origin past cylinder and the symmetric
parabolic metric ball are treated without any small-cell estimate.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

noncomputable section
namespace CKN.Core.Step4

private theorem large_cell_normalization_le
    {p q r₀ r : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    (hr₀ : 0 < r₀) (hr : r₀ ≤ r) :
    ENNReal.ofReal r ^ (-(5 * (1 - p / q) / p)) ≤
      ENNReal.ofReal (r₀ ^ (-(5 * (1 - p / q) / p))) := by
  have hq : 0 < q := hp.trans_le hpq
  have hexp : -(5 * (1 - p / q) / p) ≤ 0 := by
    apply neg_nonpos.mpr
    exact div_nonneg (mul_nonneg (by norm_num)
      (sub_nonneg.mpr ((div_le_one hq).mpr hpq))) hp.le
  rw [ENNReal.ofReal_rpow_of_pos (hr₀.trans_le hr)]
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hr₀ hr hexp)

/-- Restricting a field to a measurable carrier controls every large cell,
including cells that intersect its boundary, as used in `prop:bootstrap`. -/
theorem morreyCell_indicator_le_carrier_integral_of_large_radius
    {p q r₀ r : ℝ} {f : ParabolicPoint → ℝ} {S : Set ParabolicPoint}
    (hS : MeasurableSet S) (hp : 0 < p) (hpq : p ≤ q)
    (hr₀ : 0 < r₀) (hr : r₀ ≤ r) (z : ParabolicPoint) :
    morreyCell p q (S.indicator f) z r ≤
      ENNReal.ofReal (r₀ ^ (-(5 * (1 - p / q) / p))) *
        (∫⁻ w in S, ENNReal.ofReal |f w| ^ p) ^ (1 / p) := by
  classical
  have hint : cylinderPowerIntegral p (S.indicator f) z r ≤
      ∫⁻ w in S, ENNReal.ofReal |f w| ^ p := by
    rw [← lintegral_indicator hS]
    apply lintegral_mono' Measure.restrict_le_self
    intro w
    by_cases hw : w ∈ S
    · simp only [Set.indicator_of_mem hw, le_refl]
    · simp only [Set.indicator_of_notMem hw, abs_zero, ENNReal.ofReal_zero,
        ENNReal.zero_rpow_of_pos hp, le_refl]
  rw [morreyCell_eq]
  exact mul_le_mul' (large_cell_normalization_le hp hpq hr₀ hr)
    (ENNReal.rpow_le_rpow hint (one_div_nonneg.mpr hp.le))

/-- The origin past-cylinder carrier in `prop:bootstrap` has the large-cell
bound with constant one and explicit cutoff scale `r₀`. -/
theorem morreyCell_origin_cylinder_le_of_large_radius
    {p q r₀ r R : ℝ} {f : ParabolicPoint → ℝ}
    (hp : 0 < p) (hpq : p ≤ q) (hr₀ : 0 < r₀) (hr : r₀ ≤ r)
    (z : ParabolicPoint) :
    morreyCell p q ((parabolicCylinder 0 0 R).indicator f) z r ≤
      ENNReal.ofReal (r₀ ^ (-(5 * (1 - p / q) / p))) *
        (∫⁻ w in parabolicCylinder 0 0 R, ENNReal.ofReal |f w| ^ p) ^ (1 / p) :=
  morreyCell_indicator_le_carrier_integral_of_large_radius
    ((vec3Ball_measurable 0 R).prod measurableSet_Ioc) hp hpq hr₀ hr z

/-- The symmetric parabolic-ball carrier in `prop:bootstrap` has the same
large-cell normalization, independently of the carrier centre. -/
theorem morreyCell_ball_le_of_large_radius
    {p q r₀ r R : ℝ} {f : ParabolicPoint → ℝ} (z₀ : ParabolicPoint)
    (hp : 0 < p) (hpq : p ≤ q) (hr₀ : 0 < r₀) (hr : r₀ ≤ r)
    (z : ParabolicPoint) :
    morreyCell p q ((Metric.ball z₀ R).indicator f) z r ≤
      ENNReal.ofReal (r₀ ^ (-(5 * (1 - p / q) / p))) *
        (∫⁻ w in Metric.ball z₀ R, ENNReal.ofReal |f w| ^ p) ^ (1 / p) :=
  morreyCell_indicator_le_carrier_integral_of_large_radius
    measurableSet_ball hp hpq hr₀ hr z

/-- At pressure-gradient exponent `6/5` in `prop:bootstrap`, the origin
past-cylinder bound has scale power `5/κ - 25/6` and integral power `5/6`. -/
theorem pressure_gradient_origin_cylinder_large_cell_le
    {κ r₀ r R : ℝ} {f : ParabolicPoint → ℝ}
    (hκ : 6 / 5 ≤ κ) (hr₀ : 0 < r₀) (hr : r₀ ≤ r) (z : ParabolicPoint) :
    morreyCell (6 / 5) κ ((parabolicCylinder 0 0 R).indicator f) z r ≤
      ENNReal.ofReal (r₀ ^ (5 / κ - 25 / 6)) *
        (∫⁻ w in parabolicCylinder 0 0 R,
          ENNReal.ofReal |f w| ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) := by
  have h := morreyCell_origin_cylinder_le_of_large_radius
    (f := f) (R := R) (by norm_num : (0 : ℝ) < 6 / 5) hκ hr₀ hr z
  rw [show -(5 * (1 - (6 / 5 : ℝ) / κ) / (6 / 5)) =
    5 / κ - 25 / 6 by ring] at h
  norm_num only [one_div_div] at h
  exact h

/-- At pressure-gradient exponent `6/5` in `prop:bootstrap`, the symmetric
ball bound has scale power `5/κ - 25/6` and integral power `5/6`. -/
theorem pressure_gradient_ball_large_cell_le
    {κ r₀ r R : ℝ} {f : ParabolicPoint → ℝ} (z₀ : ParabolicPoint)
    (hκ : 6 / 5 ≤ κ) (hr₀ : 0 < r₀) (hr : r₀ ≤ r) (z : ParabolicPoint) :
    morreyCell (6 / 5) κ ((Metric.ball z₀ R).indicator f) z r ≤
      ENNReal.ofReal (r₀ ^ (5 / κ - 25 / 6)) *
        (∫⁻ w in Metric.ball z₀ R,
          ENNReal.ofReal |f w| ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) := by
  have h := morreyCell_ball_le_of_large_radius
    (f := f) (R := R) z₀ (by norm_num : (0 : ℝ) < 6 / 5) hκ hr₀ hr z
  rw [show -(5 * (1 - (6 / 5 : ℝ) / κ) / (6 / 5)) =
    5 / κ - 25 / 6 by ring] at h
  norm_num only [one_div_div] at h
  exact h

end CKN.Core.Step4
