/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Basic

/-!
# The every-cell growth bound in its two regimes

A cell of the pressure-gradient carrier is controlled by the slice estimate at
its own scale only when its ball still fits inside the carrier at that scale;
a cell that is large relative to its distance to the carrier boundary is not
reached by the slice estimate at all.  The growth bound `A · r ^ (5 (1 - P/κ))`
of the parabolic Morrey class therefore has two regimes.

Below a fixed scale `r₀` the bound is the slice bound at the cell's own radius.
At or above `r₀` the cell power integral is bounded by the whole-carrier
integral, and because the growth exponent `5 (1 - P/κ)` is nonnegative for
`P ≤ κ`, that constant bound is itself of the required form, at the cost of the
explicit scale factor `r₀ ^ (-(5 (1 - P/κ)))`.

The two regimes are combined here into a single every-cell statement whose
constant is the sum of the two.  Attempting one uniform argument across all
radii is what makes a growth clause unsatisfiable.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section
namespace CKN.Core.Step4

/-- A field vanishing off a measurable carrier has every cell power integral
bounded by its integral over that carrier. -/
theorem cylinderPowerIntegral_le_carrier_lintegral
    {S : Set ParabolicPoint} (hS : MeasurableSet S)
    {f : ParabolicPoint → ℝ} (hvan : ∀ w, w ∉ S → f w = 0)
    {P : ℝ} (hP : 0 < P) (z : ParabolicPoint) (r : ℝ) :
    cylinderPowerIntegral P f z r ≤ ∫⁻ w in S, ENNReal.ofReal |f w| ^ P := by
  classical
  have hQ : MeasurableSet (parabolicCylinder z.1 z.2 r) :=
    (vec3Ball_measurable z.1 r).prod measurableSet_Ioc
  show (∫⁻ w in parabolicCylinder z.1 z.2 r, ENNReal.ofReal |f w| ^ P) ≤ _
  rw [← lintegral_indicator hQ, ← lintegral_indicator hS]
  refine lintegral_mono fun w => ?_
  by_cases hw : w ∈ parabolicCylinder z.1 z.2 r
  · rw [Set.indicator_of_mem hw]
    by_cases hwS : w ∈ S
    · rw [Set.indicator_of_mem hwS]
    · rw [Set.indicator_of_notMem hwS, hvan w hwS]
      simp [ENNReal.zero_rpow_of_pos hP]
  · rw [Set.indicator_of_notMem hw]
    exact bot_le

/-- The large-cell regime.  At or above the scale `r₀` a constant bound on the
cell power integral is already of the Morrey growth form, with the explicit
scale factor. -/
theorem cylinderPowerIntegral_growth_of_large_cell
    {f : ParabolicPoint → ℝ} {B : ℝ≥0∞} {P κ r₀ : ℝ}
    (hP : 0 < P) (hPκ : P ≤ κ) (hr₀ : 0 < r₀)
    {z : ParabolicPoint} {r : ℝ} (hr : r₀ ≤ r)
    (hB : cylinderPowerIntegral P f z r ≤ B) :
    cylinderPowerIntegral P f z r ≤
      (B * ENNReal.ofReal (r₀ ^ (-(5 * (1 - P / κ))))) *
        ENNReal.ofReal (r ^ (5 * (1 - P / κ))) := by
  have hκ : 0 < κ := lt_of_lt_of_le hP hPκ
  have hα : 0 ≤ 5 * (1 - P / κ) :=
    mul_nonneg (by norm_num) (sub_nonneg.mpr ((div_le_one hκ).mpr hPκ))
  have hr₀α : 0 < r₀ ^ (5 * (1 - P / κ)) := Real.rpow_pos_of_pos hr₀ _
  have hone : ENNReal.ofReal (r₀ ^ (-(5 * (1 - P / κ)))) *
      ENNReal.ofReal (r₀ ^ (5 * (1 - P / κ))) = 1 := by
    rw [← ENNReal.ofReal_mul (le_of_lt (Real.rpow_pos_of_pos hr₀ _)),
      Real.rpow_neg (le_of_lt hr₀), inv_mul_cancel₀ (ne_of_gt hr₀α)]
    simp
  have hstep : B = (B * ENNReal.ofReal (r₀ ^ (-(5 * (1 - P / κ))))) *
      ENNReal.ofReal (r₀ ^ (5 * (1 - P / κ))) := by
    rw [mul_assoc, hone, mul_one]
  have hrpow : ENNReal.ofReal (r₀ ^ (5 * (1 - P / κ))) ≤
      ENNReal.ofReal (r ^ (5 * (1 - P / κ))) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (le_of_lt hr₀) hr hα)
  refine hB.trans ?_
  calc B = (B * ENNReal.ofReal (r₀ ^ (-(5 * (1 - P / κ))))) *
        ENNReal.ofReal (r₀ ^ (5 * (1 - P / κ))) := hstep
    _ ≤ (B * ENNReal.ofReal (r₀ ^ (-(5 * (1 - P / κ))))) *
        ENNReal.ofReal (r ^ (5 * (1 - P / κ))) := by gcongr

/-- The every-cell growth bound of one field, in its two regimes: the slice
bound at the cell's own scale below `r₀`, and the whole-carrier integral with
the explicit scale factor at or above `r₀`. -/
theorem cylinderPowerIntegral_growth_two_regimes
    {S : Set ParabolicPoint} (hS : MeasurableSet S)
    {f : ParabolicPoint → ℝ} (hvan : ∀ w, w ∉ S → f w = 0)
    {A B : ℝ≥0∞} {P κ r₀ : ℝ}
    (hP : 0 < P) (hPκ : P ≤ κ) (hr₀ : 0 < r₀)
    (hglobal : (∫⁻ w in S, ENNReal.ofReal |f w| ^ P) ≤ B)
    (hsmall : ∀ (z : ParabolicPoint) (r : ℝ), 0 < r → r ≤ r₀ →
      cylinderPowerIntegral P f z r ≤
        A * ENNReal.ofReal (r ^ (5 * (1 - P / κ)))) :
    ∀ (z : ParabolicPoint) (r : ℝ), 0 < r →
      cylinderPowerIntegral P f z r ≤
        (A + B * ENNReal.ofReal (r₀ ^ (-(5 * (1 - P / κ))))) *
          ENNReal.ofReal (r ^ (5 * (1 - P / κ))) := by
  intro z r hrpos
  rcases le_total r r₀ with hle | hge
  · refine (hsmall z r hrpos hle).trans ?_
    gcongr
    exact le_self_add
  · refine (cylinderPowerIntegral_growth_of_large_cell hP hPκ hr₀ hge
      ((cylinderPowerIntegral_le_carrier_lintegral hS hvan hP z r).trans
        hglobal)).trans ?_
    gcongr
    exact le_add_self

end CKN.Core.Step4
