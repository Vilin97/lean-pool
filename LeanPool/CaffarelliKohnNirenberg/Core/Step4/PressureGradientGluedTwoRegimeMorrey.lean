/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedTwoRegime

/-!
# The every-cell Morrey bound in its two regimes

The every-cell Morrey bound of a field carried by a measurable set has two
regimes.  Below the fixed scale `r₀` the cell of the field is controlled by the
slice growth bound, applied at the cell's own radius.  At or above `r₀` the
cell power integral is bounded by the whole-carrier integral, which is a
constant bound of the growth form at the cost of the explicit scale factor
`r₀ ^ (-(5 (1 - P/κ)))`.  Combining the two gives a single every-cell estimate
whose constant is the sum of the two regime constants, and hence a bound on the
Morrey seminorm itself.

A single uniform argument across all radii does not exist: the slice bound is
available only while the cell is small relative to its distance to the carrier
boundary, so the two regimes must be kept separate and then glued.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
noncomputable section
namespace CKN.Core.Step4

/-- A cell whose power integral satisfies the growth bound at its own radius is
bounded by the power of the growth constant: the radius weight of the Morrey
cell cancels the radius factor carried by the bound. -/
theorem morreyCell_le_of_cylinderPowerIntegral_growth
    {P κ : ℝ} {K : ℝ≥0∞} {f : ParabolicPoint → ℝ} {z : ParabolicPoint} {r : ℝ}
    (hP : 0 < P) (hr : 0 < r)
    (hI : cylinderPowerIntegral P f z r ≤
      K * ENNReal.ofReal (r ^ (5 * (1 - P / κ)))) :
    morreyCell P κ f z r ≤ K ^ (1 / P : ℝ) := by
  have hroot := ENNReal.rpow_le_rpow hI (one_div_nonneg.mpr hP.le)
  have hroot' : (cylinderPowerIntegral P f z r) ^ (1 / P : ℝ) ≤
      K ^ (1 / P : ℝ) * (ENNReal.ofReal r) ^ (5 * (1 - P / κ) / P) := by
    calc
      _ ≤ (K * ENNReal.ofReal (r ^ (5 * (1 - P / κ)))) ^ (1 / P : ℝ) := hroot
      _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hP.le),
          ← ENNReal.ofReal_rpow_of_pos hr, ← ENNReal.rpow_mul]
        congr 2
        ring
  have hcancel : (ENNReal.ofReal r) ^ (-(5 * (1 - P / κ) / P)) *
      (ENNReal.ofReal r) ^ (5 * (1 - P / κ) / P) = 1 := by
    rw [← ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.mpr hr).ne'
      ENNReal.ofReal_ne_top, neg_add_cancel, ENNReal.rpow_zero]
  rw [morreyCell_eq]
  calc
    _ ≤ (ENNReal.ofReal r) ^ (-(5 * (1 - P / κ) / P)) *
        (K ^ (1 / P : ℝ) * (ENNReal.ofReal r) ^ (5 * (1 - P / κ) / P)) :=
      mul_le_mul_of_nonneg_left hroot' (by positivity)
    _ = K ^ (1 / P : ℝ) := by
      rw [← mul_left_comm, hcancel, mul_one]

/-- The every-cell Morrey bound of a field carried by a measurable set, in its
two regimes: the constant is the power of the sum of the slice constant and the
whole-carrier integral rescaled by `r₀ ^ (-(5 (1 - P/κ)))`. -/
theorem morreyCell_le_two_regimes
    {S : Set ParabolicPoint} (hS : MeasurableSet S)
    {f : ParabolicPoint → ℝ} (hvan : ∀ w, w ∉ S → f w = 0)
    {A B : ℝ≥0∞} {P κ r₀ : ℝ}
    (hP : 0 < P) (hPκ : P ≤ κ) (hr₀ : 0 < r₀)
    (hglobal : (∫⁻ w in S, ENNReal.ofReal |f w| ^ P) ≤ B)
    (hsmall : ∀ (z : ParabolicPoint) (r : ℝ), 0 < r → r ≤ r₀ →
      cylinderPowerIntegral P f z r ≤
        A * ENNReal.ofReal (r ^ (5 * (1 - P / κ))))
    (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    morreyCell P κ f z r ≤
      (A + B * ENNReal.ofReal (r₀ ^ (-(5 * (1 - P / κ))))) ^ (1 / P : ℝ) :=
  morreyCell_le_of_cylinderPowerIntegral_growth hP hr
    (cylinderPowerIntegral_growth_two_regimes hS hvan hP hPκ hr₀ hglobal hsmall
      z r hr)


/-- Finite slice and carrier constants give a finite two-regime Morrey
constant. -/
theorem two_regime_morrey_constant_lt_top
    {A B : ℝ≥0∞} {P κ r₀ : ℝ} (hP : 0 < P) (hA : A < ⊤) (hB : B < ⊤) :
    (A + B * ENNReal.ofReal (r₀ ^ (-(5 * (1 - P / κ))))) ^ (1 / P : ℝ) < ⊤ := by
  have hbase : A + B * ENNReal.ofReal (r₀ ^ (-(5 * (1 - P / κ)))) < ⊤ :=
    ENNReal.add_lt_top.mpr ⟨hA, ENNReal.mul_lt_top hB ENNReal.ofReal_lt_top⟩
  exact ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hP.le) hbase.ne

/-- Restricting a field to a carrier can only decrease a cell power integral. -/
theorem cylinderPowerIntegral_indicator_le
    {S : Set ParabolicPoint} {P : ℝ} (hP : 0 < P) (g : ParabolicPoint → ℝ)
    (z : ParabolicPoint) (r : ℝ) :
    cylinderPowerIntegral P (S.indicator g) z r ≤
      cylinderPowerIntegral P g z r := by
  refine lintegral_mono fun w => ?_
  by_cases hw : w ∈ S
  · rw [Set.indicator_of_mem hw]
  · rw [Set.indicator_of_notMem hw]
    simp [ENNReal.zero_rpow_of_pos hP]

/-- A cell that misses the carrier carries no mass of the restricted field.
This is the trivial half of the small-cell regime: only cells meeting the
carrier need the slice estimate. -/
theorem cylinderPowerIntegral_indicator_eq_zero_of_disjoint
    {S : Set ParabolicPoint} {P : ℝ} (hP : 0 < P) {g : ParabolicPoint → ℝ}
    {z : ParabolicPoint} {r : ℝ}
    (hdisj : parabolicCylinder z.1 z.2 r ∩ S = ∅) :
    cylinderPowerIntegral P (S.indicator g) z r = 0 := by
  have hzero : ∀ w ∈ parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal |S.indicator g w| ^ P = 0 := by
    intro w hw
    have hwS : w ∉ S := fun h => by
      have : w ∈ parabolicCylinder z.1 z.2 r ∩ S := ⟨hw, h⟩
      rw [hdisj] at this
      exact this.elim
    rw [Set.indicator_of_notMem hwS]
    simp [ENNReal.zero_rpow_of_pos hP]
  have hQ : MeasurableSet (parabolicCylinder z.1 z.2 r) :=
    (vec3Ball_measurable z.1 r).prod measurableSet_Ioc
  show (∫⁻ w in parabolicCylinder z.1 z.2 r,
    ENNReal.ofReal |S.indicator g w| ^ P) = 0
  have heq : (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal |S.indicator g w| ^ P) =
      ∫⁻ _w in parabolicCylinder z.1 z.2 r, (0 : ℝ≥0∞) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem hQ] with w hw
    exact hzero w hw
  rw [heq, lintegral_zero]

end CKN.Core.Step4
