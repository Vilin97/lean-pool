/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.ProdSwap

/-!
# Product-box power integrals and their spatial slices

This module records the product-box form of the slice decomposition of a power
integral.  For a nonnegative function on `Vec3 × ℝ` and arbitrary sets `E` of
space points and `F` of times, the integral of the power `|g| ^ P` over the box
`E ×ˢ F` equals the integral over `F` of the spatial power integrals of the
slices `y ↦ g (y, s)`.

The second result turns an almost-everywhere bound on the `L^P` norm of the
spatial slices into a bound on the power integral over the whole box.  Both are
stated for an arbitrary spatial set and an arbitrary time set; no geometry of a
ball or a backward time window is used.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section
namespace CKN.Core.Step4

/-- The power integral over a product box is the time integral of its spatial
slices.  No positivity hypothesis is needed on the exponent `P`. -/
theorem prodPowerIntegral_eq_lintegral_slices
    {P : ℝ} {g : ParabolicPoint → ℝ} {E : Set Vec3} {F : Set ℝ}
    (hmeas : AEMeasurable g (volume.restrict (E ×ˢ F))) :
    (∫⁻ w in E ×ˢ F, ENNReal.ofReal |g w| ^ P) =
      ∫⁻ s in F, ∫⁻ y in E, ENNReal.ofReal |g (y, s)| ^ P := by
  have hprod : (volume.restrict (E ×ˢ F)) =
      (volume.restrict E).prod (volume.restrict F) := by
    rw [MeasureTheory.Measure.volume_eq_prod, Measure.prod_restrict]
  have hmeas' : AEMeasurable g ((volume.restrict E).prod (volume.restrict F)) := by
    rw [← hprod]
    exact hmeas
  have hFm : AEMeasurable (fun w : ParabolicPoint => ENNReal.ofReal |g w| ^ P)
      ((volume.restrict E).prod (volume.restrict F)) := by
    have h1 : AEMeasurable (fun w : ParabolicPoint => ‖g w‖ₑ ^ P)
        ((volume.restrict E).prod (volume.restrict F)) :=
      ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hmeas'.enorm
    simpa only [Real.enorm_eq_ofReal_abs] using h1
  exact CKN.Foundation.Parabolic.Integration.prod_lintegral_swap_cyl hFm

/-- An almost-everywhere bound on the spatial `L^P` norms of the slices bounds
the power integral over the whole product box by the time integral of the
`P`-th powers of the bounds. -/
theorem prodPowerIntegral_le_of_slice_eLpNorm
    {P : ℝ} (hP : 0 < P) {g : ParabolicPoint → ℝ} {E : Set Vec3} {F : Set ℝ}
    {M : ℝ → ℝ≥0∞}
    (hmeas : AEMeasurable g (volume.restrict (E ×ˢ F)))
    (hslice : ∀ᵐ s ∂(volume.restrict F),
      eLpNorm (fun y => g (y, s)) (ENNReal.ofReal P) (volume.restrict E) ≤ M s) :
    (∫⁻ w in E ×ˢ F, ENNReal.ofReal |g w| ^ P) ≤ ∫⁻ s in F, M s ^ P := by
  rw [prodPowerIntegral_eq_lintegral_slices hmeas]
  refine lintegral_mono_ae ?_
  filter_upwards [hslice] with s hs
  by_cases hM : M s = ⊤
  · rw [hM, ENNReal.top_rpow_of_pos hP]
    exact le_top
  · have hf : AEStronglyMeasurable (fun y => g (y, s)) (volume.restrict E) :=
      aestronglyMeasurable_of_eLpNorm_ne_top
        (ne_of_lt (lt_of_le_of_lt hs (lt_top_iff_ne_top.mpr hM)))
    have heq : eLpNorm (fun y => g (y, s)) (ENNReal.ofReal P) (volume.restrict E) =
        (∫⁻ y, ‖g (y, s)‖ₑ ^ P ∂(volume.restrict E)) ^ (1 / P) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (ENNReal.ofReal_ne_zero_iff.mpr hP) ENNReal.ofReal_ne_top hf,
        ENNReal.toReal_ofReal hP.le]
    have hstep : (∫⁻ y in E, ENNReal.ofReal |g (y, s)| ^ P) =
        (eLpNorm (fun y => g (y, s)) (ENNReal.ofReal P) (volume.restrict E)) ^ P := by
      rw [heq, one_div, ← ENNReal.rpow_mul]
      rw [inv_mul_cancel₀ hP.ne', ENNReal.rpow_one]
      simp only [Real.enorm_eq_ofReal_abs]
    rw [hstep]
    exact ENNReal.rpow_le_rpow hs hP.le

end CKN.Core.Step4
