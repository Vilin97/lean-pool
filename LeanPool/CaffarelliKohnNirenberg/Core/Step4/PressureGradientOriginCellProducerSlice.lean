/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.ProdSwap

/-!
# Slice decomposition of the power integral on a parabolic cylinder

The power integral over a backward parabolic cylinder is the time integral of
the power integrals of its spatial slices.  Consequently a bound on the `L^P`
norm of almost every spatial slice controls the full cylinder power integral.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
noncomputable section
namespace CKN.Core.Step4

/-- The power integral of a parabolic cylinder is the time integral of its
spatial slices. -/
theorem cylinderPowerIntegral_eq_lintegral_slices
    {P : ℝ} (hP : 0 < P) {g : ParabolicPoint → ℝ} {x : Vec3} {t r : ℝ}
    (hmeas : AEMeasurable g (volume.restrict (parabolicCylinder x t r))) :
    cylinderPowerIntegral P g (x, t) r =
      ∫⁻ s in Set.Ioc (t - r ^ 2) t,
        ∫⁻ y in vec3Ball x r, ENNReal.ofReal |g (y, s)| ^ P := by
  have _ : 0 < P := hP
  have hprod : (volume.restrict (vec3Ball x r ×ˢ Set.Ioc (t - r ^ 2) t)) =
      (volume.restrict (vec3Ball x r)).prod
        (volume.restrict (Set.Ioc (t - r ^ 2) t)) := by
    rw [MeasureTheory.Measure.volume_eq_prod, Measure.prod_restrict]
  have hmeas' : AEMeasurable g ((volume.restrict (vec3Ball x r)).prod
      (volume.restrict (Set.Ioc (t - r ^ 2) t))) := by
    rw [← hprod]
    exact hmeas
  have hF : AEMeasurable (fun w : ParabolicPoint => ENNReal.ofReal |g w| ^ P)
      ((volume.restrict (vec3Ball x r)).prod
        (volume.restrict (Set.Ioc (t - r ^ 2) t))) := by
    have h1 : AEMeasurable (fun w : ParabolicPoint => ‖g w‖ₑ ^ P)
        ((volume.restrict (vec3Ball x r)).prod
          (volume.restrict (Set.Ioc (t - r ^ 2) t))) :=
      ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hmeas'.enorm
    simpa only [Real.enorm_eq_ofReal_abs] using h1
  unfold cylinderPowerIntegral
  exact CKN.Foundation.Parabolic.Integration.prod_lintegral_swap_cyl hF

/-- Slicewise `L^P` bounds integrate to a bound on the cylinder power
integral. -/
theorem cylinderPowerIntegral_le_of_slice_eLpNorm
    {P : ℝ} (hP : 0 < P) {g : ParabolicPoint → ℝ} {x : Vec3} {t r : ℝ}
    {M : ℝ → ℝ≥0∞}
    (hmeas : AEMeasurable g (volume.restrict (parabolicCylinder x t r)))
    (hslice : ∀ᵐ s ∂(volume.restrict (Set.Ioc (t - r ^ 2) t)),
      eLpNorm (fun y => g (y, s)) (ENNReal.ofReal P)
        (volume.restrict (vec3Ball x r)) ≤ M s) :
    cylinderPowerIntegral P g (x, t) r ≤
      ∫⁻ s in Set.Ioc (t - r ^ 2) t, M s ^ P := by
  rw [cylinderPowerIntegral_eq_lintegral_slices hP hmeas]
  refine lintegral_mono_ae ?_
  filter_upwards [hslice] with s hs
  by_cases hM : M s = ⊤
  · rw [hM, ENNReal.top_rpow_of_pos hP]
    exact le_top
  · have hf : AEStronglyMeasurable (fun y => g (y, s))
        (volume.restrict (vec3Ball x r)) :=
      aestronglyMeasurable_of_eLpNorm_ne_top
        (ne_of_lt (lt_of_le_of_lt hs (lt_top_iff_ne_top.mpr hM)))
    have heq : eLpNorm (fun y => g (y, s)) (ENNReal.ofReal P)
        (volume.restrict (vec3Ball x r)) =
        (∫⁻ y, ‖g (y, s)‖ₑ ^ P ∂(volume.restrict (vec3Ball x r))) ^ (1 / P) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (ENNReal.ofReal_ne_zero_iff.mpr hP) ENNReal.ofReal_ne_top hf,
        ENNReal.toReal_ofReal hP.le]
    have hstep : (∫⁻ y in vec3Ball x r, ENNReal.ofReal |g (y, s)| ^ P) =
        (eLpNorm (fun y => g (y, s)) (ENNReal.ofReal P)
          (volume.restrict (vec3Ball x r))) ^ P := by
      rw [heq, one_div, ← ENNReal.rpow_mul]
      rw [inv_mul_cancel₀ hP.ne', ENNReal.rpow_one]
      simp only [Real.enorm_eq_ofReal_abs]
    rw [hstep]
    exact ENNReal.rpow_le_rpow hs hP.le

end CKN.Core.Step4
