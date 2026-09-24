/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.PotentialLocalLpGrowth
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceTimeIntegrals

/-!
# Force-potential growth constants controlled by source norms

The force constant in the harmonic part of `eq:pressure-gradient-morrey`
contains a local potential norm and a far-field mass. Both are bounded by
the spatial `L^{6/5}` norm of the compactly supported source, with explicit
fixed-radius coefficients. These estimates assert no shrinking-cell power.
-/

@[expose] public section

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Step4

private theorem source_mass_le_norm
    {G : Vec3 → ℝ} {R : ℝ}
    (hG : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hzero : ∀ y, y ∉ closedBall (0 : Vec3) R → G y = 0) :
    ENNReal.ofReal (∫ y, |G y|) ≤
      eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume *
        volume (closedBall (0 : Vec3) R) ^ (1 / 6 : ℝ) := by
  have hsupp : Function.support G ⊆ closedBall (0 : Vec3) R := by
    intro y hy
    by_contra hn
    exact hy (hzero y hn)
  have hint := integrable_of_memLp_ofReal_of_support (by norm_num : (1 : ℝ) ≤ 6 / 5) hG hzero
  have hnorm : ENNReal.ofReal (∫ y, |G y|) = eLpNorm G 1 volume := by
    rw [eLpNorm_one_eq_lintegral_enorm hG.aestronglyMeasurable]
    simpa only [Real.norm_eq_abs] using ofReal_integral_norm_eq_lintegral_enorm hint
  rw [hnorm, ← eLpNorm_restrict_eq_of_support_subset hG.aestronglyMeasurable hsupp]
  have hh := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := volume.restrict (closedBall (0 : Vec3) R))
    (p := (1 : ℝ≥0∞)) (q := ENNReal.ofReal (6 / 5 : ℝ)) (by norm_num)
    hG.aestronglyMeasurable.restrict
  simp only [eLpNorm_restrict_eq_of_support_subset hG.aestronglyMeasurable hsupp] at hh ⊢
  norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 6 / 5),
    Measure.restrict_apply_univ, one_div_one, one_div_div,
    show (1 - 5 / 6 : ℝ) = 1 / 6 by norm_num] at hh
  exact hh

/-- The Newtonian potential's growth constant is bounded by the source norm
and a fixed-radius kernel and volume coefficient. -/
theorem origin_newtonian_growth_constant_bound
    {G : Vec3 → ℝ} {R : ℝ}
    (hG : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hzero : ∀ y, y ∉ closedBall (0 : Vec3) R → G y = 0) :
    ENNReal.ofReal (newtonianPotentialGrowthConstant G R) ≤
      eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume *
        (eLpNorm (truncatedNewtonianPotentialKernel (R + 2 * R))
            (ENNReal.ofReal (6 / 5 : ℝ)) volume +
          ENNReal.ofReal (2 * (4 * Real.pi)⁻¹ * invNormBallConstant ^ (2 / 3 : ℝ)) *
            volume (closedBall (0 : Vec3) R) ^ (1 / 6 : ℝ)) := by
  obtain ⟨G', hG'm, heq, hG'zero⟩ :=
    exists_measurable_representative_of_support_closedBall hG.aestronglyMeasurable hzero
  have hnear := pressureNewtonianPotential_eLpNorm_three_halves_restrict_ball_le
    (ρ := 2 * R) hG'm hG'zero
  rw [← pressureNewtonianPotential_congr_of_ae_eq heq, ← eLpNorm_congr_ae heq] at hnear
  have hreal : ENNReal.ofReal (lpNorm (pressureNewtonianPotential G)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (ball (0 : Vec3) (2 * R)))) ≤
      eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume *
        eLpNorm (truncatedNewtonianPotentialKernel (R + 2 * R))
          (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
    rw [← toReal_eLpNorm]
    exact ENNReal.ofReal_toReal_le.trans hnear
  have hm := source_mass_le_norm hG hzero
  have hfar : ENNReal.ofReal (newtonianPotentialDecayConstant G * invNormBallConstant ^ (2 / 3 : ℝ)) ≤
      eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume *
        (ENNReal.ofReal (2 * (4 * Real.pi)⁻¹ * invNormBallConstant ^ (2 / 3 : ℝ)) *
          volume (closedBall (0 : Vec3) R) ^ (1 / 6 : ℝ)) := by
    unfold newtonianPotentialDecayConstant
    rw [show 2 * (4 * Real.pi)⁻¹ * (∫ y, |G y|) * invNormBallConstant ^ (2 / 3 : ℝ) =
      (2 * (4 * Real.pi)⁻¹ * invNormBallConstant ^ (2 / 3 : ℝ)) * (∫ y, |G y|) by ring]
    rw [ENNReal.ofReal_mul (mul_nonneg (by positivity)
      (Real.rpow_nonneg invNormBallConstant_nonneg _))]
    exact (mul_le_mul' le_rfl hm).trans_eq (by ring)
  unfold newtonianPotentialGrowthConstant invNormGrowthConstant
  rw [ENNReal.ofReal_add lpNorm_nonneg
    (mul_nonneg (newtonianPotentialDecayConstant_nonneg G)
      (Real.rpow_nonneg invNormBallConstant_nonneg _)), mul_add]
  exact add_le_add hreal hfar

/-- The derivative-potential growth constant is controlled by the same source
norm, retaining its explicit inverse-radius far-field coefficient. -/
theorem origin_newtonian_derivative_growth_constant_bound
    {G : Vec3 → ℝ} {R : ℝ} (i : Fin 3) (hR : 0 < R)
    (hG : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hzero : ∀ y, y ∉ closedBall (0 : Vec3) R → G y = 0) :
    ENNReal.ofReal (newtonianDerivativePotentialGrowthConstant i G R) ≤
      eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume *
        (eLpNorm (truncatedNewtonianDerivative (R + 2 * R) i)
            (ENNReal.ofReal (6 / 5 : ℝ)) volume +
          ENNReal.ofReal (4 * (4 * Real.pi)⁻¹ / (2 * R) * invNormBallConstant ^ (2 / 3 : ℝ)) *
            volume (closedBall (0 : Vec3) R) ^ (1 / 6 : ℝ)) := by
  obtain ⟨G', hG'm, heq, hG'zero⟩ :=
    exists_measurable_representative_of_support_closedBall hG.aestronglyMeasurable hzero
  have hnear := pressureNewtonianDerivativePotential_eLpNorm_three_halves_restrict_ball_le
    i hR (by positivity : 0 < 2 * R) hG'm (hG.ae_eq heq) hG'zero
  rw [← pressureNewtonianDerivativePotential_congr_of_ae_eq i heq, ← eLpNorm_congr_ae heq] at hnear
  have hreal : ENNReal.ofReal (lpNorm (pressureNewtonianDerivativePotential i G)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (ball (0 : Vec3) (2 * R)))) ≤
      eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume *
        eLpNorm (truncatedNewtonianDerivative (R + 2 * R) i)
          (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
    rw [← toReal_eLpNorm]
    exact ENNReal.ofReal_toReal_le.trans hnear
  have hm := source_mass_le_norm hG hzero
  have hfar : ENNReal.ofReal (newtonianDerivativePotentialDecayConstant G R * invNormBallConstant ^ (2 / 3 : ℝ)) ≤
      eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume *
        (ENNReal.ofReal (4 * (4 * Real.pi)⁻¹ / (2 * R) * invNormBallConstant ^ (2 / 3 : ℝ)) *
          volume (closedBall (0 : Vec3) R) ^ (1 / 6 : ℝ)) := by
    unfold newtonianDerivativePotentialDecayConstant
    rw [show 4 * (4 * Real.pi)⁻¹ * (∫ y, |G y|) / (2 * R) * invNormBallConstant ^ (2 / 3 : ℝ) =
      (4 * (4 * Real.pi)⁻¹ / (2 * R) * invNormBallConstant ^ (2 / 3 : ℝ)) * (∫ y, |G y|) by ring]
    rw [ENNReal.ofReal_mul (mul_nonneg (by positivity)
      (Real.rpow_nonneg invNormBallConstant_nonneg _))]
    exact (mul_le_mul' le_rfl hm).trans_eq (by ring)
  unfold newtonianDerivativePotentialGrowthConstant invNormGrowthConstant
  rw [ENNReal.ofReal_add lpNorm_nonneg
    (mul_nonneg (newtonianDerivativePotentialDecayConstant_nonneg hR G)
      (Real.rpow_nonneg invNormBallConstant_nonneg _)), mul_add]
  exact add_le_add hreal hfar

end CKN.Core.Step4
