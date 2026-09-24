/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.PotentialLocalLpGrowth
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceTimeIntegrals
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceWholeFinite
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# A measurable-norm envelope for the harmonic force term

Fixed-radius Young and far-field bounds control the force contribution
of `eq:pressure-gradient-morrey` by spatial source norms on its cutoff ball.
-/

@[expose] public section

section

/-!
# Force-potential growth constants controlled by source norms

The force constant in the harmonic part of `eq:pressure-gradient-morrey`
contains a local potential norm and a far-field mass. Both are bounded by
the spatial `L^{6/5}` norm of the compactly supported source, with explicit
fixed-radius coefficients. These estimates assert no shrinking-cell power.
-/

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
  have hfar : ENNReal.ofReal (newtonianPotentialDecayConstant G * invNormBallConstant ^ (2 / 3 :
    ℝ)) ≤
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
  have hfar : ENNReal.ofReal (newtonianDerivativePotentialDecayConstant G R * invNormBallConstant
    ^ (2 / 3 : ℝ)) ≤
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
end

end

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Step4

/-- Fixed-radius coefficient for the Newtonian potential. -/
def originNewtonianCoefficient (R : ℝ) : ℝ≥0∞ :=
  eLpNorm (truncatedNewtonianPotentialKernel (R + 2 * R)) (ENNReal.ofReal (6 / 5 : ℝ)) volume +
    ENNReal.ofReal (2 * (4 * Real.pi)⁻¹ * invNormBallConstant ^ (2 / 3 : ℝ)) *
      volume (closedBall (0 : Vec3) R) ^ (1 / 6 : ℝ)

/-- Fixed-radius coefficient for the derivative Newtonian potential. -/
def originNewtonianDerivativeCoefficient (R : ℝ) (i : Fin 3) : ℝ≥0∞ :=
  eLpNorm (truncatedNewtonianDerivative (R + 2 * R) i) (ENNReal.ofReal (6 / 5 : ℝ)) volume +
    ENNReal.ofReal (4 * (4 * Real.pi)⁻¹ / (2 * R) * invNormBallConstant ^ (2 / 3 : ℝ)) *
      volume (closedBall (0 : Vec3) R) ^ (1 / 6 : ℝ)

/-- The force-growth envelope uses only spatial norms on the origin ball. -/
def originForceGrowthEnvelope (R : ℝ) (f : ParabolicPoint → Vec3) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 + R) * ∑ j : Fin 3,
    (originNewtonianDerivativeCoefficient R j +
      ENNReal.ofReal (cutoffGradientConstant / R) * originNewtonianCoefficient R) *
        eLpNorm (fun y => f (y, s) j) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (vec3Ball (0 : Vec3) R))

private theorem cutoff_scalar_data
    {B : Set Vec3} (hB : MeasurableSet B) {η g : Vec3 → ℝ} {C : ℝ} {p : ℝ≥0∞}
    (hη : AEStronglyMeasurable η volume) (hC : 0 ≤ C)
    (hb : ∀ y, |η y| ≤ C) (hs : Function.support η ⊆ B)
    (hg : MemLp g p (volume.restrict B)) :
    MemLp (fun y => η y * g y) p volume ∧
      eLpNorm (fun y => η y * g y) p volume ≤ ENNReal.ofReal C * eLpNorm g p (volume.restrict B)
        := by
  have hid : (fun y => η y * g y) = (fun y => η y * B.indicator g y) := by
    funext y
    by_cases hy : y ∈ B
    · rw [indicator_of_mem hy]
    · rw [show η y = 0 from by by_contra hn; exact hy (hs hn)]
      simp only [zero_mul]
  rw [hid]
  have hgi : MemLp (B.indicator g) p volume := (memLp_indicator_iff_restrict hB).mpr hg
  have hmeas : AEStronglyMeasurable (fun y => η y * B.indicator g y) volume :=
    hη.mul hgi.aestronglyMeasurable
  have hnorm : ∀ᵐ y ∂volume, ‖η y * B.indicator g y‖ ≤ C * ‖B.indicator g y‖ := by
    exact Eventually.of_forall fun y => by
      rw [norm_mul, Real.norm_eq_abs (η y)]
      exact mul_le_mul_of_nonneg_right (hb y) (norm_nonneg _)
  refine ⟨hgi.of_le_mul hmeas hnorm, ?_⟩
  have hh := eLpNorm_mono_ae hmeas (hnorm.mono fun y hy => by
    simpa only [norm_mul, Real.norm_eq_abs C, abs_of_nonneg hC] using hy)
      (g := fun y => C * B.indicator g y) (p := p)
  rw [show (fun y => C * B.indicator g y) = C • B.indicator g from rfl,
    eLpNorm_const_smul, eLpNorm_indicator_eq_eLpNorm_restrict hB] at hh
  simpa only [Real.enorm_eq_ofReal_abs, abs_of_nonneg hC] using hh

/-- The harmonic force-growth constant is bounded by its norm envelope
whenever the three force components belong to the local source space. -/
theorem origin_harmonic_force_le_envelope
    {R : ℝ} (hR : 0 < R) {f : ParabolicPoint → Vec3} (s : ℝ)
    (hf : ∀ j : Fin 3, MemLp (fun y => f (y, s) j) (ENNReal.ofReal (6 / 5 : ℝ))
      (volume.restrict (vec3Ball (0 : Vec3) R))) :
    ENNReal.ofReal (harmonicRemainderForceBound ((0 : Vec3), 0) hR f s) ≤
      originForceGrowthEnvelope R f s := by
  let η := mollifiedBallCutoff (0 : Vec3) hR
  have hηsupport := pressure_cutoff_support_subset_ball (0 : Vec3) hR
  have hCd : 0 ≤ cutoffGradientConstant / R :=
    (vecEuclideanNorm_nonneg _).trans (mollifiedBallCutoff_gradient_bound (0 : Vec3) hR 0)
  have hηdata (j : Fin 3) := cutoff_scalar_data (vec3Ball_measurable (0 : Vec3) R)
    (mollifiedBallCutoff_smooth (0 : Vec3) hR).continuous.aestronglyMeasurable (by norm_num : (0 :
      ℝ) ≤ 1)
    (fun y => by
      rw [abs_of_nonneg (mollifiedBallCutoff_nonneg (0 : Vec3) hR y)]
      exact mollifiedBallCutoff_le_one (0 : Vec3) hR y)
    ((subset_tsupport _).trans hηsupport) (hf j)
  have hddata (i j : Fin 3) := cutoff_scalar_data (vec3Ball_measurable (0 : Vec3) R)
    (contDiff_spatialDeriv_smooth (mollifiedBallCutoff_smooth (0 : Vec3) hR)
      i).continuous.aestronglyMeasurable hCd
    (fun y => (abs_apply_le_vecEuclideanNorm (classicalGradient η y) i).trans
      (mollifiedBallCutoff_gradient_bound (0 : Vec3) hR y))
    ((subset_tsupport _).trans ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηsupport))
      (hf j)
  have hzero (a : Vec3 → ℝ) (ha : Function.support a ⊆ vec3Ball (0 : Vec3) R) (j : Fin 3) :
      ∀ y, y ∉ closedBall (0 : Vec3) R → a y * f (y, s) j = 0 := by
    intro y hy
    have han : a y = 0 := by
      by_contra hn
      have hball := ha hn
      have hnorm : ‖y‖ < R := (norm_le_vec3EuclideanNorm y).trans_lt (by
        simpa only [mem_vec3Ball, sub_zero] using hball)
      exact hy (mem_closedBall_zero_iff.mpr hnorm.le)
    rw [han, zero_mul]
  have h7 (j : Fin 3) : ENNReal.ofReal (newtonianDerivativePotentialGrowthConstant j
      (fun y => η y * f (y, s) j) R) ≤
      originNewtonianDerivativeCoefficient R j *
        eLpNorm (fun y => f (y, s) j) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (vec3Ball (0 : Vec3) R)) := by
    have hh := origin_newtonian_derivative_growth_constant_bound j hR (hηdata j).1
      (hzero η ((subset_tsupport _).trans hηsupport) j)
    refine hh.trans ?_
    have hb := (hηdata j).2
    simp only [ENNReal.ofReal_one, one_mul] at hb
    exact (mul_le_mul' hb le_rfl).trans_eq (mul_comm _ _)
  have h8 (j : Fin 3) : ENNReal.ofReal (newtonianPotentialGrowthConstant
      (fun y => spatialDeriv η j y * f (y, s) j) R) ≤
      (ENNReal.ofReal (cutoffGradientConstant / R) * originNewtonianCoefficient R) *
        eLpNorm (fun y => f (y, s) j) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (vec3Ball (0 : Vec3) R)) := by
    have hh := origin_newtonian_growth_constant_bound (hddata j j).1
      (hzero (spatialDeriv η j)
        ((subset_tsupport _).trans ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans
          hηsupport)) j)
    have hfactor := mul_le_mul' (hddata j j).2 (le_refl (originNewtonianCoefficient R))
    exact hh.trans (hfactor.trans_eq (by unfold originNewtonianCoefficient; ring))
  have h7nn := pressureP7GrowthConstant_nonneg η f s hR
  have h8nn := pressureP8GrowthConstant_nonneg η f s R
  unfold harmonicRemainderForceBound
  simp only [vec3EuclideanNorm_zero, zero_add, add_zero]
  rw [max_eq_left (mul_nonneg (add_nonneg h7nn h8nn) (by positivity)),
    ENNReal.ofReal_mul (add_nonneg h7nn h8nn), ENNReal.ofReal_add h7nn h8nn]
  unfold pressureP7GrowthConstant pressureP8GrowthConstant
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => newtonianDerivativePotentialGrowthConstant_nonneg j
    hR _),
    ENNReal.ofReal_sum_of_nonneg (fun j _ => newtonianPotentialGrowthConstant_nonneg _ R)]
  have hh := add_le_add (Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h7 j))
    (Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h8 j))
  refine (mul_le_mul' hh le_rfl).trans_eq ?_
  simp only [originForceGrowthEnvelope, ← Finset.sum_add_distrib, ← add_mul]
  exact mul_comm _ _

end CKN.Core.Step4
