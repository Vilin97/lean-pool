/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveLowFullEndpoint

/-!
# Exact agreement with the paper's finite low-height sum

This file commutes the finite height sum with the integral and changes
variables to the paper's `b(x-t) ψ_j(t) e(λt²)` convention. Consequently the
endpoint bound applies literally to the all-level finite-height formula.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Function

namespace QuadraticCarleson
namespace PositiveLowFullEstimate

open CalderonZygmundLevelAtoms PositiveEndpointOptimization PositiveHighHeightEstimate

theorem integrable_fixedHeightQuadraticKernel_mul_locallyIntegrable
    {b : ℝ → ℂ} (hb : LocallyIntegrable b) (r : ℕ) (lam : ℝ) (hlam : lam ≠ 0) (x : ℝ) :
    Integrable (fun t ↦ fixedHeightQuadraticKernel lam r hlam (x - t) * b t) := by
  let j := oscillatoryScaleIndex lam r hlam
  have ha : Continuous (fun t ↦ (dyadicPsi j t : ℂ)) :=
    Complex.continuous_ofReal.comp (dyadicPsi_smooth j).continuous
  have hi : Integrable (fun t ↦ (dyadicPsi j (x - t) : ℂ) * b t) :=
    hb.integrable_smul_left_of_hasCompactSupport
      (ha.comp (continuous_const.sub continuous_id))
      ((hasCompactSupport_complex_dyadicPsi j).comp_homeomorph (Homeomorph.subLeft x))
  have hp : Continuous (fun t : ℝ ↦ phase (lam * (x - t) ^ 2)) := by
    unfold phase
    fun_prop
  have hbnd : ∀ᵐ t : ℝ, ‖phase (lam * (x - t) ^ 2)‖ ≤ (1 : ℝ) := by
    filter_upwards with t
    exact (norm_phase _).le
  convert hi.mul_bdd hp.aestronglyMeasurable hbnd using 1
  funext t
  unfold fixedHeightQuadraticKernel
  dsimp only [j]
  ring

theorem integral_paperLowCZKernel_eq_sum_fixedHeights
    {b : ℝ → ℂ} (hb : LocallyIntegrable b) (B : ℕ) (lam : ℝ) (hlam : lam ≠ 0) (x : ℝ) :
    (∫ y, paperLowCZKernel lam hlam B x y * b y) =
      ∑ r ∈ Finset.range (B + 1), ∫ t, b (x - t) *
        (dyadicPsi (oscillatoryScaleIndex lam r hlam) t : ℂ) * phase (lam * t ^ 2) := by
  have hk (r : ℕ) : Integrable (fun t ↦
      (dyadicPsi (oscillatoryScaleIndex lam r hlam) (x - t) : ℂ) *
        phase (lam * (x - t) ^ 2) * b t) :=
    integrable_fixedHeightQuadraticKernel_mul_locallyIntegrable hb r lam hlam x
  unfold paperLowCZKernel paperLowOscillatoryKernel lowOscillatoryKernel
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun r _ ↦ hk r)]
  exact Finset.sum_congr rfl (fun r _ ↦ fixedHeightQuadraticKernel_integral_eq_paper r lam hlam b x)

/-- The paper's literal low contribution: first a finite sum over all
heights `0 ≤ r ≤ B_k`, then the full real supremum, then the magnitude-level sum. -/
noncomputable def paperFullLowHeightContribution {ι : Type*} (f : ℝ → ℂ)
    (z R : ι → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, ⨆ lam : {lam : ℝ // lam ≠ 0},
    ‖∑ r ∈ Finset.range (fullHighCutoff k + 1),
      ∫ t, disjointLevelAtomSum fullAmplitude f k z R (x - t) *
        (dyadicPsi (oscillatoryScaleIndex lam.1 r lam.2) t : ℂ) * phase (lam.1 * t ^ 2)‖ₑ

theorem paperFullLowContribution_eq_heightContribution
    {ι : Type*} [Countable ι] {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) (x : ℝ) :
    paperFullLowContribution f z R x = paperFullLowHeightContribution f z R x := by
  unfold paperFullLowContribution paperFullLowHeightContribution
  apply tsum_congr
  intro k
  unfold paperLowLevelMaximal
  apply iSup_congr
  intro lam
  rw [integral_paperLowCZKernel_eq_sum_fixedHeights
    ((memLp_disjointLevelAtomSum hf hfi (fullAmplitude_pos k).le z R hR hdisj).locallyIntegrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2))]

/-- Full low-oscillation endpoint estimate in the paper's exact height and
convolution conventions, with the exceptional family length left explicit. -/
theorem paperFullLowHeightContribution_levelSet_le_length_add_orlicz
    {ι : Type*} [Countable ι] {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) :
    volume {x | 1 < paperFullLowHeightContribution f z R x} ≤
      5 * (∑' i, ENNReal.ofReal (R i)) +
        fullLowEndpointConstant * ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 1 ‖f x‖) := by
  simp_rw [← paperFullLowContribution_eq_heightContribution hf hfi z R hR hdisj]
  exact paperFullLowContribution_levelSet_le_length_add_orlicz hf hfi z R hR hdisj

end PositiveLowFullEstimate
end QuadraticCarleson
