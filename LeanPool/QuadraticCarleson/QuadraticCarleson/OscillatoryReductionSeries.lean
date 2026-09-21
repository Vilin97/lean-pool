/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.OscillatoryReductionKernel
import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveLowFullHeightIdentity

/-!
# The exact oscillatory series on the paper's test domain

For fixed observation point and modulation, compact support of the input
makes every sufficiently high dyadic term identically zero. Thus all
integral/series interchanges below are genuine and require no convergence
hypothesis beyond membership in `L0Infinity`.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace QuadraticCarleson
namespace OscillatoryReduction

theorem exists_spatial_bound (f : L0Infinity) (x : ℝ) :
    ∃ M : ℝ, ∀ y : ℝ, f y ≠ 0 → |x - y| ≤ M := by
  obtain ⟨S, _, hS⟩ := f.hasCompactSupport_toFun.isBounded.exists_pos_norm_le
  refine ⟨|x| + S, ?_⟩
  intro y hy
  have hb : |y| ≤ S := by
    simpa only [Real.norm_eq_abs] using hS y (subset_tsupport f hy)
  exact (abs_sub x y).trans (add_le_add le_rfl hb)

theorem exists_eventually_zero_height_integrands
    (lam : ℝ) (hlam : lam ≠ 0) (f : L0Infinity) (x : ℝ) :
    ∃ N : ℕ, ∀ r : ℕ, N ≤ r → ∀ y : ℝ,
      fixedHeightQuadraticKernel lam r hlam (x - y) * f y = 0 := by
  obtain ⟨M, hM⟩ := exists_spatial_bound f x
  let j := oscillatoryScaleIndex lam 0 hlam
  have hp : Tendsto (fun r : ℕ ↦ (2 : ℝ) ^ r) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hc : 0 < (2 : ℝ) ^ (j - 3) := by positivity
  have hscale : Tendsto (fun r : ℕ ↦ (2 : ℝ) ^ (j + (r : ℤ) - 3)) atTop atTop := by
    convert hp.const_mul_atTop hc using 1
    funext r
    rw [show j + (r : ℤ) - 3 = (j - 3) + (r : ℤ) by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hscale.eventually_gt_atTop M)
  refine ⟨N, ?_⟩
  intro r hr y
  by_cases hy : f y = 0
  · simp [hy]
  · have hz : dyadicPsi (oscillatoryScaleIndex lam r hlam) (x - y) = 0 := by
      rw [oscillatoryScaleIndex_eq_add]
      exact dyadicPsi_eq_zero_of_abs_le ((hM y hy).trans (hN r hr).le)
    simp [fixedHeightQuadraticKernel, hz]

theorem hasSum_oscillatoryIntegrals (lam : ℝ) (hlam : lam ≠ 0)
    (f : L0Infinity) (x : ℝ) :
    HasSum (fun r : ℕ ↦ ∫ t, f (x - t) *
      (dyadicPsi (oscillatoryScaleIndex lam r hlam) t : ℂ) * phase (lam * t ^ 2))
      (∫ y, highPassKernel lam hlam (x - y) * f y) := by
  let F (r : ℕ) (y : ℝ) := fixedHeightQuadraticKernel lam r hlam (x - y) * f y
  have hI (r : ℕ) : Integrable (F r) :=
    PositiveLowFullEstimate.integrable_fixedHeightQuadraticKernel_mul_locallyIntegrable
      f.integrable.locallyIntegrable r lam hlam x
  obtain ⟨N, hN⟩ := exists_eventually_zero_height_integrands lam hlam f x
  have hn : HasFiniteSupport (fun r : ℕ ↦ ∫ y, ‖F r y‖) := by
    apply (Finset.finite_toSet (Finset.range N)).subset
    intro r hr
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra h
    apply hr
    have hz : ∀ y, F r y = 0 := hN r (Nat.le_of_not_gt h)
    simp [hz]
  have hs := hasSum_integral_of_summable_integral_norm hI
    (summable_of_hasFiniteSupport hn)
  have hpoint (y : ℝ) : (∑' r : ℕ, F r y) = highPassKernel lam hlam (x - y) * f y :=
    ((hasSum_oscillatoryKernels lam hlam (x - y)).mul_right (f y)).tsum_eq
  simp_rw [hpoint] at hs
  apply hs.congr_fun
  intro r
  exact (fixedHeightQuadraticKernel_integral_eq_paper r lam hlam f x).symm

noncomputable def paperOscillatoryAction (lam : ℝ) (hlam : lam ≠ 0)
    (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' r : ℕ, ∫ t, f (x - t) *
    (dyadicPsi (oscillatoryScaleIndex lam r hlam) t : ℂ) * phase (lam * t ^ 2)

theorem paperOscillatoryAction_eq_integral (lam : ℝ) (hlam : lam ≠ 0)
    (f : L0Infinity) (x : ℝ) :
    paperOscillatoryAction lam hlam f x =
      ∫ y, highPassKernel lam hlam (x - y) * f y :=
  (hasSum_oscillatoryIntegrals lam hlam f x).tsum_eq

end OscillatoryReduction
end QuadraticCarleson
