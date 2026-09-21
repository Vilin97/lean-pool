/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveHighHeightWeighted
import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveHighHeightConvergence

/-!
# The full-operator high contribution is bounded by the L log L modular

We make the paper's unspecified large cutoff constant explicit: `B_k = 20·2^k`.
With the proved exponent `β = 1/10`, the numerical high-frequency series is
summable. This theorem needs an explicit disjoint interval family, but no
construction of a Calderón--Zygmund decomposition and no unproved operator
estimate.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Function

namespace QuadraticCarleson
namespace PositiveHighHeightEstimate

open CalderonZygmundLevelAtoms PositiveLevelIntegration PositiveEndpointOptimization

/-- The exponentially growing height cutoff for the full modulation endpoint. -/
def fullHighCutoff (k : ℕ) : ℕ := 20 * 2 ^ k

theorem cast_fullHighCutoff (k : ℕ) : (fullHighCutoff k : ℝ) = fullCutoff 20 k := by
  simp [fullHighCutoff, fullCutoff, dyadicScale]

theorem fullHighCutoff_pos (k : ℕ) : 0 < fullHighCutoff k := by
  unfold fullHighCutoff
  positivity

/-- The series of high-frequency prefactors at the full endpoint cutoffs. -/
noncomputable def fullHighPrefactorSeries : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal (highFrequencyPrefactor (1 / 10) (fullAmplitude k) (fullCutoff 20 k))

theorem fullHighPrefactorSeries_lt_top : fullHighPrefactorSeries < ∞ := by
  exact (summable_fullHighFrequencyPrefactor (β := 1 / 10) (C := 20)
    (by norm_num) (by norm_num)).tsum_ofReal_lt_top

theorem fullHighPrefactor_eq (k : ℕ) :
    4 * fullAmplitude k * (2 : ℝ) ^ (-((fullHighCutoff k : ℕ) : ℝ) / 5) /
      fullCutoff 20 k =
      4 * highFrequencyPrefactor (1 / 10) (fullAmplitude k) (fullCutoff 20 k) := by
  rw [cast_fullHighCutoff]
  have hp : (2 : ℝ) ^ (-(fullCutoff 20 k) / 5) =
      Real.exp (-2 * (1 / 10) * Real.log 2 * fullCutoff 20 k) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [hp]
  unfold highFrequencyPrefactor
  ring

theorem tsum_fullHighPrefactor :
    (∑' k : ℕ, ENNReal.ofReal (4 * fullAmplitude k *
      (2 : ℝ) ^ (-((fullHighCutoff k : ℕ) : ℝ) / 5) / fullCutoff 20 k)) =
      4 * fullHighPrefactorSeries := by
  simp_rw [fullHighPrefactor_eq, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  rw [ENNReal.tsum_mul_left]
  norm_num [fullHighPrefactorSeries]

/-- The high-height endpoint constant obtained from the squared tail bound and prefactor series. -/
noncomputable def fullHighEndpointConstant : ℝ≥0∞ :=
  highHeightTailConstant ^ 2 * (4 * fullHighPrefactorSeries) * 80

theorem fullHighEndpointConstant_lt_top : fullHighEndpointConstant < ∞ := by
  unfold fullHighEndpointConstant
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top highHeightTailConstant_lt_top)
      (ENNReal.mul_lt_top (by finiteness) fullHighPrefactorSeries_lt_top)) (by finiteness)

/-- The actual high contribution, with the full-operator amplitude and
cutoff choices, satisfies the paper's `L log L` level-set bound. -/
theorem fullHighContribution_levelSet_le_orlicz
    {ι : Type*} [Countable ι] {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) :
    volume {x | 1 < paperHighContribution fullHighCutoff
      (fun k ↦ disjointLevelAtomSum fullAmplitude f k z R) x} ≤
      fullHighEndpointConstant * ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 1 ‖f x‖) := by
  have hmain := paperHighContribution_disjointLevelAtoms_weighted_levelSet_le
    (fun k ↦ (fullAmplitude_pos k).le) fullHighCutoff (fullCutoff 20)
    (fun k ↦ by unfold fullCutoff; exact mul_pos (by norm_num) (dyadicScale_pos k))
    hf hfi z R hR hdisj
  rw [tsum_fullHighPrefactor] at hmain
  have hweight : (∑' k : ℕ, ENNReal.ofReal (fullCutoff 20 k) *
      magnitudeLevelL1Mass volume fullAmplitude f k) ≤
      80 * ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 1 ‖f x‖) := by
    have h := tsum_full_weight_mul_levelMass_le_orlicz volume (C := 20) (by norm_num) hf
    norm_num only [show (4 : ℝ) * 20 = 80 by norm_num] at h
    simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 80)] at h
    rw [lintegral_const_mul' _ _ (by finiteness)] at h
    simpa only [ENNReal.ofReal_ofNat] using h
  apply hmain.trans
  calc
    _ ≤ highHeightTailConstant ^ 2 * (4 * fullHighPrefactorSeries) *
        (80 * ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 1 ‖f x‖)) :=
      mul_le_mul' le_rfl hweight
    _ = _ := by unfold fullHighEndpointConstant; ring

end PositiveHighHeightEstimate
end QuadraticCarleson
