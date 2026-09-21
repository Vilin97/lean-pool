/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveHighHeightFullEndpoint

/-!
# The lacunary high contribution

The lacunary amplitude levels use the exact integer cutoff `20·2^(2^k)`.
The already proved real-parameter quadratic decay is stronger than needed for
the lacunary modulation set. We first estimate that real-parameter high part,
and then restrict the supremum to the paper's dyadic modulations.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Function

namespace QuadraticCarleson
namespace PositiveHighHeightEstimate

open CalderonZygmundLevelAtoms PositiveLevelIntegration PositiveEndpointOptimization

def lacunaryHighCutoff (k : ℕ) : ℕ := 20 * 2 ^ (2 ^ k)

theorem cast_lacunaryHighCutoff (k : ℕ) :
    (lacunaryHighCutoff k : ℝ) = lacunaryCutoff 20 k := by
  simp [lacunaryHighCutoff, lacunaryCutoff, lacunaryScale_eq_two_pow]

theorem lacunaryHighCutoff_pos (k : ℕ) : 0 < lacunaryHighCutoff k := by
  unfold lacunaryHighCutoff
  positivity

noncomputable def lacunaryHighPrefactorSeries : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal
    (Real.exp (-2 * (1 / 10) * Real.log 2 * lacunaryCutoff 20 k) * lacunaryAmplitude k /
      paperLog 1 (lacunaryCutoff 20 k) ^ 2)

theorem lacunaryHighPrefactorSeries_lt_top : lacunaryHighPrefactorSeries < ∞ := by
  exact (summable_lacunaryHighFrequencyPrefactor (β := 1 / 10) (C := 20)
    (by norm_num) (by norm_num)).tsum_ofReal_lt_top

theorem lacunaryHighPrefactor_eq (k : ℕ) :
    4 * lacunaryAmplitude k * (2 : ℝ) ^ (-((lacunaryHighCutoff k : ℕ) : ℝ) / 5) /
      paperLog 1 (lacunaryCutoff 20 k) ^ 2 =
      4 * (Real.exp (-2 * (1 / 10) * Real.log 2 * lacunaryCutoff 20 k) *
        lacunaryAmplitude k / paperLog 1 (lacunaryCutoff 20 k) ^ 2) := by
  rw [cast_lacunaryHighCutoff]
  have hp : (2 : ℝ) ^ (-(lacunaryCutoff 20 k) / 5) =
      Real.exp (-2 * (1 / 10) * Real.log 2 * lacunaryCutoff 20 k) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [hp]
  ring

theorem tsum_lacunaryHighPrefactor :
    (∑' k : ℕ, ENNReal.ofReal (4 * lacunaryAmplitude k *
      (2 : ℝ) ^ (-((lacunaryHighCutoff k : ℕ) : ℝ) / 5) /
        paperLog 1 (lacunaryCutoff 20 k) ^ 2)) =
      4 * lacunaryHighPrefactorSeries := by
  simp_rw [lacunaryHighPrefactor_eq, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  rw [ENNReal.tsum_mul_left]
  norm_num [lacunaryHighPrefactorSeries]

noncomputable def lacunaryHighEndpointConstant : ℝ≥0∞ :=
  highHeightTailConstant ^ 2 * (4 * lacunaryHighPrefactorSeries) *
    ENNReal.ofReal (lacunaryHighLevelConstant 20)

theorem lacunaryHighEndpointConstant_lt_top : lacunaryHighEndpointConstant < ∞ := by
  unfold lacunaryHighEndpointConstant
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top highHeightTailConstant_lt_top)
      (ENNReal.mul_lt_top (by finiteness) lacunaryHighPrefactorSeries_lt_top)) (by finiteness)

/-- Even the real-parameter high supremum with the lacunary levels and
cutoffs has the required `L (log₂ L)²` bound. -/
theorem realHighContribution_lacunaryLevels_levelSet_le_orlicz
    {ι : Type*} [Countable ι] {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) :
    volume {x | 1 < paperHighContribution lacunaryHighCutoff
      (fun k ↦ disjointLevelAtomSum lacunaryAmplitude f k z R) x} ≤
      lacunaryHighEndpointConstant *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 2 ‖f x‖ ^ 2) := by
  have hmain := paperHighContribution_disjointLevelAtoms_weighted_levelSet_le
    (fun k ↦ (lacunaryAmplitude_pos k).le) lacunaryHighCutoff
    (fun k ↦ paperLog 1 (lacunaryCutoff 20 k) ^ 2)
    (fun k ↦ sq_pos_of_pos ((by norm_num : (0 : ℝ) < 1).trans_le
      (one_le_paperLog_one_lacunaryCutoff (by norm_num) k))) hf hfi z R hR hdisj
  rw [tsum_lacunaryHighPrefactor] at hmain
  have hc : 0 ≤ lacunaryHighLevelConstant 20 := by
    unfold lacunaryHighLevelConstant
    exact add_nonneg (lacunarySmallLevelConstant_nonneg (by norm_num))
      (mul_nonneg (by norm_num) (sq_nonneg _))
  have hweight : (∑' k : ℕ, ENNReal.ofReal (paperLog 1 (lacunaryCutoff 20 k) ^ 2) *
      magnitudeLevelL1Mass volume lacunaryAmplitude f k) ≤
      ENNReal.ofReal (lacunaryHighLevelConstant 20) *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 2 ‖f x‖ ^ 2) := by
    have h := tsum_lacunaryHighWeight_mul_levelMass_le_orlicz volume
      (C := 20) (by norm_num) hf
    simp_rw [ENNReal.ofReal_mul hc] at h
    rwa [lintegral_const_mul' _ _ (by finiteness)] at h
  apply hmain.trans
  calc
    _ ≤ highHeightTailConstant ^ 2 * (4 * lacunaryHighPrefactorSeries) *
        (ENNReal.ofReal (lacunaryHighLevelConstant 20) *
          ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 2 ‖f x‖ ^ 2)) :=
      mul_le_mul' le_rfl hweight
    _ = _ := by unfold lacunaryHighEndpointConstant; ring

/-- The paper's dyadic-modulation high contribution. -/
noncomputable def paperLacunaryHighContribution (B : ℕ → ℕ) (b : ℕ → ℝ → ℂ)
    (x : ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, ⨆ m : ℤ, ‖∑' n : ℕ,
    ∫ t, b k (x - t) *
      (dyadicPsi (oscillatoryScaleIndex ((2 : ℝ) ^ m) (B k + n + 1)
        (zpow_pos (by norm_num) m).ne') t : ℂ) *
      phase ((2 : ℝ) ^ m * t ^ 2)‖ₑ

theorem paperLacunaryHighContribution_le_real (B : ℕ → ℕ) (b : ℕ → ℝ → ℂ)
    (x : ℝ) : paperLacunaryHighContribution B b x ≤ paperHighContribution B b x := by
  apply ENNReal.tsum_le_tsum
  intro k
  apply iSup_le
  intro m
  exact le_iSup (fun lam : {lam : ℝ // lam ≠ 0} ↦ ‖∑' n : ℕ,
    ∫ t, b k (x - t) *
      (dyadicPsi (oscillatoryScaleIndex lam.val (B k + n + 1) lam.property) t : ℂ) *
        phase (lam.val * t ^ 2)‖ₑ) ⟨(2 : ℝ) ^ m, (zpow_pos (by norm_num) m).ne'⟩

theorem lacunaryHighContribution_levelSet_le_orlicz
    {ι : Type*} [Countable ι] {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) :
    volume {x | 1 < paperLacunaryHighContribution lacunaryHighCutoff
      (fun k ↦ disjointLevelAtomSum lacunaryAmplitude f k z R) x} ≤
      lacunaryHighEndpointConstant *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 2 ‖f x‖ ^ 2) := by
  apply (measure_mono (fun x hx ↦ hx.trans_le
    (paperLacunaryHighContribution_le_real _ _ x))).trans
  exact realHighContribution_lacunaryLevels_levelSet_le_orlicz hf hfi z R hR hdisj

end PositiveHighHeightEstimate
end QuadraticCarleson
