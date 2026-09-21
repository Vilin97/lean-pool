/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.LowKernelRealMaximal
import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveHighHeightFullEndpoint
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The low kernel applied to the genuine countable atom sum

For each fixed modulation the telescoped low kernel is globally bounded.
The levelwise atom masses are summable for integrable input, so the Bochner
integral commutes with their countable sum. No formal integral interchange
is left as an assumption.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Function

namespace QuadraticCarleson
namespace PositiveLowFullEstimate

open CalderonZygmundLevelAtoms LowKernelLevelSummation
open PositiveEndpointOptimization PositiveLevelIntegration PositiveHighHeightEstimate

theorem paperLowOscillatoryKernel_norm_le_global
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ) (t : ℝ) :
    ‖paperLowOscillatoryKernel lam hlam B t‖ ≤ 8 * Real.sqrt |lam| := by
  by_cases ht : paperLowOscillatoryKernel lam hlam B t = 0
  · rw [ht, norm_zero]
    positivity
  have hs := (paperLowOscillatoryKernel_support_normalized lam hlam B ht).1
  have ht0 : 0 < |t| := by
    by_contra h
    have hz : |t| = 0 := le_antisymm (le_of_not_gt h) (abs_nonneg _)
    rw [hz, zero_mul] at hs
    norm_num at hs
  apply (paperLowOscillatoryKernel_norm_le_inv_abs hlam B
    (abs_pos.mp ht0)).trans
  apply (div_le_iff₀ ht0).mpr
  nlinarith

theorem integral_paperLowCZKernel_mul_levelAtom_eq_setIntegral
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ) {A : ℕ → ℝ} {f : ℝ → ℂ}
    (k : ℕ) (z R x : ℝ) :
    (∫ y, paperLowCZKernel lam hlam B x y * levelAtom A f k z R y) =
      ∫ y in centeredInterval z R,
        paperLowCZKernel lam hlam B x y * levelAtom A f k z R y := by
  rw [← integral_indicator (show MeasurableSet (centeredInterval z R) from measurableSet_Ico)]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ centeredInterval z R
  · simp [hy]
  · simp [hy, levelAtom_eq_zero_of_not_mem hy]

theorem tsum_lintegral_enorm_paperLowCZKernel_mul_levelAtom_lt_top
    {ι : Type*} [Countable ι] {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ)
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k : ℕ} (hAk : 0 ≤ A k) (z R : ι → ℝ)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) (x : ℝ) :
    (∑' i : ι, ∫⁻ y,
      ‖paperLowCZKernel lam hlam B x y * levelAtom A f k (z i) (R i) y‖ₑ) < ∞ := by
  have hp (i : ι) : (∫⁻ y,
      ‖paperLowCZKernel lam hlam B x y * levelAtom A f k (z i) (R i) y‖ₑ) ≤
      ENNReal.ofReal (8 * Real.sqrt |lam|) *
        ENNReal.ofReal (∫ y, ‖levelAtom A f k (z i) (R i) y‖) := by
    calc
      _ ≤ ∫⁻ y, ENNReal.ofReal (8 * Real.sqrt |lam|) *
          ‖levelAtom A f k (z i) (R i) y‖ₑ := by
        apply lintegral_mono
        intro y
        dsimp only
        rw [enorm_mul]
        apply mul_le_mul' ?_ le_rfl
        simpa only [← ofReal_norm, paperLowCZKernel] using ENNReal.ofReal_le_ofReal
          (paperLowOscillatoryKernel_norm_le_global hlam B (x - y))
      _ = _ := by
        simp only [← ofReal_norm]
        rw [lintegral_const_mul' _ _ (by finiteness),
          ← ofReal_integral_eq_lintegral_ofReal (integrable_levelAtom hf hAk (z i) (R i)).norm
            (Filter.Eventually.of_forall fun y ↦ norm_nonneg (levelAtom A f k (z i) (R i) y))]
  have hs := ENNReal.tsum_le_tsum hp
  rw [ENNReal.tsum_mul_left] at hs
  apply hs.trans_lt
  have hmass : magnitudeLevelL1Mass volume A f k < ∞ := by
    apply lt_of_le_of_lt ?_ hfi.hasFiniteIntegral
    simpa only [magnitudeLevelL1Mass, ofReal_norm, Measure.restrict_univ] using
      lintegral_mono_set (μ := volume) (f := fun y ↦ ‖f y‖ₑ) (subset_univ (magnitudeLevelSet A f k))
  exact ENNReal.mul_lt_top (by finiteness)
    ((tsum_atomL1Mass_le_two_mul_global_level_mass hf hAk z R hdisj).trans_lt
      (ENNReal.mul_lt_top (by finiteness) hmass))

theorem integral_paperLowCZKernel_mul_disjointLevelAtomSum
    {ι : Type*} [Countable ι] {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ)
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k : ℕ} (hAk : 0 ≤ A k) (z R : ι → ℝ)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) (x : ℝ) :
    (∫ y, paperLowCZKernel lam hlam B x y * disjointLevelAtomSum A f k z R y) =
      ∑' i : ι, ∫ y in centeredInterval (z i) (R i),
        paperLowCZKernel lam hlam B x y * levelAtom A f k (z i) (R i) y := by
  have hmeas (i : ι) : AEStronglyMeasurable
      (fun y ↦ paperLowCZKernel lam hlam B x y * levelAtom A f k (z i) (R i) y) := by
    exact (((continuous_paperLowOscillatoryKernel hlam B).comp
      (continuous_const.sub continuous_id)).measurable.mul
        (measurable_levelAtom hf k (z i) (R i))).aestronglyMeasurable
  simp only [disjointLevelAtomSum, ← tsum_mul_left]
  rw [integral_tsum hmeas
    (tsum_lintegral_enorm_paperLowCZKernel_mul_levelAtom_lt_top hlam B hf hfi hAk z R hdisj x).ne]
  exact tsum_congr (fun i ↦
    integral_paperLowCZKernel_mul_levelAtom_eq_setIntegral hlam B k (z i) (R i) x)

/-- The actual finite low-height kernel, maximized over all real nonzero modulations. -/
noncomputable def paperLowLevelMaximal (B : ℕ) (b : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ lam : {lam : ℝ // lam ≠ 0}, ‖∫ y, paperLowCZKernel lam.1 lam.2 B x y * b y‖ₑ

theorem paperLowLevelMaximal_disjointLevelAtomSum_le
    {ι : Type*} [Countable ι] (B : ℕ) {A : ℕ → ℝ} {f : ℝ → ℂ}
    (hf : Measurable f) (hfi : Integrable f) {k : ℕ} (hAk : 0 ≤ A k)
    (z R : ι → ℝ)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) (x : ℝ) :
    paperLowLevelMaximal B (disjointLevelAtomSum A f k z R) x ≤
      ∑' i : ι, paperLowBadAtomMaximal B (levelAtom A f k (z i) (R i)) (z i) (R i) x := by
  apply iSup_le
  intro lam
  rw [integral_paperLowCZKernel_mul_disjointLevelAtomSum lam.2 B hf hfi hAk z R hdisj x]
  apply enorm_tsum_le_tsum_enorm.trans
  apply ENNReal.tsum_le_tsum
  intro i
  simpa only [ofReal_norm, paperLowBadAtomMaximal] using le_iSup (fun μ : {μ : ℝ // μ ≠ 0} ↦
    ENNReal.ofReal ‖∫ y in centeredInterval (z i) (R i),
      paperLowCZKernel μ.1 μ.2 B x y * levelAtom A f k (z i) (R i) y‖) lam

end PositiveLowFullEstimate
end QuadraticCarleson
