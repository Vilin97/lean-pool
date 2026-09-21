/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveLowFullMajorant
import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveLowFullIntegral

/-!
# The full-operator low endpoint branch

The actual low kernel acts on the genuine countable level-atom sum. Off the
union of the fivefold intervals, a common measurable majorant bounds every
real modulation simultaneously. Markov's inequality is applied only to that
majorant, giving an outer-measure bound without assuming measurability of
the real supremum. The exceptional set contributes at most five times the
sum of the interval lengths.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Function

namespace QuadraticCarleson
namespace PositiveLowFullEstimate

open CalderonZygmundLevelAtoms LowKernelLevelSummation
open PositiveEndpointOptimization PositiveLevelIntegration PositiveHighHeightEstimate

def fivefoldExceptionalSet {ι : Type*} (z R : ι → ℝ) : Set ℝ :=
  ⋃ i, centeredInterval (z i) (5 * R i)

theorem measurableSet_fivefoldExceptionalSet {ι : Type*} [Countable ι] (z R : ι → ℝ) :
    MeasurableSet (fivefoldExceptionalSet z R) :=
  MeasurableSet.iUnion (fun _ ↦ measurableSet_Ico)

theorem tripleCenteredInterval_subset_fivefold {z R : ℝ} (hR : 0 < R) :
    tripleCenteredInterval z R ⊆ centeredInterval z (5 * R) := by
  intro x hx
  obtain ⟨hl, hu⟩ := hx
  constructor <;> linarith

theorem not_mem_triple_of_not_mem_fivefoldExceptionalSet {ι : Type*} {z R : ι → ℝ}
    (hR : ∀ i, 0 < R i) {x : ℝ} (hx : x ∉ fivefoldExceptionalSet z R) (i : ι) :
    x ∉ tripleCenteredInterval (z i) (R i) := by
  intro hi
  apply hx
  exact mem_iUnion.mpr ⟨i, tripleCenteredInterval_subset_fivefold (hR i) hi⟩

theorem volume_fivefoldExceptionalSet_le {ι : Type*} [Countable ι] (z R : ι → ℝ) :
    volume (fivefoldExceptionalSet z R) ≤ 5 * ∑' i, ENNReal.ofReal (R i) := by
  apply (measure_iUnion_le _).trans_eq
  simp_rw [volume_centeredInterval, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)]
  rw [ENNReal.tsum_mul_left]
  norm_num

/-- The genuine full low contribution with `A_k = 2^(2^k)` and the exact
integer cutoff `B_k = 20·2^k`. -/
noncomputable def paperFullLowContribution {ι : Type*} (f : ℝ → ℂ)
    (z R : ι → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, paperLowLevelMaximal (fullHighCutoff k)
    (disjointLevelAtomSum fullAmplitude f k z R) x

theorem paperFullLowContribution_le_majorant {ι : Type*} [Countable ι]
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i)))
    {x : ℝ} (hx : x ∉ fivefoldExceptionalSet z R) :
    paperFullLowContribution f z R x ≤ fullLowMajorant f z R x := by
  apply ENNReal.tsum_le_tsum
  intro k
  apply (paperLowLevelMaximal_disjointLevelAtomSum_le (fullHighCutoff k) hf hfi
    (fullAmplitude_pos k).le z R hdisj x).trans
  apply ENNReal.tsum_le_tsum
  intro i
  exact paperLowBadAtomMaximal_levelAtom_le_majorant (fullHighCutoff k) hf
    (fullAmplitude_pos k).le (hR i)
    (not_mem_triple_of_not_mem_fivefoldExceptionalSet hR hx i)

/-- The integral bound on the precise exceptional-set complement. -/
theorem lintegral_paperFullLowContribution_compl_le_orlicz
    {ι : Type*} [Countable ι] {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) :
    (∫⁻ x in (fivefoldExceptionalSet z R)ᶜ, paperFullLowContribution f z R x) ≤
      fullLowEndpointConstant * ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 1 ‖f x‖) := by
  calc
    _ ≤ ∫⁻ x in (fivefoldExceptionalSet z R)ᶜ, fullLowMajorant f z R x := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_fivefoldExceptionalSet z R).compl] with x hx
      exact paperFullLowContribution_le_majorant hf hfi z R hR hdisj hx
    _ ≤ ∫⁻ x, fullLowMajorant f z R x := by
      simpa only [Measure.restrict_univ] using lintegral_mono_set
        (μ := volume) (f := fullLowMajorant f z R) (subset_univ (fivefoldExceptionalSet z R)ᶜ)
    _ ≤ _ := lintegral_fullLowMajorant_le_orlicz hf z R hR hdisj

/-- Markov is used on the common measurable majorant, not on the
uncountable real supremum. Hence this is a valid outer-measure statement. -/
theorem paperFullLowContribution_levelSet_le_exceptional_add_orlicz
    {ι : Type*} [Countable ι] {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) :
    volume {x | 1 < paperFullLowContribution f z R x} ≤
      volume (fivefoldExceptionalSet z R) +
        fullLowEndpointConstant * ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 1 ‖f x‖) := by
  have hset : {x | 1 < paperFullLowContribution f z R x} ⊆
      fivefoldExceptionalSet z R ∪ {x | 1 ≤ fullLowMajorant f z R x} := by
    intro x hx
    by_cases he : x ∈ fivefoldExceptionalSet z R
    · exact Or.inl he
    · exact Or.inr (hx.trans_le (paperFullLowContribution_le_majorant hf hfi z R hR hdisj he)).le
  apply (measure_mono hset).trans
  apply (measure_union_le _ _).trans
  apply add_le_add le_rfl
  have hm : volume {x | 1 ≤ fullLowMajorant f z R x} ≤ ∫⁻ x, fullLowMajorant f z R x := by
    simpa only [one_mul] using mul_meas_ge_le_lintegral (μ := volume)
      (measurable_fullLowMajorant f z R) 1
  exact hm.trans (lintegral_fullLowMajorant_le_orlicz hf z R hR hdisj)

/-- The full low endpoint branch for any explicit countable disjoint
interval family: only its total length remains as the exceptional term. -/
theorem paperFullLowContribution_levelSet_le_length_add_orlicz
    {ι : Type*} [Countable ι] {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) :
    volume {x | 1 < paperFullLowContribution f z R x} ≤
      5 * (∑' i, ENNReal.ofReal (R i)) +
        fullLowEndpointConstant * ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 1 ‖f x‖) := by
  exact (paperFullLowContribution_levelSet_le_exceptional_add_orlicz hf hfi z R hR hdisj).trans
    (add_le_add (volume_fivefoldExceptionalSet_le z R) le_rfl)

end PositiveLowFullEstimate
end QuadraticCarleson
