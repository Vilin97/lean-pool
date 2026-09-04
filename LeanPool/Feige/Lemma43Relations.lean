/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.Lemma43

/-!
# Automatic elementary relations for the local transfer step

The relations `B = A + u + v` and `F = B - v` are pointwise identities
between the two transfer test functions and their upper/lower exponential
tails.  Consequently the `ProbabilityRelations` input of `Lemma43.complete`
holds for every finite law and need not remain an external hypothesis.
-/

open MeasureTheory Real Set

namespace Feige
namespace Lemma43

open TransferStein TransferTestFunctions

theorem transferPsi_eq_transferPhi_add_tails
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (z : ℝ) :
    transferPsi c z =
      transferPhi d z + uTailIntegrand d z + vTailIntegrand c z := by
  by_cases hz : 0 ≤ z
  · rw [transferPsi_of_nonneg hc hz, transferPhi_of_nonneg hd hz]
    simp [uTailIntegrand, vTailIntegrand, hz, not_lt_of_ge hz]
  · have hz' : z < 0 := lt_of_not_ge hz
    rw [transferPsi_of_nonpos hc hz'.le,
      transferPhi_of_nonpos hd hz'.le]
    simp [uTailIntegrand, vTailIntegrand, hz, hz']

theorem indicator_Ici_eq_transferPsi_sub_vTail
    {c : ℝ} (hc : 0 < c) (z : ℝ) :
    (Ici (0 : ℝ)).indicator (fun _ ↦ (1 : ℝ)) z =
      transferPsi c z - vTailIntegrand c z := by
  by_cases hz : 0 ≤ z
  · simp [Set.indicator, hz, transferPsi_of_nonneg hc hz,
      vTailIntegrand, not_lt_of_ge hz]
  · have hz' : z < 0 := lt_of_not_ge hz
    simp [Set.indicator, hz, transferPsi_of_nonpos hc hz'.le,
      vTailIntegrand, hz']

lemma integrable_transferPhi
    (ν : Measure ℝ) [IsFiniteMeasure ν] {d : ℝ} (hd : 0 < d) :
    Integrable (transferPhi d) ν := by
  apply Integrable.of_bound
    (continuous_transferPhi d).measurable.aestronglyMeasurable 1
  filter_upwards with z
  exact norm_transferPhi_le_one hd z

lemma integrable_transferPsi
    (ν : Measure ℝ) [IsFiniteMeasure ν] (c : ℝ) :
    Integrable (transferPsi c) ν := by
  apply Integrable.of_bound
    (continuous_transferPsi c).measurable.aestronglyMeasurable 1
  filter_upwards with z
  exact norm_transferPsi_le_one c z

/-- `B = A + w` for every finite law. -/
theorem B_eq_A_add_w
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    B ν c = A ν d + w ν c d := by
  rw [B, A, w, u, v, uProbability_eq_integral ν hd,
    vProbability_eq_integral ν hc]
  have hphi := integrable_transferPhi ν hd
  have hu := integrable_uTailIntegrand ν hd
  have hv := integrable_vTailIntegrand ν hc
  calc
    (∫ z, transferPsi c z ∂ν) =
        ∫ z, transferPhi d z +
          (uTailIntegrand d z + vTailIntegrand c z) ∂ν := by
      apply integral_congr_ae
      filter_upwards with z
      simpa [add_assoc] using
        transferPsi_eq_transferPhi_add_tails hc hd z
    _ = (∫ z, transferPhi d z ∂ν) +
        ∫ z, uTailIntegrand d z + vTailIntegrand c z ∂ν := by
      simpa only [Pi.add_apply] using integral_add hphi (hu.add hv)
    _ = (∫ z, transferPhi d z ∂ν) +
        ((∫ z, uTailIntegrand d z ∂ν) +
          ∫ z, vTailIntegrand c z ∂ν) := by
      rw [integral_add hu hv]

/-- `F = B - v` for every finite law. -/
theorem F_eq_B_sub_v
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    {c : ℝ} (hc : 0 < c) :
    F ν = B ν c - v ν c := by
  rw [F, B, v, vProbability_eq_integral ν hc]
  change ν.real (Ici (0 : ℝ)) =
    (∫ z, transferPsi c z ∂ν) -
      ∫ z, vTailIntegrand c z ∂ν
  rw [← integral_indicator_one measurableSet_Ici]
  have hpsi := integrable_transferPsi ν c
  have hv := integrable_vTailIntegrand ν hc
  rw [← integral_sub hpsi hv]
  apply integral_congr_ae
  filter_upwards with z
  exact indicator_Ici_eq_transferPsi_sub_vTail hc z

/-- The elementary relation bundle required by `Lemma43.transfer_identity`
is automatic for any two finite laws. -/
theorem probabilityRelations
    (νP νM : Measure ℝ) [IsFiniteMeasure νP] [IsFiniteMeasure νM]
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    ProbabilityRelations νP νM c d :=
  ⟨B_eq_A_add_w νP hc hd, B_eq_A_add_w νM hc hd,
    F_eq_B_sub_v νP hc, F_eq_B_sub_v νM hc⟩

end Lemma43
end Feige
