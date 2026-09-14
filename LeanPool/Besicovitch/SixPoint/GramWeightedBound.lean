/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.GramCertificateCover
public import LeanPool.Besicovitch.SixPoint.EndpointPacking

/-!
# The coordinate-free weighted bound at the small rational weights

Combining the local Gram certificates with the finite cover of second-child radii gives the
weighted geometric bound for every pair of separated sibling pairs in the unit ball.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

/-- A separated sibling pair in the unit ball has its second radius in `[barC - 1, 1]`. -/
private theorem second_radius_mem {E : Type*} [NormedAddCommGroup E] {p₁ p₂ : E}
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hsep : barC ≤ ‖p₁ - p₂‖) :
    barC - 1 ≤ ‖p₂‖ ∧ ‖p₂‖ ≤ 1 := by
  refine ⟨?_, hp₂⟩
  have := norm_sub_le p₁ p₂
  linarith

/-- Every separated pair of sibling pairs in the unit ball has strictly negative weighted score. -/
theorem weightedPairScore_le_of_separated {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1)
    (hw₁ : ‖w₁‖ ≤ 1) (hw₂ : ‖w₂‖ ≤ 1)
    (hpsep : barC ≤ ‖p₁ - p₂‖) (hwsep : barC ≤ ‖w₁ - w₂‖) :
    weightedPairScore e barC gramLambda gramMu p₁ p₂ w₁ w₂ ≤ -(1 / 2000) := by
  obtain ⟨hpLow, hpHigh⟩ := second_radius_mem hp₁ hp₂ hpsep
  obtain ⟨hwLow, hwHigh⟩ := second_radius_mem hw₁ hw₂ hwsep
  obtain ⟨k, hk₀, hk₁⟩ := exists_band ‖p₂‖ hpLow hpHigh
  obtain ⟨l, hl₀, hl₁⟩ := exists_band ‖w₂‖ hwLow hwHigh
  have hcontains := bandCertificate_contains k l
  set certificate := gramCertificates (bandCertificate k l) with hcert
  have hvalid : certificate.Valid := gramCertificates_valid _
  by_cases hswap : bandSwapped k l = true
  · rw [if_pos hswap] at hcontains
    obtain ⟨hpL, hpU, hwL, hwU⟩ := hcontains
    rw [weightedPairScore_swap]
    refine weightedPairScore_le_of_gramCertificate certificate hvalid e w₁ w₂ p₁ p₂ he
      hw₁ hp₁ hwsep hpsep ?_ ?_ ?_ ?_
    · exact le_trans (by exact_mod_cast hpL) hl₀
    · exact le_trans hl₁ (by exact_mod_cast hpU)
    · exact le_trans (by exact_mod_cast hwL) hk₀
    · exact le_trans hk₁ (by exact_mod_cast hwU)
  · rw [if_neg hswap] at hcontains
    obtain ⟨hpL, hpU, hwL, hwU⟩ := hcontains
    refine weightedPairScore_le_of_gramCertificate certificate hvalid e p₁ p₂ w₁ w₂ he
      hp₁ hw₁ hpsep hwsep ?_ ?_ ?_ ?_
    · exact le_trans (by exact_mod_cast hpL) hk₀
    · exact le_trans hk₁ (by exact_mod_cast hpU)
    · exact le_trans (by exact_mod_cast hwL) hl₀
    · exact le_trans hl₁ (by exact_mod_cast hwU)

/-- The Gram certificates prove the weighted geometric bound at the small rational weights. -/
theorem weightedGeometricBound_gram : WeightedGeometricBound gramLambda gramMu := by
  intro e p₁ p₂ w₁ w₂ he hp₁ hp₂ hw₁ hw₂ hpChord hwChord
  have := weightedPairScore_le_of_separated e p₁ p₂ w₁ w₂ he hp₁ hp₂ hw₁ hw₂ hpChord
    hwChord
  linarith

end LeanPool.Besicovitch
