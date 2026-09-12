/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.EndpointGeometry
import Mathlib.Topology.Order.IntermediateValue

/-!
# Radial reduction for the weighted six-point inequality

This file records the exact weighted score and proves that its two second children may be
moved inward until both sibling distances equal the endpoint chord length.
-/

@[expose] public section

noncomputable section

open Set

namespace LeanPool.Besicovitch

/-- The coefficient penalizing the first child radii in the weighted score. -/
def weightedFirstPenalty (c lambda mu : ℝ) : ℝ :=
  (c - 1) * (lambda / 2 + mu)

/-- The coefficient penalizing the second child radii in the weighted score. -/
def weightedSecondPenalty (c lambda mu : ℝ) : ℝ :=
  (c + 1) * lambda / 2 + 3 * c * mu

/-- The constant term in the weighted combination of the three failure slacks. -/
def weightedConstantTerm (c lambda mu : ℝ) : ℝ :=
  2 * c * (2 * c - 1) + lambda * (3 * c ^ 2 - 3 * c + 2) / 2 +
    mu * (c ^ 2 - c)

/-- The weighted failure score for two ordered sibling pairs relative to a unit root vector. -/
def weightedPairScore {E : Type*} [NormedAddCommGroup E]
    (e : E) (c lambda mu : ℝ) (p₁ p₂ w₁ w₂ : E) : ℝ :=
  (1 + lambda) * ‖e - p₁ - w₁‖ + ‖e - p₂ - w₂‖ +
    mu / 2 * (‖e - p₁‖ + ‖e - w₁‖ + ‖e - p₁ - w₂‖ + ‖e - w₁ - p₂‖) -
    weightedFirstPenalty c lambda mu / 2 * (‖p₁‖ + ‖w₁‖) -
    weightedSecondPenalty c lambda mu / 2 * (‖p₂‖ + ‖w₂‖) -
    weightedConstantTerm c lambda mu

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Scaling a point inward reaches every intermediate distance from another point. -/
theorem exists_norm_sub_smul_eq {p q : E} {c : ℝ} (hp : ‖p‖ < c)
    (hpq : c ≤ ‖p - q‖) :
    ∃ a ∈ Icc (0 : ℝ) 1, ‖p - a • q‖ = c := by
  let f : ℝ → ℝ := fun a ↦ ‖p - a • q‖
  have hf : Continuous f := continuous_norm.comp
    (continuous_const.sub (continuous_id.smul continuous_const))
  have hc_mem : c ∈ Icc (f 0) (f 1) := by
    simpa [f] using ⟨hp.le, hpq⟩
  obtain ⟨a, ha, hfa⟩ :=
    intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hf.continuousOn hc_mem
  exact ⟨a, ha, hfa⟩

private theorem norm_eq_norm_smul_add_norm_sub_smul {q : E} {a : ℝ}
    (ha_zero : 0 ≤ a) (ha_one : a ≤ 1) :
    ‖q‖ = ‖a • q‖ + ‖q - a • q‖ := by
  have h_one_sub : 0 ≤ 1 - a := sub_nonneg.mpr ha_one
  have hq : q - a • q = (1 - a) • q := by module
  rw [hq, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ha_zero, abs_of_nonneg h_one_sub]
  ring

private theorem norm_replace_by_smul_le (x q : E) {a : ℝ}
    (ha_zero : 0 ≤ a) (ha_one : a ≤ 1) :
    ‖x - q‖ ≤ ‖x - a • q‖ + (‖q‖ - ‖a • q‖) := by
  have h := norm_le_norm_add_norm_sub' (x - q) (x - a • q)
  have hdiff : (x - q) - (x - a • q) = -(q - a • q) := by abel
  rw [hdiff, norm_neg] at h
  have hnorm := norm_eq_norm_smul_add_norm_sub_smul (q := q) ha_zero ha_one
  linarith

/-- Moving the second child of the first pair inward cannot decrease the weighted score. -/
theorem weightedPairScore_le_smul_second_left (e : E) (c lambda mu : ℝ)
    (p₁ p₂ w₁ w₂ : E) {a : ℝ} (ha_zero : 0 ≤ a) (ha_one : a ≤ 1)
    (hmu : 0 ≤ mu) (hpenalty : 2 + mu ≤ weightedSecondPenalty c lambda mu) :
    weightedPairScore e c lambda mu p₁ p₂ w₁ w₂ ≤
      weightedPairScore e c lambda mu p₁ (a • p₂) w₁ w₂ := by
  have hnorm := norm_eq_norm_smul_add_norm_sub_smul (q := p₂) ha_zero ha_one
  have hdifference : 0 ≤ ‖p₂‖ - ‖a • p₂‖ := by
    rw [hnorm]
    simp
  have hfirst := norm_replace_by_smul_le (e - w₂) p₂ ha_zero ha_one
  have hsecond := norm_replace_by_smul_le (e - w₁) p₂ ha_zero ha_one
  have hsecond' :
      mu / 2 * ‖e - w₁ - p₂‖ ≤
        mu / 2 * ‖e - w₁ - a • p₂‖ + mu / 2 * (‖p₂‖ - ‖a • p₂‖) := by
    calc
      _ ≤ mu / 2 * (‖e - w₁ - a • p₂‖ +
          (‖p₂‖ - ‖a • p₂‖)) :=
        mul_le_mul_of_nonneg_left hsecond (div_nonneg hmu (by norm_num))
      _ = _ := by ring
  have hmargin := mul_nonneg (sub_nonneg.mpr hpenalty) hdifference
  simp only [weightedPairScore, weightedFirstPenalty, weightedSecondPenalty,
    weightedConstantTerm]
  dsimp only [weightedSecondPenalty] at hmargin
  rw [show e - p₂ - w₂ = (e - w₂) - p₂ by abel,
    show e - a • p₂ - w₂ = (e - w₂) - a • p₂ by abel,
    show e - w₁ - p₂ = (e - w₁) - p₂ by abel,
    show e - w₁ - a • p₂ = (e - w₁) - a • p₂ by abel]
  nlinarith

omit [NormedSpace ℝ E] in
/-- The weighted score is symmetric in its two sibling pairs. -/
theorem weightedPairScore_swap (e : E) (c lambda mu : ℝ) (p₁ p₂ w₁ w₂ : E) :
    weightedPairScore e c lambda mu p₁ p₂ w₁ w₂ =
      weightedPairScore e c lambda mu w₁ w₂ p₁ p₂ := by
  simp only [weightedPairScore]
  rw [show ‖e - p₁ - w₁‖ = ‖e - w₁ - p₁‖ by
      congr 1
      abel,
    show ‖e - p₂ - w₂‖ = ‖e - w₂ - p₂‖ by
      congr 1
      abel]
  ring

/-- Moving the second child of the second pair inward cannot decrease the weighted score. -/
theorem weightedPairScore_le_smul_second_right (e : E) (c lambda mu : ℝ)
    (p₁ p₂ w₁ w₂ : E) {a : ℝ} (ha_zero : 0 ≤ a) (ha_one : a ≤ 1)
    (hmu : 0 ≤ mu) (hpenalty : 2 + mu ≤ weightedSecondPenalty c lambda mu) :
    weightedPairScore e c lambda mu p₁ p₂ w₁ w₂ ≤
      weightedPairScore e c lambda mu p₁ p₂ w₁ (a • w₂) := by
  rw [weightedPairScore_swap e c lambda mu p₁ p₂ w₁ w₂,
    weightedPairScore_swap e c lambda mu p₁ p₂ w₁ (a • w₂)]
  exact weightedPairScore_le_smul_second_left e c lambda mu w₁ w₂ p₁ p₂
    ha_zero ha_one hmu hpenalty

/-- Both sibling pairs reduce to endpoint-length chords without lowering the weighted score. -/
theorem exists_weightedPairScore_chord_reduction (e : E) {c lambda mu : ℝ}
    {p₁ p₂ w₁ w₂ : E} (hc : 1 < c)
    (hp₁ : ‖p₁‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hp : c ≤ ‖p₁ - p₂‖) (hw : c ≤ ‖w₁ - w₂‖)
    (hmu : 0 ≤ mu) (hpenalty : 2 + mu ≤ weightedSecondPenalty c lambda mu) :
    ∃ p₂' w₂' : E,
      ‖p₁ - p₂'‖ = c ∧ ‖w₁ - w₂'‖ = c ∧
      ‖p₂'‖ ≤ ‖p₂‖ ∧ ‖w₂'‖ ≤ ‖w₂‖ ∧
      weightedPairScore e c lambda mu p₁ p₂ w₁ w₂ ≤
        weightedPairScore e c lambda mu p₁ p₂' w₁ w₂' := by
  obtain ⟨a, ⟨ha_zero, ha_one⟩, ha⟩ :=
    exists_norm_sub_smul_eq (p := p₁) (q := p₂) (c := c) (hp₁.trans_lt hc) hp
  obtain ⟨b, ⟨hb_zero, hb_one⟩, hb⟩ :=
    exists_norm_sub_smul_eq (p := w₁) (q := w₂) (c := c) (hw₁.trans_lt hc) hw
  refine ⟨a • p₂, b • w₂, ha, hb, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha_zero]
    exact mul_le_of_le_one_left (norm_nonneg _) ha_one
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb_zero]
    exact mul_le_of_le_one_left (norm_nonneg _) hb_one
  · exact (weightedPairScore_le_smul_second_left e c lambda mu p₁ p₂ w₁ w₂
      ha_zero ha_one hmu hpenalty).trans
      (weightedPairScore_le_smul_second_right e c lambda mu p₁ (a • p₂) w₁ w₂
        hb_zero hb_one hmu hpenalty)

end LeanPool.Besicovitch
