/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.CardinalMass
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.ShiftPartition
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Ingredients

/-! The smooth, compactly supported part of the small time partition. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Cutoff

/-- Width of the transition zone, chosen from the cardinal step's quadratic mass. -/
def zetaWidth : ℝ := (20 * cardinalMass)⁻¹

/-- Radius of the region on which the small cutoff is identically one. -/
def zetaCoreRadius : ℝ := (1 - zetaWidth) / 2

/-- Outer radius of the small cutoff's support. -/
def zetaOuterRadius : ℝ := zetaCoreRadius + zetaWidth

theorem zetaWidth_pos : 0 < zetaWidth := by
  unfold zetaWidth
  exact inv_pos.mpr (mul_pos (by norm_num) cardinalMass_pos)

theorem zetaWidth_le_one_third : zetaWidth ≤ 1 / 3 := by
  have hmass := cardinalMass_lower
  have hlarge : 3 ≤ 20 * cardinalMass := by nlinarith
  unfold zetaWidth
  simpa [one_div] using one_div_le_one_div_of_le (by norm_num) hlarge

theorem zetaWidth_lt_one : zetaWidth < 1 := by
  have h := zetaWidth_le_one_third
  linarith

theorem zetaCoreRadius_pos : 0 < zetaCoreRadius := by
  unfold zetaCoreRadius
  linarith [zetaWidth_lt_one]

theorem zetaCoreRadius_add_width : zetaCoreRadius + zetaWidth = 1 - zetaCoreRadius := by
  unfold zetaCoreRadius
  ring

theorem zetaOuterRadius_sub_coreRadius :
    zetaOuterRadius - zetaCoreRadius = zetaWidth := by
  unfold zetaOuterRadius
  ring

theorem zetaSupportRadius_le : zetaCoreRadius + zetaWidth ≤ 2 / 3 := by
  unfold zetaCoreRadius
  have hw := zetaWidth_le_one_third
  nlinarith

theorem zetaOuterRadius_le_one : zetaOuterRadius ≤ 1 := by
  unfold zetaOuterRadius
  linarith [zetaSupportRadius_le]

/-- The small time cutoff. Its transition profile is the flatter cardinal smooth step. -/
def cardinalZeta (t : ℝ) : ℝ :=
  cardinalStep ((t + zetaOuterRadius) / zetaWidth) *
    cardinalStep ((zetaOuterRadius - t) / zetaWidth)

@[fun_prop]
theorem cardinalZeta_contDiff : ContDiff ℝ (⊤ : ℕ∞) cardinalZeta := by
  unfold cardinalZeta
  fun_prop

theorem cardinalZeta_nonneg (t : ℝ) : 0 ≤ cardinalZeta t := by
  unfold cardinalZeta
  exact mul_nonneg (step_nonneg _) (step_nonneg _)

theorem cardinalZeta_le_one (t : ℝ) : cardinalZeta t ≤ 1 := by
  unfold cardinalZeta
  have ha := (show cardinalStep ((t + zetaOuterRadius) / zetaWidth) ≤ 1 from step_le_one _)
  have hb0 := (show 0 ≤ cardinalStep ((zetaOuterRadius - t) / zetaWidth) from step_nonneg _)
  have hb := (show cardinalStep ((zetaOuterRadius - t) / zetaWidth) ≤ 1 from step_le_one _)
  calc
    cardinalStep ((t + zetaOuterRadius) / zetaWidth) *
        cardinalStep ((zetaOuterRadius - t) / zetaWidth)
      ≤ 1 * cardinalStep ((zetaOuterRadius - t) / zetaWidth) :=
        mul_le_mul_of_nonneg_right ha hb0
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = 1 := by norm_num

theorem cardinalZeta_eq_one {t : ℝ} (ht₁ : -zetaCoreRadius ≤ t)
    (ht₂ : t ≤ zetaCoreRadius) : cardinalZeta t = 1 := by
  unfold cardinalZeta
  have hgap := zetaOuterRadius_sub_coreRadius
  rw [cardinalStep_one_of_one_le, cardinalStep_one_of_one_le]
  · norm_num
  · rw [le_div_iff₀ zetaWidth_pos]
    linarith
  · rw [le_div_iff₀ zetaWidth_pos]
    linarith

theorem cardinalZeta_eq_zero_of_le {t : ℝ}
    (ht : t ≤ -zetaOuterRadius) : cardinalZeta t = 0 := by
  unfold cardinalZeta
  have hz : cardinalStep ((t + zetaOuterRadius) / zetaWidth) = 0 :=
    cardinalStep_zero_of_nonpos (by
      rw [div_le_iff₀ zetaWidth_pos]
      linarith)
  rw [hz, zero_mul]

theorem cardinalZeta_eq_zero_of_ge {t : ℝ}
    (ht : zetaOuterRadius ≤ t) : cardinalZeta t = 0 := by
  unfold cardinalZeta
  have hz : cardinalStep ((zetaOuterRadius - t) / zetaWidth) = 0 :=
    cardinalStep_zero_of_nonpos (by
      rw [div_le_iff₀ zetaWidth_pos]
      linarith)
  rw [hz, mul_zero]

theorem cardinalZeta_even (t : ℝ) : cardinalZeta (-t) = cardinalZeta t := by
  unfold cardinalZeta
  have h₁ : (-t + zetaOuterRadius) / zetaWidth =
      (zetaOuterRadius - t) / zetaWidth := by ring
  have h₂ : (zetaOuterRadius - -t) / zetaWidth =
      (t + zetaOuterRadius) / zetaWidth := by ring
  rw [h₁, h₂, mul_comm]

theorem cardinalZeta_le_indIcc (t : ℝ) :
    cardinalZeta t ≤ AVenhance.indIcc (-(2 / 3)) (2 / 3) t := by
  by_cases ht : t ∈ Set.Icc (-(2 / 3 : ℝ)) (2 / 3)
  · simp only [indIcc, ht, Set.indicator_of_mem]
    exact cardinalZeta_le_one t
  · have hzero : cardinalZeta t = 0 := by
      have ht' : ¬ (-(2 / 3 : ℝ) ≤ t ∧ t ≤ 2 / 3) := by simpa [Set.mem_Icc] using ht
      rcases not_and_or.mp ht' with h | h
      · apply cardinalZeta_eq_zero_of_le
        have hs : zetaOuterRadius ≤ 2 / 3 := by
          simpa [zetaOuterRadius] using zetaSupportRadius_le
        linarith
      · apply cardinalZeta_eq_zero_of_ge
        have hs : zetaOuterRadius ≤ 2 / 3 := by
          simpa [zetaOuterRadius] using zetaSupportRadius_le
        linarith
    simp [AVenhance.indIcc, ht, hzero]

theorem cardinalZeta_compact : HasCompactSupport cardinalZeta := by
  have hcompact : IsCompact (Set.Icc (-(2 / 3 : ℝ)) (2 / 3)) := isCompact_Icc
  apply HasCompactSupport.of_support_subset_isCompact hcompact
  intro t ht
  have hs : zetaOuterRadius ≤ 2 / 3 := by
    simpa [zetaOuterRadius] using zetaSupportRadius_le
  have hne : cardinalZeta t ≠ 0 := by simpa [Function.mem_support] using ht
  constructor
  · by_contra hleft
    have htl : t < -(2 / 3 : ℝ) := lt_of_not_ge hleft
    have hbound : -(2 / 3 : ℝ) ≤ -zetaOuterRadius := by linarith
    have hz := cardinalZeta_eq_zero_of_le (t := t) (by
      exact htl.le.trans hbound)
    exact hne hz
  · by_contra hright
    have htr : (2 / 3 : ℝ) < t := lt_of_not_ge hright
    have hz := cardinalZeta_eq_zero_of_ge (t := t) (by
      exact le_trans hs htr.le)
    exact hne hz

theorem cardinalZeta_deriv_bound (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j : ℕ, j ≤ N → ∀ t : ℝ,
      |iteratedDeriv j cardinalZeta t| ≤ C :=
  exists_iteratedDeriv_bound cardinalZeta_contDiff cardinalZeta_compact N

theorem cardinalZeta_eq_cellCutoff (t : ℝ) :
    cardinalZeta t = cellCutoff cardinalStep 1 (zetaWidth / 2) t := by
  unfold cardinalZeta cellCutoff zetaOuterRadius zetaCoreRadius
  have hw : zetaWidth ≠ 0 := ne_of_gt zetaWidth_pos
  field_simp [hw]
  ring_nf

theorem cardinalZeta_partition (t : ℝ) :
    ∑' k : ℤ, cardinalZeta (t - k) = 1 := by
  simp_rw [cardinalZeta_eq_cellCutoff]
  have hwidth := zetaWidth_le_one_third
  have hpartition := cellCutoff_lattice_partition
    (s := cardinalStep) (period := (1 : ℝ)) (margin := zetaWidth / 2) (t := t)
    (by norm_num) (div_pos zetaWidth_pos (by norm_num)) (by nlinarith)
    (fun y hy => cardinalStep_zero_of_nonpos hy)
    (fun y hy => cardinalStep_one_of_one_le hy)
    cardinalStep_one_sub
  simpa using hpartition

end AVenhance.Infra.Cutoff
