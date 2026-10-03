/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.CardinalZeta
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.ShiftPartition
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.TimeScaleFacts
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.IndIcc

/-! The unit-scale cutoff with a partition on odd integer translates. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Cutoff

/-- Cardinal cutoff profile with period two and transition margin one quarter. -/
def cardinalXi (t : ℝ) : ℝ := cellCutoff cardinalStep 2 (1 / 4) t

theorem cardinalXi_contDiff : ContDiff ℝ (⊤ : ℕ∞) cardinalXi := by
  unfold cardinalXi cellCutoff
  fun_prop

theorem cardinalXi_nonneg (t : ℝ) : 0 ≤ cardinalXi t := by
  unfold cardinalXi cellCutoff
  exact mul_nonneg (step_nonneg _) (step_nonneg _)

theorem cardinalXi_le_one (t : ℝ) : cardinalXi t ≤ 1 := by
  change cardinalStep ((t + 2 / 2 + 1 / 4) / (2 * (1 / 4))) *
    cardinalStep ((2 / 2 + 1 / 4 - t) / (2 * (1 / 4))) ≤ 1
  have h₁ : cardinalStep ((t + 2 / 2 + 1 / 4) / (2 * (1 / 4))) ≤ 1 := by
    unfold cardinalStep
    exact step_le_one _
  have h₂0 : 0 ≤ cardinalStep ((2 / 2 + 1 / 4 - t) / (2 * (1 / 4))) := by
    unfold cardinalStep
    exact step_nonneg _
  have h₂ : cardinalStep ((2 / 2 + 1 / 4 - t) / (2 * (1 / 4))) ≤ 1 := by
    unfold cardinalStep
    exact step_le_one _
  calc
    _ ≤ 1 * cardinalStep ((2 / 2 + 1 / 4 - t) / (2 * (1 / 4))) :=
      mul_le_mul_of_nonneg_right h₁ h₂0
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left h₂ (by norm_num)
    _ = 1 := by norm_num

theorem cardinalXi_eq_one {t : ℝ} (ht₁ : -3 / 4 ≤ t) (ht₂ : t ≤ 3 / 4) :
    cardinalXi t = 1 := by
  unfold cardinalXi
  have h := cellCutoff_one_on_core
    (s := cardinalStep) (period := (2 : ℝ)) (margin := 1 / 4) (x := t)
    (by norm_num) (fun y hy => cardinalStep_one_of_one_le hy)
    (by norm_num at ht₁ ⊢; linarith) (by norm_num at ht₂ ⊢; linarith)
  exact h

theorem cardinalXi_eq_zero_of_le {t : ℝ} (ht : t ≤ -(5 / 4)) : cardinalXi t = 0 := by
  unfold cardinalXi
  apply cellCutoff_zero_of_le (by norm_num) (fun y hy => cardinalStep_zero_of_nonpos hy)
  norm_num at ht ⊢
  linarith

theorem cardinalXi_eq_zero_of_ge {t : ℝ} (ht : 5 / 4 ≤ t) : cardinalXi t = 0 := by
  unfold cardinalXi
  apply cellCutoff_zero_of_ge (by norm_num) (fun y hy => cardinalStep_zero_of_nonpos hy)
  norm_num at ht ⊢
  linarith

theorem cardinalXi_le_indIcc (t : ℝ) :
    cardinalXi t ≤ AVenhance.indIcc (-(5 / 4)) (5 / 4) t := by
  by_cases ht : t ∈ Set.Icc (-(5 / 4 : ℝ)) (5 / 4)
  · simp only [indIcc, ht, Set.indicator_of_mem]
    exact cardinalXi_le_one t
  · have ht' : t < -(5 / 4 : ℝ) ∨ (5 / 4 : ℝ) < t := by
      have hmem : ¬ (-(5 / 4 : ℝ) ≤ t ∧ t ≤ 5 / 4) := by
        simpa [Set.mem_Icc] using ht
      rcases not_and_or.mp hmem with h | h
      · exact Or.inl (lt_of_not_ge h)
      · exact Or.inr (lt_of_not_ge h)
    rcases ht' with hleft | hright
    · have hz := cardinalXi_eq_zero_of_le hleft.le
      simp [AVenhance.indIcc, ht, hz]
    · have hz := cardinalXi_eq_zero_of_ge hright.le
      simp [AVenhance.indIcc, ht, hz]

theorem cardinalXi_ind_le (t : ℝ) :
    AVenhance.indIcc (-(3 / 4)) (3 / 4) t ≤ cardinalXi t := by
  by_cases ht : t ∈ Set.Icc (-(3 / 4 : ℝ)) (3 / 4)
  · have hlo : -3 / 4 ≤ t := by
      have h := ht.1
      norm_num at h ⊢
      exact h
    have hhi : t ≤ 3 / 4 := by
      have h := ht.2
      norm_num at h ⊢
      exact h
    simp [AVenhance.indIcc, ht, cardinalXi_eq_one hlo hhi]
  · simp only [indIcc, ht, not_false_eq_true, Set.indicator_of_notMem]
    exact cardinalXi_nonneg t

theorem cardinalXi_compact : HasCompactSupport cardinalXi := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-(5 / 4 : ℝ)) (5 / 4)) isCompact_Icc
  intro t ht
  have hne : cardinalXi t ≠ 0 := by simpa [Function.mem_support] using ht
  constructor
  · by_contra hleft
    have hz := cardinalXi_eq_zero_of_le (t := t) (by linarith)
    exact hne hz
  · by_contra hright
    have hz := cardinalXi_eq_zero_of_ge (t := t) (by linarith)
    exact hne hz

theorem cardinalXi_deriv_bound (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j : ℕ, j ≤ N → ∀ t : ℝ,
      |iteratedDeriv j cardinalXi t| ≤ C :=
  exists_iteratedDeriv_bound cardinalXi_contDiff cardinalXi_compact N

/-- Enumerate the odd integers by the map sending an integer to twice it plus one. -/
def BaseCutoffs.oddIntEquiv : ℤ ≃ {k : ℤ // Odd k} where
  toFun n := ⟨2 * n + 1, ⟨n, by ring⟩⟩
  invFun k := (k.val - 1) / 2
  left_inv n := by dsimp; omega
  right_inv k := by
    obtain ⟨n, hn⟩ := k.property
    apply Subtype.ext
    dsimp
    rw [hn]
    omega

theorem cardinalXi_partition (t : ℝ) :
    ∑' k : {k : ℤ // Odd k}, cardinalXi (t - (k : ℤ)) = 1 := by
  rw [← BaseCutoffs.oddIntEquiv.tsum_eq]
  have hterms (n : ℤ) :
      cardinalXi (t - ((BaseCutoffs.oddIntEquiv n).val : ℝ)) =
        cellCutoff cardinalStep 2 (1 / 4) ((t - 1) - (n : ℝ) * 2) := by
    change cellCutoff cardinalStep 2 (1 / 4)
      (t - ((BaseCutoffs.oddIntEquiv n).val : ℝ)) = _
    have hcast : ((BaseCutoffs.oddIntEquiv n).val : ℝ) = 2 * (n : ℝ) + 1 := by
      simp [BaseCutoffs.oddIntEquiv]
    rw [hcast]
    congr 1
    ring
  simp_rw [hterms]
  exact cellCutoff_lattice_partition
    (s := cardinalStep) (period := 2) (margin := 1 / 4) (t := t - 1)
    (by norm_num) (by norm_num) (by norm_num)
    (fun y hy => cardinalStep_zero_of_nonpos hy)
    (fun y hy => cardinalStep_one_of_one_le hy)
    cardinalStep_one_sub

end AVenhance.Infra.Cutoff
