/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ChoiceCountSystem
/-!
# Explicit counts for basic-factor choices

This module solves the coordinate-count system and relates its solution to the
label-count and multinomial choice spaces.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

/--
Establishes the identity `q + formalLogOnePlusProductArgumentMixedChoiceCount q l = e (0 : Fin 2)
+ e (1 : Fin 2)`.
-/
theorem formalLogOnePlusProductArgument_choiceCounts_total_add_mixed_eq_coord_sum
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    q + formalLogOnePlusProductArgumentMixedChoiceCount q l =
      e (0 : Fin 2) + e (1 : Fin 2) := by
  rcases formalLogOnePlusProductArgument_choiceCounts_system
      hl hbasic with ⟨hleft, hright, htotal⟩
  calc
    q + formalLogOnePlusProductArgumentMixedChoiceCount q l =
        (formalLogOnePlusProductArgumentLeftChoiceCount q l +
            formalLogOnePlusProductArgumentRightChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l) +
            formalLogOnePlusProductArgumentMixedChoiceCount q l := by
      exact (congrArg
        (fun t : ℕ => t + formalLogOnePlusProductArgumentMixedChoiceCount q l)
        htotal).symm
    _ =
        (formalLogOnePlusProductArgumentLeftChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l) +
        (formalLogOnePlusProductArgumentRightChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l) := by
      simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    _ = e (0 : Fin 2) + e (1 : Fin 2) := by
      rw [hleft, hright]

/-- Proves the bound `q ≤ e (0 : Fin 2) + e (1 : Fin 2)`. -/
theorem formalLogOnePlusProductArgument_choiceCounts_q_le_coord_sum
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    q ≤ e (0 : Fin 2) + e (1 : Fin 2) := by
  have hsum :=
    formalLogOnePlusProductArgument_choiceCounts_total_add_mixed_eq_coord_sum
      hl hbasic
  exact Nat.le.intro hsum

/--
Establishes the identity `formalLogOnePlusProductArgumentMixedChoiceCount q l = e (0 : Fin 2) + e
(1 : Fin 2) - q`.
-/
theorem formalLogOnePlusProductArgument_mixedChoiceCount_eq_coord_sum_sub_q
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    formalLogOnePlusProductArgumentMixedChoiceCount q l =
      e (0 : Fin 2) + e (1 : Fin 2) - q := by
  have hsum :=
    formalLogOnePlusProductArgument_choiceCounts_total_add_mixed_eq_coord_sum
      hl hbasic
  calc
    formalLogOnePlusProductArgumentMixedChoiceCount q l =
        q + formalLogOnePlusProductArgumentMixedChoiceCount q l - q := by
      rw [Nat.add_sub_cancel_left]
    _ = e (0 : Fin 2) + e (1 : Fin 2) - q := by
      rw [hsum]

/--
Establishes the identity `formalLogOnePlusProductArgumentLeftChoiceCount q l = q - e (1 : Fin 2)`.
-/
theorem formalLogOnePlusProductArgument_leftChoiceCount_eq_q_sub_right_coord
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    formalLogOnePlusProductArgumentLeftChoiceCount q l =
      q - e (1 : Fin 2) := by
  rcases formalLogOnePlusProductArgument_choiceCounts_system
      hl hbasic with ⟨_hleft, hright, htotal⟩
  have hq :
      e (1 : Fin 2) +
          formalLogOnePlusProductArgumentLeftChoiceCount q l =
        q := by
    calc
      e (1 : Fin 2) +
          formalLogOnePlusProductArgumentLeftChoiceCount q l =
        (formalLogOnePlusProductArgumentRightChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l) +
            formalLogOnePlusProductArgumentLeftChoiceCount q l := by
        rw [hright]
      _ =
        formalLogOnePlusProductArgumentLeftChoiceCount q l +
            formalLogOnePlusProductArgumentRightChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l := by
        simp only [Nat.add_left_comm, Nat.add_comm]
      _ = q := htotal
  calc
    formalLogOnePlusProductArgumentLeftChoiceCount q l =
        e (1 : Fin 2) +
            formalLogOnePlusProductArgumentLeftChoiceCount q l -
          e (1 : Fin 2) := by
      rw [Nat.add_sub_cancel_left]
    _ = q - e (1 : Fin 2) := by
      rw [hq]

/--
Establishes the identity `formalLogOnePlusProductArgumentRightChoiceCount q l = q - e (0 : Fin
2)`.
-/
theorem formalLogOnePlusProductArgument_rightChoiceCount_eq_q_sub_left_coord
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    formalLogOnePlusProductArgumentRightChoiceCount q l =
      q - e (0 : Fin 2) := by
  rcases formalLogOnePlusProductArgument_choiceCounts_system
      hl hbasic with ⟨hleft, _hright, htotal⟩
  have hq :
      e (0 : Fin 2) +
          formalLogOnePlusProductArgumentRightChoiceCount q l =
        q := by
    calc
      e (0 : Fin 2) +
          formalLogOnePlusProductArgumentRightChoiceCount q l =
        (formalLogOnePlusProductArgumentLeftChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l) +
            formalLogOnePlusProductArgumentRightChoiceCount q l := by
        rw [hleft]
      _ =
        formalLogOnePlusProductArgumentLeftChoiceCount q l +
            formalLogOnePlusProductArgumentRightChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l := by
        simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      _ = q := htotal
  calc
    formalLogOnePlusProductArgumentRightChoiceCount q l =
        e (0 : Fin 2) +
            formalLogOnePlusProductArgumentRightChoiceCount q l -
          e (0 : Fin 2) := by
      rw [Nat.add_sub_cancel_left]
    _ = q - e (0 : Fin 2) := by
      rw [hq]

/--
Establishes the identity `formalLogOnePlusProductArgumentLeftChoiceCount q l = q - e (1 : Fin 2) ∧
formalLogOnePlusProductArgumentRightChoiceCount q l = q - e (0 : Fin 2) ∧
formalLogOnePlusProductArgumentMixedChoiceCount q l = e (0 : Fin 2) + e (1 : Fin 2) - q`.
-/
theorem formalLogOnePlusProductArgument_choiceCounts_explicit
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    formalLogOnePlusProductArgumentLeftChoiceCount q l =
          q - e (1 : Fin 2) ∧
      formalLogOnePlusProductArgumentRightChoiceCount q l =
          q - e (0 : Fin 2) ∧
        formalLogOnePlusProductArgumentMixedChoiceCount q l =
          e (0 : Fin 2) + e (1 : Fin 2) - q := by
  exact
    ⟨formalLogOnePlusProductArgument_leftChoiceCount_eq_q_sub_right_coord
        hl hbasic,
      formalLogOnePlusProductArgument_rightChoiceCount_eq_q_sub_left_coord
        hl hbasic,
      formalLogOnePlusProductArgument_mixedChoiceCount_eq_coord_sum_sub_q
        hl hbasic⟩

/--
Establishes the identity `formalLogOnePlusProductArgumentBasicFactorLabelCount q l 0 = q - e (1 :
Fin 2) ∧ formalLogOnePlusProductArgumentBasicFactorLabelCount q l 1 = q - e (0 : Fin 2) ∧
formalLogOnePlusProductArgumentBasicFactorLabelCount q l 2 = e (0 : Fin 2) + e (1 : Fin 2) - q`.
-/
theorem formalLogOnePlusProductArgument_labelCounts_explicit
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    formalLogOnePlusProductArgumentBasicFactorLabelCount q l 0 =
          q - e (1 : Fin 2) ∧
      formalLogOnePlusProductArgumentBasicFactorLabelCount q l 1 =
          q - e (0 : Fin 2) ∧
        formalLogOnePlusProductArgumentBasicFactorLabelCount q l 2 =
          e (0 : Fin 2) + e (1 : Fin 2) - q := by
  rcases formalLogOnePlusProductArgument_choiceCounts_explicit
      hl hbasic with ⟨hleft, hright, hmixed⟩
  exact
    ⟨by
      rw [← formalLogOnePlusProductArgument_leftChoiceCount_eq_labelCount_zero]
      exact hleft,
    by
      rw [← formalLogOnePlusProductArgument_rightChoiceCount_eq_labelCount_one]
      exact hright,
    by
      rw [←
        formalLogOnePlusProductArgument_mixedChoiceCount_eq_labelCount_two
          hbasic]
      exact hmixed⟩

/--
Establishes the identity `formalLogOnePlusProductArgumentBasicFactorLabelCount q l 0 = q - e (1 :
Fin 2) ∧ formalLogOnePlusProductArgumentBasicFactorLabelCount q l 1 = q - e (0 : Fin 2) ∧
formalLogOnePlusProductArgumentBasicFactorLabelCount q l 2 = e (0 : Fin 2) + e (1 : Fin 2) - q`.
-/
theorem formalLogOnePlusProductArgumentBasicFactorChoices_labelCounts_explicit
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ formalLogOnePlusProductArgumentBasicFactorChoices q e) :
    formalLogOnePlusProductArgumentBasicFactorLabelCount q l 0 =
          q - e (1 : Fin 2) ∧
      formalLogOnePlusProductArgumentBasicFactorLabelCount q l 1 =
          q - e (0 : Fin 2) ∧
        formalLogOnePlusProductArgumentBasicFactorLabelCount q l 2 =
          e (0 : Fin 2) + e (1 : Fin 2) - q := by
  rw [mem_formalLogOnePlusProductArgumentBasicFactorChoices] at hl
  exact formalLogOnePlusProductArgument_labelCounts_explicit hl.1 hl.2

/-- Every basic-factor choice satisfies the corresponding three label-count constraints. -/
theorem formalLogOnePlusProductArgumentBasicFactorChoices_subset_labelCountChoices
    (q : ℕ) (e : Fin 2 →₀ ℕ) :
    formalLogOnePlusProductArgumentBasicFactorChoices q e ⊆
      formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e := by
  intro l hl
  rw [mem_formalLogOnePlusProductArgumentBasicFactorLabelCountChoices]
  rw [mem_formalLogOnePlusProductArgumentBasicFactorChoices] at hl
  have hprod :
      l ∈ formalLogOnePlusProductArgumentBasicFactorProductChoices q := by
    rw [mem_formalLogOnePlusProductArgumentBasicFactorProductChoices]
    exact ⟨(Finset.mem_finsuppAntidiag.mp hl.1).2, hl.2⟩
  exact
    ⟨hprod,
      formalLogOnePlusProductArgument_labelCounts_explicit hl.1 hl.2⟩

/--
Proves the bound `(formalLogOnePlusProductArgumentBasicFactorChoices q e).card ≤
(formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e).card`.
-/
theorem formalLogOnePlusProductArgumentBasicFactorChoices_card_le_labelCountChoices
    (q : ℕ) (e : Fin 2 →₀ ℕ) :
    (formalLogOnePlusProductArgumentBasicFactorChoices q e).card ≤
      (formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e).card :=
  Finset.card_le_card
    (formalLogOnePlusProductArgumentBasicFactorChoices_subset_labelCountChoices
      q e)


end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
