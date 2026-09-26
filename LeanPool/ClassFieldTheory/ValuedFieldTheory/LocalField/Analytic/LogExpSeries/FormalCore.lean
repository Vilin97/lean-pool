/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ChoicePositions
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.PowerSeriesComposition
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ProductArgument
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.BasicFactors
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ChoiceCountSystem
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ExplicitChoiceCounts

/-! # Formal Core -/

@[expose] public section
open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology

/-!
# Choice-count combinatorics for the formal logarithm product

This module completes the formal logarithm core by identifying the basic-factor
choices with pairs of finite position sets and evaluating their cardinality.
The formal-series identities and the underlying position calculus live in
`FormalCoreBase`.
-/

noncomputable
section

attribute [local instance] Classical.propDecidable

universe u

open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

/-- Defines `formalLogOnePlusProductArgumentMixedLeftChoices`. -/
noncomputable def formalLogOnePlusProductArgumentMixedLeftChoices
    (q a b : ℕ) : Finset (Σ _ : Finset ℕ, Finset ℕ) :=
  ((Finset.range q).powersetCard (a + b - q)).sigma fun M =>
    ((Finset.range q \ M).powersetCard (q - b))

/--
Establishes the identity `(formalLogOnePlusProductArgumentMixedLeftChoices q a b).card =
Nat.choose q (a + b - q) * Nat.choose (q - (a + b - q)) (q - b)`.
-/
theorem formalLogOnePlusProductArgumentMixedLeftChoices_card
    (q a b : ℕ) :
    (formalLogOnePlusProductArgumentMixedLeftChoices q a b).card =
      Nat.choose q (a + b - q) *
        Nat.choose (q - (a + b - q)) (q - b) := by
  classical
  rw [formalLogOnePlusProductArgumentMixedLeftChoices, Finset.card_sigma]
  calc
    (∑ M ∈ (Finset.range q).powersetCard (a + b - q),
        ((Finset.range q \ M).powersetCard (q - b)).card)
        = ∑ M ∈ (Finset.range q).powersetCard (a + b - q),
            Nat.choose (q - (a + b - q)) (q - b) := by
          apply Finset.sum_congr rfl
          intro M hM
          rw [Finset.card_powersetCard]
          have hsub : M ⊆ Finset.range q :=
            (Finset.mem_powersetCard.mp hM).1
          have hcard : M.card = a + b - q :=
            (Finset.mem_powersetCard.mp hM).2
          rw [Finset.card_sdiff_of_subset hsub, Finset.card_range, hcard]
    _ = Nat.choose q (a + b - q) *
          Nat.choose (q - (a + b - q)) (q - b) := by
          rw [Finset.sum_const]
          simp [Finset.card_powersetCard]

/--
Establishes the membership statement `(⟨formalLogOnePlusProductArgumentMixedPositions q l,
formalLogOnePlusProductArgumentLeftPositions q l⟩ : Σ _ : Finset ℕ, Finset ℕ) ∈
formalLogOnePlusProductArgumentMixedLeftChoices q (e (0 : Fin 2)) (e (1 : Fin 2))`.
-/
theorem formalLogOnePlusProductArgument_toMixedLeft_mem
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl :
      l ∈ formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e) :
    (⟨formalLogOnePlusProductArgumentMixedPositions q l,
        formalLogOnePlusProductArgumentLeftPositions q l⟩ :
      Σ _ : Finset ℕ, Finset ℕ) ∈
      formalLogOnePlusProductArgumentMixedLeftChoices q
        (e (0 : Fin 2)) (e (1 : Fin 2)) := by
  rw [mem_formalLogOnePlusProductArgumentBasicFactorLabelCountChoices] at hl
  rcases hl with ⟨_hprod, hlabel0, _hlabel1, hlabel2⟩
  rw [formalLogOnePlusProductArgumentMixedLeftChoices, Finset.mem_sigma]
  constructor
  · rw [Finset.mem_powersetCard]
    exact
      ⟨fun i hi => (Finset.mem_filter.mp hi).1,
        by
          rw [formalLogOnePlusProductArgumentMixedPositions_card, hlabel2]⟩
  · rw [Finset.mem_powersetCard]
    constructor
    · intro i hi
      rw [Finset.mem_sdiff]
      constructor
      · exact (Finset.mem_filter.mp hi).1
      · intro hmix
        have h0 :
            formalLogOnePlusProductArgumentBasicFactorLabel (l i) =
              (0 : Fin 3) :=
          (Finset.mem_filter.mp hi).2
        have h2 :
            formalLogOnePlusProductArgumentBasicFactorLabel (l i) =
              (2 : Fin 3) :=
          (Finset.mem_filter.mp hmix).2
        omega
    · rw [formalLogOnePlusProductArgumentLeftPositions_card, hlabel0]

/--
Establishes the membership statement `formalLogOnePlusProductArgumentChoiceFromMixedLeft q P.1 P.2
∈ formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e`.
-/
theorem formalLogOnePlusProductArgument_fromMixedLeft_mem
    {q : ℕ} {e : Fin 2 →₀ ℕ}
    {P : Σ _ : Finset ℕ, Finset ℕ}
    (hleft : e (0 : Fin 2) ≤ q) (hright : e (1 : Fin 2) ≤ q)
    (hsum : q ≤ e (0 : Fin 2) + e (1 : Fin 2))
    (hP :
      P ∈ formalLogOnePlusProductArgumentMixedLeftChoices q
        (e (0 : Fin 2)) (e (1 : Fin 2))) :
    formalLogOnePlusProductArgumentChoiceFromMixedLeft q P.1 P.2 ∈
      formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e := by
  rw [formalLogOnePlusProductArgumentMixedLeftChoices, Finset.mem_sigma] at hP
  rcases hP with ⟨hMmem, hLmem⟩
  rw [Finset.mem_powersetCard] at hMmem hLmem
  rcases hMmem with ⟨hMsub, hMcard⟩
  rcases hLmem with ⟨hLsub, hLcard⟩
  rw [mem_formalLogOnePlusProductArgumentBasicFactorLabelCountChoices]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mem_formalLogOnePlusProductArgumentBasicFactorProductChoices]
    refine ⟨?_, ?_⟩
    · exact Finsupp.support_onFinset_subset
    · intro i hi
      by_cases hMi : i ∈ P.1
      · simp [formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem hi,
          hMi, formalLogOnePlusProductArgumentBasicFactorMixed,
          formalLogOnePlusProductArgumentBasicFactor]
      · by_cases hLi : i ∈ P.2
        · simp [formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem hi,
            hMi, hLi, formalLogOnePlusProductArgumentBasicFactorLeft,
            formalLogOnePlusProductArgumentBasicFactor]
        · simp [formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem hi,
            hMi, hLi, formalLogOnePlusProductArgumentBasicFactorRight,
            formalLogOnePlusProductArgumentBasicFactor]
  · rw [← formalLogOnePlusProductArgumentLeftPositions_card,
      formalLogOnePlusProductArgumentLeftPositions_choiceFromMixedLeft hLsub,
      hLcard]
  · rw [← formalLogOnePlusProductArgumentRightPositions_card]
    exact
      formalLogOnePlusProductArgumentRightPositions_choiceFromMixedLeft_card
        hMsub hMcard hLsub hLcard hleft hright hsum
  · rw [← formalLogOnePlusProductArgumentMixedPositions_card,
      formalLogOnePlusProductArgumentMixedPositions_choiceFromMixedLeft hMsub,
      hMcard]

/--
Establishes the identity `formalLogOnePlusProductArgumentChoiceFromMixedLeft q
(formalLogOnePlusProductArgumentMixedPositions q l) (formalLogOnePlusProductArgumentLeftPositions
q l) = l`.
-/
theorem formalLogOnePlusProductArgument_from_to_choice
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl :
      l ∈ formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e) :
    formalLogOnePlusProductArgumentChoiceFromMixedLeft q
      (formalLogOnePlusProductArgumentMixedPositions q l)
      (formalLogOnePlusProductArgumentLeftPositions q l) = l := by
  rw [mem_formalLogOnePlusProductArgumentBasicFactorLabelCountChoices] at hl
  rcases hl with ⟨hprod, _h0, _h1, _h2⟩
  rw [mem_formalLogOnePlusProductArgumentBasicFactorProductChoices] at hprod
  rcases hprod with ⟨hsupp, hbasic⟩
  ext i a
  by_cases hi : i ∈ Finset.range q
  · have hb := hbasic i hi
    by_cases h2 :
        formalLogOnePlusProductArgumentBasicFactorLabel (l i) =
          (2 : Fin 3)
    · have hmixed :
          l i = formalLogOnePlusProductArgumentBasicFactorMixed :=
        (formalLogOnePlusProductArgumentBasicFactorLabel_eq_two_iff_of_basic
          hb).1 h2
      simp [formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem hi,
        formalLogOnePlusProductArgumentMixedPositions,
        formalLogOnePlusProductArgumentLeftPositions, hi, hmixed,
        formalLogOnePlusProductArgumentBasicFactorMixed]
    · by_cases h0 :
        formalLogOnePlusProductArgumentBasicFactorLabel (l i) =
          (0 : Fin 3)
      · have hleft :
            l i = formalLogOnePlusProductArgumentBasicFactorLeft := by
          simpa [formalLogOnePlusProductArgumentBasicFactorLeft] using
            (formalLogOnePlusProductArgumentBasicFactorLabel_eq_zero.1 h0)
        simp [formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem hi,
          formalLogOnePlusProductArgumentMixedPositions,
          formalLogOnePlusProductArgumentLeftPositions, hi, hleft,
          formalLogOnePlusProductArgumentBasicFactorLeft]
      · have h1 :
          formalLogOnePlusProductArgumentBasicFactorLabel (l i) =
            (1 : Fin 3) := by
          generalize hlabel :
            formalLogOnePlusProductArgumentBasicFactorLabel (l i) = j
          fin_cases j
          · exact False.elim (h0 hlabel)
          · rfl
          · exact False.elim (h2 hlabel)
        have hright :
            l i = formalLogOnePlusProductArgumentBasicFactorRight := by
          simpa [formalLogOnePlusProductArgumentBasicFactorRight] using
            (formalLogOnePlusProductArgumentBasicFactorLabel_eq_one.1 h1)
        simp [formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem hi,
          formalLogOnePlusProductArgumentMixedPositions,
          formalLogOnePlusProductArgumentLeftPositions, hi, hright,
          formalLogOnePlusProductArgumentBasicFactorRight]
  · have hli : l i = 0 := by
      exact Finsupp.notMem_support_iff.mp (fun hsup => hi (hsupp hsup))
    simp [formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_not_mem hi,
      hli]

/--
Establishes the identity `(⟨formalLogOnePlusProductArgumentMixedPositions q
(formalLogOnePlusProductArgumentChoiceFromMixedLeft q P.1 P.2),
formalLogOnePlusProductArgumentLeftPositions q (formalLogOnePlusProductArgumentChoiceFromMixedLeft
q P.1 P.2)⟩ : Σ _ : Finset ℕ, Finset ℕ) = P`.
-/
theorem formalLogOnePlusProductArgument_to_from_pair
    {q : ℕ} {e : Fin 2 →₀ ℕ}
    {P : Σ _ : Finset ℕ, Finset ℕ}
    (hP :
      P ∈ formalLogOnePlusProductArgumentMixedLeftChoices q
        (e (0 : Fin 2)) (e (1 : Fin 2))) :
    (⟨formalLogOnePlusProductArgumentMixedPositions q
        (formalLogOnePlusProductArgumentChoiceFromMixedLeft q P.1 P.2),
      formalLogOnePlusProductArgumentLeftPositions q
        (formalLogOnePlusProductArgumentChoiceFromMixedLeft q P.1 P.2)⟩ :
      Σ _ : Finset ℕ, Finset ℕ) = P := by
  rw [formalLogOnePlusProductArgumentMixedLeftChoices, Finset.mem_sigma] at hP
  rcases P with ⟨M, L⟩
  rcases hP with ⟨hMmem, hLmem⟩
  rw [Finset.mem_powersetCard] at hMmem hLmem
  rcases hMmem with ⟨hMsub, _hMcard⟩
  rcases hLmem with ⟨hLsub, _hLcard⟩
  simp [formalLogOnePlusProductArgumentMixedPositions_choiceFromMixedLeft hMsub,
    formalLogOnePlusProductArgumentLeftPositions_choiceFromMixedLeft hLsub]

/--
Establishes the identity `(formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e).card =
(formalLogOnePlusProductArgumentMixedLeftChoices q (e (0 : Fin 2)) (e (1 : Fin 2))).card`.
-/
theorem formalLogOnePlusProductArgumentBasicFactorLabelCountChoices_card_eq_mixedLeftChoices_card
    {q : ℕ} {e : Fin 2 →₀ ℕ}
    (hleft : e (0 : Fin 2) ≤ q) (hright : e (1 : Fin 2) ≤ q)
    (hsum : q ≤ e (0 : Fin 2) + e (1 : Fin 2)) :
    (formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e).card =
      (formalLogOnePlusProductArgumentMixedLeftChoices q
        (e (0 : Fin 2)) (e (1 : Fin 2))).card := by
  refine Finset.card_bij'
    (fun l _ =>
      (⟨formalLogOnePlusProductArgumentMixedPositions q l,
        formalLogOnePlusProductArgumentLeftPositions q l⟩ :
        Σ _ : Finset ℕ, Finset ℕ))
    (fun P _ => formalLogOnePlusProductArgumentChoiceFromMixedLeft q P.1 P.2)
    ?_ ?_ ?_ ?_
  · intro l hl
    exact formalLogOnePlusProductArgument_toMixedLeft_mem hl
  · intro P hP
    exact formalLogOnePlusProductArgument_fromMixedLeft_mem
      hleft hright hsum hP
  · intro l hl
    exact formalLogOnePlusProductArgument_from_to_choice hl
  · intro P hP
    exact formalLogOnePlusProductArgument_to_from_pair hP

/-- Under the coordinate bounds, every label-count choice is a valid basic-factor choice. -/
theorem formalLogOnePlusProductArgumentBasicFactorLabelCountChoices_subset_choices
    {q : ℕ} {e : Fin 2 →₀ ℕ}
    (hleft : e (0 : Fin 2) ≤ q) (hright : e (1 : Fin 2) ≤ q)
    (hsum : q ≤ e (0 : Fin 2) + e (1 : Fin 2)) :
    formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e ⊆
      formalLogOnePlusProductArgumentBasicFactorChoices q e := by
  intro l hl
  rw [mem_formalLogOnePlusProductArgumentBasicFactorLabelCountChoices] at hl
  rw [mem_formalLogOnePlusProductArgumentBasicFactorChoices]
  rcases hl with ⟨hprod, hlabel0, hlabel1, hlabel2⟩
  rw [mem_formalLogOnePlusProductArgumentBasicFactorProductChoices] at hprod
  rcases hprod with ⟨hsupp, hbasic⟩
  refine ⟨?_, hbasic⟩
  rw [Finset.mem_finsuppAntidiag]
  refine ⟨?_, hsupp⟩
  ext j
  fin_cases j
  · rw [Finsupp.finsetSum_apply]
    have hcoord :=
      formalLogOnePlusProductArgument_leftCoord_sum_eq_choiceCounts
        (q := q) (l := l) hbasic
    have hleftCount :
        formalLogOnePlusProductArgumentLeftChoiceCount q l =
          q - e (1 : Fin 2) := by
      rw [formalLogOnePlusProductArgument_leftChoiceCount_eq_labelCount_zero]
      exact hlabel0
    have hmixedCount :
        formalLogOnePlusProductArgumentMixedChoiceCount q l =
          e (0 : Fin 2) + e (1 : Fin 2) - q := by
      rw [formalLogOnePlusProductArgument_mixedChoiceCount_eq_labelCount_two
        hbasic]
      exact hlabel2
    have htarget :
        (∑ i ∈ Finset.range q, (l i) (0 : Fin 2)) =
          e (0 : Fin 2) := by
      rw [hcoord, hleftCount, hmixedCount]
      omega
    simpa using htarget
  · rw [Finsupp.finsetSum_apply]
    have hcoord :=
      formalLogOnePlusProductArgument_rightCoord_sum_eq_choiceCounts
        (q := q) (l := l) hbasic
    have hrightCount :
        formalLogOnePlusProductArgumentRightChoiceCount q l =
          q - e (0 : Fin 2) := by
      rw [formalLogOnePlusProductArgument_rightChoiceCount_eq_labelCount_one]
      exact hlabel1
    have hmixedCount :
        formalLogOnePlusProductArgumentMixedChoiceCount q l =
          e (0 : Fin 2) + e (1 : Fin 2) - q := by
      rw [formalLogOnePlusProductArgument_mixedChoiceCount_eq_labelCount_two
        hbasic]
      exact hlabel2
    have htarget :
        (∑ i ∈ Finset.range q, (l i) (1 : Fin 2)) =
          e (1 : Fin 2) := by
      rw [hcoord, hrightCount, hmixedCount]
      omega
    simpa using htarget

/--
Establishes the identity `(formalLogOnePlusProductArgumentBasicFactorChoices q e).card =
Nat.choose q (e (0 : Fin 2) + e (1 : Fin 2) - q) * Nat.choose (q - (e (0 : Fin 2) + e (1 : Fin 2)
- q)) (q - e (1 : Fin 2))`.
-/
theorem formalLogOnePlusProductArgumentBasicFactorChoices_card_eq_choose_mul_choose
    {q : ℕ} {e : Fin 2 →₀ ℕ}
    (hleft : e (0 : Fin 2) ≤ q) (hright : e (1 : Fin 2) ≤ q)
    (hsum : q ≤ e (0 : Fin 2) + e (1 : Fin 2)) :
    (formalLogOnePlusProductArgumentBasicFactorChoices q e).card =
      Nat.choose q (e (0 : Fin 2) + e (1 : Fin 2) - q) *
        Nat.choose
          (q - (e (0 : Fin 2) + e (1 : Fin 2) - q))
          (q - e (1 : Fin 2)) := by
  have hEq :
      formalLogOnePlusProductArgumentBasicFactorChoices q e =
        formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e := by
    apply Finset.Subset.antisymm
    · exact
        formalLogOnePlusProductArgumentBasicFactorChoices_subset_labelCountChoices
          q e
    · exact
        formalLogOnePlusProductArgumentBasicFactorLabelCountChoices_subset_choices
          hleft hright hsum
  rw [hEq]
  rw [formalLogOnePlusProductArgumentBasicFactorLabelCountChoices_card_eq_mixedLeftChoices_card
    hleft hright hsum]
  rw [formalLogOnePlusProductArgumentMixedLeftChoices_card]

/-- Proves the bound `e (0 : Fin 2) ≤ q`. -/
theorem formalLogOnePlusProductArgument_choiceCounts_left_coord_le_q
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    e (0 : Fin 2) ≤ q := by
  rcases formalLogOnePlusProductArgument_choiceCounts_system
      hl hbasic with ⟨hleft, _hright, htotal⟩
  have hq :
      q =
        e (0 : Fin 2) +
          formalLogOnePlusProductArgumentRightChoiceCount q l := by
    calc
      q =
        formalLogOnePlusProductArgumentLeftChoiceCount q l +
            formalLogOnePlusProductArgumentRightChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l := htotal.symm
      _ =
        (formalLogOnePlusProductArgumentLeftChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l) +
            formalLogOnePlusProductArgumentRightChoiceCount q l := by
        simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      _ =
        e (0 : Fin 2) +
          formalLogOnePlusProductArgumentRightChoiceCount q l := by
        rw [hleft]
  exact Nat.le.intro hq.symm

/-- Proves the bound `e (1 : Fin 2) ≤ q`. -/
theorem formalLogOnePlusProductArgument_choiceCounts_right_coord_le_q
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    e (1 : Fin 2) ≤ q := by
  rcases formalLogOnePlusProductArgument_choiceCounts_system
      hl hbasic with ⟨_hleft, hright, htotal⟩
  have hq :
      q =
        e (1 : Fin 2) +
          formalLogOnePlusProductArgumentLeftChoiceCount q l := by
    calc
      q =
        formalLogOnePlusProductArgumentLeftChoiceCount q l +
            formalLogOnePlusProductArgumentRightChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l := htotal.symm
      _ =
        (formalLogOnePlusProductArgumentRightChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l) +
            formalLogOnePlusProductArgumentLeftChoiceCount q l := by
        simp only [Nat.add_left_comm, Nat.add_comm]
      _ =
        e (1 : Fin 2) +
          formalLogOnePlusProductArgumentLeftChoiceCount q l := by
        rw [hright]
  exact Nat.le.intro hq.symm

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
