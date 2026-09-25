/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ProductArgument
/-!
# Basic factors in the formal logarithm product argument

This module packages the three possible nonzero monomial factors and their
finite choice spaces.
-/

@[expose] public section

noncomputable section

attribute [local instance] Classical.propDecidable

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

/-- The three exponent vectors with nonzero coefficient in `X + Y + XY`. -/
def formalLogOnePlusProductArgumentBasicFactor
    (m : Fin 2 →₀ ℕ) : Prop :=
  m = Finsupp.single (0 : Fin 2) 1 ∨
    m = Finsupp.single (1 : Fin 2) 1 ∨
      m =
        Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2) 1

/-- The finite set of the left, right, and mixed basic exponent vectors. -/
noncomputable def formalLogOnePlusProductArgumentBasicFactorFinset :
    Finset (Fin 2 →₀ ℕ) := by
  classical
  exact
    {Finsupp.single (0 : Fin 2) 1,
      Finsupp.single (1 : Fin 2) 1,
      Finsupp.single (0 : Fin 2) 1 +
        Finsupp.single (1 : Fin 2) 1}

/--
Characterizes `m ∈ formalLogOnePlusProductArgumentBasicFactorFinset` by the equivalent condition
`formalLogOnePlusProductArgumentBasicFactor m`.
-/
theorem mem_formalLogOnePlusProductArgumentBasicFactorFinset
    {m : Fin 2 →₀ ℕ} :
    m ∈ formalLogOnePlusProductArgumentBasicFactorFinset ↔
      formalLogOnePlusProductArgumentBasicFactor m := by
  classical
  simp [formalLogOnePlusProductArgumentBasicFactorFinset,
    formalLogOnePlusProductArgumentBasicFactor]

/-- Establishes the identity `formalLogOnePlusProductArgumentBasicFactorFinset.card = 3`. -/
@[simp] theorem formalLogOnePlusProductArgumentBasicFactorFinset_card :
    formalLogOnePlusProductArgumentBasicFactorFinset.card = 3 := by
  classical
  simp [formalLogOnePlusProductArgumentBasicFactorFinset,
    finsupp_fin_two_single_left_ne_single_right]

/-- Labels the left, right, and mixed basic factors by `0`, `1`, and `2`.
Non-basic inputs receive the mixed label; all uses that recover a factor from
its label therefore carry a basic-factor hypothesis. -/
def formalLogOnePlusProductArgumentBasicFactorLabel
    (m : Fin 2 →₀ ℕ) : Fin 3 :=
  if m = Finsupp.single (0 : Fin 2) 1 then 0
  else if m = Finsupp.single (1 : Fin 2) 1 then 1
  else 2

/--
Establishes the identity `formalLogOnePlusProductArgumentBasicFactorLabel (Finsupp.single (0 : Fin
2) 1) = 0`.
-/
@[simp] theorem formalLogOnePlusProductArgumentBasicFactorLabel_left :
    formalLogOnePlusProductArgumentBasicFactorLabel
        (Finsupp.single (0 : Fin 2) 1) = 0 := by
  simp [formalLogOnePlusProductArgumentBasicFactorLabel]

/--
Establishes the identity `formalLogOnePlusProductArgumentBasicFactorLabel (Finsupp.single (1 : Fin
2) 1) = 1`.
-/
@[simp] theorem formalLogOnePlusProductArgumentBasicFactorLabel_right :
    formalLogOnePlusProductArgumentBasicFactorLabel
        (Finsupp.single (1 : Fin 2) 1) = 1 := by
  simp [formalLogOnePlusProductArgumentBasicFactorLabel,
    finsupp_fin_two_single_left_ne_single_right.symm]

/--
Establishes the identity `formalLogOnePlusProductArgumentBasicFactorLabel (Finsupp.single (0 : Fin
2) 1 + Finsupp.single (1 : Fin 2) 1) = 2`.
-/
@[simp] theorem formalLogOnePlusProductArgumentBasicFactorLabel_mixed :
    formalLogOnePlusProductArgumentBasicFactorLabel
        (Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2) 1) = 2 := by
  simp [formalLogOnePlusProductArgumentBasicFactorLabel,
    finsupp_fin_two_single_left_ne_mixed.symm,
    finsupp_fin_two_single_right_ne_mixed.symm]

/--
Characterizes `formalLogOnePlusProductArgumentBasicFactorLabel m = (0 : Fin 3)` by the equivalent
condition `m = Finsupp.single (0 : Fin 2) 1`.
-/
theorem formalLogOnePlusProductArgumentBasicFactorLabel_eq_zero
    {m : Fin 2 →₀ ℕ} :
    formalLogOnePlusProductArgumentBasicFactorLabel m = (0 : Fin 3) ↔
      m = Finsupp.single (0 : Fin 2) 1 := by
  unfold formalLogOnePlusProductArgumentBasicFactorLabel
  by_cases hleft : m = Finsupp.single (0 : Fin 2) 1
  · simp [hleft]
  · by_cases hright : m = Finsupp.single (1 : Fin 2) 1
    · simp [hright]
    · simp [hleft, hright]

/--
Characterizes `formalLogOnePlusProductArgumentBasicFactorLabel m = (1 : Fin 3)` by the equivalent
condition `m = Finsupp.single (1 : Fin 2) 1`.
-/
theorem formalLogOnePlusProductArgumentBasicFactorLabel_eq_one
    {m : Fin 2 →₀ ℕ} :
    formalLogOnePlusProductArgumentBasicFactorLabel m = (1 : Fin 3) ↔
      m = Finsupp.single (1 : Fin 2) 1 := by
  unfold formalLogOnePlusProductArgumentBasicFactorLabel
  by_cases hleft : m = Finsupp.single (0 : Fin 2) 1
  · simp [hleft, finsupp_fin_two_single_left_ne_single_right]
  · by_cases hright : m = Finsupp.single (1 : Fin 2) 1
    · have hrightLeft :
          Finsupp.single (1 : Fin 2) 1 ≠
            Finsupp.single (0 : Fin 2) 1 :=
        finsupp_fin_two_single_left_ne_single_right.symm
      simp [hright, hrightLeft]
    · simp [hleft, hright]

/-- Finitely supported sequences of `q` basic factors. -/
noncomputable def formalLogOnePlusProductArgumentBasicFactorProductChoices
    (q : ℕ) : Finset (ℕ →₀ (Fin 2 →₀ ℕ)) := by
  classical
  exact
    (Finset.range q).finsupp
      (fun _ => formalLogOnePlusProductArgumentBasicFactorFinset)

/--
Characterizes `l ∈ formalLogOnePlusProductArgumentBasicFactorProductChoices q` by the equivalent
condition `l.support ⊆ Finset.range q ∧ ∀ i ∈ Finset.range q,
formalLogOnePlusProductArgumentBasicFactor (l i)`.
-/
theorem mem_formalLogOnePlusProductArgumentBasicFactorProductChoices
    {q : ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)} :
    l ∈ formalLogOnePlusProductArgumentBasicFactorProductChoices q ↔
      l.support ⊆ Finset.range q ∧
        ∀ i ∈ Finset.range q,
          formalLogOnePlusProductArgumentBasicFactor (l i) := by
  classical
  rw [formalLogOnePlusProductArgumentBasicFactorProductChoices,
    Finset.mem_finsupp_iff]
  constructor
  · intro h
    exact
      ⟨h.1, fun i hi =>
        mem_formalLogOnePlusProductArgumentBasicFactorFinset.1
          (h.2 i hi)⟩
  · intro h
    exact
      ⟨h.1, fun i hi =>
        mem_formalLogOnePlusProductArgumentBasicFactorFinset.2
          (h.2 i hi)⟩

/--
Establishes the identity `(formalLogOnePlusProductArgumentBasicFactorProductChoices q).card = 3 ^
q`.
-/
theorem formalLogOnePlusProductArgumentBasicFactorProductChoices_card
    (q : ℕ) :
    (formalLogOnePlusProductArgumentBasicFactorProductChoices q).card =
      3 ^ q := by
  classical
  rw [formalLogOnePlusProductArgumentBasicFactorProductChoices,
    Finset.card_finsupp]
  simp

/-- Sequences of `q` basic factors whose exponent-vector sum is `e`. -/
noncomputable def formalLogOnePlusProductArgumentBasicFactorChoices
    (q : ℕ) (e : Fin 2 →₀ ℕ) :
    Finset (ℕ →₀ (Fin 2 →₀ ℕ)) := by
  classical
  exact
    (Finset.finsuppAntidiag (Finset.range q) e).filter
      (fun l : ℕ →₀ (Fin 2 →₀ ℕ) =>
        ∀ i ∈ Finset.range q,
          formalLogOnePlusProductArgumentBasicFactor (l i))

/--
Characterizes `l ∈ formalLogOnePlusProductArgumentBasicFactorChoices q e` by the equivalent
condition `l ∈ Finset.finsuppAntidiag (Finset.range q) e ∧ ∀ i ∈ Finset.range q,
formalLogOnePlusProductArgumentBasicFactor (l i)`.
-/
theorem mem_formalLogOnePlusProductArgumentBasicFactorChoices
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)} :
    l ∈ formalLogOnePlusProductArgumentBasicFactorChoices q e ↔
      l ∈ Finset.finsuppAntidiag (Finset.range q) e ∧
        ∀ i ∈ Finset.range q,
          formalLogOnePlusProductArgumentBasicFactor (l i) := by
  classical
  simp [formalLogOnePlusProductArgumentBasicFactorChoices]

/-- Proves the bound `(formalLogOnePlusProductArgumentBasicFactorChoices q e).card ≤ 3 ^ q`. -/
theorem formalLogOnePlusProductArgumentBasicFactorChoices_card_le_three_pow
    (q : ℕ) (e : Fin 2 →₀ ℕ) :
    (formalLogOnePlusProductArgumentBasicFactorChoices q e).card ≤ 3 ^ q := by
  classical
  calc
    (formalLogOnePlusProductArgumentBasicFactorChoices q e).card ≤
        (formalLogOnePlusProductArgumentBasicFactorProductChoices q).card := by
      apply Finset.card_le_card
      intro l hl
      rw [mem_formalLogOnePlusProductArgumentBasicFactorProductChoices]
      rw [mem_formalLogOnePlusProductArgumentBasicFactorChoices] at hl
      exact ⟨(Finset.mem_finsuppAntidiag.mp hl.1).2, hl.2⟩
    _ = 3 ^ q :=
      formalLogOnePlusProductArgumentBasicFactorProductChoices_card q

/-- The number of left factors among the first `q` entries of `l`. -/
def formalLogOnePlusProductArgumentLeftChoiceCount
    (q : ℕ) (l : ℕ →₀ (Fin 2 →₀ ℕ)) : ℕ :=
  ∑ i ∈ Finset.range q,
    if l i = Finsupp.single (0 : Fin 2) 1 then 1 else 0

/-- The number of right factors among the first `q` entries of `l`. -/
def formalLogOnePlusProductArgumentRightChoiceCount
    (q : ℕ) (l : ℕ →₀ (Fin 2 →₀ ℕ)) : ℕ :=
  ∑ i ∈ Finset.range q,
    if l i = Finsupp.single (1 : Fin 2) 1 then 1 else 0

/-- The number of mixed factors among the first `q` entries of `l`. -/
def formalLogOnePlusProductArgumentMixedChoiceCount
    (q : ℕ) (l : ℕ →₀ (Fin 2 →₀ ℕ)) : ℕ :=
  ∑ i ∈ Finset.range q,
    if l i =
        Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2) 1
    then 1 else 0

/-- The number of entries among the first `q` positions with label `j`. -/
def formalLogOnePlusProductArgumentBasicFactorLabelCount
    (q : ℕ) (l : ℕ →₀ (Fin 2 →₀ ℕ)) (j : Fin 3) : ℕ :=
  ∑ i ∈ Finset.range q,
    if formalLogOnePlusProductArgumentBasicFactorLabel (l i) = j
    then 1 else 0

/--
Establishes the identity `formalLogOnePlusProductArgumentLeftChoiceCount q l =
formalLogOnePlusProductArgumentBasicFactorLabelCount q l 0`.
-/
theorem formalLogOnePlusProductArgument_leftChoiceCount_eq_labelCount_zero
    (q : ℕ) (l : ℕ →₀ (Fin 2 →₀ ℕ)) :
    formalLogOnePlusProductArgumentLeftChoiceCount q l =
      formalLogOnePlusProductArgumentBasicFactorLabelCount q l 0 := by
  classical
  rw [formalLogOnePlusProductArgumentLeftChoiceCount,
    formalLogOnePlusProductArgumentBasicFactorLabelCount]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hleft : l i = Finsupp.single (0 : Fin 2) 1
  · simp [hleft]
  · have hlabel :
        formalLogOnePlusProductArgumentBasicFactorLabel (l i) ≠
          (0 : Fin 3) := by
      intro hzero
      exact hleft
        (formalLogOnePlusProductArgumentBasicFactorLabel_eq_zero.1 hzero)
    simp [hleft, hlabel]

/--
Establishes the identity `formalLogOnePlusProductArgumentRightChoiceCount q l =
formalLogOnePlusProductArgumentBasicFactorLabelCount q l 1`.
-/
theorem formalLogOnePlusProductArgument_rightChoiceCount_eq_labelCount_one
    (q : ℕ) (l : ℕ →₀ (Fin 2 →₀ ℕ)) :
    formalLogOnePlusProductArgumentRightChoiceCount q l =
      formalLogOnePlusProductArgumentBasicFactorLabelCount q l 1 := by
  classical
  rw [formalLogOnePlusProductArgumentRightChoiceCount,
    formalLogOnePlusProductArgumentBasicFactorLabelCount]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hright : l i = Finsupp.single (1 : Fin 2) 1
  · simp [hright]
  · have hlabel :
        formalLogOnePlusProductArgumentBasicFactorLabel (l i) ≠
          (1 : Fin 3) := by
      intro hone
      exact hright
        (formalLogOnePlusProductArgumentBasicFactorLabel_eq_one.1 hone)
    simp [hright, hlabel]

/--
Establishes the identity `formalLogOnePlusProductArgumentMixedChoiceCount q l =
formalLogOnePlusProductArgumentBasicFactorLabelCount q l 2`.
-/
theorem formalLogOnePlusProductArgument_mixedChoiceCount_eq_labelCount_two
    {q : ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    formalLogOnePlusProductArgumentMixedChoiceCount q l =
      formalLogOnePlusProductArgumentBasicFactorLabelCount q l 2 := by
  classical
  rw [formalLogOnePlusProductArgumentMixedChoiceCount,
    formalLogOnePlusProductArgumentBasicFactorLabelCount]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hmixed :
      l i =
        Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2) 1
  · simp [hmixed]
  · have hlabel :
        formalLogOnePlusProductArgumentBasicFactorLabel (l i) ≠
          (2 : Fin 3) := by
      intro htwo
      rcases hbasic i hi with hleft | hright | hmixed'
      · rw [hleft] at htwo
        simp at htwo
      · rw [hright] at htwo
        simp at htwo
      · exact hmixed hmixed'
    simp [hmixed, hlabel]


end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
