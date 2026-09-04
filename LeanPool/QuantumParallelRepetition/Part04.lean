/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.QuantumParallelRepetition.Part03
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-! # Quantum parallel repetition, part 04 -/

noncomputable section

namespace QuantumParallelRepetition

/-- The local matrix norm instance used while elaborating part four. -/
noncomputable local instance matrixComplexContinuousENormPartFour
    {m n : Type*} [Fintype m] [Fintype n] :
    ContinuousENorm (Matrix m n ℂ) :=
  @SeminormedAddGroup.toContinuousENorm (Matrix m n ℂ)
    (Matrix.normedAddCommGroup.toSeminormedAddCommGroup.toSeminormedAddGroup)

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

section

open scoped BigOperators

/-- The type used to represent source remaining coordinate in the exact sampling construction. -/
abbrev SourceRemainingCoordinate {n : ℕ} (D : Finset (Fin n)) :=
  ↥(Finset.univ \ D)

private abbrev SourceRemainingPermutation {n : ℕ} (D : Finset (Fin n)) :=
  Equiv.Perm (SourceRemainingCoordinate D)

private def sourceRemainingPermutationRank
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D) :
    SourceRemainingCoordinate D ≃ Fin (Finset.univ \ D).card :=
  π.symm.trans (Finset.equivFin (Finset.univ \ D))

private def sourceRemainingPermutationCoordinateSubtype
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) :
    SourceRemainingCoordinate D :=
  (sourceRemainingPermutationRank D π).symm k

private def sourceRemainingPermutationCoordinate
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) : Fin n :=
  (sourceRemainingPermutationCoordinateSubtype D π k).val

@[simp] theorem sourceRemainingPermutationRank_coordinate
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) :
    sourceRemainingPermutationRank D π
      (sourceRemainingPermutationCoordinateSubtype D π k) = k := by
  simp only [sourceRemainingPermutationCoordinateSubtype, Equiv.apply_symm_apply]

theorem sourceRemainingPermutationCoordinate_not_mem
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) :
    sourceRemainingPermutationCoordinate D π k ∉ D := by
  have h := (sourceRemainingPermutationCoordinateSubtype D π k).property
  exact (Finset.mem_sdiff.mp h).2

private def sourceRemainingPermutationPrefixSubtype
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin ((Finset.univ \ D).card + 1)) :
    Finset (SourceRemainingCoordinate D) := by
  classical
  exact Finset.univ.filter fun i =>
    (sourceRemainingPermutationRank D π i).val < k.val

private def sourceRemainingPermutationPrefix
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin ((Finset.univ \ D).card + 1)) : Finset (Fin n) := by
  classical
  exact (sourceRemainingPermutationPrefixSubtype D π k).image
    (fun i : SourceRemainingCoordinate D => i.val)

theorem sourceRemainingPermutationPrefix_subset
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin ((Finset.univ \ D).card + 1)) :
    sourceRemainingPermutationPrefix D π k ⊆ Finset.univ \ D := by
  classical
  intro i hi
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
  simpa only [mem_sdiff, mem_univ, true_and, hj] using j.property

theorem sourceRemainingPermutationCoordinate_not_mem_prefix
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) :
    sourceRemainingPermutationCoordinate D π k ∉
      sourceRemainingPermutationPrefix D π k.castSucc := by
  classical
  intro hmem
  obtain ⟨j, hj, hval⟩ := Finset.mem_image.mp hmem
  have heq : j = sourceRemainingPermutationCoordinateSubtype D π k := by
    apply Subtype.ext
    exact hval
  subst j
  have hlt := (Finset.mem_filter.mp hj).2
  simp only [sourceRemainingPermutationRank_coordinate, Fin.val_castSucc,
    lt_self_iff_false] at hlt

theorem sourceRemainingPermutationPrefixSubtype_succ
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) :
    sourceRemainingPermutationPrefixSubtype D π k.succ =
      insert (sourceRemainingPermutationCoordinateSubtype D π k)
        (sourceRemainingPermutationPrefixSubtype D π k.castSucc) := by
  classical
  ext i
  simp only [sourceRemainingPermutationPrefixSubtype,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  change
    (sourceRemainingPermutationRank D π i).val < k.val + 1 ↔
      i = sourceRemainingPermutationCoordinateSubtype D π k ∨
        (sourceRemainingPermutationRank D π i).val < k.val
  constructor
  · intro hi
    by_cases hlt : (sourceRemainingPermutationRank D π i).val < k.val
    · exact Or.inr hlt
    · left
      apply (sourceRemainingPermutationRank D π).injective
      have heq :
          sourceRemainingPermutationRank D π i = k := by
        apply Fin.ext
        omega
      simpa only [sourceRemainingPermutationRank_coordinate] using heq
  · intro hi
    rcases hi with hi | hi
    · subst i
      simp only [sourceRemainingPermutationRank_coordinate, lt_add_iff_pos_right,
        Order.lt_one_iff]
    · omega

theorem sourceRemainingPermutationPrefix_succ
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) :
    sourceRemainingPermutationPrefix D π k.succ =
      insert (sourceRemainingPermutationCoordinate D π k)
        (sourceRemainingPermutationPrefix D π k.castSucc) := by
  classical
  unfold sourceRemainingPermutationPrefix
  rw [sourceRemainingPermutationPrefixSubtype_succ,
    Finset.image_insert]
  rfl

@[simp] theorem sourceRemainingPermutationPrefix_zero
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D) :
    sourceRemainingPermutationPrefix D π 0 = ∅ := by
  classical
  simp only [sourceRemainingPermutationPrefix, sourceRemainingPermutationPrefixSubtype,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, not_lt_zero, filter_false, image_empty]

@[simp] theorem sourceRemainingPermutationPrefix_last
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D) :
    sourceRemainingPermutationPrefix D π
        (Fin.last (Finset.univ \ D).card) =
      Finset.univ \ D := by
  classical
  ext i
  constructor
  · intro hi
    exact sourceRemainingPermutationPrefix_subset D π _ hi
  · intro hi
    apply Finset.mem_image.mpr
    refine ⟨(⟨i, hi⟩ : SourceRemainingCoordinate D), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,
      (sourceRemainingPermutationRank D π
        (⟨i, hi⟩ : SourceRemainingCoordinate D)).isLt⟩

theorem sourceRemainingPermutationCoordinate_sum
    {T : Type*} [AddCommMonoid T]
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (f : Fin n → T) :
    (∑ k : Fin (Finset.univ \ D).card,
      f (sourceRemainingPermutationCoordinate D π k)) =
      ∑ i : SourceRemainingCoordinate D, f i.val := by
  classical
  exact (sourceRemainingPermutationRank D π).symm.sum_comp
    (fun i : SourceRemainingCoordinate D => f i.val)

theorem fin_sum_successive_sub
    {m : ℕ} (f : Fin (m + 1) → ℝ) :
    (∑ k : Fin m, (f k.succ - f k.castSucc)) =
      f (Fin.last m) - f 0 := by
  rw [Finset.sum_sub_distrib]
  have hfirst := Fin.sum_univ_succ f
  have hlast := Fin.sum_univ_castSucc f
  linarith

section ActualEntropyBudgets

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def sourcePermutationAliceEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) : ℝ :=
  fullCoordinateAliceTotalEntropyIncrement G n S D
    (sourceRemainingPermutationPrefix D π k.castSucc)
    (sourceRemainingPermutationCoordinate D π k)

theorem sourcePermutationAliceEntropyIncrement_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) :
    0 ≤ sourcePermutationAliceEntropyIncrement G n S D π k := by
  apply fullCoordinateAliceTotalEntropyIncrement_nonneg
  · exact sourceRemainingPermutationCoordinate_not_mem D π k
  · exact sourceRemainingPermutationCoordinate_not_mem_prefix D π k

theorem sourcePermutationAliceEntropyPotential_step
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) :
    fullHistoryAliceEntropyPotential G n S D
        (sourceRemainingPermutationPrefix D π k.succ) -
      fullHistoryAliceEntropyPotential G n S D
        (sourceRemainingPermutationPrefix D π k.castSucc) =
      sourcePermutationAliceEntropyIncrement G n S D π k := by
  rw [sourceRemainingPermutationPrefix_succ]
  exact fullHistoryAliceEntropyPotential_increment G n S D
    (sourceRemainingPermutationPrefix D π k.castSucc)
    (sourceRemainingPermutationCoordinate D π k)
    (sourceRemainingPermutationCoordinate_not_mem D π k)
    (sourceRemainingPermutationCoordinate_not_mem_prefix D π k)

theorem sourcePermutationAliceEntropyIncrement_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (π : SourceRemainingPermutation D) :
    (∑ k : Fin (Finset.univ \ D).card,
      sourcePermutationAliceEntropyIncrement G n S D π k) =
      fullHistoryAliceEntropyPotential G n S D (Finset.univ \ D) -
        fullHistoryAliceEntropyPotential G n S D ∅ := by
  calc
    (∑ k : Fin (Finset.univ \ D).card,
      sourcePermutationAliceEntropyIncrement G n S D π k) =
      ∑ k : Fin (Finset.univ \ D).card,
        (fullHistoryAliceEntropyPotential G n S D
            (sourceRemainingPermutationPrefix D π k.succ) -
          fullHistoryAliceEntropyPotential G n S D
            (sourceRemainingPermutationPrefix D π k.castSucc)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact (sourcePermutationAliceEntropyPotential_step G n S D π k).symm
    _ = fullHistoryAliceEntropyPotential G n S D
            (sourceRemainingPermutationPrefix D π
              (Fin.last (Finset.univ \ D).card)) -
          fullHistoryAliceEntropyPotential G n S D
            (sourceRemainingPermutationPrefix D π 0) :=
      fin_sum_successive_sub
        (fun k => fullHistoryAliceEntropyPotential G n S D
          (sourceRemainingPermutationPrefix D π k))
    _ = _ := by simp only [sourceRemainingPermutationPrefix_last,
                  sourceRemainingPermutationPrefix_zero]

theorem sourcePermutationAliceEntropyIncrement_sum_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (hp : 0 < (strategyEventLaw (G.repeat n) S).eventMass
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D))
    (π : SourceRemainingPermutation D) :
    (∑ k : Fin (Finset.univ \ D).card,
      sourcePermutationAliceEntropyIncrement G n S D π k) ≤
      (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D) *
        Real.log
          (fullHistoryAnswerCount (A := A) (B := B) D /
            (strategyEventLaw (G.repeat n) S).eventMass
              (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)) := by
  classical
  rw [sourcePermutationAliceEntropyIncrement_sum]
  have hlast := fullHistoryAliceEntropyPotential_nonpos
    G n S D (Finset.univ \ D)
  have hfirst := fullHistoryAliceEntropyPotential_lower_bound
    G n S D ∅ (Finset.empty_subset _) hp
  linarith

private def sourceUniformPermutationAverage
    {n : ℕ} (D : Finset (Fin n))
    (f : SourceRemainingPermutation D →
      Fin (Finset.univ \ D).card → ℝ) : ℝ :=
  (∑ π : SourceRemainingPermutation D,
    ∑ k : Fin (Finset.univ \ D).card, f π k) /
    ((Fintype.card (SourceRemainingPermutation D) : ℝ) *
      ((Finset.univ \ D).card : ℝ))

theorem sourceRemainingPermutation_card_pos
    {n : ℕ} (D : Finset (Fin n)) :
    0 < (Fintype.card (SourceRemainingPermutation D) : ℝ) := by
  classical
  exact_mod_cast (Fintype.card_pos_iff.mpr
    ⟨Equiv.refl (SourceRemainingCoordinate D)⟩ :
      0 < Fintype.card (SourceRemainingPermutation D))

theorem sourceUniformPermutationAverage_le
    {n : ℕ} (D : Finset (Fin n))
    (hm : 0 < (Finset.univ \ D).card)
    (f : SourceRemainingPermutation D →
      Fin (Finset.univ \ D).card → ℝ)
    {C : ℝ}
    (hC : ∀ π : SourceRemainingPermutation D,
      (∑ k : Fin (Finset.univ \ D).card, f π k) ≤ C) :
    sourceUniformPermutationAverage D f ≤
      C / ((Finset.univ \ D).card : ℝ) := by
  classical
  have hperm := sourceRemainingPermutation_card_pos D
  have hmreal : 0 < ((Finset.univ \ D).card : ℝ) := by
    exact_mod_cast hm
  have hden : 0 <
      (Fintype.card (SourceRemainingPermutation D) : ℝ) *
        ((Finset.univ \ D).card : ℝ) :=
    mul_pos hperm hmreal
  have hsum :
      (∑ π : SourceRemainingPermutation D,
        ∑ k : Fin (Finset.univ \ D).card, f π k) ≤
        (Fintype.card (SourceRemainingPermutation D) : ℝ) * C := by
    calc
      (∑ π : SourceRemainingPermutation D,
        ∑ k : Fin (Finset.univ \ D).card, f π k) ≤
          ∑ _π : SourceRemainingPermutation D, C := by
        apply Finset.sum_le_sum
        intro π _
        exact hC π
      _ = (Fintype.card (SourceRemainingPermutation D) : ℝ) * C := by
        simp only [sum_const, card_univ, nsmul_eq_mul]
  unfold sourceUniformPermutationAverage
  calc
    (∑ π : SourceRemainingPermutation D,
        ∑ k : Fin (Finset.univ \ D).card, f π k) /
      ((Fintype.card (SourceRemainingPermutation D) : ℝ) *
        ((Finset.univ \ D).card : ℝ)) ≤
      ((Fintype.card (SourceRemainingPermutation D) : ℝ) * C) /
        ((Fintype.card (SourceRemainingPermutation D) : ℝ) *
          ((Finset.univ \ D).card : ℝ)) :=
        (div_le_div_iff_of_pos_right hden).mpr hsum
    _ = C / ((Finset.univ \ D).card : ℝ) :=
      mul_div_mul_left C ((Finset.univ \ D).card : ℝ) hperm.ne'

theorem sourceUniformPermutationAverage_nonneg
    {n : ℕ} (D : Finset (Fin n))
    (f : SourceRemainingPermutation D →
      Fin (Finset.univ \ D).card → ℝ)
    (hf : ∀ π k, 0 ≤ f π k) :
    0 ≤ sourceUniformPermutationAverage D f := by
  classical
  apply div_nonneg
  · exact Finset.sum_nonneg fun π _ =>
      Finset.sum_nonneg fun k _ => hf π k
  · exact mul_nonneg
      (Nat.cast_nonneg (Fintype.card (SourceRemainingPermutation D)))
      (Nat.cast_nonneg (Finset.univ \ D).card)

theorem sourceUniformPermutationAliceEntropyBudget
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (hm : 0 < (Finset.univ \ D).card)
    (hp : 0 < (strategyEventLaw (G.repeat n) S).eventMass
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)) :
    sourceUniformPermutationAverage D
        (sourcePermutationAliceEntropyIncrement G n S D) ≤
      (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D) *
        Real.log
          (fullHistoryAnswerCount (A := A) (B := B) D /
            (strategyEventLaw (G.repeat n) S).eventMass
              (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)) /
          ((Finset.univ \ D).card : ℝ) := by
  apply sourceUniformPermutationAverage_le D hm
  intro π
  exact sourcePermutationAliceEntropyIncrement_sum_le G n S D hp π

end ActualEntropyBudgets

end

section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The exact left construction used in the quantum parallel-repetition argument. -/
def exactLeft
    {M : Type*} [Fintype M] [DecidableEq M]
    (coordinate : M) (partition : M → Bool) : Finset M :=
  Finset.univ.filter fun j => j ≠ coordinate ∧ partition j = false

/-- The exact right construction used in the quantum parallel-repetition argument. -/
def exactRight
    {M : Type*} [Fintype M] [DecidableEq M]
    (coordinate : M) (partition : M → Bool) : Finset M :=
  Finset.univ.filter fun j => j ≠ coordinate ∧ partition j = true

theorem exactLeft_coordinate_not_mem
    {M : Type*} [Fintype M] [DecidableEq M]
    (coordinate : M) (partition : M → Bool) :
    coordinate ∉ exactLeft coordinate partition := by
  simp only [exactLeft, ne_eq, mem_filter, mem_univ, not_true_eq_false, false_and, and_false,
    not_false_eq_true]

theorem exactRight_coordinate_not_mem
    {M : Type*} [Fintype M] [DecidableEq M]
    (coordinate : M) (partition : M → Bool) :
    coordinate ∉ exactRight coordinate partition := by
  simp only [exactRight, ne_eq, mem_filter, mem_univ, not_true_eq_false, false_and, and_false,
    not_false_eq_true]

/-- The coordinate, partition, orders, and cuts sampled by the exact forward process. -/
structure ExactForwardSeed
    (M : Type*) [Fintype M] [DecidableEq M] where
  /-- The marked coordinate of the seed. -/
  coordinate : M
  /-- The binary partition of coordinates carried by the seed. -/
  partition : M → Bool
  /-- The ordering of coordinates on the left side of the partition. -/
  leftOrder : Equiv.Perm
    {j : M // j ∈ exactLeft coordinate partition}
  /-- The ordering of coordinates on the right side of the partition. -/
  rightOrder : Equiv.Perm
    {j : M // j ∈ exactRight coordinate partition}
  /-- The reveal cut in the left-side ordering. -/
  leftCut : Fin ((exactLeft coordinate partition).card + 1)
  /-- The reveal cut in the right-side ordering. -/
  rightCut : Fin ((exactRight coordinate partition).card + 1)
  deriving Fintype

/-- The type used to represent exact remaining seed in the exact sampling construction. -/
abbrev ExactRemainingSeed
    {n : ℕ} (D : Finset (Fin n)) :=
  ExactForwardSeed (SourceRemainingCoordinate D)

/-- The rank map for exact left. -/
def exactLeftRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    {j : M // j ∈ exactLeft seed.coordinate seed.partition} ≃
      Fin (exactLeft seed.coordinate seed.partition).card :=
  seed.leftOrder.symm.trans
    (Finset.equivFin (exactLeft seed.coordinate seed.partition))

/-- The rank map for exact right. -/
def exactRightRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    {j : M // j ∈ exactRight seed.coordinate seed.partition} ≃
      Fin (exactRight seed.coordinate seed.partition).card :=
  seed.rightOrder.symm.trans
    (Finset.equivFin (exactRight seed.coordinate seed.partition))

/-- The exact left prefix construction used in the quantum parallel-repetition argument. -/
def exactLeftPrefix
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : Finset M :=
  (Finset.univ.filter
    (fun j : {j : M //
      j ∈ exactLeft seed.coordinate seed.partition} =>
      (exactLeftRank seed j).val < seed.leftCut.val)).image
        Subtype.val

/-- The exact right prefix construction used in the quantum parallel-repetition argument. -/
def exactRightPrefix
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : Finset M :=
  (Finset.univ.filter
    (fun j : {j : M //
      j ∈ exactRight seed.coordinate seed.partition} =>
      (exactRightRank seed j).val < seed.rightCut.val)).image
        Subtype.val

theorem exactLeftPrefix_subset
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactLeftPrefix seed ⊆
      exactLeft seed.coordinate seed.partition := by
  intro j hj
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hj
  exact ha ▸ a.property

theorem exactRightPrefix_subset
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactRightPrefix seed ⊆
      exactRight seed.coordinate seed.partition := by
  intro j hj
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hj
  exact ha ▸ a.property

/-- The probability weight for exact seed. -/
def exactSeedWeight
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : ℝ :=
  (1 / (Fintype.card M : ℝ)) *
    (1 / (Fintype.card (M → Bool) : ℝ)) *
    (1 / (Fintype.card
      (Equiv.Perm
        {j : M // j ∈
          exactLeft seed.coordinate seed.partition}) : ℝ)) *
    (1 / (Fintype.card
      (Equiv.Perm
        {j : M // j ∈
          exactRight seed.coordinate seed.partition}) : ℝ)) *
    (1 / ((exactLeft
      seed.coordinate seed.partition).card + 1 : ℝ)) *
    (1 / ((exactRight
      seed.coordinate seed.partition).card + 1 : ℝ))

theorem exactSeedWeight_nonneg
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    0 ≤ exactSeedWeight seed := by
  unfold exactSeedWeight
  positivity

private abbrev ExactSeedTuple
    (M : Type*) [Fintype M] [DecidableEq M] :=
  Σ i : M, Σ partition : M → Bool,
    (Equiv.Perm {j : M // j ∈ exactLeft i partition}) ×
    (Equiv.Perm {j : M // j ∈ exactRight i partition}) ×
    Fin ((exactLeft i partition).card + 1) ×
    Fin ((exactRight i partition).card + 1)

private def exactSeedEquiv
    (M : Type*) [Fintype M] [DecidableEq M] :
    ExactForwardSeed M ≃ ExactSeedTuple M where
  toFun seed := ⟨seed.coordinate, seed.partition,
    seed.leftOrder, seed.rightOrder, seed.leftCut, seed.rightCut⟩
  invFun t :=
    ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1,
      t.2.2.2.2.1, t.2.2.2.2.2⟩
  left_inv seed := by
    cases seed
    rfl
  right_inv t := by
    rcases t with ⟨i, partition, leftOrder, rightOrder,
      leftCut, rightCut⟩
    rfl

@[simp] theorem exactSeedEquiv_symm_apply
    {M : Type*} [Fintype M] [DecidableEq M]
    (t : ExactSeedTuple M) :
    (exactSeedEquiv M).symm t =
      ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1,
        t.2.2.2.2.1, t.2.2.2.2.2⟩ := by
  rfl

theorem exactForwardSeed_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (f : ExactForwardSeed M → ℝ) :
    (∑ seed : ExactForwardSeed M, f seed) =
      ∑ i : M,
      ∑ partition : M → Bool,
      ∑ leftOrder : Equiv.Perm
        {j : M // j ∈ exactLeft i partition},
      ∑ rightOrder : Equiv.Perm
        {j : M // j ∈ exactRight i partition},
      ∑ leftCut : Fin ((exactLeft i partition).card + 1),
      ∑ rightCut : Fin ((exactRight i partition).card + 1),
        f ⟨i, partition, leftOrder, rightOrder, leftCut, rightCut⟩ := by
  classical
  calc
    (∑ seed : ExactForwardSeed M, f seed) =
        ∑ t : ExactSeedTuple M,
          f ((exactSeedEquiv M).symm t) :=
      ((exactSeedEquiv M).symm.sum_comp f).symm
    _ = _ := by
      simp only [exactSeedEquiv_symm_apply, Fintype.sum_sigma, Fintype.sum_prod_type]

theorem exactUniform_sum
    {T : Type*} [Fintype T]
    (positive : 0 < Fintype.card T) :
    (∑ _t : T, (1 / (Fintype.card T : ℝ))) = 1 := by
  have hcard : (Fintype.card T : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt positive)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hcard]

theorem exactUniform_sum_mul
    {T : Type*} [Fintype T]
    (positive : 0 < Fintype.card T) (value : ℝ) :
    (∑ _t : T,
      value * (1 / (Fintype.card T : ℝ))) = value := by
  rw [← Finset.mul_sum, exactUniform_sum positive]
  ring

theorem exactPrefixUniform_sum_mul
    (m : ℕ) (value : ℝ) :
    (∑ _k : Fin (m + 1),
      value * (1 / ((m : ℝ) + 1))) = value := by
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
    (exactUniform_sum_mul
      (T := Fin (m + 1)) (by simp only [Fintype.card_fin, lt_add_iff_pos_left,
                               Order.lt_add_one_iff, zero_le]) value)

theorem exactPermutationUniform_sum_mul
    {T : Type*} [Fintype T] (value : ℝ) :
    (∑ _π : Equiv.Perm T,
      value * (1 / (Fintype.card (Equiv.Perm T) : ℝ))) = value := by
  exact exactUniform_sum_mul
    (Fintype.card_pos_iff.mpr ⟨Equiv.refl T⟩) value

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


theorem common_finite_purification_pair_jensen
    {ι κ d : Type*}
    [Fintype ι] [Fintype κ] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ)
    (F : κ → Matrix d d ℂ)
    (anchor : Matrix d d ℂ)
    (positive : ∀ k, (F k).PosSemidef)
    (hanchor : anchor.PosSemidef)
    (choose : ι → κ) (meanIndex : κ)
    (nonnegative : ∀ a, 0 ≤ weight a)
    (normalized : (∑ a : ι, weight a) = 1)
    (mean : (∑ a : ι, weight a • F (choose a)) = F meanIndex) :
    ((∑ a : ι, weight a •
        cfc (fun z : ℝ => z * Real.log z) (F (choose a))) -
      cfc (fun z : ℝ => z * Real.log z) (F meanIndex) -
      (∑ a : ι, weight a •
        ((finitePurificationMatrix F anchor positive hanchor (choose a) -
            finitePurificationMatrix F anchor positive hanchor meanIndex).conjTranspose *
          (finitePurificationMatrix F anchor positive hanchor (choose a) -
            finitePurificationMatrix F anchor positive hanchor meanIndex)))).PosSemidef := by
  classical
  let H : ι → Matrix d d ℂ := fun a => F (choose a)
  let M : Matrix d d ℂ := F meanIndex
  have hH : ∀ a, (H a).PosSemidef := fun a => positive (choose a)
  have hM : M.PosSemidef := positive meanIndex
  have hmean : (∑ a : ι, weight a • H a) = M := mean
  have hlocal := finite_purification_log_entropy_jensen
    weight H M nonnegative normalized hmean hH
  change
    ((∑ a : ι, weight a •
        cfc (fun z : ℝ => z * Real.log z) (H a)) -
      cfc (fun z : ℝ => z * Real.log z) M -
      (∑ a : ι, weight a •
        ((finitePurificationMatrix H M hH hM a -
            meanFinitePurificationMatrix H M hH hM).conjTranspose *
          (finitePurificationMatrix H M hH hM a -
            meanFinitePurificationMatrix H M hH hM)))).PosSemidef at hlocal
  have hpair (a : ι) :
      (finitePurificationMatrix F anchor positive hanchor (choose a) -
          finitePurificationMatrix F anchor positive hanchor meanIndex).conjTranspose *
        (finitePurificationMatrix F anchor positive hanchor (choose a) -
          finitePurificationMatrix F anchor positive hanchor meanIndex) =
      (finitePurificationMatrix H M hH hM a -
          meanFinitePurificationMatrix H M hH hM).conjTranspose *
        (finitePurificationMatrix H M hH hM a -
          meanFinitePurificationMatrix H M hH hM) := by
    rw [finitePurificationMatrix_pair_difference_gram_eq_integral,
      finitePurificationMatrix_difference_gram_eq_integral]
  change
    ((∑ a : ι, weight a •
        cfc (fun z : ℝ => z * Real.log z) (H a)) -
      cfc (fun z : ℝ => z * Real.log z) M -
      (∑ a : ι, weight a •
        ((finitePurificationMatrix F anchor positive hanchor (choose a) -
            finitePurificationMatrix F anchor positive hanchor meanIndex).conjTranspose *
          (finitePurificationMatrix F anchor positive hanchor (choose a) -
            finitePurificationMatrix F anchor positive hanchor meanIndex)))).PosSemidef
  simp_rw [hpair]
  exact hlocal

theorem commonFinitePurification_weighted_left_variation_le
    {X Y A B ι κ eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype ι] [Fintype κ] [Fintype eB]
    {G : Game X Y A B} (S : Strategy G)
    (weight : ι → ℝ)
    (F : κ → Matrix S.Alice S.Alice ℂ)
    (anchor : Matrix S.Alice S.Alice ℂ)
    (positive : ∀ k, (F k).PosSemidef)
    (hanchor : anchor.PosSemidef)
    (choose : ι → κ) (meanIndex : κ)
    (nonnegative : ∀ a, 0 ≤ weight a)
    (normalized : (∑ a : ι, weight a) = 1)
    (mean : (∑ a : ι, weight a • F (choose a)) = F meanIndex)
    (KB : Matrix eB S.Bob ℂ) :
    (∑ a : ι, weight a *
      ‖finiteLocalPurificationVector S
          (finitePurificationMatrix F anchor positive hanchor (choose a)) KB -
        finiteLocalPurificationVector S
          (finitePurificationMatrix F anchor positive hanchor meanIndex) KB‖ ^ 2) ≤
      bornTracePairing S.state.matrix
        ((∑ a : ι, weight a •
            cfc (fun z : ℝ => z * Real.log z) (F (choose a))) -
          cfc (fun z : ℝ => z * Real.log z) (F meanIndex))
        (KB.conjTranspose * KB) := by
  classical
  have hJ := common_finite_purification_pair_jensen
    weight F anchor positive hanchor choose meanIndex
    nonnegative normalized mean
  have hnonneg := trace_mul_posSemidef_nonneg S.state.positive
    (hJ.kronecker (Matrix.posSemidef_conjTranspose_mul_self KB))
  change
    0 ≤ bornTracePairing S.state.matrix
      (((∑ a : ι, weight a •
          cfc (fun z : ℝ => z * Real.log z) (F (choose a))) -
        cfc (fun z : ℝ => z * Real.log z) (F meanIndex)) -
       (∑ a : ι, weight a •
        ((finitePurificationMatrix F anchor positive hanchor (choose a) -
            finitePurificationMatrix F anchor positive hanchor meanIndex).conjTranspose *
          (finitePurificationMatrix F anchor positive hanchor (choose a) -
            finitePurificationMatrix F anchor positive hanchor meanIndex))))
      (KB.conjTranspose * KB) at hnonneg
  have hsum :
      bornTracePairing S.state.matrix
        (∑ a : ι, weight a •
          ((finitePurificationMatrix F anchor positive hanchor (choose a) -
              finitePurificationMatrix F anchor positive hanchor meanIndex).conjTranspose *
            (finitePurificationMatrix F anchor positive hanchor (choose a) -
              finitePurificationMatrix F anchor positive hanchor meanIndex)))
        (KB.conjTranspose * KB) =
        ∑ a : ι, weight a *
          ‖finiteLocalPurificationVector S
              (finitePurificationMatrix F anchor positive hanchor (choose a)) KB -
            finiteLocalPurificationVector S
              (finitePurificationMatrix F anchor positive hanchor meanIndex) KB‖ ^ 2 := by
    simp only [map_sum, LinearMap.sum_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [finiteLocalPurificationVector_sub_left_norm_sq]
  rw [map_sub] at hnonneg
  change
    0 ≤
      bornTracePairing S.state.matrix
        ((∑ a : ι, weight a •
            cfc (fun z : ℝ => z * Real.log z) (F (choose a))) -
          cfc (fun z : ℝ => z * Real.log z) (F meanIndex))
        (KB.conjTranspose * KB) -
      bornTracePairing S.state.matrix
        (∑ a : ι, weight a •
          ((finitePurificationMatrix F anchor positive hanchor (choose a) -
              finitePurificationMatrix F anchor positive hanchor meanIndex).conjTranspose *
            (finitePurificationMatrix F anchor positive hanchor (choose a) -
              finitePurificationMatrix F anchor positive hanchor meanIndex)))
        (KB.conjTranspose * KB) at hnonneg
  rw [hsum] at hnonneg
  linarith

theorem commonFinitePurification_weighted_right_variation_le
    {X Y A B ι κ eA : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype ι] [Fintype κ] [Fintype eA]
    {G : Game X Y A B} (S : Strategy G)
    (weight : ι → ℝ)
    (F : κ → Matrix S.Bob S.Bob ℂ)
    (anchor : Matrix S.Bob S.Bob ℂ)
    (positive : ∀ k, (F k).PosSemidef)
    (hanchor : anchor.PosSemidef)
    (choose : ι → κ) (meanIndex : κ)
    (nonnegative : ∀ b, 0 ≤ weight b)
    (normalized : (∑ b : ι, weight b) = 1)
    (mean : (∑ b : ι, weight b • F (choose b)) = F meanIndex)
    (KA : Matrix eA S.Alice ℂ) :
    (∑ b : ι, weight b *
      ‖finiteLocalPurificationVector S KA
          (finitePurificationMatrix F anchor positive hanchor (choose b)) -
        finiteLocalPurificationVector S KA
          (finitePurificationMatrix F anchor positive hanchor meanIndex)‖ ^ 2) ≤
      bornTracePairing S.state.matrix
        (KA.conjTranspose * KA)
        ((∑ b : ι, weight b •
            cfc (fun z : ℝ => z * Real.log z) (F (choose b))) -
          cfc (fun z : ℝ => z * Real.log z) (F meanIndex)) := by
  classical
  have hJ := common_finite_purification_pair_jensen
    weight F anchor positive hanchor choose meanIndex
    nonnegative normalized mean
  have hnonneg := trace_mul_posSemidef_nonneg S.state.positive
    ((Matrix.posSemidef_conjTranspose_mul_self KA).kronecker hJ)
  change
    0 ≤ bornTracePairing S.state.matrix
      (KA.conjTranspose * KA)
      (((∑ b : ι, weight b •
          cfc (fun z : ℝ => z * Real.log z) (F (choose b))) -
        cfc (fun z : ℝ => z * Real.log z) (F meanIndex)) -
       (∑ b : ι, weight b •
        ((finitePurificationMatrix F anchor positive hanchor (choose b) -
            finitePurificationMatrix F anchor positive hanchor meanIndex).conjTranspose *
          (finitePurificationMatrix F anchor positive hanchor (choose b) -
            finitePurificationMatrix F anchor positive hanchor meanIndex)))) at hnonneg
  have hsum :
      bornTracePairing S.state.matrix
        (KA.conjTranspose * KA)
        (∑ b : ι, weight b •
          ((finitePurificationMatrix F anchor positive hanchor (choose b) -
              finitePurificationMatrix F anchor positive hanchor meanIndex).conjTranspose *
            (finitePurificationMatrix F anchor positive hanchor (choose b) -
              finitePurificationMatrix F anchor positive hanchor meanIndex))) =
        ∑ b : ι, weight b *
          ‖finiteLocalPurificationVector S KA
              (finitePurificationMatrix F anchor positive hanchor (choose b)) -
            finiteLocalPurificationVector S KA
              (finitePurificationMatrix F anchor positive hanchor meanIndex)‖ ^ 2 := by
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro b _
    rw [finiteLocalPurificationVector_sub_right_norm_sq]
  rw [map_sub, hsum] at hnonneg
  linarith

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem rectangular_matrix_quadratic_compression
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (K : Matrix e d ℂ) (E : Matrix e e ℂ)
    (z : EuclideanSpace ℂ d) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := e) (𝕜 := ℂ) E)
      (toLp 2 (K.mulVec (ofLp z))) =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)
          (K.conjTranspose * E * K)) z := by
  unfold quadraticExpectation
  rw [EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct]
  change
    (E.mulVec (K.mulVec (ofLp z)) ⬝ᵥ
      star (K.mulVec (ofLp z))).re =
    ((K.conjTranspose * E * K).mulVec (ofLp z) ⬝ᵥ
      star (ofLp z)).re
  rw [dotProduct_comm (E.mulVec (K.mulVec (ofLp z))),
    Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]
  rw [dotProduct_comm]

theorem finiteLocalPurificationJointMatrix_compression
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype eA] [Fintype eB]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ) (KB : Matrix eB S.Bob ℂ)
    (EA : Matrix eA eA ℂ) (EB : Matrix eB eB ℂ) :
    (finiteLocalPurificationJointMatrix S KA KB).conjTranspose *
        (((EA ⊗ₖ
            (1 : Matrix (S.Alice × S.Bob)
              (S.Alice × S.Bob) ℂ)) ⊗ₖ EB)) *
        finiteLocalPurificationJointMatrix S KA KB =
      (((KA.conjTranspose * EA * KA) ⊗ₖ
          (1 : Matrix (S.Alice × S.Bob)
            (S.Alice × S.Bob) ℂ)) ⊗ₖ
        (KB.conjTranspose * EB * KB)) := by
  classical
  unfold finiteLocalPurificationJointMatrix
  rw [Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]
  simp only [conjTranspose_one, mul_one]

theorem finiteLocalPurificationVector_quadratic
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype eA] [Fintype eB]
    [DecidableEq eA] [DecidableEq eB]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ) (KB : Matrix eB S.Bob ℂ)
    (EA : Matrix eA eA ℂ) (EB : Matrix eB eB ℂ) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (eA × (S.Alice × S.Bob)) × eB) (𝕜 := ℂ)
        (((EA ⊗ₖ
          (1 : Matrix (S.Alice × S.Bob)
            (S.Alice × S.Bob) ℂ)) ⊗ₖ EB)))
      (finiteLocalPurificationVector S KA KB) =
      bornTracePairing S.state.matrix
        (KA.conjTranspose * EA * KA)
        (KB.conjTranspose * EB * KB) := by
  unfold finiteLocalPurificationVector
  rw [rectangular_matrix_quadratic_compression,
    finiteLocalPurificationJointMatrix_compression]
  exact strategyPurificationVector_quadratic S
    (KA.conjTranspose * EA * KA)
    (KB.conjTranspose * EB * KB)

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The measurement effect for conditioned alice coordinate. -/
def conditionedAliceCoordinateEffect
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {j : Fin n // j ∈ D} → A)
    (xs : Fin n → X) (i : Fin n) (a : A) :
    Matrix S.Alice S.Alice ℂ := by
  classical
  exact ∑ answers : Fin n → A,
    if (∀ (j : Fin n) (hj : j ∈ D), answers j = α ⟨j, hj⟩) ∧
      answers i = a
    then (S.aliceMeasurement xs).effect answers
    else 0

/-- The measurement effect for conditioned bob coordinate. -/
def conditionedBobCoordinateEffect
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (β : {j : Fin n // j ∈ D} → B)
    (ys : Fin n → Y) (i : Fin n) (b : B) :
    Matrix S.Bob S.Bob ℂ := by
  classical
  exact ∑ answers : Fin n → B,
    if (∀ (j : Fin n) (hj : j ∈ D), answers j = β ⟨j, hj⟩) ∧
      answers i = b
    then (S.bobMeasurement ys).effect answers
    else 0

theorem conditionedAliceCoordinateEffect_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {j : Fin n // j ∈ D} → A)
    (xs : Fin n → X) (i : Fin n) (a : A) :
    (conditionedAliceCoordinateEffect G n S D α xs i a).PosSemidef := by
  classical
  unfold conditionedAliceCoordinateEffect
  apply Matrix.posSemidef_sum Finset.univ
  intro answers _
  split_ifs
  · exact (S.aliceMeasurement xs).positive answers
  · exact Matrix.PosSemidef.zero

theorem conditionedBobCoordinateEffect_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (β : {j : Fin n // j ∈ D} → B)
    (ys : Fin n → Y) (i : Fin n) (b : B) :
    (conditionedBobCoordinateEffect G n S D β ys i b).PosSemidef := by
  classical
  unfold conditionedBobCoordinateEffect
  apply Matrix.posSemidef_sum Finset.univ
  intro answers _
  split_ifs
  · exact (S.bobMeasurement ys).positive answers
  · exact Matrix.PosSemidef.zero

theorem conditionedAliceCoordinateEffect_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {j : Fin n // j ∈ D} → A)
    (xs : Fin n → X) (i : Fin n) :
    (∑ a : A, conditionedAliceCoordinateEffect G n S D α xs i a) =
      conditionedAliceEffect G n S D α xs := by
  classical
  unfold conditionedAliceCoordinateEffect conditionedAliceEffect
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro answers _
  calc
    (∑ a : A,
      if (∀ (j : Fin n) (hj : j ∈ D), answers j = α ⟨j, hj⟩) ∧
        answers i = a
      then (S.aliceMeasurement xs).effect answers
      else 0) =
      if (∀ (j : Fin n) (hj : j ∈ D), answers j = α ⟨j, hj⟩) ∧
        answers i = answers i
      then (S.aliceMeasurement xs).effect answers
      else 0 := by
        apply Fintype.sum_eq_single (answers i)
        intro a ha
        simp only [ha.symm, and_false, ↓reduceIte]
    _ = _ := by simp only [and_true]

theorem conditionedBobCoordinateEffect_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (β : {j : Fin n // j ∈ D} → B)
    (ys : Fin n → Y) (i : Fin n) :
    (∑ b : B, conditionedBobCoordinateEffect G n S D β ys i b) =
      conditionedBobEffect G n S D β ys := by
  classical
  unfold conditionedBobCoordinateEffect conditionedBobEffect
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro answers _
  calc
    (∑ b : B,
      if (∀ (j : Fin n) (hj : j ∈ D), answers j = β ⟨j, hj⟩) ∧
        answers i = b
      then (S.bobMeasurement ys).effect answers
      else 0) =
      if (∀ (j : Fin n) (hj : j ∈ D), answers j = β ⟨j, hj⟩) ∧
        answers i = answers i
      then (S.bobMeasurement ys).effect answers
      else 0 := by
        apply Fintype.sum_eq_single (answers i)
        intro b hb
        simp only [hb.symm, and_false, ↓reduceIte]
    _ = _ := by simp only [and_true]

private def fullHistoryAliceCoordinateEffect
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (α : {j : Fin n // j ∈ D} → A)
    (i : Fin n) (a : A) :
    Matrix S.Alice S.Alice ℂ :=
  ∑ hidden : {j : Fin n // j ∈ fullHistoryRemaining n D L} → X,
    fullHistoryHiddenAliceWeight G h hidden •
      conditionedAliceCoordinateEffect G n S D α
        (fullHistoryAliceQuestion h hidden) i a

private def fullHistoryBobCoordinateEffect
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (β : {j : Fin n // j ∈ D} → B)
    (i : Fin n) (b : B) :
    Matrix S.Bob S.Bob ℂ :=
  ∑ hidden : {j : Fin n // j ∈ L} → Y,
    fullHistoryHiddenBobWeight G h hidden •
      conditionedBobCoordinateEffect G n S D β
        (fullHistoryBobQuestion h hidden) i b

private def fullCoordinateAliceRefinementEffect
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A)
    (x : X) (a : A) : Matrix S.Alice S.Alice ℂ :=
  fullHistoryAliceCoordinateEffect G n S D (insert i L)
    (fullCoordinateNewHistory D L i r x) α i a

private def fullCoordinateBobRefinementEffect
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (β : {j : Fin n // j ∈ D} → B)
    (y : Y) (b : B) : Matrix S.Bob S.Bob ℂ :=
  fullHistoryBobCoordinateEffect G n S D L
    (fullCoordinateOldHistory D L i r y) β i b

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The exact conditioned transcript associated with a forward seed. -/
structure ExactRevealHistory
    (X Y : Type*) [Fintype X] [Fintype Y]
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) where
  /-- Alice's questions on conditioned coordinates. -/
  aliceConditioned : {j : Fin n // j ∈ D} → X
  /-- Bob's questions on conditioned coordinates. -/
  bobConditioned : {j : Fin n // j ∈ D} → Y
  /-- Alice's questions revealed on the left side. -/
  aliceLeft :
    {j : SourceRemainingCoordinate D //
      j ∈ exactLeft seed.coordinate seed.partition} → X
  /-- Bob's questions revealed on the right side. -/
  bobRight :
    {j : SourceRemainingCoordinate D //
      j ∈ exactRight seed.coordinate seed.partition} → Y
  /-- Bob's revealed prefix on the left side. -/
  bobLeftPrefix :
    {j : SourceRemainingCoordinate D //
      j ∈ exactLeftPrefix seed} → Y
  /-- Alice's revealed prefix on the right side. -/
  aliceRightPrefix :
    {j : SourceRemainingCoordinate D //
      j ∈ exactRightPrefix seed} → X

/-- The type used to represent exact reveal history tuple in the exact sampling construction. -/
abbrev ExactRevealHistoryTuple
    (X Y : Type*)
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :=
  ({j : Fin n // j ∈ D} → X) ×
  ({j : Fin n // j ∈ D} → Y) ×
  ({j : SourceRemainingCoordinate D //
      j ∈ exactLeft seed.coordinate seed.partition} → X) ×
  ({j : SourceRemainingCoordinate D //
      j ∈ exactRight seed.coordinate seed.partition} → Y) ×
  ({j : SourceRemainingCoordinate D //
      j ∈ exactLeftPrefix seed} → Y) ×
  ({j : SourceRemainingCoordinate D //
      j ∈ exactRightPrefix seed} → X)

/-- The finite equivalence encoding exact reveal history. -/
def exactRevealHistoryEquiv
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :
    ExactRevealHistory X Y D seed ≃
      ExactRevealHistoryTuple X Y D seed where
  toFun h := ⟨h.aliceConditioned, h.bobConditioned,
    h.aliceLeft, h.bobRight, h.bobLeftPrefix, h.aliceRightPrefix⟩
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1,
    t.2.2.2.2.1, t.2.2.2.2.2⟩
  left_inv h := by cases h; rfl
  right_inv t := by
    rcases t with ⟨ac, bc, al, br, bl, ar⟩
    rfl

noncomputable instance exactRevealHistoryFintype
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :
    Fintype (ExactRevealHistory X Y D seed) := by
  classical
  exact Fintype.ofEquiv (ExactRevealHistoryTuple X Y D seed)
    (exactRevealHistoryEquiv
      (X := X) (Y := Y) D seed).symm

/-- The type used to represent exact full question in the exact sampling construction. -/
abbrev ExactFullQuestion
    (X Y : Type*) (n : ℕ) :=
  (Fin n → X) × (Fin n → Y)

/-- The finite encoding of exact reveal. -/
def exactRevealCode
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (q : ExactFullQuestion X Y n) :
    ExactRevealHistory X Y D seed where
  aliceConditioned j := q.1 j.val
  bobConditioned j := q.2 j.val
  aliceLeft j := q.1 j.val.val
  bobRight j := q.2 j.val.val
  bobLeftPrefix j := q.2 j.val.val
  aliceRightPrefix j := q.1 j.val.val

/-- The probability weight for exact prior question. -/
def exactPriorQuestionWeight
    (G : Game X Y A B) (n : ℕ)
    (q : ExactFullQuestion X Y n) : ℝ :=
  (G.repeat n).questionWeight q.1 q.2

theorem exactPriorQuestionWeight_nonneg
    (G : Game X Y A B) (n : ℕ)
    (q : ExactFullQuestion X Y n) :
    0 ≤ exactPriorQuestionWeight G n q :=
  (G.repeat n).weight_nonneg q.1 q.2

theorem exactPriorQuestionWeight_sum
    (G : Game X Y A B) (n : ℕ) :
    (∑ q : ExactFullQuestion X Y n,
      exactPriorQuestionWeight G n q) = 1 := by
  simpa only [exactPriorQuestionWeight, Game.repeat_questionWeight,
    Fintype.sum_prod_type] using (G.repeat n).weight_normalized

/-- The total probability mass of exact reveal. -/
def exactRevealMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed) : ℝ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history
    then exactPriorQuestionWeight G n q
    else 0

theorem exactRevealMass_nonneg
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed) :
    0 ≤ exactRevealMass G n D seed history := by
  unfold exactRevealMass
  apply Finset.sum_nonneg
  intro q _
  split
  · exact exactPriorQuestionWeight_nonneg G n q
  · exact le_rfl

theorem exactRevealMass_sum
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :
    (∑ history : ExactRevealHistory X Y D seed,
      exactRevealMass G n D seed history) = 1 := by
  classical
  unfold exactRevealMass
  rw [Finset.sum_comm]
  simp_rw [Fintype.sum_ite_eq]
  exact exactPriorQuestionWeight_sum G n

/-- The total probability mass of exact alice question. -/
def exactAliceQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) : ℝ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.1 seed.coordinate.val = x
    then exactPriorQuestionWeight G n q
    else 0

/-- The total probability mass of exact bob question. -/
def exactBobQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (y : Y) : ℝ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.2 seed.coordinate.val = y
    then exactPriorQuestionWeight G n q
    else 0

/-- The total probability mass of exact joint question. -/
def exactJointQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y) : ℝ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.1 seed.coordinate.val = x ∧
      q.2 seed.coordinate.val = y
    then exactPriorQuestionWeight G n q
    else 0

theorem exactAliceQuestionMass_nonneg
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) :
    0 ≤ exactAliceQuestionMass G n D seed history x := by
  unfold exactAliceQuestionMass
  apply Finset.sum_nonneg
  intro q _
  split
  · exact exactPriorQuestionWeight_nonneg G n q
  · exact le_rfl

theorem exactBobQuestionMass_nonneg
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (y : Y) :
    0 ≤ exactBobQuestionMass G n D seed history y := by
  unfold exactBobQuestionMass
  apply Finset.sum_nonneg
  intro q _
  split
  · exact exactPriorQuestionWeight_nonneg G n q
  · exact le_rfl

/-- The spectral filter for exact alice question. -/
def exactAliceQuestionFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) : Matrix S.Alice S.Alice ℂ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.1 seed.coordinate.val = x
    then
      (exactPriorQuestionWeight G n q /
        exactAliceQuestionMass G n D seed history x) •
        conditionedAliceEffect G n S D answer q.1
    else 0

/-- The spectral filter for exact bob question. -/
def exactBobQuestionFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (y : Y) : Matrix S.Bob S.Bob ℂ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.2 seed.coordinate.val = y
    then
      (exactPriorQuestionWeight G n q /
        exactBobQuestionMass G n D seed history y) •
        conditionedBobEffect G n S D answer q.2
    else 0

theorem exactAliceQuestionFilter_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) :
    (exactAliceQuestionFilter
      G n S D seed history answer x).PosSemidef := by
  unfold exactAliceQuestionFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro q _
  split
  · exact (conditionedAliceEffect_positive G n S D answer q.1).smul
      (div_nonneg
        (exactPriorQuestionWeight_nonneg G n q)
        (exactAliceQuestionMass_nonneg
          G n D seed history x))
  · exact Matrix.PosSemidef.zero

theorem exactBobQuestionFilter_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (y : Y) :
    (exactBobQuestionFilter
      G n S D seed history answer y).PosSemidef := by
  unfold exactBobQuestionFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro q _
  split
  · exact (conditionedBobEffect_positive G n S D answer q.2).smul
      (div_nonneg
        (exactPriorQuestionWeight_nonneg G n q)
        (exactBobQuestionMass_nonneg
          G n D seed history y))
  · exact Matrix.PosSemidef.zero

/-- The spectral filter for exact alice mean. -/
def exactAliceMeanFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (y : Y) : Matrix S.Alice S.Alice ℂ :=
  ∑ x : X, G.conditionalXGivenY y x •
    exactAliceQuestionFilter G n S D seed history answer x

/-- The spectral filter for exact bob mean. -/
def exactBobMeanFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (x : X) : Matrix S.Bob S.Bob ℂ :=
  ∑ y : Y, G.conditionalYGivenX x y •
    exactBobQuestionFilter G n S D seed history answer y

theorem exactAliceMeanFilter_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (y : Y) :
    (exactAliceMeanFilter
      G n S D seed history answer y).PosSemidef := by
  unfold exactAliceMeanFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro x _
  exact (exactAliceQuestionFilter_posSemidef
    G n S D seed history answer x).smul
    (G.conditionalXGivenY_nonneg y x)

theorem exactBobMeanFilter_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (x : X) :
    (exactBobMeanFilter
      G n S D seed history answer x).PosSemidef := by
  unfold exactBobMeanFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro y _
  exact (exactBobQuestionFilter_posSemidef
    G n S D seed history answer y).smul
    (G.conditionalYGivenX_nonneg x y)

/-- The spectral filter for exact alice coordinate. -/
def exactAliceCoordinateFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) (a : A) : Matrix S.Alice S.Alice ℂ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.1 seed.coordinate.val = x
    then
      (exactPriorQuestionWeight G n q /
        exactAliceQuestionMass G n D seed history x) •
        conditionedAliceCoordinateEffect G n S D answer q.1
          seed.coordinate.val a
    else 0

/-- The spectral filter for exact bob coordinate. -/
def exactBobCoordinateFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (y : Y) (b : B) : Matrix S.Bob S.Bob ℂ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.2 seed.coordinate.val = y
    then
      (exactPriorQuestionWeight G n q /
        exactBobQuestionMass G n D seed history y) •
        conditionedBobCoordinateEffect G n S D answer q.2
          seed.coordinate.val b
    else 0

theorem exactAliceCoordinateFilter_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) (a : A) :
    (exactAliceCoordinateFilter
      G n S D seed history answer x a).PosSemidef := by
  unfold exactAliceCoordinateFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro q _
  split
  · exact (conditionedAliceCoordinateEffect_posSemidef
      G n S D answer q.1 seed.coordinate.val a).smul
      (div_nonneg
        (exactPriorQuestionWeight_nonneg G n q)
        (exactAliceQuestionMass_nonneg
          G n D seed history x))
  · exact Matrix.PosSemidef.zero

theorem exactBobCoordinateFilter_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (y : Y) (b : B) :
    (exactBobCoordinateFilter
      G n S D seed history answer y b).PosSemidef := by
  unfold exactBobCoordinateFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro q _
  split
  · exact (conditionedBobCoordinateEffect_posSemidef
      G n S D answer q.2 seed.coordinate.val b).smul
      (div_nonneg
        (exactPriorQuestionWeight_nonneg G n q)
        (exactBobQuestionMass_nonneg
          G n D seed history y))
  · exact Matrix.PosSemidef.zero

theorem exactAliceCoordinateFilter_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) :
    (∑ a : A,
      exactAliceCoordinateFilter
        G n S D seed history answer x a) =
      exactAliceQuestionFilter
        G n S D seed history answer x := by
  classical
  unfold exactAliceCoordinateFilter
    exactAliceQuestionFilter
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : exactRevealCode D seed q = history ∧
      q.1 seed.coordinate.val = x
  · simp only [hq, and_self, ↓reduceIte, ← smul_sum, conditionedAliceCoordinateEffect_sum]
  · simp only [hq, ↓reduceIte, sum_const_zero]

theorem exactBobCoordinateFilter_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (y : Y) :
    (∑ b : B,
      exactBobCoordinateFilter
        G n S D seed history answer y b) =
      exactBobQuestionFilter
        G n S D seed history answer y := by
  classical
  unfold exactBobCoordinateFilter
    exactBobQuestionFilter
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : exactRevealCode D seed q = history ∧
      q.2 seed.coordinate.val = y
  · simp only [hq, and_self, ↓reduceIte, ← smul_sum, conditionedBobCoordinateEffect_sum]
  · simp only [hq, ↓reduceIte, sum_const_zero]

/--
The exact alice purification family construction used in the quantum parallel-repetition
argument.
-/
def exactAlicePurificationFamily
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A) :
    Sum X Y → Matrix S.Alice S.Alice ℂ :=
  Sum.elim
    (exactAliceQuestionFilter G n S D seed history answer)
    (exactAliceMeanFilter G n S D seed history answer)

/--
The exact bob purification family construction used in the quantum parallel-repetition argument.
-/
def exactBobPurificationFamily
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B) :
    Sum Y X → Matrix S.Bob S.Bob ℂ :=
  Sum.elim
    (exactBobQuestionFilter G n S D seed history answer)
    (exactBobMeanFilter G n S D seed history answer)

theorem exactAlicePurificationFamily_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (q : Sum X Y) :
    (exactAlicePurificationFamily
      G n S D seed history answer q).PosSemidef := by
  cases q with
  | inl x =>
      exact exactAliceQuestionFilter_posSemidef
        G n S D seed history answer x
  | inr y =>
      exact exactAliceMeanFilter_posSemidef
        G n S D seed history answer y

theorem exactBobPurificationFamily_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (q : Sum Y X) :
    (exactBobPurificationFamily
      G n S D seed history answer q).PosSemidef := by
  cases q with
  | inl y =>
      exact exactBobQuestionFilter_posSemidef
        G n S D seed history answer y
  | inr x =>
      exact exactBobMeanFilter_posSemidef
        G n S D seed history answer x

/-- The type used to represent exact alice lift index in the exact sampling construction. -/
abbrev ExactAliceLiftIndex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A) :=
  S.Alice × Fin (Module.finrank ℂ
    (commonPurificationSubspace
      (exactAlicePurificationFamily
        G n S D seed history answer)
      (0 : Matrix S.Alice S.Alice ℂ)
      (exactAlicePurificationFamily_posSemidef
        G n S D seed history answer)
      Matrix.PosSemidef.zero))

/-- The type used to represent exact bob lift index in the exact sampling construction. -/
abbrev ExactBobLiftIndex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B) :=
  S.Bob × Fin (Module.finrank ℂ
    (commonPurificationSubspace
      (exactBobPurificationFamily
        G n S D seed history answer)
      (0 : Matrix S.Bob S.Bob ℂ)
      (exactBobPurificationFamily_posSemidef
        G n S D seed history answer)
      Matrix.PosSemidef.zero))

/-- The matrix representation of exact alice purification. -/
def exactAlicePurificationMatrix
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (q : Sum X Y) :
    Matrix (ExactAliceLiftIndex
      G n S D seed history answer) S.Alice ℂ :=
  finitePurificationMatrix
    (exactAlicePurificationFamily
      G n S D seed history answer)
    0
    (exactAlicePurificationFamily_posSemidef
      G n S D seed history answer)
    Matrix.PosSemidef.zero q

/-- The matrix representation of exact bob purification. -/
def exactBobPurificationMatrix
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (q : Sum Y X) :
    Matrix (ExactBobLiftIndex
      G n S D seed history answer) S.Bob ℂ :=
  finitePurificationMatrix
    (exactBobPurificationFamily
      G n S D seed history answer)
    0
    (exactBobPurificationFamily_posSemidef
      G n S D seed history answer)
    Matrix.PosSemidef.zero q

theorem exactAlicePurificationMatrix_gram
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (q : Sum X Y) :
    (exactAlicePurificationMatrix
      G n S D seed history answer q).conjTranspose *
      exactAlicePurificationMatrix
        G n S D seed history answer q =
      exactAlicePurificationFamily
        G n S D seed history answer q :=
  finitePurificationMatrix_gram
    (exactAlicePurificationFamily
      G n S D seed history answer)
    0
    (exactAlicePurificationFamily_posSemidef
      G n S D seed history answer)
    Matrix.PosSemidef.zero q

theorem exactBobPurificationMatrix_gram
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (q : Sum Y X) :
    (exactBobPurificationMatrix
      G n S D seed history answer q).conjTranspose *
      exactBobPurificationMatrix
        G n S D seed history answer q =
      exactBobPurificationFamily
        G n S D seed history answer q :=
  finitePurificationMatrix_gram
    (exactBobPurificationFamily
      G n S D seed history answer)
    0
    (exactBobPurificationFamily_posSemidef
      G n S D seed history answer)
    Matrix.PosSemidef.zero q

/-- A seed and transcript together with the answers at its marked coordinate. -/
@[ext (iff := false)] structure ExactHistoryFlag
    (X Y A B : Type*)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) where
  /-- The forward seed carried by the flag. -/
  seed : ExactRemainingSeed D
  /-- The exact reveal history carried by the flag. -/
  history : ExactRevealHistory X Y D seed
  /-- Alice's answer at the marked coordinate. -/
  aliceAnswer : {j : Fin n // j ∈ D} → A
  /-- Bob's answer at the marked coordinate. -/
  bobAnswer : {j : Fin n // j ∈ D} → B

/-- The type used to represent exact history flag tuple in the exact sampling construction. -/
abbrev ExactHistoryFlagTuple
    (X Y A B : Type*)
    [Fintype X] [Fintype Y]
    {n : ℕ} (D : Finset (Fin n)) :=
  Σ seed : ExactRemainingSeed D,
    ExactRevealHistory X Y D seed ×
      ({j : Fin n // j ∈ D} → A) ×
      ({j : Fin n // j ∈ D} → B)

/-- The finite equivalence encoding exact history flag. -/
def exactHistoryFlagEquiv
    {n : ℕ} (D : Finset (Fin n)) :
    ExactHistoryFlag X Y A B D ≃
      ExactHistoryFlagTuple X Y A B D where
  toFun r := ⟨r.seed, r.history, r.aliceAnswer, r.bobAnswer⟩
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
  left_inv r := by cases r; rfl
  right_inv t := by
    rcases t with ⟨seed, history, aliceAnswer, bobAnswer⟩
    rfl

noncomputable instance exactHistoryFlagFintype
    {n : ℕ} (D : Finset (Fin n)) :
    Fintype (ExactHistoryFlag X Y A B D) := by
  classical
  exact Fintype.ofEquiv (ExactHistoryFlagTuple X Y A B D)
    (exactHistoryFlagEquiv
      (X := X) (Y := Y) (A := A) (B := B) D).symm

theorem exactHistoryFlag_sum
    {n : ℕ} (D : Finset (Fin n))
    (f : ExactHistoryFlag X Y A B D → ℝ) :
    (∑ r : ExactHistoryFlag X Y A B D, f r) =
      ∑ seed : ExactRemainingSeed D,
      ∑ history : ExactRevealHistory X Y D seed,
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        f ⟨seed, history, aliceAnswer, bobAnswer⟩ := by
  classical
  calc
    (∑ r : ExactHistoryFlag X Y A B D, f r) =
        ∑ t : ExactHistoryFlagTuple X Y A B D,
          f ((exactHistoryFlagEquiv
            (X := X) (Y := Y) (A := A) (B := B) D).symm t) :=
      ((exactHistoryFlagEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm.sum_comp f).symm
    _ = _ := by
      simp only [exactHistoryFlagEquiv, Equiv.symm_mk, Equiv.coe_fn_mk, Fintype.sum_sigma,
        Fintype.sum_prod_type]

/-- The type used to represent exact alice local index in the exact sampling construction. -/
abbrev ExactAliceLocalIndex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :=
  ExactAliceLiftIndex
    G n S D r.seed r.history r.aliceAnswer × (S.Alice × S.Bob)

/-- The type used to represent exact bob local index in the exact sampling construction. -/
abbrev ExactBobLocalIndex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :=
  ExactBobLiftIndex
    G n S D r.seed r.history r.bobAnswer

/-- The exact unnormalized psi construction used in the quantum parallel-repetition argument. -/
def exactUnnormalizedPsi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r) :=
  finiteLocalPurificationVector S
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inl x))
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inl y))

/-- The exact unnormalized phi construction used in the quantum parallel-repetition argument. -/
def exactUnnormalizedPhi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (y : Y) :
    EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r) :=
  finiteLocalPurificationVector S
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inr y))
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inl y))

/-- The exact unnormalized gamma construction used in the quantum parallel-repetition argument. -/
def exactUnnormalizedGamma
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) :
    EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r) :=
  finiteLocalPurificationVector S
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inl x))
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inr x))

theorem exactUnnormalizedPsi_norm_sq
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    ‖exactUnnormalizedPsi G n S D r x y‖ ^ 2 =
      bornTracePairing S.state.matrix
        (exactAliceQuestionFilter
          G n S D r.seed r.history r.aliceAnswer x)
        (exactBobQuestionFilter
          G n S D r.seed r.history r.bobAnswer y) := by
  unfold exactUnnormalizedPsi
  rw [finiteLocalPurificationVector_norm_sq,
    exactAlicePurificationMatrix_gram,
    exactBobPurificationMatrix_gram]
  rfl

theorem exactAliceQuestionPurificationMatrix_gram
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) :
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inl x)).conjTranspose *
      exactAlicePurificationMatrix
        G n S D r.seed r.history r.aliceAnswer (.inl x) =
      exactAliceQuestionFilter
        G n S D r.seed r.history r.aliceAnswer x :=
  exactAlicePurificationMatrix_gram
    G n S D r.seed r.history r.aliceAnswer (.inl x)

theorem exactBobQuestionPurificationMatrix_gram
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (y : Y) :
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inl y)).conjTranspose *
      exactBobPurificationMatrix
        G n S D r.seed r.history r.bobAnswer (.inl y) =
      exactBobQuestionFilter
        G n S D r.seed r.history r.bobAnswer y :=
  exactBobPurificationMatrix_gram
    G n S D r.seed r.history r.bobAnswer (.inl y)

/-- The positive operator-valued measurement implementing exact alice refined. -/
def exactAliceRefinedPOVM
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (x : X) :
    POVM A (ExactAliceLiftIndex
      G n S D r.seed r.history r.aliceAnswer) :=
  purifiedRefinedPOVM
    (exactAliceQuestionFilter
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAliceQuestionFilter_posSemidef
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inl x))
    (exactAliceQuestionPurificationMatrix_gram G n S D r x)
    (exactAliceCoordinateFilter
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAliceCoordinateFilter_posSemidef
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAliceCoordinateFilter_sum
      G n S D r.seed r.history r.aliceAnswer x)
    a₀

/-- The positive operator-valued measurement implementing exact bob refined. -/
def exactBobRefinedPOVM
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (b₀ : B) (y : Y) :
    POVM B (ExactBobLiftIndex
      G n S D r.seed r.history r.bobAnswer) :=
  purifiedRefinedPOVM
    (exactBobQuestionFilter
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobQuestionFilter_posSemidef
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inl y))
    (exactBobQuestionPurificationMatrix_gram G n S D r y)
    (exactBobCoordinateFilter
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobCoordinateFilter_posSemidef
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobCoordinateFilter_sum
      G n S D r.seed r.history r.bobAnswer y)
    b₀

theorem exactAliceRefinedPOVM_compression
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (x : X) (a : A) :
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inl x)).conjTranspose *
      (exactAliceRefinedPOVM G n S D r a₀ x).effect a *
      exactAlicePurificationMatrix
        G n S D r.seed r.history r.aliceAnswer (.inl x) =
      exactAliceCoordinateFilter
        G n S D r.seed r.history r.aliceAnswer x a := by
  exact purifiedRefinedPOVM_compression
    (exactAliceQuestionFilter
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAliceQuestionFilter_posSemidef
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inl x))
    (exactAliceQuestionPurificationMatrix_gram G n S D r x)
    (exactAliceCoordinateFilter
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAliceCoordinateFilter_posSemidef
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAliceCoordinateFilter_sum
      G n S D r.seed r.history r.aliceAnswer x)
    a₀ a

theorem exactBobRefinedPOVM_compression
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (b₀ : B) (y : Y) (b : B) :
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inl y)).conjTranspose *
      (exactBobRefinedPOVM G n S D r b₀ y).effect b *
      exactBobPurificationMatrix
        G n S D r.seed r.history r.bobAnswer (.inl y) =
      exactBobCoordinateFilter
        G n S D r.seed r.history r.bobAnswer y b := by
  exact purifiedRefinedPOVM_compression
    (exactBobQuestionFilter
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobQuestionFilter_posSemidef
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inl y))
    (exactBobQuestionPurificationMatrix_gram G n S D r y)
    (exactBobCoordinateFilter
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobCoordinateFilter_posSemidef
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobCoordinateFilter_sum
      G n S D r.seed r.history r.bobAnswer y)
    b₀ b

theorem exactRefinedPOVM_quadratic
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) (a : A) (b : B) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := ExactAliceLocalIndex G n S D r ×
          ExactBobLocalIndex G n S D r)
        (𝕜 := ℂ)
        (((exactAliceRefinedPOVM
          G n S D r a₀ x).effect a ⊗ₖ
          (1 : Matrix (S.Alice × S.Bob)
            (S.Alice × S.Bob) ℂ)) ⊗ₖ
          (exactBobRefinedPOVM
            G n S D r b₀ y).effect b))
      (exactUnnormalizedPsi G n S D r x y) =
      bornTracePairing S.state.matrix
        (exactAliceCoordinateFilter
          G n S D r.seed r.history r.aliceAnswer x a)
        (exactBobCoordinateFilter
          G n S D r.seed r.history r.bobAnswer y b) := by
  unfold exactUnnormalizedPsi
  rw [finiteLocalPurificationVector_quadratic,
    exactAliceRefinedPOVM_compression,
    exactBobRefinedPOVM_compression]

/-- The type used to represent exact padded local index in the exact sampling construction. -/
abbrev ExactPaddedLocalIndex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :=
  PUnit.{1} ⊕
    (ExactAliceLocalIndex G n S D r ⊕
      ExactBobLocalIndex G n S D r)

/-- The state vector representing exact padded. -/
def exactPaddedVector
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (z : EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r)) :
    EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r) :=
  toLp 2 fun q =>
    match q.1, q.2 with
    | .inr (.inl a), .inr (.inr b) => z (a, b)
    | _, _ => 0

theorem exactPaddedVector_norm
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (z : EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r)) :
    ‖exactPaddedVector G n S D r z‖ = ‖z‖ := by
  classical
  have hsquare :
      ‖exactPaddedVector G n S D r z‖ ^ 2 = ‖z‖ ^ 2 := by
    simp only [exactPaddedVector, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
      Fintype.sum_sum_type, univ_unique, PUnit.default_eq_unit, norm_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero, zero_add, add_zero]
  nlinarith [norm_nonneg (exactPaddedVector G n S D r z),
    norm_nonneg z]

theorem exactPaddedVector_sub
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (u v : EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r)) :
    exactPaddedVector G n S D r (u - v) =
      exactPaddedVector G n S D r u -
        exactPaddedVector G n S D r v := by
  classical
  ext q
  rcases q with ⟨a, b⟩
  rcases a with a | (a | a) <;>
    rcases b with b | (b | b) <;>
    simp only [exactPaddedVector, PiLp.sub_apply, sub_zero]

/-- The exact padded default construction used in the quantum parallel-repetition argument. -/
def exactPaddedDefault
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r) := by
  classical
  exact PiLp.single 2 (.inl PUnit.unit, .inl PUnit.unit) (1 : ℂ)

theorem exactPaddedDefault_norm
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    ‖exactPaddedDefault G n S D r‖ = 1 := by
  classical
  simp only [exactPaddedDefault, PiLp.norm_single, norm_one]

/-- The exact psi construction used in the quantum parallel-repetition argument. -/
def exactPsi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r) :=
  normalizeOrDefault (exactPaddedDefault G n S D r)
    (exactPaddedVector G n S D r
      (exactUnnormalizedPsi G n S D r x y))

/-- The exact phi construction used in the quantum parallel-repetition argument. -/
def exactPhi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (y : Y) :
    EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r) :=
  normalizeOrDefault (exactPaddedDefault G n S D r)
    (exactPaddedVector G n S D r
      (exactUnnormalizedPhi G n S D r y))

/-- The exact gamma construction used in the quantum parallel-repetition argument. -/
def exactGamma
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) :
    EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r) :=
  normalizeOrDefault (exactPaddedDefault G n S D r)
    (exactPaddedVector G n S D r
      (exactUnnormalizedGamma G n S D r x))

end

section

open scoped BigOperators


attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/--
The exact alice question compatible construction used in the quantum parallel-repetition
argument.
-/
def exactAliceQuestionCompatible
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (xs : Fin n → X) : Prop :=
  (∀ j : {j : Fin n // j ∈ D},
      xs j.val = history.aliceConditioned j) ∧
  (∀ j : {j : SourceRemainingCoordinate D //
      j ∈ exactLeft seed.coordinate seed.partition},
      xs j.val.val = history.aliceLeft j) ∧
  (∀ j : {j : SourceRemainingCoordinate D //
      j ∈ exactRightPrefix seed},
      xs j.val.val = history.aliceRightPrefix j) ∧
  xs seed.coordinate.val = x

/--
The exact bob question compatible construction used in the quantum parallel-repetition argument.
-/
def exactBobQuestionCompatible
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (y : Y) (ys : Fin n → Y) : Prop :=
  (∀ j : {j : Fin n // j ∈ D},
      ys j.val = history.bobConditioned j) ∧
  (∀ j : {j : SourceRemainingCoordinate D //
      j ∈ exactRight seed.coordinate seed.partition},
      ys j.val.val = history.bobRight j) ∧
  (∀ j : {j : SourceRemainingCoordinate D //
      j ∈ exactLeftPrefix seed},
      ys j.val.val = history.bobLeftPrefix j) ∧
  ys seed.coordinate.val = y

theorem exactRevealCode_compatible_iff
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y)
    (xs : Fin n → X) (ys : Fin n → Y) :
    (exactRevealCode D seed (xs, ys) = history ∧
      xs seed.coordinate.val = x ∧ ys seed.coordinate.val = y) ↔
      exactAliceQuestionCompatible
        D seed history x xs ∧
      exactBobQuestionCompatible
        D seed history y ys := by
  constructor
  · rintro ⟨h, hx, hy⟩
    subst history
    exact ⟨⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, hx⟩,
      ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, hy⟩⟩
  · rintro ⟨⟨hxc, hxl, hxr, hx⟩,
      ⟨hyc, hyr, hyl, hy⟩⟩
    refine ⟨?_, hx, hy⟩
    cases history with
    | mk ac bc al br bl ar =>
      have hac :
          (fun j : {j : Fin n // j ∈ D} => xs j.val) = ac :=
        funext hxc
      have hbc :
          (fun j : {j : Fin n // j ∈ D} => ys j.val) = bc :=
        funext hyc
      have hal :
          (fun j : {j : SourceRemainingCoordinate D //
            j ∈ exactLeft seed.coordinate seed.partition} =>
            xs j.val.val) = al :=
        funext hxl
      have hbr :
          (fun j : {j : SourceRemainingCoordinate D //
            j ∈ exactRight seed.coordinate seed.partition} =>
            ys j.val.val) = br :=
        funext hyr
      have hbl :
          (fun j : {j : SourceRemainingCoordinate D //
            j ∈ exactLeftPrefix seed} =>
            ys j.val.val) = bl :=
        funext hyl
      have har :
          (fun j : {j : SourceRemainingCoordinate D //
            j ∈ exactRightPrefix seed} =>
            xs j.val.val) = ar :=
        funext hxr
      cases hac
      cases hbc
      cases hal
      cases hbr
      cases hbl
      cases har
      rfl

theorem exactCompatible_coordinate_eq_or
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y)
    (xs xs' : Fin n → X) (ys ys' : Fin n → Y)
    (ha : exactAliceQuestionCompatible
      D seed history x xs)
    (ha' : exactAliceQuestionCompatible
      D seed history x xs')
    (hb : exactBobQuestionCompatible
      D seed history y ys)
    (hb' : exactBobQuestionCompatible
      D seed history y ys')
    (j : Fin n) :
    xs j = xs' j ∨ ys j = ys' j := by
  by_cases hj : j ∈ D
  · left
    exact (ha.1 ⟨j, hj⟩).trans (ha'.1 ⟨j, hj⟩).symm
  · let jr : SourceRemainingCoordinate D :=
      ⟨j, by simp only [mem_sdiff, mem_univ, hj, not_false_eq_true, and_self]⟩
    by_cases hcoordinate : jr = seed.coordinate
    · left
      have hval : j = seed.coordinate.val :=
        congrArg Subtype.val hcoordinate
      rw [hval]
      exact ha.2.2.2.trans ha'.2.2.2.symm
    · cases hbit : seed.partition jr with
      | false =>
          left
          have hleft :
              jr ∈ exactLeft
                seed.coordinate seed.partition := by
            simp only [exactLeft, ne_eq, univ_eq_attach, mem_filter, mem_attach, hcoordinate,
              not_false_eq_true, hbit, and_self]
          exact (ha.2.1 ⟨jr, hleft⟩).trans
            (ha'.2.1 ⟨jr, hleft⟩).symm
      | true =>
          right
          have hright :
              jr ∈ exactRight
                seed.coordinate seed.partition := by
            simp only [exactRight, ne_eq, univ_eq_attach, mem_filter, mem_attach, hcoordinate,
              not_false_eq_true, hbit, and_self]
          exact (hb.2.1 ⟨jr, hright⟩).trans
            (hb'.2.1 ⟨jr, hright⟩).symm

theorem exactQuestionWeight_rectangle
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y)
    (xs xs' : Fin n → X) (ys ys' : Fin n → Y)
    (ha : exactAliceQuestionCompatible
      D seed history x xs)
    (ha' : exactAliceQuestionCompatible
      D seed history x xs')
    (hb : exactBobQuestionCompatible
      D seed history y ys)
    (hb' : exactBobQuestionCompatible
      D seed history y ys') :
    (G.repeat n).questionWeight xs ys *
        (G.repeat n).questionWeight xs' ys' =
      (G.repeat n).questionWeight xs ys' *
        (G.repeat n).questionWeight xs' ys := by
  simp only [Game.repeat_questionWeight]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rcases exactCompatible_coordinate_eq_or
    D seed history x y xs xs' ys ys'
    ha ha' hb hb' j with hAlice | hBob
  · simp only [hAlice, mul_comm]
  · simp only [hBob]

/-- The probability weight for exact fiber question. -/
def exactFiberQuestionWeight
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y)
    (xs : Fin n → X) (ys : Fin n → Y) : ℝ :=
  if exactAliceQuestionCompatible
      D seed history x xs ∧
      exactBobQuestionCompatible
        D seed history y ys
  then (G.repeat n).questionWeight xs ys
  else 0

theorem exactFiberQuestionWeight_rectangle
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y)
    (xs xs' : Fin n → X) (ys ys' : Fin n → Y) :
    exactFiberQuestionWeight
        G n D seed history x y xs ys *
      exactFiberQuestionWeight
        G n D seed history x y xs' ys' =
    exactFiberQuestionWeight
        G n D seed history x y xs ys' *
      exactFiberQuestionWeight
        G n D seed history x y xs' ys := by
  classical
  by_cases ha : exactAliceQuestionCompatible
      D seed history x xs <;>
    by_cases ha' : exactAliceQuestionCompatible
      D seed history x xs' <;>
    by_cases hb : exactBobQuestionCompatible
      D seed history y ys <;>
    by_cases hb' : exactBobQuestionCompatible
      D seed history y ys' <;>
    simp [exactFiberQuestionWeight,
      ha, ha', hb, hb']
  simpa only [Game.repeat_questionWeight] using
    (exactQuestionWeight_rectangle
      G n D seed history x y xs xs' ys ys'
      ha ha' hb hb')

private def exactFiberAliceMarginal
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y) (xs : Fin n → X) : ℝ :=
  ∑ ys : Fin n → Y,
    exactFiberQuestionWeight G n D seed history x y xs ys

private def exactFiberBobMarginal
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y) (ys : Fin n → Y) : ℝ :=
  ∑ xs : Fin n → X,
    exactFiberQuestionWeight G n D seed history x y xs ys

/-- The total probability mass of exact fiber question. -/
def exactFiberQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y) : ℝ :=
  ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
    exactFiberQuestionWeight G n D seed history x y xs ys

theorem exactFiberQuestionWeight_mul_mass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y)
    (xs : Fin n → X) (ys : Fin n → Y) :
    exactFiberQuestionWeight
        G n D seed history x y xs ys *
      exactFiberQuestionMass G n D seed history x y =
    exactFiberAliceMarginal
        G n D seed history x y xs *
      exactFiberBobMarginal
        G n D seed history x y ys := by
  classical
  symm
  calc
    exactFiberAliceMarginal
        G n D seed history x y xs *
      exactFiberBobMarginal
        G n D seed history x y ys =
      ∑ u : Fin n → Y, ∑ v : Fin n → X,
        exactFiberQuestionWeight
          G n D seed history x y xs u *
        exactFiberQuestionWeight
          G n D seed history x y v ys := by
      unfold exactFiberAliceMarginal
        exactFiberBobMarginal
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.mul_sum]
    _ = ∑ u : Fin n → Y, ∑ v : Fin n → X,
        exactFiberQuestionWeight
          G n D seed history x y xs ys *
        exactFiberQuestionWeight
          G n D seed history x y v u := by
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      exact exactFiberQuestionWeight_rectangle
        G n D seed history x y xs v u ys
    _ = ∑ v : Fin n → X, ∑ u : Fin n → Y,
        exactFiberQuestionWeight
          G n D seed history x y xs ys *
        exactFiberQuestionWeight
          G n D seed history x y v u := by
      rw [Finset.sum_comm]
    _ = exactFiberQuestionWeight
        G n D seed history x y xs ys *
      exactFiberQuestionMass
        G n D seed history x y := by
      unfold exactFiberQuestionMass
      simp only [Finset.mul_sum]

end

section

open scoped BigOperators


attribute [local instance] Classical.propDecidable

theorem exactFintypeCard_eq
    {T : Type*} (first second : Fintype T) :
    @Fintype.card T first = @Fintype.card T second :=
  @Fintype.card_congr T T first second (Equiv.refl T)

theorem exactSeedWeight_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M) :
    (∑ seed : ExactForwardSeed M,
      exactSeedWeight seed) = 1 := by
  classical
  have hbits : 0 < Fintype.card (M → Bool) :=
    Fintype.card_pos_iff.mpr ⟨fun _ => false⟩
  rw [exactForwardSeed_sum]
  conv_rhs => rw [← exactUniform_sum nonempty]
  apply Finset.sum_congr (by ext; simp only [mem_univ])
  intro coordinate _
  conv_rhs =>
    rw [← exactUniform_sum_mul hbits
      (1 / (Fintype.card M : ℝ))]
  apply Finset.sum_congr (by ext; simp only [mem_univ])
  intro partition _
  let : DecidableEq
      {j : M // j ∈ exactLeft coordinate partition} :=
    fun a b => Classical.propDecidable (a = b)
  let : DecidableEq
      {j : M // j ∈ exactRight coordinate partition} :=
    fun a b => Classical.propDecidable (a = b)
  conv_rhs =>
    rw [← exactPermutationUniform_sum_mul
      (T := {j : M // j ∈ exactLeft coordinate partition})
      ((1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ)))]
  apply Finset.sum_congr (by ext; simp only [mem_univ])
  intro leftOrder _
  conv_rhs =>
    rw [← exactPermutationUniform_sum_mul
      (T := {j : M // j ∈ exactRight coordinate partition})
      ((1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ)) *
        (1 / (Fintype.card
          (Equiv.Perm
            {j : M // j ∈ exactLeft coordinate partition}) : ℝ)))]
  apply Finset.sum_congr (by ext; simp only [mem_univ])
  intro rightOrder _
  conv_rhs =>
    rw [← exactPrefixUniform_sum_mul
      (exactLeft coordinate partition).card
      ((1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ)) *
        (1 / (Fintype.card
          (Equiv.Perm
            {j : M // j ∈ exactLeft coordinate partition}) : ℝ)) *
        (1 / (Fintype.card
          (Equiv.Perm
            {j : M // j ∈ exactRight coordinate partition}) : ℝ)))]
  apply Finset.sum_congr (by ext; simp only [mem_univ])
  intro leftCut _
  conv_rhs =>
    rw [← exactPrefixUniform_sum_mul
      (exactRight coordinate partition).card
      ((1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ)) *
        (1 / (Fintype.card
          (Equiv.Perm
            {j : M // j ∈ exactLeft coordinate partition}) : ℝ)) *
        (1 / (Fintype.card
          (Equiv.Perm
            {j : M // j ∈ exactRight coordinate partition}) : ℝ)) *
        (1 / ((exactLeft coordinate partition).card + 1 : ℝ)))]
  apply Finset.sum_congr (by ext; simp only [mem_univ])
  intro rightCut _
  simp only [exactSeedWeight]
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (congrArg₂ (· * ·) rfl ?_) ?_) rfl) rfl
  · exact congrArg (fun k : ℕ => 1 / (k : ℝ)) (exactFintypeCard_eq _ _)
  · exact congrArg (fun k : ℕ => 1 / (k : ℝ)) (exactFintypeCard_eq _ _)

end

section

open scoped BigOperators

/-- The numerical bound for has exponential. -/
def HasExponentialBound (v : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, v n ≤ C * Real.exp (-c * (n : ℝ))

/-- The has subexponential witness construction used in the quantum parallel-repetition argument. -/
def HasSubexponentialWitness (v : ℕ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ C : ℝ, 0 < C →
    ∃ n : ℕ, C * Real.exp (-c * (n : ℝ)) < v n

theorem not_hasExponentialBound_iff (v : ℕ → ℝ) :
    ¬ HasExponentialBound v ↔ HasSubexponentialWitness v := by
  simp only [HasExponentialBound, neg_mul, not_exists, not_and, not_forall, not_le,
    HasSubexponentialWitness]

theorem arbitrarily_large_witness_of_not_hasExponentialBound
    {v : ℕ → ℝ}
    (hv : ∀ n : ℕ, v n ≤ 1)
    (h_no_bound : ¬ HasExponentialBound v)
    {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ Real.exp (-c * (n : ℝ)) < v n := by
  have h_witness := (not_hasExponentialBound_iff v).mp h_no_bound
  obtain ⟨n, hn⟩ :=
    h_witness c hc (Real.exp (c * (N : ℝ))) (Real.exp_pos _)
  have hN : N < n := by
    by_contra h_not
    have hnN : n ≤ N := Nat.le_of_not_gt h_not
    have hnN_real : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
    have h_nonneg : 0 ≤ c * ((N : ℝ) - (n : ℝ)) :=
      mul_nonneg hc.le (sub_nonneg.mpr hnN_real)
    have h_lower :
        1 ≤ Real.exp (c * (N : ℝ)) * Real.exp (-c * (n : ℝ)) := by
      calc
        1 ≤ Real.exp (c * ((N : ℝ) - (n : ℝ))) :=
          Real.one_le_exp h_nonneg
        _ = Real.exp (c * (N : ℝ)) * Real.exp (-c * (n : ℝ)) := by
          rw [← Real.exp_add]
          congr 1
          ring
    linarith [hv n]
  refine ⟨n, hN, ?_⟩
  have h_prefactor : 1 ≤ Real.exp (c * (N : ℝ)) :=
    Real.one_le_exp (mul_nonneg hc.le (Nat.cast_nonneg _))
  calc
    Real.exp (-c * (n : ℝ)) =
        1 * Real.exp (-c * (n : ℝ)) := by rw [one_mul]
    _ ≤ Real.exp (c * (N : ℝ)) * Real.exp (-c * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right h_prefactor (Real.exp_pos _).le
    _ < v n := hn

end

section

open scoped BigOperators

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The standard exponential-decay statement for quantum parallel repetition. -/
def StandardQuantumParallelRepetition (G : Game X Y A B) : Prop :=
  entangledValue G < 1 →
    HasExponentialBound (repeatedEntangledValue G)

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker

theorem sum_positive_difference_eq_totalVariation
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp : (∑ i, p i) = 1)
    (hq : (∑ i, q i) = 1) :
    (∑ i, max (p i - q i) 0) = finiteTotalVariation p q := by
  classical
  have hpoint (x : ℝ) : max x 0 = (|x| + x) / 2 := by
    by_cases hx : 0 ≤ x
    · rw [max_eq_left hx, abs_of_nonneg hx]
      ring
    · have hxneg : x < 0 := lt_of_not_ge hx
      rw [max_eq_right hxneg.le, abs_of_neg hxneg]
      ring
  have hzero : (∑ i, (p i - q i)) = 0 := by
    rw [Finset.sum_sub_distrib, hp, hq, sub_self]
  unfold finiteTotalVariation
  simp_rw [hpoint]
  rw [← Finset.sum_div, Finset.sum_add_distrib, hzero, add_zero]

theorem finiteTotalVariation_comm
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) :
    finiteTotalVariation p q = finiteTotalVariation q p := by
  unfold finiteTotalVariation
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact abs_sub_comm (p i) (q i)

theorem expectation_le_add_totalVariation
    {ι : Type*} [Fintype ι]
    (p q f : ι → ℝ)
    (hp : (∑ i, p i) = 1)
    (hq : (∑ i, q i) = 1)
    (U : ℝ)
    (hfzero : ∀ i, 0 ≤ f i)
    (hfupper : ∀ i, f i ≤ U) :
    (∑ i, p i * f i) ≤
      (∑ i, q i * f i) + U * finiteTotalVariation p q := by
  classical
  have hterm (i : ι) :
      (p i - q i) * f i ≤ U * max (p i - q i) 0 := by
    by_cases hi : 0 ≤ p i - q i
    · rw [max_eq_left hi]
      linarith [mul_nonneg hi (sub_nonneg.mpr (hfupper i))]
    · have hineg : p i - q i < 0 := lt_of_not_ge hi
      rw [max_eq_right hineg.le]
      simp only [mul_zero]
      exact mul_nonpos_of_nonpos_of_nonneg hineg.le (hfzero i)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  have hpositive := sum_positive_difference_eq_totalVariation p q hp hq
  calc
    (∑ i, p i * f i) =
        (∑ i, q i * f i) + ∑ i, (p i - q i) * f i := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ ≤ (∑ i, q i * f i) +
          ∑ i, U * max (p i - q i) 0 := by
      linarith
    _ = (∑ i, q i * f i) +
          U * finiteTotalVariation p q := by
      rw [← Finset.mul_sum, hpositive]

theorem winning_expectation_transfer
    {ι : Type*} [Fintype ι]
    (p q win : ι → ℝ)
    (hp : (∑ i, p i) = 1)
    (hq : (∑ i, q i) = 1)
    (hzero : ∀ i, 0 ≤ win i)
    (hone : ∀ i, win i ≤ 1) :
    (∑ i, q i * win i) - finiteTotalVariation p q ≤
      ∑ i, p i * win i := by
  have h := expectation_le_add_totalVariation
    q p win hq hp (1 : ℝ) hzero hone
  rw [← finiteTotalVariation_comm p q] at h
  norm_num at h ⊢
  linarith

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

section ActualSharedFlag

variable {X Y A B dA dB J : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
variable [Fintype J] [DecidableEq J]

/-- The measurement effect for pure verifier. -/
def pureVerifierEffect
    (G : Game X Y A B)
    (z : EuclideanSpace ℂ (dA × dB)) (hz : ‖z‖ = 1)
    (PA : X → POVM A dA) (PB : Y → POVM B dB)
    (x : X) (y : Y) : Matrix (dA × dB) (dA × dB) ℂ :=
  (pureVectorStrategy G z hz PA PB).winningEffect x y

theorem pureVectorWinningProbability_eq
    (G : Game X Y A B)
    (z : EuclideanSpace ℂ (dA × dB)) (hz : ‖z‖ = 1)
    (PA : X → POVM A dA) (PB : Y → POVM B dB) :
    (pureVectorStrategy G z hz PA PB).winProbability =
      ∑ x : X, ∑ y : Y, G.questionWeight x y *
        quadraticExpectation
          (Matrix.toEuclideanCLM (n := dA × dB) (𝕜 := ℂ)
            (pureVerifierEffect G z hz PA PB x y)) z := by
  classical
  rw [(pureVectorStrategy G z hz PA PB).winProbability_eq_winningEffect_born]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  exact pureDensityMatrix_trace_mul z hz
    (pureVerifierEffect G z hz PA PB x y)

/-- The probability weight for flagged question. -/
def flaggedQuestionWeight
    (G : Game X Y A B) (flagWeight : J → ℝ)
    (ω : J × (X × Y)) : ℝ :=
  flagWeight ω.1 * G.questionWeight ω.2.1 ω.2.2

omit [Fintype J] [DecidableEq J] in
theorem flaggedQuestionWeight_nonneg
    (G : Game X Y A B) (flagWeight : J → ℝ)
    (nonnegative : ∀ j, 0 ≤ flagWeight j)
    (ω : J × (X × Y)) :
    0 ≤ flaggedQuestionWeight G flagWeight ω :=
  mul_nonneg (nonnegative ω.1)
    (G.weight_nonneg ω.2.1 ω.2.2)

omit [DecidableEq J] in
theorem flaggedQuestionWeight_sum
    (G : Game X Y A B) (flagWeight : J → ℝ)
    (normalized : (∑ j, flagWeight j) = 1) :
    (∑ ω : J × (X × Y),
      flaggedQuestionWeight G flagWeight ω) = 1 := by
  classical
  simp only [flaggedQuestionWeight, Fintype.sum_prod_type, ← mul_sum, G.weight_normalized,
    mul_one, normalized]

end ActualSharedFlag

end

section

open Filter
open scoped Topology

/-- A universal upper bound for the accumulated rounding error. -/
def universalErrorCeiling (K₀ : ℝ) : ℝ :=
  K₀ * (1 + (2 : ℝ) ^ (1 / 6 : ℝ)) + 2

/-- The combined information-theoretic loss from the sampling steps. -/
def totalSamplingLoss (K₀ α η lam : ℝ) : ℝ :=
  5 * lam +
    2 * (K₀ * (α ^ (1 / 12 : ℝ) +
        (32 * η) ^ (1 / 12 : ℝ)) +
      Real.sqrt (8 * η) + universalErrorCeiling K₀ * lam)

/-- The numerical bound for rounded winning lower. -/
def roundedWinningLowerBound (ε K₀ α η lam : ℝ) : ℝ :=
  1 - ε / 2 - totalSamplingLoss K₀ α η lam

theorem totalSamplingLoss_tendsto_zero
    {ι : Type*} {l : Filter ι}
    (K₀ : ℝ) {α η lam : ι → ℝ}
    (hα : Tendsto α l (𝓝 0))
    (hη : Tendsto η l (𝓝 0))
    (hlam : Tendsto lam l (𝓝 0)) :
    Tendsto (fun i => totalSamplingLoss K₀ (α i) (η i) (lam i))
      l (𝓝 0) := by
  have hαroot :
      Tendsto (fun i => (α i) ^ (1 / 12 : ℝ)) l (𝓝 0) :=
    hα.rpow_const_nhds_zero (by norm_num)
  have hηscaled : Tendsto (fun i => 32 * η i) l (𝓝 0) := by
    simpa only [mul_zero] using hη.const_mul (32 : ℝ)
  have hηroot :
      Tendsto (fun i => (32 * η i) ^ (1 / 12 : ℝ)) l (𝓝 0) :=
    hηscaled.rpow_const_nhds_zero (by norm_num)
  have hηeight : Tendsto (fun i => 8 * η i) l (𝓝 0) := by
    simpa only [mul_zero] using hη.const_mul (8 : ℝ)
  have hsqrt : Tendsto (fun i => Real.sqrt (8 * η i)) l (𝓝 0) := by
    simpa only [Nat.ofNat_nonneg, Real.sqrt_mul, Real.sqrt_zero] using hηeight.sqrt
  have hquantum :
      Tendsto
        (fun i => K₀ * ((α i) ^ (1 / 12 : ℝ) +
          (32 * η i) ^ (1 / 12 : ℝ))) l (𝓝 0) := by
    simpa only [one_div, add_zero, mul_zero] using (hαroot.add hηroot).const_mul K₀
  have hceiling :
      Tendsto (fun i => universalErrorCeiling K₀ * lam i)
        l (𝓝 0) := by
    simpa only [mul_zero] using hlam.const_mul (universalErrorCeiling K₀)
  have hinner :
      Tendsto
        (fun i => K₀ * ((α i) ^ (1 / 12 : ℝ) +
            (32 * η i) ^ (1 / 12 : ℝ)) +
          Real.sqrt (8 * η i) + universalErrorCeiling K₀ * lam i)
        l (𝓝 0) := by
    simpa only [one_div, Nat.ofNat_nonneg, Real.sqrt_mul,
      add_zero] using (hquantum.add hsqrt).add hceiling
  have hclassical : Tendsto (fun i => 5 * lam i) l (𝓝 0) := by
    simpa only [mul_zero] using hlam.const_mul (5 : ℝ)
  have hdouble :
      Tendsto
        (fun i => 2 *
          (K₀ * ((α i) ^ (1 / 12 : ℝ) +
              (32 * η i) ^ (1 / 12 : ℝ)) +
            Real.sqrt (8 * η i) + universalErrorCeiling K₀ * lam i))
        l (𝓝 0) := by
    simpa only [one_div, Nat.ofNat_nonneg, Real.sqrt_mul, mul_zero] using hinner.const_mul (2 : ℝ)
  simpa only [totalSamplingLoss, one_div, Nat.ofNat_nonneg, Real.sqrt_mul,
    add_zero] using hclassical.add hdouble

theorem totalSamplingLoss_eventually_lt
    {ι : Type*} {l : Filter ι}
    (K₀ : ℝ) {α η lam : ι → ℝ}
    (hα : Tendsto α l (𝓝 0))
    (hη : Tendsto η l (𝓝 0))
    (hlam : Tendsto lam l (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, totalSamplingLoss K₀ (α i) (η i) (lam i) < ε :=
  (totalSamplingLoss_tendsto_zero K₀ hα hη hlam).eventually
    (gt_mem_nhds hε)

theorem source_equation_twenty_nine_contradiction
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B)
    (S : Strategy G)
    (K₀ α η lam : ℝ)
    (hbound :
      roundedWinningLowerBound (1 - entangledValue G)
        K₀ α η lam ≤ S.winProbability)
    (herror :
      totalSamplingLoss K₀ α η lam < (1 - entangledValue G) / 2) :
    False := by
  have hsup : S.winProbability ≤ entangledValue G := by
    unfold entangledValue
    exact le_csSup (winProbabilities_bddAbove G) ⟨S, rfl⟩
  unfold roundedWinningLowerBound at hbound
  linarith

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem matched_payoff_discard_le
    {ι : Type*} [Fintype ι]
    (weight payoff : ι → ℝ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (payoff_le_one : ∀ i, payoff i ≤ 1)
    (matched : ι → Bool) :
    (∑ i, weight i * payoff i) -
        (∑ i, weight i * if matched i then 0 else 1) ≤
      ∑ i, weight i * if matched i then payoff i else 0 := by
  classical
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : matched i = true
  · simp only [hi, ↓reduceIte, mul_zero, sub_zero, Std.le_refl]
  · have hone := payoff_le_one i
    simp only [Bool.not_eq_true] at hi
    simp only [hi, Bool.false_eq_true, ↓reduceIte, mul_one, mul_zero, tsub_le_iff_right, zero_add,
      ge_iff_le]
    linarith [mul_nonneg (nonnegative i)
      (sub_nonneg.mpr hone)]

end

section

open scoped BigOperators

theorem squared_state_triangle
    {E : Type*} [NormedAddCommGroup E]
    (gamma psi phi : E) :
    ‖gamma - phi‖ ^ 2 ≤
      2 * (‖gamma - psi‖ ^ 2 + ‖psi - phi‖ ^ 2) := by
  have hsplit : gamma - phi = (gamma - psi) + (psi - phi) := by
    abel
  have htriangle :
      ‖gamma - phi‖ ≤ ‖gamma - psi‖ + ‖psi - phi‖ := by
    rw [hsplit]
    exact norm_add_le _ _
  have hnonneg : 0 ≤ ‖gamma - phi‖ := norm_nonneg _
  have ha : 0 ≤ ‖gamma - psi‖ := norm_nonneg _
  have hb : 0 ≤ ‖psi - phi‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖gamma - psi‖ - ‖psi - phi‖)]

theorem source_equation_twenty_one
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    (weight : ι → ℝ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (gamma psi phi : ι → E)
    (η : ℝ)
    (hgamma : (∑ i, weight i * ‖gamma i - psi i‖ ^ 2) ≤ 8 * η)
    (hphi : (∑ i, weight i * ‖psi i - phi i‖ ^ 2) ≤ 8 * η) :
    (∑ i, weight i * ‖gamma i - phi i‖ ^ 2) ≤ 32 * η := by
  classical
  calc
    (∑ i, weight i * ‖gamma i - phi i‖ ^ 2) ≤
        ∑ i, weight i *
          (2 * (‖gamma i - psi i‖ ^ 2 + ‖psi i - phi i‖ ^ 2)) := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left
            (squared_state_triangle (gamma i) (psi i) (phi i))
            (nonnegative i)
    _ = 2 *
          ((∑ i, weight i * ‖gamma i - psi i‖ ^ 2) +
           (∑ i, weight i * ‖psi i - phi i‖ ^ 2)) := by
          calc
            (∑ i, weight i *
              (2 * (‖gamma i - psi i‖ ^ 2 + ‖psi i - phi i‖ ^ 2))) =
                ∑ i, (2 * (weight i * ‖gamma i - psi i‖ ^ 2) +
                  2 * (weight i * ‖psi i - phi i‖ ^ 2)) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    ring
            _ = _ := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
              ring
    _ ≤ 32 * η := by linarith

theorem weighted_rpow_mean_le
    {ι : Type*} [Fintype ι]
    (weight value : ι → ℝ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (normalized : (∑ i, weight i) = 1)
    (value_nonnegative : ∀ i, 0 ≤ value i)
    {r : ℝ} (hrzero : 0 ≤ r) (hrone : r ≤ 1) :
    (∑ i, weight i * value i ^ r) ≤
      (∑ i, weight i * value i) ^ r := by
  classical
  simpa only [smul_eq_mul] using
    (Real.concaveOn_rpow hrzero hrone).le_map_sum
      (t := Finset.univ)
      (w := weight)
      (p := value)
      (fun i _ => nonnegative i)
      normalized
      (fun i _ => value_nonnegative i)

end

section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder


theorem fullHistoryRemaining_insert_conditioned
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n) :
    fullHistoryRemaining n (insert i D) L =
      fullHistoryRemaining n D (insert i L) := by
  ext j
  simp only [fullHistoryRemaining, Finset.mem_sdiff,
    Finset.mem_univ, true_and, Finset.mem_insert]
  tauto

private def fullHistoryRemainingInsertedEquiv
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n) :
    {j : Fin n // j ∈ fullHistoryRemaining n (insert i D) L} ≃
      {j : Fin n // j ∈ fullHistoryRemaining n D (insert i L)} :=
  Equiv.subtypeEquivRight fun j => by
    rw [fullHistoryRemaining_insert_conditioned D L i]

private def fullCoordinateAnswerExtension
    {T : Type*} {n : ℕ}
    (D : Finset (Fin n)) (i : Fin n)
    (α : {j : Fin n // j ∈ D} → T) (a : T) :
    {j : Fin n // j ∈ insert i D} → T := by
  classical
  intro j
  by_cases hj : (j : Fin n) = i
  · exact a
  · exact α ⟨j, (Finset.mem_insert.mp j.property).resolve_left hj⟩

private def fullCoordinateAnswerExtensionEquiv
    {T : Type*} {n : ℕ}
    (D : Finset (Fin n)) (i : Fin n) (hiD : i ∉ D) :
    (({j : Fin n // j ∈ D} → T) × T) ≃
      ({j : Fin n // j ∈ insert i D} → T) where
  toFun t := fullCoordinateAnswerExtension D i t.1 t.2
  invFun α :=
    (fun j => α ⟨j, Finset.mem_insert_of_mem j.property⟩,
      α ⟨i, Finset.mem_insert_self i D⟩)
  left_inv t := by
    rcases t with ⟨α, a⟩
    apply Prod.ext
    · funext j
      have hj : (j : Fin n) ≠ i := by
        intro he
        exact hiD (he ▸ j.property)
      simp only [fullCoordinateAnswerExtension, hj, ↓reduceDIte, Subtype.coe_eta]
    · simp only [fullCoordinateAnswerExtension, ↓reduceDIte]
  right_inv α := by
    funext j
    by_cases hj : (j : Fin n) = i
    · have hjsub :
          j = (⟨i, Finset.mem_insert_self i D⟩ :
            {j : Fin n // j ∈ insert i D}) := Subtype.ext hj
      subst j
      simp only [fullCoordinateAnswerExtension, ↓reduceDIte]
    · simp only [fullCoordinateAnswerExtension, hj, ↓reduceDIte, Subtype.coe_eta]

private def fullCoordinateInsertedHistory
    {X Y : Type*}
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y) :
    FullSubsetHistory X Y n (insert i D) L := by
  classical
  refine ⟨
    fullCoordinateAnswerExtension D i r.aliceConditioned x,
    fullCoordinateAnswerExtension D i r.bobConditioned y,
    r.aliceRevealed,
    fun j => r.bobRemaining ⟨j, ?_⟩⟩
  rw [← fullHistoryRemaining_insert_conditioned D L i]
  exact j.property

private def fullCoordinateBaseOfInsertedHistory
    {X Y : Type*}
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (h : FullSubsetHistory X Y n (insert i D) L) :
    FullCoordinateRevealHistory X Y n D L i := by
  refine ⟨
    fun j => h.aliceConditioned
      ⟨j, Finset.mem_insert_of_mem j.property⟩,
    fun j => h.bobConditioned
      ⟨j, Finset.mem_insert_of_mem j.property⟩,
    h.aliceRevealed,
    fun j => h.bobRemaining ⟨j, ?_⟩⟩
  rw [fullHistoryRemaining_insert_conditioned D L i]
  exact j.property

private def fullCoordinateInsertedHistoryEquiv
    {X Y : Type*}
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) :
    (FullCoordinateRevealHistory X Y n D L i × X × Y) ≃
      FullSubsetHistory X Y n (insert i D) L where
  toFun t := fullCoordinateInsertedHistory D L i t.1 t.2.1 t.2.2
  invFun h :=
    (fullCoordinateBaseOfInsertedHistory D L i h,
      h.aliceConditioned ⟨i, Finset.mem_insert_self i D⟩,
      h.bobConditioned ⟨i, Finset.mem_insert_self i D⟩)
  left_inv t := by
    rcases t with ⟨r, x, y⟩
    apply Prod.ext
    · apply FullCoordinateRevealHistory.ext
      · funext j
        have hj : (j : Fin n) ≠ i := by
          intro he
          exact hiD (he ▸ j.property)
        simp only [fullCoordinateBaseOfInsertedHistory, fullCoordinateInsertedHistory,
          fullCoordinateAnswerExtension, Subtype.coe_eta, dite_eq_ite, hj, ↓reduceIte]
      · funext j
        have hj : (j : Fin n) ≠ i := by
          intro he
          exact hiD (he ▸ j.property)
        simp only [fullCoordinateBaseOfInsertedHistory, fullCoordinateInsertedHistory,
          fullCoordinateAnswerExtension, Subtype.coe_eta, dite_eq_ite, hj, ↓reduceIte]
      · rfl
      · rfl
    · apply Prod.ext <;>
        simp only [fullCoordinateInsertedHistory, fullCoordinateAnswerExtension, ↓reduceDIte]
  right_inv h := by
    apply FullSubsetHistory.ext
    · funext j
      by_cases hj : (j : Fin n) = i
      · have hjsub :
            j = (⟨i, Finset.mem_insert_self i D⟩ :
              {j : Fin n // j ∈ insert i D}) := Subtype.ext hj
        subst j
        simp only [fullCoordinateInsertedHistory, fullCoordinateBaseOfInsertedHistory,
          Subtype.coe_eta, fullCoordinateAnswerExtension, ↓reduceDIte]
      · simp only [fullCoordinateInsertedHistory, fullCoordinateBaseOfInsertedHistory,
          Subtype.coe_eta, fullCoordinateAnswerExtension, hj, ↓reduceDIte]
    · funext j
      by_cases hj : (j : Fin n) = i
      · have hjsub :
            j = (⟨i, Finset.mem_insert_self i D⟩ :
              {j : Fin n // j ∈ insert i D}) := Subtype.ext hj
        subst j
        simp only [fullCoordinateInsertedHistory, fullCoordinateBaseOfInsertedHistory,
          Subtype.coe_eta, fullCoordinateAnswerExtension, ↓reduceDIte]
      · simp only [fullCoordinateInsertedHistory, fullCoordinateBaseOfInsertedHistory,
          Subtype.coe_eta, fullCoordinateAnswerExtension, hj, ↓reduceDIte]
    · rfl
    · rfl

section InsertedWeights

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem fullCoordinateInsertedHistory_weight
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n) (hiD : i ∉ D)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y) :
    fullHistoryWeight G (fullCoordinateInsertedHistory D L i r x y) =
      fullCoordinateBaseWeight G D L i r * G.questionWeight x y := by
  classical
  have hremaining :
      (∏ j : {j : Fin n //
        j ∈ fullHistoryRemaining n (insert i D) L},
        G.marginalY
          ((fullCoordinateInsertedHistory D L i r x y).bobRemaining j)) =
      ∏ j : {j : Fin n //
        j ∈ fullHistoryRemaining n D (insert i L)},
        G.marginalY (r.bobRemaining j) := by
    let e := fullHistoryRemainingInsertedEquiv D L i
    calc
      (∏ j : {j : Fin n //
        j ∈ fullHistoryRemaining n (insert i D) L},
        G.marginalY
          ((fullCoordinateInsertedHistory D L i r x y).bobRemaining j)) =
        ∏ j : {j : Fin n //
          j ∈ fullHistoryRemaining n (insert i D) L},
          G.marginalY (r.bobRemaining (e j)) := by
            apply Finset.prod_congr rfl
            intro j _
            rfl
      _ = _ := e.prod_comp (fun j => G.marginalY (r.bobRemaining j))
  have hpair (j : {j : Fin n // j ∈ D}) :
      G.questionWeight
        ((fullCoordinateInsertedHistory D L i r x y).aliceConditioned
          ⟨j, Finset.mem_insert_of_mem j.property⟩)
        ((fullCoordinateInsertedHistory D L i r x y).bobConditioned
          ⟨j, Finset.mem_insert_of_mem j.property⟩) =
      G.questionWeight (r.aliceConditioned j) (r.bobConditioned j) := by
    have hj : (j : Fin n) ≠ i := by
      intro he
      exact hiD (he ▸ j.property)
    simp only [fullCoordinateInsertedHistory, fullCoordinateAnswerExtension, hj, ↓reduceDIte,
      Subtype.coe_eta]
  unfold fullHistoryWeight fullCoordinateBaseWeight
  change
    (∏ j : {j : Fin n // j ∈ insert i D},
      G.questionWeight
        ((fullCoordinateInsertedHistory D L i r x y).aliceConditioned j)
        ((fullCoordinateInsertedHistory D L i r x y).bobConditioned j)) *
    (∏ j : {j : Fin n // j ∈ L},
      G.marginalX (r.aliceRevealed j)) *
    (∏ j : {j : Fin n //
      j ∈ fullHistoryRemaining n (insert i D) L},
      G.marginalY
        ((fullCoordinateInsertedHistory D L i r x y).bobRemaining j)) = _
  rw [finsetSubtype_prod_insert D i hiD]
  rw [hremaining]
  simp_rw [hpair]
  simp only [fullCoordinateInsertedHistory, fullCoordinateAnswerExtension, ↓reduceDIte,
    univ_eq_attach]
  ring

theorem conditionedAliceEffect_insert_eq_coordinate
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (i : Fin n) (hiD : i ∉ D)
    (α : {j : Fin n // j ∈ D} → A)
    (a : A) (xs : Fin n → X) :
    conditionedAliceEffect G n S (insert i D)
      (fullCoordinateAnswerExtension D i α a) xs =
      conditionedAliceCoordinateEffect G n S D α xs i a := by
  classical
  unfold conditionedAliceEffect conditionedAliceCoordinateEffect
  apply Finset.sum_congr rfl
  intro answers _
  have hiff :
      (∀ (j : Fin n) (hj : j ∈ insert i D),
        answers j = fullCoordinateAnswerExtension D i α a ⟨j, hj⟩) ↔
      ((∀ (j : Fin n) (hj : j ∈ D), answers j = α ⟨j, hj⟩) ∧
        answers i = a) := by
    constructor
    · intro h
      constructor
      · intro j hj
        have hji : j ≠ i := by
          intro he
          exact hiD (he ▸ hj)
        simpa only [fullCoordinateAnswerExtension, hji, ↓reduceDIte]
          using h j (Finset.mem_insert_of_mem hj)
      · simpa only [fullCoordinateAnswerExtension, ↓reduceDIte]
          using h i (Finset.mem_insert_self i D)
    · rintro ⟨hD, ha⟩ j hj
      by_cases hji : j = i
      · subst j
        simpa only [fullCoordinateAnswerExtension, ↓reduceDIte] using ha
      · have hjD := (Finset.mem_insert.mp hj).resolve_left hji
        simpa only [fullCoordinateAnswerExtension, hji, ↓reduceDIte] using hD j hjD
  by_cases h :
      ∀ (j : Fin n) (hj : j ∈ insert i D),
        answers j = fullCoordinateAnswerExtension D i α a ⟨j, hj⟩
  · simp only [ite_eq_left h, ite_eq_left (hiff.mp h)]
  · have hnot := mt hiff.mpr h
    simp only [ite_eq_right h, ite_eq_right hnot]

theorem conditionedBobEffect_insert_eq_coordinate
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (i : Fin n) (hiD : i ∉ D)
    (β : {j : Fin n // j ∈ D} → B)
    (b : B) (ys : Fin n → Y) :
    conditionedBobEffect G n S (insert i D)
      (fullCoordinateAnswerExtension D i β b) ys =
      conditionedBobCoordinateEffect G n S D β ys i b := by
  classical
  unfold conditionedBobEffect conditionedBobCoordinateEffect
  apply Finset.sum_congr rfl
  intro answers _
  have hiff :
      (∀ (j : Fin n) (hj : j ∈ insert i D),
        answers j = fullCoordinateAnswerExtension D i β b ⟨j, hj⟩) ↔
      ((∀ (j : Fin n) (hj : j ∈ D), answers j = β ⟨j, hj⟩) ∧
        answers i = b) := by
    constructor
    · intro h
      constructor
      · intro j hj
        have hji : j ≠ i := by
          intro he
          exact hiD (he ▸ hj)
        simpa only [fullCoordinateAnswerExtension, hji, ↓reduceDIte]
          using h j (Finset.mem_insert_of_mem hj)
      · simpa only [fullCoordinateAnswerExtension, ↓reduceDIte]
          using h i (Finset.mem_insert_self i D)
    · rintro ⟨hD, hb⟩ j hj
      by_cases hji : j = i
      · subst j
        simpa only [fullCoordinateAnswerExtension, ↓reduceDIte] using hb
      · have hjD := (Finset.mem_insert.mp hj).resolve_left hji
        simpa only [fullCoordinateAnswerExtension, hji, ↓reduceDIte] using hD j hjD
  by_cases h :
      ∀ (j : Fin n) (hj : j ∈ insert i D),
        answers j = fullCoordinateAnswerExtension D i β b ⟨j, hj⟩
  · simp only [ite_eq_left h, ite_eq_left (hiff.mp h)]
  · have hnot := mt hiff.mpr h
    simp only [ite_eq_right h, ite_eq_right hnot]

end InsertedWeights

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem conditionedCoordinateEffects_born_expansion
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {j : Fin n // j ∈ D} → A)
    (β : {j : Fin n // j ∈ D} → B)
    (xs : Fin n → X) (ys : Fin n → Y)
    (i : Fin n) (a : A) (b : B) :
    bornTracePairing S.state.matrix
        (conditionedAliceCoordinateEffect G n S D α xs i a)
        (conditionedBobCoordinateEffect G n S D β ys i b) =
      ∑ aa : Fin n → A, ∑ bb : Fin n → B,
        if (∀ (j : Fin n) (hj : j ∈ D), aa j = α ⟨j, hj⟩) ∧
          aa i = a then
          if (∀ (j : Fin n) (hj : j ∈ D), bb j = β ⟨j, hj⟩) ∧
            bb i = b then S.outcomeProbability xs ys aa bb else 0
        else 0 := by
  classical
  simp only [conditionedAliceCoordinateEffect,
    conditionedBobCoordinateEffect,
    map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro aa _
  split_ifs with ha
  · apply Finset.sum_congr rfl
    intro bb _
    split_ifs with hb
    · rfl
    · exact map_zero _
  · simp only [map_zero, LinearMap.zero_apply, sum_const_zero]

end

section

open scoped BigOperators ComplexConjugate ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

/-- The state vector representing normalized pure. -/
def normalizedPureVector
    {d : Type*} [Fintype d]
    (z : EuclideanSpace ℂ d) : EuclideanSpace ℂ d :=
  ((‖z‖⁻¹ : ℝ) : ℂ) • z

theorem quadraticExpectation_normalizedPureVector
    {d : Type*} [Fintype d]
    (W : EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d)
    (z : EuclideanSpace ℂ d) :
    quadraticExpectation W (normalizedPureVector z) =
      quadraticExpectation W z / ‖z‖ ^ 2 := by
  unfold quadraticExpectation normalizedPureVector
  rw [map_smul, inner_smul_left, inner_smul_right]
  simp only [ofReal_inv, map_inv₀, conj_ofReal, mul_re, inv_re, ofReal_re, normSq_ofReal,
    div_eq_mul_inv, _root_.mul_inv_rev, inv_im, ofReal_im, neg_zero, zero_mul, sub_zero, mul_im,
    add_zero, pow_two]
  by_cases hz : ‖z‖ = 0
  · simp only [hz, _root_.inv_zero, mul_zero, zero_mul]
  · field_simp

end

section

open scoped BigOperators

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exists_repeatedStrategy_of_lt_entangledValue
    (G : Game X Y A B) {n : ℕ} {r : ℝ}
    (hr : 0 < r)
    (hvalue : r < repeatedEntangledValue G n) :
    ∃ S : Strategy (G.repeat n), r < S.winProbability := by
  let values : Set ℝ :=
    Set.range (Strategy.winProbability (G := G.repeat n))
  have hnonempty : values.Nonempty := by
    by_contra hempty
    have heq : values = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    have hzero : repeatedEntangledValue G n = 0 := by
      change sSup values = 0
      rw [heq, Real.sSup_empty]
    linarith
  have hs : r < sSup values := by
    exact hvalue
  obtain ⟨v, ⟨S, hS⟩, hv⟩ := exists_lt_of_lt_csSup hnonempty hs
  subst v
  exact ⟨S, hv⟩

theorem exists_purifiedRepeatedStrategy_of_lt_entangledValue
    (G : Game X Y A B) {n : ℕ} {r : ℝ}
    (hr : 0 < r)
    (hvalue : r < repeatedEntangledValue G n) :
    ∃ S : Strategy (G.repeat n),
      r < (purifiedStrategy S).winProbability := by
  obtain ⟨S, hS⟩ :=
    exists_repeatedStrategy_of_lt_entangledValue G hr hvalue
  refine ⟨S, ?_⟩
  rwa [purifiedStrategy_winProbability]

theorem arbitrarily_large_purifiedRepeatedStrategy_of_subexponentialWitness
    (G : Game X Y A B)
    (hwitness : HasSubexponentialWitness (repeatedEntangledValue G))
    {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∃ n : ℕ, N < n ∧
      ∃ S : Strategy (G.repeat n),
        Real.exp (-c * (n : ℝ)) <
          (purifiedStrategy S).winProbability := by
  have hno : ¬ HasExponentialBound (repeatedEntangledValue G) :=
    (not_hasExponentialBound_iff (repeatedEntangledValue G)).mpr hwitness
  have hbounded (n : ℕ) : repeatedEntangledValue G n ≤ 1 :=
    entangledValue_le_one (G.repeat n)
  obtain ⟨n, hn, hvalue⟩ :=
    arbitrarily_large_witness_of_not_hasExponentialBound
      hbounded hno hc N
  exact ⟨n, hn,
    exists_purifiedRepeatedStrategy_of_lt_entangledValue G
      (Real.exp_pos _) hvalue⟩

theorem postselection_log_cost_le
    {θ p : ℝ} (hθ : 0 < θ) (hθp : θ ≤ p) :
    Real.log (1 / p) ≤ Real.log (1 / θ) := by
  have hp : 0 < p := lt_of_lt_of_le hθ hθp
  have hinv : 1 / p ≤ 1 / θ := by
    exact one_div_le_one_div_of_le hθ hθp
  exact Real.log_le_log (by positivity : 0 < 1 / p) hinv

theorem greedy_terminal_of_log_cost
    {θ η : ℝ} {T : ℕ}
    (hθ : 0 < θ)
    (hη_one : η ≤ 1)
    (hcost : Real.log (1 / θ) < η * (T : ℝ)) :
    (1 - η) ^ T < θ := by
  have hbase : 1 - η ≤ Real.exp (-η) := by
    have h := Real.add_one_le_exp (-η)
    linarith
  have hpow :
      (1 - η) ^ T ≤ Real.exp (-η) ^ T :=
    pow_le_pow_left₀ (sub_nonneg.mpr hη_one) hbase T
  have hlog : -η * (T : ℝ) < Real.log θ := by
    rw [one_div, Real.log_inv] at hcost
    linarith
  calc
    (1 - η) ^ T ≤ Real.exp (-η) ^ T := hpow
    _ = Real.exp (-η * (T : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ < θ := (Real.exp_lt_exp.mpr hlog).trans_eq
      (Real.exp_log hθ)

theorem divisorStopping_nat_bound
    {n q : ℕ} (hq : 0 < q) (hqn : q ≤ n) :
    n < 2 * (n / q) * q := by
  have hT : 0 < n / q := by
    apply (Nat.le_div_iff_mul_le hq).2
    simpa only [Nat.succ_eq_add_one, zero_add, one_mul] using hqn
  have hnext : n < (n / q + 1) * q := by
    exact (Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_self (n / q))
  have hfactor : n / q + 1 ≤ 2 * (n / q) := by
    omega
  exact hnext.trans_le (Nat.mul_le_mul_right q hfactor)

theorem sourceRate_mul_lt_divisorStopping
    {n q : ℕ} (hq : 0 < q) (hqn : q ≤ n)
    {η : ℝ} (hη : 0 < η) :
    (η / (4 * (q : ℝ))) * (n : ℝ) <
      η * ((n / q : ℕ) : ℝ) := by
  have hcast :
      (n : ℝ) < 2 * ((n / q : ℕ) : ℝ) * (q : ℝ) := by
    exact_mod_cast divisorStopping_nat_bound hq hqn
  have hqreal : 0 < (q : ℝ) := by exact_mod_cast hq
  have hT : 0 < ((n / q : ℕ) : ℝ) := by
    exact_mod_cast ((Nat.le_div_iff_mul_le hq).2 (by simpa only [one_mul] using hqn) :
      1 ≤ n / q)
  have hrate : 0 < η / (4 * (q : ℝ)) := by positivity
  calc
    (η / (4 * (q : ℝ))) * (n : ℝ) <
        (η / (4 * (q : ℝ))) *
          (2 * ((n / q : ℕ) : ℝ) * (q : ℝ)) :=
      mul_lt_mul_of_pos_left hcast hrate
    _ = η * ((n / q : ℕ) : ℝ) / 2 := by
      field_simp
      ring
    _ < η * ((n / q : ℕ) : ℝ) := by
      have hpositive : 0 < η * ((n / q : ℕ) : ℝ) :=
        mul_pos hη hT
      linarith

theorem repeatedStrategy_exists_divisor_greedy_conditioning
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    {η : ℝ} {q : ℕ}
    (hη : 0 < η) (hη_one : η ≤ 1)
    (hq : 0 < q) (hqn : q ≤ n)
    (hwitness :
      Real.exp (-(η / (4 * (q : ℝ))) * (n : ℝ)) <
        S.winProbability) :
    ∃ D : Finset (Fin n),
      D.card < n / q ∧
      S.winProbability ≤
        (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent
            (repeatedCoordinateWin G n) D) ∧
      (∑ i ∈ Finset.univ \ D,
        FiniteEventLaw.failureMass
          (strategyEventLaw (G.repeat n) S)
          (repeatedCoordinateWin G n) D i)
        <
      ((Finset.univ \ D).card : ℝ) *
        (η * (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent
            (repeatedCoordinateWin G n) D)) := by
  have hθ : 0 < S.winProbability :=
    lt_trans (Real.exp_pos _) hwitness
  have hlog :
      Real.log (1 / S.winProbability) <
        (η / (4 * (q : ℝ))) * (n : ℝ) := by
    have hlog' :
        -(η / (4 * (q : ℝ))) * (n : ℝ) <
          Real.log S.winProbability :=
      (Real.lt_log_iff_exp_lt hθ).mpr hwitness
    rw [one_div, Real.log_inv]
    linarith
  have hterminal :
      (1 - η) ^ (n / q) < S.winProbability := by
    apply greedy_terminal_of_log_cost hθ hη_one
    exact hlog.trans (sourceRate_mul_lt_divisorStopping hq hqn hη)
  apply repeatedStrategy_exists_greedy_conditioning
    G n S hθ hη hη_one (Nat.div_le_self n q) (le_refl _) hterminal

theorem divisor_greedy_card_mul_lt
    {n q : ℕ} (hq : 0 < q)
    {D : Finset (Fin n)} (hD : D.card < n / q) :
    D.card * q < n := by
  have hmul : D.card * q < (n / q) * q :=
    Nat.mul_lt_mul_of_pos_right hD hq
  exact hmul.trans_le (Nat.div_mul_le_self n q)

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private structure SourceHistoryFlag
    (X Y A B : Type*)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) where
  permutation : SourceRemainingPermutation D
  position : Fin (Finset.univ \ D).card
  history : FullCoordinateRevealHistory X Y n D
    (sourceRemainingPermutationPrefix D permutation position.castSucc)
    (sourceRemainingPermutationCoordinate D permutation position)
  aliceAnswer : {i : Fin n // i ∈ D} → A
  bobAnswer : {i : Fin n // i ∈ D} → B

private abbrev SourceHistoryFlagTuple
    (X Y A B : Type*)
    {n : ℕ} (D : Finset (Fin n)) :=
  Σ π : SourceRemainingPermutation D,
    Σ k : Fin (Finset.univ \ D).card,
      FullCoordinateRevealHistory X Y n D
        (sourceRemainingPermutationPrefix D π k.castSucc)
        (sourceRemainingPermutationCoordinate D π k) ×
      ({i : Fin n // i ∈ D} → A) ×
      ({i : Fin n // i ∈ D} → B)

private def sourceHistoryFlagEquiv
    {n : ℕ} (D : Finset (Fin n)) :
    SourceHistoryFlag X Y A B D ≃ SourceHistoryFlagTuple X Y A B D where
  toFun r := ⟨r.permutation, r.position,
    r.history, r.aliceAnswer, r.bobAnswer⟩
  invFun t := ⟨t.1, t.2.1,
    t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩
  left_inv r := by cases r; rfl
  right_inv t := by
    rcases t with ⟨π, k, r, α, β⟩
    rfl

noncomputable instance sourceHistoryFlagFintype
    {n : ℕ} (D : Finset (Fin n)) :
    Fintype (SourceHistoryFlag X Y A B D) := by
  classical
  exact Fintype.ofEquiv (SourceHistoryFlagTuple X Y A B D)
    (sourceHistoryFlagEquiv (X := X) (Y := Y)
      (A := A) (B := B) D).symm

theorem sourceHistoryFlag_sum
    {n : ℕ} (D : Finset (Fin n))
    (f : SourceHistoryFlag X Y A B D → ℝ) :
    (∑ r : SourceHistoryFlag X Y A B D, f r) =
      ∑ π : SourceRemainingPermutation D,
      ∑ k : Fin (Finset.univ \ D).card,
      ∑ r : FullCoordinateRevealHistory X Y n D
          (sourceRemainingPermutationPrefix D π k.castSucc)
          (sourceRemainingPermutationCoordinate D π k),
      ∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
        f ⟨π, k, r, α, β⟩ := by
  classical
  calc
    (∑ r : SourceHistoryFlag X Y A B D, f r) =
        ∑ t : SourceHistoryFlagTuple X Y A B D,
          f ((sourceHistoryFlagEquiv (X := X) (Y := Y)
            (A := A) (B := B) D).symm t) :=
      ((sourceHistoryFlagEquiv (X := X) (Y := Y)
        (A := A) (B := B) D).symm.sum_comp f).symm
    _ = _ := by
      simp only [sourceHistoryFlagEquiv, Equiv.symm_mk, Equiv.coe_fn_mk, Fintype.sum_sigma,
        Fintype.sum_prod_type]

private def sourceHistoryPermutationPositionWeight
    {n : ℕ} (D : Finset (Fin n)) : ℝ :=
  1 / ((Fintype.card (SourceRemainingPermutation D) : ℝ) *
    ((Finset.univ \ D).card : ℝ))

private def sourceHistoryRaw
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (r : SourceHistoryFlag X Y A B D) : ℝ :=
  sourceHistoryPermutationPositionWeight D *
    fullCoordinateBaseWeight G D
      (sourceRemainingPermutationPrefix D
        r.permutation r.position.castSucc)
      (sourceRemainingPermutationCoordinate D
        r.permutation r.position)
      r.history *
    fullCoordinateBaseWinIndicator G D
      (sourceRemainingPermutationPrefix D
        r.permutation r.position.castSucc)
      (sourceRemainingPermutationCoordinate D
        r.permutation r.position)
      r.history r.aliceAnswer r.bobAnswer

end

section

open scoped BigOperators

section FiniteSamples

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

/-- The total probability mass of postselection. -/
def postselectionMass
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (C : Finset ι) : ℝ :=
  law.eventMass (FiniteEventLaw.winEvent wins C)

omit [DecidableEq ι] in
theorem allWinMass_le_postselectionMass
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (C : Finset ι) :
    law.eventMass (FiniteEventLaw.winEvent wins Finset.univ) ≤
      postselectionMass law wins C :=
  law.allWinMass_le_partial wins C

omit [Fintype ι] [DecidableEq ι] in
theorem postselectionMass_le_one
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (C : Finset ι) :
    postselectionMass law wins C ≤ 1 := by
  calc
    postselectionMass law wins C ≤ law.eventMass Finset.univ :=
      law.eventMass_mono (Finset.subset_univ _)
    _ = 1 := law.eventMass_univ

/--
The conditional coordinate failure construction used in the quantum parallel-repetition
argument.
-/
def conditionalCoordinateFailure
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (C : Finset ι) (i : ι) : ℝ :=
  FiniteEventLaw.failureMass law wins C i /
    postselectionMass law wins C

/-- The uniform remaining failure construction used in the quantum parallel-repetition argument. -/
def uniformRemainingFailure
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (C : Finset ι) : ℝ :=
  (∑ i ∈ Finset.univ \ C,
    conditionalCoordinateFailure law wins C i) /
    ((Finset.univ \ C).card : ℝ)

theorem uniformRemainingFailure_lt_of_failure_sum
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (C : Finset ι) {η : ℝ}
    (hp : 0 < postselectionMass law wins C)
    (hm : 0 < (Finset.univ \ C).card)
    (hfailure :
      (∑ i ∈ Finset.univ \ C,
        FiniteEventLaw.failureMass law wins C i) <
        ((Finset.univ \ C).card : ℝ) *
          (η * postselectionMass law wins C)) :
    uniformRemainingFailure law wins C < η := by
  have hmreal : 0 < ((Finset.univ \ C).card : ℝ) := by
    exact_mod_cast hm
  unfold uniformRemainingFailure conditionalCoordinateFailure
  rw [← Finset.sum_div]
  apply (div_lt_iff₀ hmreal).mpr
  apply (div_lt_iff₀ hp).mpr
  linarith

end FiniteSamples

section ActualRepeatedStrategy

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The total probability mass of repeated postselection. -/
def repeatedPostselectionMass
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (C : Finset (Fin n)) : ℝ :=
  postselectionMass (strategyEventLaw (G.repeat n) S)
    (repeatedCoordinateWin G n) C

theorem repeated_winProbability_le_postselectionMass
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (C : Finset (Fin n)) :
    S.winProbability ≤ repeatedPostselectionMass G n S C := by
  rw [← repeated_allWinMass_eq G n S]
  exact allWinMass_le_postselectionMass
    (strategyEventLaw (G.repeat n) S) (repeatedCoordinateWin G n) C

theorem repeatedPostselectionMass_pos
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (C : Finset (Fin n))
    (hwin : 0 < S.winProbability) :
    0 < repeatedPostselectionMass G n S C :=
  lt_of_lt_of_le hwin
    (repeated_winProbability_le_postselectionMass G n S C)

theorem remainingCoordinates_card
    {n : ℕ} (C : Finset (Fin n)) :
    (Finset.univ \ C).card = n - C.card := by
  simp only [Finset.card_sdiff_of_subset (Finset.subset_univ C), card_univ, Fintype.card_fin]

theorem repeatedStrategy_exists_conditioning
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    {η : ℝ} {q : ℕ}
    (hwin : 0 < S.winProbability)
    (hη : 0 < η) (hη_one : η ≤ 1)
    (hq : q ≤ n)
    (hterminal : (1 - η) ^ q < S.winProbability) :
    ∃ C : Finset (Fin n),
      C.card < q ∧
      S.winProbability ≤ repeatedPostselectionMass G n S C ∧
      0 < repeatedPostselectionMass G n S C ∧
      0 < (Finset.univ \ C).card ∧
      uniformRemainingFailure
        (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) C < η := by
  obtain ⟨C, hC, hmass, hfailure⟩ :=
    repeatedStrategy_exists_greedy_conditioning G n S
      hwin hη hη_one hq (le_refl _) hterminal
  have hremaining : 0 < (Finset.univ \ C).card := by
    rw [remainingCoordinates_card]
    omega
  have hp : 0 < repeatedPostselectionMass G n S C :=
    repeatedPostselectionMass_pos G n S C hwin
  refine ⟨C, hC, ?_, hp, hremaining, ?_⟩
  · simpa only [repeatedPostselectionMass, postselectionMass] using hmass
  · apply uniformRemainingFailure_lt_of_failure_sum
      (strategyEventLaw (G.repeat n) S)
      (repeatedCoordinateWin G n) C
      (by simpa only [repeatedPostselectionMass] using hp)
      hremaining
    simpa only [subset_univ, sum_sdiff_eq_sub, postselectionMass] using hfailure

end ActualRepeatedStrategy

end

section

open scoped BigOperators ComplexOrder MatrixOrder

theorem source_equation_nineteen_alice
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ) (hF : F.PosSemidef)
    (hFcomplement : (1 - F).PosSemidef)
    (G : Matrix dB dB ℂ) (hG : G.PosSemidef)
    (hGcomplement : (1 - G).PosSemidef) :
    -bornTracePairing ρ.matrix
        (cfc (fun z : ℝ => z * Real.log z) F) G ≤
      Real.negMulLog (bornTracePairing ρ.matrix F G) :=
  matrixLogEntropy_born_lower_bound_left
    ρ F hF hFcomplement G hG hGcomplement

theorem source_equation_nineteen_bob
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ) (hF : F.PosSemidef)
    (hFcomplement : (1 - F).PosSemidef)
    (G : Matrix dB dB ℂ) (hG : G.PosSemidef)
    (hGcomplement : (1 - G).PosSemidef) :
    -bornTracePairing ρ.matrix F
        (cfc (fun z : ℝ => z * Real.log z) G) ≤
      Real.negMulLog (bornTracePairing ρ.matrix F G) :=
  matrixLogEntropy_born_lower_bound_right
    ρ F hF hFcomplement G hG hGcomplement

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


section ActualFilters

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The postselection log cost construction used in the quantum parallel-repetition argument. -/
def postselectionLogCost
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : ℝ :=
  Real.log (1 / repeatedPostselectionMass G n S D)

/-- The answer log cost construction used in the quantum parallel-repetition argument. -/
def answerLogCost
    {A B : Type*} [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) : ℝ :=
  (D.card : ℝ) *
    Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))

/-- The error rate associated with martingale. -/
def martingaleRate
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : ℝ :=
  (postselectionLogCost G n S D +
      answerLogCost (A := A) (B := B) D) /
    ((Finset.univ \ D).card : ℝ)

theorem answerCount_pos_of_postselection
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (hp : 0 < repeatedPostselectionMass G n S D) :
    0 < fullHistoryAnswerCount (A := A) (B := B) D := by
  classical
  have hmass := fullHistoryAtomBornMass_sum G n S D ∅
    (Finset.empty_subset _)
  have hfirst :
      (∑ z : FullHistoryEntropyAtom X Y A B n D ∅,
        fullHistoryAtomCountingWeight G D ∅ z *
          fullHistoryAtomBornMass G n S D ∅ z) ≤
        ∑ z : FullHistoryEntropyAtom X Y A B n D ∅,
          fullHistoryAtomCountingWeight G D ∅ z := by
    apply Finset.sum_le_sum
    intro z _
    exact mul_le_of_le_one_right
      (fullHistoryAtomCountingWeight_nonneg G D ∅ z)
      (fullHistoryAtomBornMass_le_one G n S D ∅ z)
  have hsecond := fullHistoryAtomCountingWeight_sum_le G D ∅
  change 0 <
    (strategyEventLaw (G.repeat n) S).eventMass
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D) at hp
  linarith

theorem martingale_log_cost_eq
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (hp : 0 < repeatedPostselectionMass G n S D) :
    Real.log
        (fullHistoryAnswerCount (A := A) (B := B) D /
          repeatedPostselectionMass G n S D) =
      postselectionLogCost G n S D +
        answerLogCost (A := A) (B := B) D := by
  have hN := answerCount_pos_of_postselection G n S D hp
  calc
    Real.log
        (fullHistoryAnswerCount (A := A) (B := B) D /
          repeatedPostselectionMass G n S D) =
        Real.log (fullHistoryAnswerCount (A := A) (B := B) D) -
          Real.log (repeatedPostselectionMass G n S D) :=
            Real.log_div hN.ne' hp.ne'
    _ = (D.card : ℝ) *
          Real.log ((Fintype.card A : ℝ) *
            (Fintype.card B : ℝ)) -
          Real.log (repeatedPostselectionMass G n S D) := by
            rw [fullHistoryAnswerCount_eq, ← mul_pow, Real.log_pow]
    _ = postselectionLogCost G n S D +
          answerLogCost (A := A) (B := B) D := by
            simp only [postselectionLogCost,
              answerLogCost, one_div, Real.log_inv]
            ring

theorem aliceMartingaleEntropyBudget
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (hm : 0 < (Finset.univ \ D).card)
    (hp : 0 < repeatedPostselectionMass G n S D) :
    sourceUniformPermutationAverage D
        (sourcePermutationAliceEntropyIncrement G n S D) ≤
      repeatedPostselectionMass G n S D *
        martingaleRate G n S D := by
  have hbudget := sourceUniformPermutationAliceEntropyBudget
    G n S D hm hp
  change sourceUniformPermutationAverage D
    (sourcePermutationAliceEntropyIncrement G n S D) ≤
    repeatedPostselectionMass G n S D *
      Real.log
        (fullHistoryAnswerCount (A := A) (B := B) D /
          repeatedPostselectionMass G n S D) /
        ((Finset.univ \ D).card : ℝ) at hbudget
  rw [martingale_log_cost_eq G n S D hp] at hbudget
  simpa only [martingaleRate, ge_iff_le, mul_div_assoc] using hbudget

end ActualFilters

section ActualPurificationHistories

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem bornWeighted_normalized_distance
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (fallback u v : E) (hfallback : ‖fallback‖ = 1) :
    ‖u‖ ^ 2 *
      ‖normalizeOrDefault fallback u -
        normalizeOrDefault fallback v‖ ^ 2 ≤
      4 * ‖u - v‖ ^ 2 := by
  by_cases hu : u = 0
  · simp only [hu, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      zero_sub, norm_neg, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, norm_nonneg, pow_succ_nonneg]
  · have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hdist := normalizeOrDefault_sub_le fallback u v hfallback hu
    have hscaled :
        ‖normalizeOrDefault fallback u -
          normalizeOrDefault fallback v‖ * ‖u‖ ≤
          2 * ‖u - v‖ :=
      (le_div_iff₀ hu_pos).mp hdist
    have hsquare := mul_self_le_mul_self
      (mul_nonneg (norm_nonneg _) (norm_nonneg u)) hscaled
    linarith [sq_nonneg
      (‖normalizeOrDefault fallback u -
        normalizeOrDefault fallback v‖ * ‖u‖),
      sq_nonneg (‖u - v‖)]

end ActualPurificationHistories

end

section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem fullCoordinateInsertedHistory_winIndicator_eq
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n) (hiD : i ∉ D)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (α : {j : Fin n // j ∈ D} → A) (a : A)
    (β : {j : Fin n // j ∈ D} → B) (b : B) :
    fullHistoryWinIndicator G
      (fullCoordinateInsertedHistory D L i r x y)
      (fullCoordinateAnswerExtension D i α a)
      (fullCoordinateAnswerExtension D i β b) =
      fullCoordinateBaseWinIndicator G D L i r α β *
        (if G.predicate x y a b = true then 1 else 0) := by
  classical
  have hiff :
      (∀ j : {j : Fin n // j ∈ insert i D},
        G.predicate
          ((fullCoordinateInsertedHistory D L i r x y).aliceConditioned j)
          ((fullCoordinateInsertedHistory D L i r x y).bobConditioned j)
          (fullCoordinateAnswerExtension D i α a j)
          (fullCoordinateAnswerExtension D i β b j) = true) ↔
      ((∀ j : {j : Fin n // j ∈ D},
        G.predicate (r.aliceConditioned j) (r.bobConditioned j)
          (α j) (β j) = true) ∧ G.predicate x y a b = true) := by
    constructor
    · intro h
      constructor
      · intro j
        have hji : (j : Fin n) ≠ i := by
          intro he
          exact hiD (he ▸ j.property)
        simpa only [fullCoordinateInsertedHistory, fullCoordinateAnswerExtension, hji,
          ↓reduceDIte, Subtype.coe_eta] using
          h ⟨j, Finset.mem_insert_of_mem j.property⟩
      · simpa only [fullCoordinateInsertedHistory, fullCoordinateAnswerExtension,
          ↓reduceDIte] using
          h ⟨i, Finset.mem_insert_self i D⟩
    · rintro ⟨hD, hi⟩ j
      by_cases hji : (j : Fin n) = i
      · have hjsub :
            j = (⟨i, Finset.mem_insert_self i D⟩ :
              {j : Fin n // j ∈ insert i D}) := Subtype.ext hji
        subst j
        simpa only [fullCoordinateInsertedHistory, fullCoordinateAnswerExtension,
          ↓reduceDIte] using hi
      · have hjD : (j : Fin n) ∈ D :=
          (Finset.mem_insert.mp j.property).resolve_left hji
        simpa only [fullCoordinateInsertedHistory, fullCoordinateAnswerExtension, hji,
          ↓reduceDIte] using hD ⟨j, hjD⟩
  change
    (if ∀ j : {j : Fin n // j ∈ insert i D},
      G.predicate
        ((fullCoordinateInsertedHistory D L i r x y).aliceConditioned j)
        ((fullCoordinateInsertedHistory D L i r x y).bobConditioned j)
        (fullCoordinateAnswerExtension D i α a j)
        (fullCoordinateAnswerExtension D i β b j) = true
      then (1 : ℝ) else 0) =
      (if ∀ j : {j : Fin n // j ∈ D},
        G.predicate (r.aliceConditioned j) (r.bobConditioned j)
          (α j) (β j) = true then (1 : ℝ) else 0) *
      (if G.predicate x y a b = true then (1 : ℝ) else 0)
  split_ifs with hall hD hi <;> aesop

private def fullCoordinateInsertedHiddenAliceEquiv
    {X : Type*} {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n) :
    ({j : Fin n // j ∈ fullHistoryRemaining n (insert i D) L} → X) ≃
      ({j : Fin n // j ∈ fullHistoryRemaining n D (insert i L)} → X) where
  toFun hidden j :=
    hidden ((fullHistoryRemainingInsertedEquiv D L i).symm j)
  invFun hidden j := hidden (fullHistoryRemainingInsertedEquiv D L i j)
  left_inv hidden := by
    funext j
    simp only [Equiv.symm_apply_apply]
  right_inv hidden := by
    funext j
    simp only [Equiv.apply_symm_apply]

omit [Fintype X] [Fintype Y] in
theorem fullCoordinateInsertedAliceQuestion_eq
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (hidden : {j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)} → X) :
    fullHistoryAliceQuestion
      (fullCoordinateInsertedHistory D L i r x y)
      ((fullCoordinateInsertedHiddenAliceEquiv (X := X) D L i).symm hidden) =
      fullHistoryAliceQuestion
        (fullCoordinateNewHistory D L i r x) hidden := by
  classical
  funext j
  by_cases hjD : j ∈ D
  · have hji : j ≠ i := by
      intro he
      exact hiD (he ▸ hjD)
    simp only [fullHistoryAliceQuestion, mem_insert, hji, hjD, or_true, ↓reduceDIte,
      fullCoordinateInsertedHistory, fullCoordinateAnswerExtension, fullCoordinateNewHistory]
  · by_cases hji : j = i
    · subst j
      simp only [fullHistoryAliceQuestion, mem_insert, hiD, or_false, ↓reduceDIte,
        fullCoordinateInsertedHistory, fullCoordinateAnswerExtension, hiL,
        fullCoordinateNewHistory]
    · by_cases hjL : j ∈ L
      · simp only [fullHistoryAliceQuestion, mem_insert, hji, hjD, or_self, ↓reduceDIte, hjL,
          fullCoordinateInsertedHistory, or_true, fullCoordinateNewHistory]
      · simp only [fullHistoryAliceQuestion, mem_insert, hji, hjD, or_self, ↓reduceDIte, hjL,
          fullCoordinateInsertedHiddenAliceEquiv, fullHistoryRemainingInsertedEquiv,
          Equiv.symm_mk, Equiv.coe_fn_mk]
        congr 1

theorem fullCoordinateInsertedHiddenAliceWeight_eq
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (hidden : {j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)} → X) :
    fullHistoryHiddenAliceWeight G
      (fullCoordinateInsertedHistory D L i r x y)
      ((fullCoordinateInsertedHiddenAliceEquiv (X := X) D L i).symm hidden) =
      fullHistoryHiddenAliceWeight G
        (fullCoordinateNewHistory D L i r x) hidden := by
  classical
  let e := fullHistoryRemainingInsertedEquiv D L i
  unfold fullHistoryHiddenAliceWeight
  calc
    (∏ j : {j : Fin n //
      j ∈ fullHistoryRemaining n (insert i D) L},
      G.conditionalXGivenY
        ((fullCoordinateInsertedHistory D L i r x y).bobRemaining j)
        (((fullCoordinateInsertedHiddenAliceEquiv
          (X := X) D L i).symm hidden) j)) =
      ∏ j : {j : Fin n //
        j ∈ fullHistoryRemaining n (insert i D) L},
        G.conditionalXGivenY (r.bobRemaining (e j)) (hidden (e j)) := by
          apply Finset.prod_congr rfl
          intro j _
          rfl
    _ = ∏ j : {j : Fin n //
        j ∈ fullHistoryRemaining n D (insert i L)},
        G.conditionalXGivenY (r.bobRemaining j) (hidden j) :=
      e.prod_comp (fun j =>
        G.conditionalXGivenY (r.bobRemaining j) (hidden j))
    _ = _ := rfl

omit [Fintype X] [Fintype Y] in
theorem fullCoordinateInsertedBobQuestion_eq
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (hidden : {j : Fin n // j ∈ L} → Y) :
    fullHistoryBobQuestion
      (fullCoordinateInsertedHistory D L i r x y) hidden =
      fullHistoryBobQuestion
        (fullCoordinateOldHistory D L i r y) hidden := by
  classical
  funext j
  by_cases hjD : j ∈ D
  · have hji : j ≠ i := by
      intro he
      exact hiD (he ▸ hjD)
    simp only [fullHistoryBobQuestion, mem_insert, hji, hjD, or_true, ↓reduceDIte,
      fullCoordinateInsertedHistory, fullCoordinateAnswerExtension, fullCoordinateOldHistory]
  · by_cases hji : j = i
    · subst j
      simp only [fullHistoryBobQuestion, mem_insert, hiD, or_false, ↓reduceDIte,
        fullCoordinateInsertedHistory, fullCoordinateAnswerExtension, hiL,
        fullCoordinateOldHistory]
    · by_cases hjL : j ∈ L
      · simp only [fullHistoryBobQuestion, mem_insert, hji, hjD, or_self, ↓reduceDIte, hjL]
      · simp only [fullHistoryBobQuestion, mem_insert, hji, hjD, or_self, ↓reduceDIte, hjL,
          fullCoordinateInsertedHistory, fullCoordinateOldHistory]

theorem fullCoordinateInsertedHiddenBobWeight_eq
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (hidden : {j : Fin n // j ∈ L} → Y) :
    fullHistoryHiddenBobWeight G
      (fullCoordinateInsertedHistory D L i r x y) hidden =
    fullHistoryHiddenBobWeight G
        (fullCoordinateOldHistory D L i r y) hidden := by
  rfl

theorem fullCoordinateInsertedHistory_aliceFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (α : {j : Fin n // j ∈ D} → A) (a : A) :
    fullHistoryAliceFilter G n S (insert i D) L
      (fullCoordinateInsertedHistory D L i r x y)
      (fullCoordinateAnswerExtension D i α a) =
      fullCoordinateAliceRefinementEffect G n S D L i r α x a := by
  classical
  change
    (∑ hidden : {j : Fin n //
      j ∈ fullHistoryRemaining n (insert i D) L} → X,
      fullHistoryHiddenAliceWeight G
        (fullCoordinateInsertedHistory D L i r x y) hidden •
      conditionedAliceEffect G n S (insert i D)
        (fullCoordinateAnswerExtension D i α a)
        (fullHistoryAliceQuestion
          (fullCoordinateInsertedHistory D L i r x y) hidden)) =
      ∑ hidden : {j : Fin n //
        j ∈ fullHistoryRemaining n D (insert i L)} → X,
        fullHistoryHiddenAliceWeight G
          (fullCoordinateNewHistory D L i r x) hidden •
        conditionedAliceCoordinateEffect G n S D α
          (fullHistoryAliceQuestion
            (fullCoordinateNewHistory D L i r x) hidden) i a
  calc
    (∑ hidden : {j : Fin n //
      j ∈ fullHistoryRemaining n (insert i D) L} → X,
      fullHistoryHiddenAliceWeight G
        (fullCoordinateInsertedHistory D L i r x y) hidden •
      conditionedAliceEffect G n S (insert i D)
        (fullCoordinateAnswerExtension D i α a)
        (fullHistoryAliceQuestion
          (fullCoordinateInsertedHistory D L i r x y) hidden)) =
      ∑ hidden : {j : Fin n //
        j ∈ fullHistoryRemaining n D (insert i L)} → X,
        fullHistoryHiddenAliceWeight G
          (fullCoordinateInsertedHistory D L i r x y)
          ((fullCoordinateInsertedHiddenAliceEquiv
            (X := X) D L i).symm hidden) •
        conditionedAliceEffect G n S (insert i D)
          (fullCoordinateAnswerExtension D i α a)
          (fullHistoryAliceQuestion
            (fullCoordinateInsertedHistory D L i r x y)
            ((fullCoordinateInsertedHiddenAliceEquiv
              (X := X) D L i).symm hidden)) := by
        exact ((fullCoordinateInsertedHiddenAliceEquiv
          (X := X) D L i).symm.sum_comp
          (fun hidden =>
            fullHistoryHiddenAliceWeight G
              (fullCoordinateInsertedHistory D L i r x y) hidden •
            conditionedAliceEffect G n S (insert i D)
              (fullCoordinateAnswerExtension D i α a)
              (fullHistoryAliceQuestion
                (fullCoordinateInsertedHistory D L i r x y)
                hidden))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro hidden _
      rw [fullCoordinateInsertedHiddenAliceWeight_eq
        G D L i r x y hidden]
      rw [fullCoordinateInsertedAliceQuestion_eq
        D L i hiD hiL r x y hidden]
      rw [conditionedAliceEffect_insert_eq_coordinate
        G n S D i hiD α a]

theorem fullCoordinateInsertedHistory_bobFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (β : {j : Fin n // j ∈ D} → B) (b : B) :
    fullHistoryBobFilter G n S (insert i D) L
      (fullCoordinateInsertedHistory D L i r x y)
      (fullCoordinateAnswerExtension D i β b) =
      fullCoordinateBobRefinementEffect G n S D L i r β y b := by
  classical
  change
    (∑ hidden : {j : Fin n // j ∈ L} → Y,
      fullHistoryHiddenBobWeight G
        (fullCoordinateInsertedHistory D L i r x y) hidden •
      conditionedBobEffect G n S (insert i D)
        (fullCoordinateAnswerExtension D i β b)
        (fullHistoryBobQuestion
          (fullCoordinateInsertedHistory D L i r x y) hidden)) =
      ∑ hidden : {j : Fin n // j ∈ L} → Y,
        fullHistoryHiddenBobWeight G
          (fullCoordinateOldHistory D L i r y) hidden •
        conditionedBobCoordinateEffect G n S D β
          (fullHistoryBobQuestion
            (fullCoordinateOldHistory D L i r y) hidden) i b
  apply Finset.sum_congr rfl
  intro hidden _
  rw [fullCoordinateInsertedHiddenBobWeight_eq G D L i r x y hidden]
  rw [fullCoordinateInsertedBobQuestion_eq D L i hiD hiL r x y hidden]
  rw [conditionedBobEffect_insert_eq_coordinate G n S D i hiD β b]

theorem fullCoordinateInsertedHistory_sum
    {T : Type*} [AddCommMonoid T]
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D)
    (f : FullSubsetHistory X Y n (insert i D) L → T) :
    (∑ h : FullSubsetHistory X Y n (insert i D) L, f h) =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ x : X, ∑ y : Y,
        f (fullCoordinateInsertedHistory D L i r x y) := by
  classical
  simpa only [fullCoordinateInsertedHistoryEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type]
    using ((fullCoordinateInsertedHistoryEquiv
      (X := X) (Y := Y) D L i hiD).sum_comp f).symm

theorem fullCoordinateAnswerExtension_sum
    {T R : Type*} [Fintype T] [AddCommMonoid R]
    {n : ℕ} (D : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D)
    (f : ({j : Fin n // j ∈ insert i D} → T) → R) :
    (∑ α : {j : Fin n // j ∈ insert i D} → T, f α) =
      ∑ α : {j : Fin n // j ∈ D} → T, ∑ a : T,
        f (fullCoordinateAnswerExtension D i α a) := by
  classical
  simpa only [fullCoordinateAnswerExtensionEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type]
    using ((fullCoordinateAnswerExtensionEquiv
      (T := T) D i hiD).sum_comp f).symm

theorem fullCoordinateWeightedInsertedSum
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D)
    (value : (h : FullSubsetHistory X Y n (insert i D) L) →
      ({j : Fin n // j ∈ insert i D} → A) →
      ({j : Fin n // j ∈ insert i D} → B) → ℝ) :
    (∑ h : FullSubsetHistory X Y n (insert i D) L,
      ∑ α : {j : Fin n // j ∈ insert i D} → A,
      ∑ β : {j : Fin n // j ∈ insert i D} → B,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
          value h α β) =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ α : {j : Fin n // j ∈ D} → A,
      ∑ β : {j : Fin n // j ∈ D} → B,
        fullCoordinateBaseWeight G D L i r *
          fullCoordinateBaseWinIndicator G D L i r α β *
          (∑ x : X, ∑ y : Y, G.questionWeight x y *
            (∑ a : A, ∑ b : B,
              (if G.predicate x y a b = true then 1 else 0) *
                value (fullCoordinateInsertedHistory D L i r x y)
                  (fullCoordinateAnswerExtension D i α a)
                  (fullCoordinateAnswerExtension D i β b))) := by
  classical
  calc
    (∑ h : FullSubsetHistory X Y n (insert i D) L,
      ∑ α : {j : Fin n // j ∈ insert i D} → A,
      ∑ β : {j : Fin n // j ∈ insert i D} → B,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
          value h α β) =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ x : X, ∑ y : Y,
      ∑ α : {j : Fin n // j ∈ insert i D} → A,
      ∑ β : {j : Fin n // j ∈ insert i D} → B,
        fullHistoryWeight G
            (fullCoordinateInsertedHistory D L i r x y) *
          fullHistoryWinIndicator G
            (fullCoordinateInsertedHistory D L i r x y) α β *
          value (fullCoordinateInsertedHistory D L i r x y) α β :=
      fullCoordinateInsertedHistory_sum D L i hiD
        (fun h =>
          ∑ α : {j : Fin n // j ∈ insert i D} → A,
          ∑ β : {j : Fin n // j ∈ insert i D} → B,
            fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
              value h α β)
    _ =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ x : X, ∑ y : Y,
      ∑ α : {j : Fin n // j ∈ D} → A, ∑ a : A,
      ∑ β : {j : Fin n // j ∈ D} → B, ∑ b : B,
        fullHistoryWeight G
            (fullCoordinateInsertedHistory D L i r x y) *
          fullHistoryWinIndicator G
            (fullCoordinateInsertedHistory D L i r x y)
            (fullCoordinateAnswerExtension D i α a)
            (fullCoordinateAnswerExtension D i β b) *
          value (fullCoordinateInsertedHistory D L i r x y)
            (fullCoordinateAnswerExtension D i α a)
            (fullCoordinateAnswerExtension D i β b) := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [fullCoordinateAnswerExtension_sum (T := A) D i hiD]
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro a _
      rw [fullCoordinateAnswerExtension_sum (T := B) D i hiD]
    _ =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ α : {j : Fin n // j ∈ D} → A,
      ∑ β : {j : Fin n // j ∈ D} → B,
      ∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B,
        fullHistoryWeight G
            (fullCoordinateInsertedHistory D L i r x y) *
          fullHistoryWinIndicator G
            (fullCoordinateInsertedHistory D L i r x y)
            (fullCoordinateAnswerExtension D i α a)
            (fullCoordinateAnswerExtension D i β b) *
          value (fullCoordinateInsertedHistory D L i r x y)
            (fullCoordinateAnswerExtension D i α a)
            (fullCoordinateAnswerExtension D i β b) := by
      apply Finset.sum_congr rfl
      intro r _
      calc
        (∑ x : X, ∑ y : Y,
          ∑ α : {j : Fin n // j ∈ D} → A, ∑ a : A,
          ∑ β : {j : Fin n // j ∈ D} → B, ∑ b : B,
            fullHistoryWeight G
                (fullCoordinateInsertedHistory D L i r x y) *
              fullHistoryWinIndicator G
                (fullCoordinateInsertedHistory D L i r x y)
                (fullCoordinateAnswerExtension D i α a)
                (fullCoordinateAnswerExtension D i β b) *
              value (fullCoordinateInsertedHistory D L i r x y)
                (fullCoordinateAnswerExtension D i α a)
                (fullCoordinateAnswerExtension D i β b)) =
          ∑ x : X, ∑ y : Y,
          ∑ α : {j : Fin n // j ∈ D} → A,
          ∑ β : {j : Fin n // j ∈ D} → B,
          ∑ a : A, ∑ b : B,
            fullHistoryWeight G
                (fullCoordinateInsertedHistory D L i r x y) *
              fullHistoryWinIndicator G
                (fullCoordinateInsertedHistory D L i r x y)
                (fullCoordinateAnswerExtension D i α a)
                (fullCoordinateAnswerExtension D i β b) *
              value (fullCoordinateInsertedHistory D L i r x y)
                (fullCoordinateAnswerExtension D i α a)
                (fullCoordinateAnswerExtension D i β b) := by
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro y _
            apply Finset.sum_congr rfl
            intro α _
            rw [Finset.sum_comm]
        _ = _ := finite_sum_four_swap (fun x y α β =>
          ∑ a : A, ∑ b : B,
            fullHistoryWeight G
                (fullCoordinateInsertedHistory D L i r x y) *
              fullHistoryWinIndicator G
                (fullCoordinateInsertedHistory D L i r x y)
                (fullCoordinateAnswerExtension D i α a)
                (fullCoordinateAnswerExtension D i β b) *
              value (fullCoordinateInsertedHistory D L i r x y)
                (fullCoordinateAnswerExtension D i α a)
                (fullCoordinateAnswerExtension D i β b))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro β _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [fullCoordinateInsertedHistory_weight G D L i hiD r x y]
      rw [fullCoordinateInsertedHistory_winIndicator_eq
        G D L i hiD r x y α a β b]
      ring

private def fullCoordinateAcceptedPostselectedMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n) : ℝ :=
  ∑ r : FullCoordinateRevealHistory X Y n D L i,
  ∑ α : {j : Fin n // j ∈ D} → A,
  ∑ β : {j : Fin n // j ∈ D} → B,
    fullCoordinateBaseWeight G D L i r *
      fullCoordinateBaseWinIndicator G D L i r α β *
      (∑ x : X, ∑ y : Y, G.questionWeight x y *
        (∑ a : A, ∑ b : B,
          (if G.predicate x y a b = true then 1 else 0) *
            bornTracePairing S.state.matrix
              (fullCoordinateAliceRefinementEffect
                G n S D L i r α x a)
              (fullCoordinateBobRefinementEffect
                G n S D L i r β y b)))

theorem fullCoordinateAcceptedPostselectedMass_eq
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (hL : L ⊆ Finset.univ \ D) :
    fullCoordinateAcceptedPostselectedMass G n S D L i =
      (strategyEventLaw (G.repeat n) S).eventMass
        (FiniteEventLaw.winEvent
          (repeatedCoordinateWin G n) (insert i D)) := by
  classical
  have hLinsert : L ⊆ Finset.univ \ insert i D := by
    intro j hj
    have hjD : j ∉ D := (Finset.mem_sdiff.mp (hL hj)).2
    have hji : j ≠ i := by
      intro he
      exact hiL (he ▸ hj)
    simp only [mem_sdiff, mem_univ, mem_insert, hji, hjD, or_self, not_false_eq_true, and_self]
  calc
    fullCoordinateAcceptedPostselectedMass G n S D L i =
      ∑ h : FullSubsetHistory X Y n (insert i D) L,
      ∑ α : {j : Fin n // j ∈ insert i D} → A,
      ∑ β : {j : Fin n // j ∈ insert i D} → B,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
          bornTracePairing S.state.matrix
            (fullHistoryAliceFilter G n S (insert i D) L h α)
            (fullHistoryBobFilter G n S (insert i D) L h β) := by
      have hweighted := fullCoordinateWeightedInsertedSum
        G D L i hiD
        (fun h α β => bornTracePairing S.state.matrix
          (fullHistoryAliceFilter G n S (insert i D) L h α)
          (fullHistoryBobFilter G n S (insert i D) L h β))
      simp_rw [fullCoordinateInsertedHistory_aliceFilter
        G n S D L i hiD hiL,
        fullCoordinateInsertedHistory_bobFilter
          G n S D L i hiD hiL] at hweighted
      simpa only [fullCoordinateAcceptedPostselectedMass, ite_mul, one_mul,
        zero_mul] using hweighted.symm
    _ = _ := fullSubsetHistory_mass_eq_postselection
      G n S (insert i D) L hLinsert

end

section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def sourceHistoryAcceptedQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (D : Finset (Fin n))
    (r : SourceHistoryFlag X Y A B D)
    (x : X) (y : Y) : ℝ :=
  ∑ a : A, ∑ b : B,
    (if G.predicate x y a b = true then 1 else 0) *
      bornTracePairing S.state.matrix
        (fullCoordinateAliceRefinementEffect G n S D
          (sourceRemainingPermutationPrefix D
            r.permutation r.position.castSucc)
          (sourceRemainingPermutationCoordinate D
            r.permutation r.position)
          r.history r.aliceAnswer x a)
        (fullCoordinateBobRefinementEffect G n S D
          (sourceRemainingPermutationPrefix D
            r.permutation r.position.castSucc)
          (sourceRemainingPermutationCoordinate D
            r.permutation r.position)
          r.history r.bobAnswer y b)

/-- The total probability mass of source history accepted. -/
def sourceHistoryAcceptedMass
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (D : Finset (Fin n)) : ℝ :=
  ∑ r : SourceHistoryFlag X Y A B D,
    sourceHistoryRaw G n D r *
      (∑ x : X, ∑ y : Y, G.questionWeight x y *
        sourceHistoryAcceptedQuestionMass G n S D r x y)

theorem sourceHistoryQuadraticExpectation_matrix_sum
    {I d : Type*} [Fintype I] [Fintype d] [DecidableEq d]
    (M : I → Matrix d d ℂ) (z : EuclideanSpace ℂ d) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) (∑ i : I, M i)) z =
      ∑ i : I,
        quadraticExpectation
          (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) (M i)) z := by
  simp only [quadraticExpectation, map_sum, _root_.sum_apply, CStarModule.inner_sum_right, re_sum]

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem sourceHistoryAcceptedMass_eq_uniform
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (D : Finset (Fin n)) :
    sourceHistoryAcceptedMass G n S D =
      sourceUniformPermutationAverage D
        (fun π k =>
          (strategyEventLaw (G.repeat n) S).eventMass
            (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
              (insert (sourceRemainingPermutationCoordinate D π k) D))) := by
  classical
  have hlocal (π : SourceRemainingPermutation D)
      (k : Fin (Finset.univ \ D).card) :
      fullCoordinateAcceptedPostselectedMass G n S D
        (sourceRemainingPermutationPrefix D π k.castSucc)
        (sourceRemainingPermutationCoordinate D π k) =
        (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
            (insert (sourceRemainingPermutationCoordinate D π k) D)) := by
    apply fullCoordinateAcceptedPostselectedMass_eq
    · exact sourceRemainingPermutationCoordinate_not_mem D π k
    · exact sourceRemainingPermutationCoordinate_not_mem_prefix D π k
    · exact sourceRemainingPermutationPrefix_subset D π k.castSucc
  calc
    sourceHistoryAcceptedMass G n S D =
      ∑ π : SourceRemainingPermutation D,
      ∑ k : Fin (Finset.univ \ D).card,
        sourceHistoryPermutationPositionWeight D *
          fullCoordinateAcceptedPostselectedMass G n S D
            (sourceRemainingPermutationPrefix D π k.castSucc)
            (sourceRemainingPermutationCoordinate D π k) := by
      unfold sourceHistoryAcceptedMass
      rw [sourceHistoryFlag_sum]
      apply Finset.sum_congr rfl
      intro π _
      apply Finset.sum_congr rfl
      intro k _
      unfold fullCoordinateAcceptedPostselectedMass
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro β _
      simp only [sourceHistoryRaw, sourceHistoryAcceptedQuestionMass,
        Finset.mul_sum]
      ring_nf
    _ =
      ∑ π : SourceRemainingPermutation D,
      ∑ k : Fin (Finset.univ \ D).card,
        sourceHistoryPermutationPositionWeight D *
          (strategyEventLaw (G.repeat n) S).eventMass
            (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
              (insert (sourceRemainingPermutationCoordinate D π k) D)) := by
      apply Finset.sum_congr rfl
      intro π _
      apply Finset.sum_congr rfl
      intro k _
      rw [hlocal π k]
    _ = _ := by
      unfold sourceHistoryPermutationPositionWeight
        sourceUniformPermutationAverage
      simp_rw [one_div, div_eq_mul_inv]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro π _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem sourceHistoryAcceptedMass_eq_remaining_average
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (D : Finset (Fin n)) :
    sourceHistoryAcceptedMass G n S D =
      (∑ i : SourceRemainingCoordinate D,
        (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
            (insert i.val D))) /
        ((Finset.univ \ D).card : ℝ) := by
  classical
  rw [sourceHistoryAcceptedMass_eq_uniform]
  have hperm := sourceRemainingPermutation_card_pos D
  unfold sourceUniformPermutationAverage
  simp_rw [sourceRemainingPermutationCoordinate_sum D _
    (fun i : Fin n =>
      (strategyEventLaw (G.repeat n) S).eventMass
        (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
          (insert i D)))]
  have hsum :
      (∑ _π : SourceRemainingPermutation D,
        ∑ i : SourceRemainingCoordinate D,
          (strategyEventLaw (G.repeat n) S).eventMass
            (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
              (insert i.val D))) =
      (Fintype.card (SourceRemainingPermutation D) : ℝ) *
        (∑ i : SourceRemainingCoordinate D,
          (strategyEventLaw (G.repeat n) S).eventMass
            (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
              (insert i.val D))) := by simp only [univ_eq_attach, sum_const, card_univ,
                                         nsmul_eq_mul]
  rw [hsum]
  exact mul_div_mul_left _ _ hperm.ne'

theorem sourceHistoryAcceptedMass_gt_of_greedy
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (D : Finset (Fin n))
    (hm : 0 < (Finset.univ \ D).card)
    {η : ℝ}
    (hgreedy :
      (∑ i ∈ Finset.univ \ D,
        FiniteEventLaw.failureMass
          (strategyEventLaw (G.repeat n) S)
          (repeatedCoordinateWin G n) D i) <
        ((Finset.univ \ D).card : ℝ) *
          (η * (strategyEventLaw (G.repeat n) S).eventMass
            (FiniteEventLaw.winEvent
              (repeatedCoordinateWin G n) D))) :
    (1 - η) *
        (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent
            (repeatedCoordinateWin G n) D) <
      sourceHistoryAcceptedMass G n S D := by
  classical
  let p : ℝ := (strategyEventLaw (G.repeat n) S).eventMass
    (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
  have hmreal : 0 < ((Finset.univ \ D).card : ℝ) := by
    exact_mod_cast hm
  have hsub := Finset.sum_subtype (F := inferInstance)
    (Finset.univ \ D)
    (fun i : Fin n => Iff.rfl)
    (fun i : Fin n => (strategyEventLaw (G.repeat n) S).eventMass
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
        (insert i D)))
  have hfails :
      (∑ i ∈ Finset.univ \ D,
        FiniteEventLaw.failureMass
          (strategyEventLaw (G.repeat n) S)
          (repeatedCoordinateWin G n) D i) =
        ((Finset.univ \ D).card : ℝ) * p -
          (∑ i ∈ Finset.univ \ D,
            (strategyEventLaw (G.repeat n) S).eventMass
              (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
                (insert i D))) := by
    simp only [FiniteEventLaw.failureMass, sum_sub_distrib, sum_const, nsmul_eq_mul, subset_univ,
      sum_sdiff_eq_sub, p]
  rw [sourceHistoryAcceptedMass_eq_remaining_average]
  rw [← hsub]
  apply (lt_div_iff₀ hmreal).mpr
  change (1 - η) * p * ((Finset.univ \ D).card : ℝ) < _
  change
    (∑ i ∈ Finset.univ \ D,
      FiniteEventLaw.failureMass
        (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) D i) <
      ((Finset.univ \ D).card : ℝ) * (η * p) at hgreedy
  linarith [hgreedy, hfails]

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


section TaggedTensorBlocks

variable {R : Type*} [Fintype R]
variable {ι : R → Type*} [∀ r, Fintype (ι r)]

/-- The state vector representing tagged tensor. -/
def taggedTensorVector
    (r : R) (z : EuclideanSpace ℂ (ι r × ι r)) :
    EuclideanSpace ℂ
      ((PUnit.{1} ⊕ (Σ r : R, ι r)) ×
        (PUnit.{1} ⊕ (Σ r : R, ι r))) := by
  classical
  exact toLp 2 fun q =>
    match q.1, q.2 with
    | .inr ⟨rA, a⟩, .inr ⟨rB, b⟩ =>
        if hA : rA = r then
          if hB : rB = r then
            z (hA ▸ a, hB ▸ b)
          else 0
        else 0
    | _, _ => 0

theorem taggedTensorVector_norm
    (r : R) (z : EuclideanSpace ℂ (ι r × ι r)) :
    ‖taggedTensorVector r z‖ = ‖z‖ := by
  classical
  have hsquare :
      ‖taggedTensorVector r z‖ ^ 2 = ‖z‖ ^ 2 := by
    simp only [taggedTensorVector, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
      Fintype.sum_sum_type, univ_unique, PUnit.default_eq_unit, norm_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero, Fintype.sum_sigma,
      zero_add]
    calc
      _ = ∑ a : ι r, ∑ rB : R, ∑ b : ι rB,
          ‖if hA : (r : R) = r then
              if hB : rB = r then z (hA ▸ a, hB ▸ b) else 0
            else 0‖ ^ 2 := by
        apply Fintype.sum_eq_single r
        intro rA hA
        simp only [hA, ↓reduceDIte, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, sum_const_zero]
      _ = ∑ a : ι r, ∑ rB : R, ∑ b : ι rB,
          ‖if hB : rB = r then z (a, hB ▸ b) else 0‖ ^ 2 := by
        simp only [↓reduceDIte]
      _ = ∑ a : ι r, ∑ b : ι r,
          ‖if hB : (r : R) = r then z (a, hB ▸ b) else 0‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro a _
        apply Fintype.sum_eq_single r
        intro rB hB
        simp only [hB, ↓reduceDIte, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, sum_const_zero]
      _ = _ := by simp only [↓reduceDIte]
  nlinarith [norm_nonneg (taggedTensorVector r z),
    norm_nonneg z]

omit [Fintype R] [∀ r, Fintype (ι r)] in
theorem taggedTensorVector_sub
    (r : R) (u v : EuclideanSpace ℂ (ι r × ι r)) :
    taggedTensorVector r (u - v) =
      taggedTensorVector r u - taggedTensorVector r v := by
  classical
  ext q
  rcases q with ⟨a, b⟩
  rcases a with a | ⟨rA, a⟩ <;> rcases b with b | ⟨rB, b⟩ <;>
    simp only [taggedTensorVector, PiLp.sub_apply, sub_zero]
  split_ifs <;> simp

end TaggedTensorBlocks

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem martingaleRate_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (hm : 0 < (Finset.univ \ D).card)
    (hp : 0 < repeatedPostselectionMass G n S D) :
    0 ≤ martingaleRate G n S D := by
  have hnonnegative := sourceUniformPermutationAverage_nonneg D
    (sourcePermutationAliceEntropyIncrement G n S D)
    (fun π k => sourcePermutationAliceEntropyIncrement_nonneg
      G n S D π k)
  have hbudget := aliceMartingaleEntropyBudget
    G n S D hm hp
  nlinarith

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem remainingCoordinate_card_pos
    {n : ℕ} (D : Finset (Fin n))
    (hm : 0 < (Finset.univ \ D).card) :
    0 < Fintype.card (SourceRemainingCoordinate D) := by
  simpa only [Fintype.card_coe, card_pos] using hm

theorem finiteTotalVariation_triangle
    {ι : Type*} [Fintype ι]
    (p q r : ι → ℝ) :
    finiteTotalVariation p r ≤
      finiteTotalVariation p q + finiteTotalVariation q r := by
  unfold finiteTotalVariation
  calc
    (∑ i, |p i - r i|) / 2 ≤
        ((∑ i, |p i - q i|) +
          (∑ i, |q i - r i|)) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      exact abs_sub_le (p i) (q i) (r i)
    _ = (∑ i, |p i - q i|) / 2 +
        (∑ i, |q i - r i|) / 2 := by ring

/-- The weighted conditional joint construction used in the quantum parallel-repetition argument. -/
def weightedConditionalJoint
    {κ ι : Type*}
    (weight : κ → ℝ) (conditional : κ → ι → ℝ) :
    κ × ι → ℝ :=
  fun t => weight t.1 * conditional t.1 t.2

theorem weightedConditionalJoint_totalVariation
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (weight : κ → ℝ) (hweight : ∀ k, 0 ≤ weight k)
    (left right : κ → ι → ℝ) :
    finiteTotalVariation
        (weightedConditionalJoint weight left)
        (weightedConditionalJoint weight right) =
      ∑ k : κ, weight k *
        finiteTotalVariation (left k) (right k) := by
  unfold finiteTotalVariation weightedConditionalJoint
  rw [Fintype.sum_prod_type]
  calc
    (∑ k : κ, ∑ i : ι,
      |weight k * left k i - weight k * right k i|) / 2 =
      (∑ k : κ, weight k *
        (∑ i : ι, |left k i - right k i|)) / 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_sub, abs_mul, abs_of_nonneg (hweight k)]
    _ = ∑ k : κ,
        weight k * ((∑ i : ι, |left k i - right k i|) / 2) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem finiteTotalVariation_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (p q : κ → ℝ) :
    finiteTotalVariation (p ∘ e) (q ∘ e) =
      finiteTotalVariation p q := by
  unfold finiteTotalVariation
  congr 1
  exact e.sum_comp (fun i => |p i - q i|)

/-- The type used to represent local question context in the exact sampling construction. -/
abbrev LocalQuestionContext
    (X Y : Type*)
    {n : ℕ} (D : Finset (Fin n)) :=
  SourceRemainingCoordinate D × (X × Y)

/-- The probability weight for local question. -/
def localQuestionWeight
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (c : LocalQuestionContext X Y D) : ℝ :=
  G.questionWeight c.2.1 c.2.2 /
    (Fintype.card (SourceRemainingCoordinate D) : ℝ)

theorem localQuestionWeight_nonneg
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (c : LocalQuestionContext X Y D) :
    0 ≤ localQuestionWeight G n D c := by
  exact div_nonneg (G.weight_nonneg c.2.1 c.2.2)
    (Nat.cast_nonneg _)

theorem localQuestionWeight_sum
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (hm : 0 < (Finset.univ \ D).card) :
    (∑ c : LocalQuestionContext X Y D,
      localQuestionWeight G n D c) = 1 := by
  have hcard : (Fintype.card (SourceRemainingCoordinate D) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt
      (remainingCoordinate_card_pos D hm))
  calc
    (∑ c : LocalQuestionContext X Y D,
      localQuestionWeight G n D c) =
      (∑ i : SourceRemainingCoordinate D,
        ∑ x : X, ∑ y : Y, G.questionWeight x y) /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ) := by
      simp only [localQuestionWeight, Fintype.sum_prod_type]
      simp_rw [← Finset.sum_div]
    _ = 1 := by
      simp_rw [G.weight_normalized]
      simp only [Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one]
      exact div_self hcard

/-- The probability distribution for conditioned event. -/
def conditionedEventDistribution
    {Ω : Type*} [Fintype Ω]
    (law : FiniteEventLaw Ω) (event : Finset Ω) : Ω → ℝ :=
  fun ω => if ω ∈ event then law.weight ω / law.eventMass event else 0

theorem conditionedEventDistribution_nonneg
    {Ω : Type*} [Fintype Ω]
    (law : FiniteEventLaw Ω) (event : Finset Ω)
    (positive : 0 < law.eventMass event) (ω : Ω) :
    0 ≤ conditionedEventDistribution law event ω := by
  unfold conditionedEventDistribution
  split_ifs
  · exact div_nonneg (law.weight_nonneg ω) positive.le
  · exact le_rfl

theorem conditionedEventDistribution_sum
    {Ω : Type*} [Fintype Ω]
    (law : FiniteEventLaw Ω) (event : Finset Ω)
    (positive : 0 < law.eventMass event) :
    (∑ ω : Ω, conditionedEventDistribution law event ω) = 1 := by
  classical
  unfold conditionedEventDistribution
  calc
    (∑ ω : Ω,
      if ω ∈ event then law.weight ω / law.eventMass event else 0) =
      (∑ ω ∈ event, law.weight ω) / law.eventMass event := by
      rw [Finset.sum_div]
      simp only [sum_ite_mem, univ_inter]
    _ = 1 := by
      change law.eventMass event / law.eventMass event = 1
      exact div_self positive.ne'

theorem conditionedEventDistribution_absolute_continuity
    {Ω : Type*} [Fintype Ω]
    (law : FiniteEventLaw Ω) (event : Finset Ω) (ω : Ω) :
    law.weight ω = 0 →
      conditionedEventDistribution law event ω = 0 := by
  intro hzero
  simp only [conditionedEventDistribution, hzero, zero_div, ite_self]

theorem conditionedEventDistribution_relativeEntropy
    {Ω : Type*} [Fintype Ω]
    (law : FiniteEventLaw Ω) (event : Finset Ω)
    (positive : 0 < law.eventMass event) :
    finiteRelativeEntropy
        (conditionedEventDistribution law event)
        law.weight =
      Real.log (1 / law.eventMass event) := by
  rw [finiteRelativeEntropy_eq_log_sum_of_absolute_continuity
    (conditionedEventDistribution law event)
    law.weight law.weight_nonneg
    (conditionedEventDistribution_absolute_continuity law event)
    (conditionedEventDistribution_sum law event positive)
    law.weight_sum]
  calc
    (∑ ω : Ω,
      conditionedEventDistribution law event ω *
        Real.log
          (conditionedEventDistribution law event ω /
            law.weight ω)) =
      ∑ ω : Ω,
        conditionedEventDistribution law event ω *
          Real.log (1 / law.eventMass event) := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hmem : ω ∈ event
      · by_cases hweight : law.weight ω = 0
        · simp only [conditionedEventDistribution, hmem, ↓reduceIte, hweight, zero_div, div_zero,
            Real.log_zero, mul_zero, one_div, Real.log_inv, mul_neg, zero_mul, neg_zero]
        · have hratio :
              (law.weight ω / law.eventMass event) /
                  law.weight ω = 1 / law.eventMass event := by
                field_simp [hweight, positive.ne']
          simp only [conditionedEventDistribution,
            ite_eq_left hmem, hratio]
      · simp only [conditionedEventDistribution, hmem, ↓reduceIte, zero_div, Real.log_zero,
          mul_zero, one_div, Real.log_inv, mul_neg, zero_mul, neg_zero]
    _ = Real.log (1 / law.eventMass event) := by
      rw [← Finset.sum_mul,
        conditionedEventDistribution_sum law event positive]
      ring

theorem conditionedEventDistribution_projection_relativeEntropy_le
    {Ω κ : Type*} [Fintype Ω] [Fintype κ]
    (law : FiniteEventLaw Ω) (event : Finset Ω)
    (positive : 0 < law.eventMass event)
    (projection : Ω → κ) :
    finiteRelativeEntropy
        (groupedMass projection
          (conditionedEventDistribution law event))
        (groupedMass projection law.weight) ≤
      Real.log (1 / law.eventMass event) := by
  calc
    finiteRelativeEntropy
        (groupedMass projection
          (conditionedEventDistribution law event))
        (groupedMass projection law.weight) ≤
      finiteRelativeEntropy
        (conditionedEventDistribution law event)
        law.weight :=
      finite_relative_entropy_data_processing
        projection
        (conditionedEventDistribution law event)
        law.weight
        (conditionedEventDistribution_nonneg law event positive)
        law.weight_nonneg
        (conditionedEventDistribution_absolute_continuity
          law event)
    _ = Real.log (1 / law.eventMass event) :=
      conditionedEventDistribution_relativeEntropy
        law event positive

/-- The finite probability law for repeated conditioned outcome. -/
def repeatedConditionedOutcomeLaw
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    StrategyOutcome
      (Fin n → X) (Fin n → Y)
      (Fin n → A) (Fin n → B) → ℝ :=
  conditionedEventDistribution
    (strategyEventLaw (G.repeat n) S)
    (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)

theorem repeatedConditionedOutcomeLaw_relativeEntropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (hp : 0 < repeatedPostselectionMass G n S D) :
    finiteRelativeEntropy
        (repeatedConditionedOutcomeLaw G n S D)
        (strategyEventLaw (G.repeat n) S).weight =
      postselectionLogCost G n S D := by
  exact conditionedEventDistribution_relativeEntropy
    (strategyEventLaw (G.repeat n) S)
    (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D) hp

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

/-- The probability weight for finite uniform. -/
def finiteUniformWeight (Z : Type*) [Fintype Z] : ℝ :=
  1 / (Fintype.card Z : ℝ)

theorem finiteUniformWeight_pos
    {Z : Type*} [Fintype Z]
    (positive : 0 < Fintype.card Z) :
    0 < finiteUniformWeight Z := by
  unfold finiteUniformWeight
  exact one_div_pos.mpr (by exact_mod_cast positive)

theorem finiteUniformWeight_sum
    {Z : Type*} [Fintype Z]
    (positive : 0 < Fintype.card Z) :
    (∑ _z : Z, finiteUniformWeight Z) = 1 := by
  have hcard : (Fintype.card Z : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt positive)
  unfold finiteUniformWeight
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hcard]

theorem finiteProbability_le_one
    {Z : Type*} [Fintype Z]
    (p : Z → ℝ)
    (nonnegative : ∀ z, 0 ≤ p z)
    (normalized : (∑ z, p z) = 1)
    (z : Z) :
    p z ≤ 1 := by
  calc
    p z ≤ ∑ a : Z, p a :=
      Finset.single_le_sum
        (fun a _ => nonnegative a) (Finset.mem_univ z)
    _ = 1 := normalized

theorem finiteRelativeEntropy_uniform_le_log_card
    {Z : Type*} [Fintype Z]
    (p : Z → ℝ)
    (nonnegative : ∀ z, 0 ≤ p z)
    (normalized : (∑ z, p z) = 1)
    (positive : 0 < Fintype.card Z) :
    finiteRelativeEntropy p
        (fun _ : Z => finiteUniformWeight Z) ≤
      Real.log (Fintype.card Z : ℝ) := by
  have hcardpos : 0 < (Fintype.card Z : ℝ) := by
    exact_mod_cast positive
  have hcardne : (Fintype.card Z : ℝ) ≠ 0 := hcardpos.ne'
  rw [finiteRelativeEntropy_eq_log_sum p
    (fun _ : Z => finiteUniformWeight Z)
    (fun _ => finiteUniformWeight_pos positive)
    normalized (finiteUniformWeight_sum positive)]
  calc
    (∑ z : Z, p z *
      Real.log (p z / finiteUniformWeight Z)) ≤
      ∑ z : Z, p z * Real.log (Fintype.card Z : ℝ) := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hzero : p z = 0
      · simp only [hzero, zero_div, Real.log_zero, mul_zero, zero_mul, Std.le_refl]
      · have hp : 0 < p z :=
          lt_of_le_of_ne (nonnegative z) (Ne.symm hzero)
        have hpone : p z ≤ 1 :=
          finiteProbability_le_one p nonnegative normalized z
        have hratio :
            p z / finiteUniformWeight Z =
              p z * (Fintype.card Z : ℝ) := by
          unfold finiteUniformWeight
          field_simp [hcardne]
        rw [hratio]
        apply mul_le_mul_of_nonneg_left _ (nonnegative z)
        apply Real.log_le_log (mul_pos hp hcardpos)
        nlinarith
    _ = Real.log (Fintype.card Z : ℝ) := by
      rw [← Finset.sum_mul, normalized]
      ring

/-- The uniform flag reference construction used in the quantum parallel-repetition argument. -/
def uniformFlagReference
    {Ω Z : Type*} [Fintype Z]
    (prior : Ω → ℝ) : Ω × Z → ℝ :=
  fun t => prior t.1 * finiteUniformWeight Z

theorem uniformFlagReference_nonneg
    {Ω Z : Type*} [Fintype Z]
    (prior : Ω → ℝ)
    (nonnegative : ∀ ω, 0 ≤ prior ω)
    (positive : 0 < Fintype.card Z)
    (t : Ω × Z) :
    0 ≤ uniformFlagReference (Z := Z) prior t := by
  exact mul_nonneg (nonnegative t.1)
    (finiteUniformWeight_pos positive).le

theorem uniformFlagReference_sum
    {Ω Z : Type*} [Fintype Ω] [Fintype Z]
    (prior : Ω → ℝ)
    (normalized : (∑ ω, prior ω) = 1)
    (positive : 0 < Fintype.card Z) :
    (∑ t : Ω × Z,
      uniformFlagReference (Z := Z) prior t) = 1 := by
  rw [Fintype.sum_prod_type]
  unfold uniformFlagReference
  simp_rw [← Finset.mul_sum,
    finiteUniformWeight_sum positive, mul_one]
  exact normalized

theorem uniformFlagReference_firstMarginal
    {Ω Z : Type*} [Fintype Z]
    (prior : Ω → ℝ)
    (positive : 0 < Fintype.card Z) :
    jointFirstMarginal
        (uniformFlagReference (Z := Z) prior) = prior := by
  funext ω
  change
    (∑ z : Z, prior ω * finiteUniformWeight Z) = prior ω
  rw [← Finset.mul_sum, finiteUniformWeight_sum positive]
  ring

theorem uniformFlagReference_conditional
    {Ω Z : Type*} [Fintype Z]
    (prior : Ω → ℝ)
    (positive : 0 < Fintype.card Z)
    (ω : Ω) (hprior : prior ω ≠ 0) :
    jointConditional
        (uniformFlagReference (Z := Z) prior) ω =
      fun _ : Z => finiteUniformWeight Z := by
  funext z
  unfold jointConditional
  rw [uniformFlagReference_firstMarginal prior positive]
  change
    prior ω * finiteUniformWeight Z / prior ω =
      finiteUniformWeight Z
  field_simp [hprior]

theorem uniformFlagReference_absolute_continuity
    {Ω Z : Type*} [Fintype Z]
    (joint : Ω × Z → ℝ)
    (prior : Ω → ℝ)
    (hjoint : ∀ t, 0 ≤ joint t)
    (absolute_continuity :
      ∀ ω, prior ω = 0 → jointFirstMarginal joint ω = 0)
    (positive : 0 < Fintype.card Z)
    (t : Ω × Z) :
    uniformFlagReference (Z := Z) prior t = 0 →
      joint t = 0 := by
  rcases t with ⟨ω, z⟩
  intro hzero
  change prior ω * finiteUniformWeight Z = 0 at hzero
  have hflag : finiteUniformWeight Z ≠ 0 :=
    (finiteUniformWeight_pos positive).ne'
  have hprior : prior ω = 0 :=
    (mul_eq_zero.mp hzero).resolve_right hflag
  have hmarginal := absolute_continuity ω hprior
  change (∑ a : Z, joint (ω, a)) = 0 at hmarginal
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun a _ => hjoint (ω, a))).mp
      hmarginal z (Finset.mem_univ z)

theorem uniformFlagRelativeEntropy_le
    {Ω Z : Type*} [Fintype Ω] [Fintype Z]
    (joint : Ω × Z → ℝ)
    (prior : Ω → ℝ)
    (hjoint : ∀ t, 0 ≤ joint t)
    (hprior : ∀ ω, 0 ≤ prior ω)
    (joint_normalized : (∑ t, joint t) = 1)
    (prior_normalized : (∑ ω, prior ω) = 1)
    (absolute_continuity :
      ∀ ω, prior ω = 0 → jointFirstMarginal joint ω = 0)
    (positive : 0 < Fintype.card Z) :
    finiteRelativeEntropy joint
        (uniformFlagReference (Z := Z) prior) ≤
      finiteRelativeEntropy (jointFirstMarginal joint) prior +
        Real.log (Fintype.card Z : ℝ) := by
  have hreference_nonneg :=
    uniformFlagReference_nonneg prior hprior positive
  have hreference_normalized :=
    uniformFlagReference_sum prior prior_normalized positive
  have hreference_absolute :=
    uniformFlagReference_absolute_continuity
      joint prior hjoint absolute_continuity positive
  have hmarginal_normalized :
      (∑ ω : Ω, jointFirstMarginal joint ω) = 1 :=
    (jointFirstMarginal_sum joint).trans joint_normalized
  have hmarginal_nonnegative :
      ∀ ω : Ω, 0 ≤ jointFirstMarginal joint ω :=
    jointFirstMarginal_nonneg joint hjoint
  rw [finite_relative_entropy_joint_chain_rule
    joint (uniformFlagReference (Z := Z) prior)
    hjoint hreference_nonneg hreference_absolute
    joint_normalized hreference_normalized,
    uniformFlagReference_firstMarginal prior positive]
  gcongr
  calc
    (∑ ω : Ω,
      jointFirstMarginal joint ω *
        finiteRelativeEntropy (jointConditional joint ω)
          (jointConditional
            (uniformFlagReference (Z := Z) prior) ω)) ≤
      ∑ ω : Ω,
        jointFirstMarginal joint ω *
          Real.log (Fintype.card Z : ℝ) := by
      apply Finset.sum_le_sum
      intro ω _
      by_cases hmass : jointFirstMarginal joint ω = 0
      · simp only [hmass, zero_mul, Std.le_refl]
      · have hprior_ne : prior ω ≠ 0 := by
          intro hzero
          exact hmass (absolute_continuity ω hzero)
        rw [uniformFlagReference_conditional
          prior positive ω hprior_ne]
        apply mul_le_mul_of_nonneg_left _
          (hmarginal_nonnegative ω)
        apply finiteRelativeEntropy_uniform_le_log_card
        · intro z
          exact div_nonneg (hjoint (ω, z))
            (hmarginal_nonnegative ω)
        · exact jointConditional_sum joint ω hmass
        · exact positive
    _ = Real.log (Fintype.card Z : ℝ) := by
      rw [← Finset.sum_mul, hmarginal_normalized]
      ring

theorem finiteRelativeEntropy_nonneg
    {Ω : Type*} [Fintype Ω]
    (p q : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω)
    (hq : ∀ ω, 0 ≤ q ω) :
    0 ≤ finiteRelativeEntropy p q := by
  unfold finiteRelativeEntropy
  apply Finset.sum_nonneg
  intro ω _
  exact mul_nonneg (hq ω)
    (InformationTheory.klFun_nonneg (div_nonneg (hp ω) (hq ω)))

theorem groupedMass_nonneg
    {Ω κ : Type*} [Fintype Ω] [DecidableEq κ]
    (f : Ω → κ) (p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (a : κ) :
    0 ≤ groupedMass f p a := by
  unfold groupedMass
  exact Finset.sum_nonneg (fun ω _ => hp ω)

theorem groupedMass_absolute_continuity
    {Ω κ : Type*} [Fintype Ω] [DecidableEq κ]
    (f : Ω → κ) (p q : Ω → ℝ)
    (hq : ∀ ω, 0 ≤ q ω)
    (absolute_continuity : ∀ ω, q ω = 0 → p ω = 0)
    (a : κ) :
    groupedMass f q a = 0 → groupedMass f p a = 0 := by
  intro hzero
  change
    (∑ ω ∈ (Finset.univ.filter fun ω => f ω = a), q ω) = 0 at hzero
  change
    (∑ ω ∈ (Finset.univ.filter fun ω => f ω = a), p ω) = 0
  apply Finset.sum_eq_zero
  intro ω hω
  have hqzero : q ω = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun ω _ => hq ω)).mp hzero ω hω
  exact absolute_continuity ω hqzero

theorem groupedMass_comp
    {Ω κ θ : Type*} [Fintype Ω] [Fintype κ]
    [DecidableEq κ] [DecidableEq θ]
    (f : Ω → κ) (g : κ → θ) (p : Ω → ℝ) :
    groupedMass g (groupedMass f p) =
      groupedMass (g ∘ f) p := by
  funext a
  unfold groupedMass
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
    Function.comp_apply] using
    (Finset.sum_fiberwise_eq_sum_filter
      (Finset.univ : Finset Ω)
      (Finset.univ.filter fun b : κ => g b = a)
      f p)

theorem groupedMass_id
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : Ω → ℝ) :
    groupedMass id p = p := by
  funext ω
  have hfilter :
      (Finset.univ.filter fun a : Ω => a = ω) = {ω} := by
    ext a
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
  unfold groupedMass
  change
    (∑ a ∈ (Finset.univ.filter fun a : Ω => a = ω), p a) = p ω
  rw [hfilter]
  simp only [sum_singleton]

/-- The finite prefix mask construction used in the quantum parallel-repetition argument. -/
def finitePrefixMask
    {Ω Y : Type*} {h : ℕ} (base : Y)
    (k : Fin (h + 1)) :
    (Ω × (Fin h → Y)) → (Ω × (Fin h → Y)) :=
  fun t => (t.1, fun j => if j.val < k.val then t.2 j else base)

theorem finitePrefixMask_comp
    {Ω Y : Type*} {h : ℕ} (base : Y)
    (k : Fin h) :
    finitePrefixMask (Ω := Ω) base k.castSucc ∘
        finitePrefixMask (Ω := Ω) base k.succ =
      finitePrefixMask (Ω := Ω) base k.castSucc := by
  funext t
  rcases t with ⟨ω, values⟩
  apply Prod.ext
  · rfl
  · funext j
    by_cases hj : j.val < k.val
    · have hjfin : j < k := hj
      have hjle : j ≤ k := le_of_lt hjfin
      simp only [Function.comp_apply, finitePrefixMask, Fin.val_succ, Order.lt_add_one_iff,
        Fin.val_fin_le, Fin.val_castSucc, Fin.val_fin_lt, hjfin, ↓reduceIte, hjle]
    · have hjfin : ¬ j < k := hj
      simp only [Function.comp_apply, finitePrefixMask, Fin.val_succ, Order.lt_add_one_iff,
        Fin.val_fin_le, Fin.val_castSucc, Fin.val_fin_lt, hjfin, ↓reduceIte]

theorem finitePrefixMask_last
    {Ω Y : Type*} {h : ℕ} (base : Y) :
    finitePrefixMask (Ω := Ω) base (Fin.last h) = id := by
  funext t
  rcases t with ⟨ω, values⟩
  apply Prod.ext
  · rfl
  · funext j
    simp only [finitePrefixMask, Fin.val_last, Fin.is_lt, ↓reduceIte, id_eq]

/-- The entropy quantity for finite prefix relative. -/
def finitePrefixRelativeEntropy
    {Ω Y : Type*} [Fintype Ω] [Fintype Y] {h : ℕ}
    (joint prior : Ω × (Fin h → Y) → ℝ)
    (base : Y) (k : Fin (h + 1)) : ℝ :=
  finiteRelativeEntropy
    (groupedMass (finitePrefixMask base k) joint)
    (groupedMass (finitePrefixMask base k) prior)

theorem finitePrefixRelativeEntropy_telescope
    {Ω Y : Type*} [Fintype Ω] [Fintype Y] {h : ℕ}
    (joint prior : Ω × (Fin h → Y) → ℝ)
    (base : Y) :
    (∑ k : Fin h,
      (finitePrefixRelativeEntropy joint prior base k.succ -
        finitePrefixRelativeEntropy joint prior base k.castSucc)) =
      finiteRelativeEntropy joint prior -
        finitePrefixRelativeEntropy joint prior base 0 := by
  have hfirst := Fin.sum_univ_succ
    (fun k : Fin (h + 1) =>
      finitePrefixRelativeEntropy joint prior base k)
  have hlast := Fin.sum_univ_castSucc
    (fun k : Fin (h + 1) =>
      finitePrefixRelativeEntropy joint prior base k)
  have hendpoint :
      finitePrefixRelativeEntropy joint prior base
          (Fin.last h) =
        finiteRelativeEntropy joint prior := by
    simp only [finitePrefixRelativeEntropy,
      finitePrefixMask_last, groupedMass_id]
  rw [Finset.sum_sub_distrib]
  linarith

theorem finitePrefixRelativeEntropy_budget
    {Ω Y : Type*} [Fintype Ω] [Fintype Y] {h : ℕ}
    (joint prior : Ω × (Fin h → Y) → ℝ)
    (hjoint : ∀ t, 0 ≤ joint t)
    (hprior : ∀ t, 0 ≤ prior t)
    (base : Y) :
    (∑ k : Fin h,
      (finitePrefixRelativeEntropy joint prior base k.succ -
        finitePrefixRelativeEntropy joint prior base k.castSucc)) ≤
      finiteRelativeEntropy joint prior := by
  rw [finitePrefixRelativeEntropy_telescope]
  have hzero :
      0 ≤ finitePrefixRelativeEntropy joint prior base 0 :=
    finiteRelativeEntropy_nonneg
      (groupedMass (finitePrefixMask base 0) joint)
      (groupedMass (finitePrefixMask base 0) prior)
      (groupedMass_nonneg
        (finitePrefixMask base 0) joint hjoint)
      (groupedMass_nonneg
        (finitePrefixMask base 0) prior hprior)
  linarith

theorem reversePartition_relativeEntropy_budget
    {M : Type*} [Fintype M]
    (nonempty : 0 < Fintype.card M)
    (increment : (s : Finset M) → Fin s.card → ℝ)
    {cost : ℝ} (hcost : 0 ≤ cost)
    (hbudget : ∀ s : Finset M,
      (∑ k : Fin s.card, increment s k) ≤ cost) :
    (∑ s : Finset M,
      reversePartitionWeight s *
        ((∑ k : Fin s.card, increment s k) /
          (s.card : ℝ))) ≤
      2 * cost / (Fintype.card M : ℝ) := by
  classical
  have hcard : 0 < (Fintype.card M : ℝ) := by
    exact_mod_cast nonempty
  calc
    (∑ s : Finset M,
      reversePartitionWeight s *
        ((∑ k : Fin s.card, increment s k) /
          (s.card : ℝ))) ≤
      ∑ s : Finset M,
        fairPartitionWeight M *
          (2 * cost / (Fintype.card M : ℝ)) := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : s.card = 0
      · have hempty : s = ∅ := Finset.card_eq_zero.mp hs
        subst s
        simp only [reversePartitionWeight_empty, zero_mul]
        exact mul_nonneg (fairPartitionWeight_nonneg (α := M))
          (div_nonneg (mul_nonneg (by norm_num) hcost) hcard.le)
      · have hsreal : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs
        calc
          reversePartitionWeight s *
              ((∑ k : Fin s.card, increment s k) /
                (s.card : ℝ)) =
            (fairPartitionWeight M *
              (2 / (Fintype.card M : ℝ))) *
                (∑ k : Fin s.card, increment s k) := by
              unfold reversePartitionWeight
              field_simp [hsreal, hcard.ne']
          _ ≤ (fairPartitionWeight M *
              (2 / (Fintype.card M : ℝ))) * cost := by
            apply mul_le_mul_of_nonneg_left (hbudget s)
            exact mul_nonneg (fairPartitionWeight_nonneg (α := M))
              (div_nonneg (by norm_num) hcard.le)
          _ = fairPartitionWeight M *
              (2 * cost / (Fintype.card M : ℝ)) := by ring
    _ = 2 * cost / (Fintype.card M : ℝ) := by
      rw [← Finset.sum_mul, fairPartitionWeight_sum (α := M)]
      ring

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem groupedMass_sum
    {Ω κ : Type*} [Fintype Ω] [Fintype κ] [DecidableEq κ]
    (projection : Ω → κ) (mass : Ω → ℝ) :
    (∑ a : κ, groupedMass projection mass a) =
      ∑ ω : Ω, mass ω := by
  unfold groupedMass
  exact Finset.sum_fiberwise Finset.univ projection mass

theorem groupedMass_first
    {Ω Z : Type*} [Fintype Ω] [Fintype Z]
    [DecidableEq Ω]
    (joint : Ω × Z → ℝ) :
    groupedMass Prod.fst joint = jointFirstMarginal joint := by
  funext ω
  classical
  simp only [groupedMass, jointFirstMarginal,
    Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [sum_ite_eq', mem_univ, ↓reduceIte]

/-- The type used to represent conditioned answer flag in the exact sampling construction. -/
abbrev ConditionedAnswerFlag
    (A B : Type*)
    {n : ℕ} (D : Finset (Fin n)) :=
  ({i : Fin n // i ∈ D} → A) ×
    ({i : Fin n // i ∈ D} → B)

/--
The repeated conditioned answer flag construction used in the quantum parallel-repetition
argument.
-/
def repeatedConditionedAnswerFlag
    (G : Game X Y A B) (n : ℕ) (_S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (ω : StrategyOutcome
      (Fin n → X) (Fin n → Y)
      (Fin n → A) (Fin n → B)) :
    ConditionedAnswerFlag A B D :=
  (fun i => ω.2.2.1 i, fun i => ω.2.2.2 i)

theorem conditionedAnswerFlag_card
    {n : ℕ} (D : Finset (Fin n)) :
    (Fintype.card (ConditionedAnswerFlag A B D) : ℝ) =
      fullHistoryAnswerCount (A := A) (B := B) D := by
  simp only [Fintype.card_prod, Fintype.card_pi, univ_eq_attach, prod_const, card_attach,
    Nat.cast_mul, Nat.cast_pow, fullHistoryAnswerCount]

theorem conditionedAnswerFlag_card_pos
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (hp : 0 < repeatedPostselectionMass G n S D) :
    0 < Fintype.card (ConditionedAnswerFlag A B D) := by
  have hreal :
      0 < (Fintype.card (ConditionedAnswerFlag A B D) : ℝ) := by
    rw [conditionedAnswerFlag_card]
    exact answerCount_pos_of_postselection G n S D hp
  exact_mod_cast hreal

theorem conditionedAnswerFlag_log_card
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (hp : 0 < repeatedPostselectionMass G n S D) :
    Real.log (Fintype.card (ConditionedAnswerFlag A B D) : ℝ) =
      answerLogCost (A := A) (B := B) D := by
  rw [conditionedAnswerFlag_card]
  have hanswer := answerCount_pos_of_postselection G n S D hp
  have hcost := martingale_log_cost_eq G n S D hp
  have hsplit := Real.log_div hanswer.ne' hp.ne'
  have hpost :
      postselectionLogCost G n S D =
        -Real.log (repeatedPostselectionMass G n S D) := by
    simp only [postselectionLogCost, one_div, Real.log_inv]
  linarith

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The type used to represent exact outcome in the exact sampling construction. -/
abbrev ExactOutcome (X Y A B : Type*) (n : ℕ) :=
  StrategyOutcome (Fin n → X) (Fin n → Y)
    (Fin n → A) (Fin n → B)

/-- The type used to represent exact joint outcome in the exact sampling construction. -/
abbrev ExactJointOutcome
    (X Y A B : Type*) {n : ℕ} (D : Finset (Fin n)) :=
  ExactRemainingSeed D × ExactOutcome X Y A B n

theorem exactRemainingSeedWeight_sum
    {n : ℕ} (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card) :
    (∑ seed : ExactRemainingSeed D,
      exactSeedWeight seed) = 1 := by
  apply exactSeedWeight_sum
  simpa only [Fintype.card_coe, card_pos] using remaining

/-- The finite probability law for exact postselected joint. -/
def exactPostselectedJointLaw
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (q : ExactJointOutcome X Y A B D) : ℝ :=
  exactSeedWeight q.1 *
    repeatedConditionedOutcomeLaw G n S D q.2

theorem exactPostselectedJointLaw_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (q : ExactJointOutcome X Y A B D) :
    0 ≤ exactPostselectedJointLaw G n S D q := by
  apply mul_nonneg (exactSeedWeight_nonneg q.1)
  exact conditionedEventDistribution_nonneg
    (strategyEventLaw (G.repeat n) S)
    (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
    positive q.2

theorem exactPostselectedJointLaw_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D) :
    (∑ q : ExactJointOutcome X Y A B D,
      exactPostselectedJointLaw G n S D q) = 1 := by
  have hconditional_sum :
      (∑ outcome : ExactOutcome X Y A B n,
        repeatedConditionedOutcomeLaw G n S D outcome) = 1 := by
    exact conditionedEventDistribution_sum
      (strategyEventLaw (G.repeat n) S)
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
      positive
  unfold exactPostselectedJointLaw
  rw [Fintype.sum_prod_type]
  calc
    (∑ seed : ExactRemainingSeed D,
      ∑ outcome : ExactOutcome X Y A B n,
        exactSeedWeight seed *
          repeatedConditionedOutcomeLaw G n S D outcome) =
      ∑ seed : ExactRemainingSeed D,
        exactSeedWeight seed *
          (∑ outcome : ExactOutcome X Y A B n,
            repeatedConditionedOutcomeLaw G n S D outcome) := by
          simp_rw [Finset.mul_sum]
    _ = ∑ seed : ExactRemainingSeed D,
        exactSeedWeight seed := by
          rw [hconditional_sum]
          simp only [mul_one]
    _ = 1 := exactRemainingSeedWeight_sum D remaining

/-- The exact source pushforward construction used in the quantum parallel-repetition argument. -/
def exactSourcePushforward
    {K : Type*}
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (projection : ExactJointOutcome X Y A B D → K) :
    K → ℝ :=
  groupedMass projection (exactPostselectedJointLaw G n S D)

theorem exactSourcePushforward_nonneg
    {K : Type*}
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (projection : ExactJointOutcome X Y A B D → K)
    (k : K) :
    0 ≤ exactSourcePushforward G n S D projection k := by
  exact groupedMass_nonneg projection
    (exactPostselectedJointLaw G n S D)
    (exactPostselectedJointLaw_nonneg G n S D positive) k

theorem exactSourcePushforward_sum
    {K : Type*} [Fintype K]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (projection : ExactJointOutcome X Y A B D → K) :
    (∑ k : K,
      exactSourcePushforward G n S D projection k) = 1 := by
  unfold exactSourcePushforward
  rw [groupedMass_sum]
  exact exactPostselectedJointLaw_sum
    G n S D remaining positive

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The type used to represent exact locally sampleable tuple in the exact sampling construction. -/
abbrev ExactLocallySampleableTuple
    (X Y A B : Type*)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) :=
  SourceRemainingCoordinate D ×
    (X × (Y × ExactHistoryFlag X Y A B D))

/-- The finite encoding of exact history. -/
def exactHistoryCode
    {n : ℕ} (D : Finset (Fin n))
    (q : ExactJointOutcome X Y A B D) :
    ExactHistoryFlag X Y A B D where
  seed := q.1
  history := exactRevealCode D q.1 (q.2.1, q.2.2.1)
  aliceAnswer := fun j => q.2.2.2.1 j.val
  bobAnswer := fun j => q.2.2.2.2 j.val

/-- The finite encoding of exact locally sampleable. -/
def exactLocallySampleableCode
    {n : ℕ} (D : Finset (Fin n))
    (q : ExactJointOutcome X Y A B D) :
    ExactLocallySampleableTuple X Y A B D :=
  (q.1.coordinate,
    q.2.1 q.1.coordinate.val,
    q.2.2.1 q.1.coordinate.val,
    exactHistoryCode D q)

/-- The finite probability law for exact locally sampleable. -/
def exactLocallySampleableLaw
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    ExactLocallySampleableTuple X Y A B D → ℝ :=
  exactSourcePushforward G n S D
    (exactLocallySampleableCode D)

theorem exactLocallySampleableLaw_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (t : ExactLocallySampleableTuple X Y A B D) :
    0 ≤ exactLocallySampleableLaw G n S D t :=
  exactSourcePushforward_nonneg G n S D positive
    (exactLocallySampleableCode D) t

theorem exactLocallySampleableLaw_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D) :
    (∑ t : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D t) = 1 :=
  exactSourcePushforward_sum G n S D remaining positive
    (exactLocallySampleableCode D)

theorem exactLocallySampleableLaw_eq_zero_of_question_zero
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (i : SourceRemainingCoordinate D) (x : X) (y : Y)
    (r : ExactHistoryFlag X Y A B D)
    (zero : G.questionWeight x y = 0) :
    exactLocallySampleableLaw G n S D (i, x, y, r) = 0 := by
  classical
  unfold exactLocallySampleableLaw
    exactSourcePushforward groupedMass
  apply Finset.sum_eq_zero
  intro q hq
  have hcode :
      exactLocallySampleableCode D q = (i, x, y, r) := by
    exact ((@Finset.mem_filter
      (ExactJointOutcome X Y A B D)
      (fun a => exactLocallySampleableCode D a = (i, x, y, r))
      (fun _ => Classical.propDecidable _)
      Finset.univ q).mp hq).2
  have hx : q.2.1 q.1.coordinate.val = x :=
    congrArg
      (fun t : ExactLocallySampleableTuple X Y A B D =>
        t.2.1) hcode
  have hy : q.2.2.1 q.1.coordinate.val = y :=
    congrArg
      (fun t : ExactLocallySampleableTuple X Y A B D =>
        t.2.2.1) hcode
  have hproduct :
      (G.repeat n).questionWeight q.2.1 q.2.2.1 = 0 := by
    rw [Game.repeat_questionWeight]
    apply Finset.prod_eq_zero
      (Finset.mem_univ q.1.coordinate.val)
    simpa only [hx, hy] using zero
  have hprod :
      (∏ j : Fin n,
        G.questionWeight (q.2.1 j) (q.2.2.1 j)) = 0 := by
    simpa only [Game.repeat_questionWeight] using hproduct
  simp only [exactPostselectedJointLaw, repeatedConditionedOutcomeLaw,
    conditionedEventDistribution, strategyEventLaw, Game.repeat_questionWeight, hprod, zero_mul,
    zero_div, ite_self, mul_zero]

/-- The total probability mass of exact alice local. -/
def exactAliceLocalMass
    {n : ℕ} (D : Finset (Fin n))
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (i : SourceRemainingCoordinate D) (x : X) : ℝ :=
  ∑ r : ExactHistoryFlag X Y A B D,
    ∑ y : Y, Q (i, x, y, r)

/-- The total probability mass of exact bob local. -/
def exactBobLocalMass
    {n : ℕ} (D : Finset (Fin n))
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (i : SourceRemainingCoordinate D) (y : Y) : ℝ :=
  ∑ r : ExactHistoryFlag X Y A B D,
    ∑ x : X, Q (i, x, y, r)

theorem exactAliceLocalMass_nonneg
    {n : ℕ} (D : Finset (Fin n))
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (nonnegative : ∀ t, 0 ≤ Q t)
    (i : SourceRemainingCoordinate D) (x : X) :
    0 ≤ exactAliceLocalMass D Q i x := by
  unfold exactAliceLocalMass
  exact Finset.sum_nonneg
    (fun r _ => Finset.sum_nonneg (fun y _ => nonnegative (i, x, y, r)))

theorem exactBobLocalMass_nonneg
    {n : ℕ} (D : Finset (Fin n))
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (nonnegative : ∀ t, 0 ≤ Q t)
    (i : SourceRemainingCoordinate D) (y : Y) :
    0 ≤ exactBobLocalMass D Q i y := by
  unfold exactBobLocalMass
  exact Finset.sum_nonneg
    (fun r _ => Finset.sum_nonneg (fun x _ => nonnegative (i, x, y, r)))

/--
The exact alice local conditional construction used in the quantum parallel-repetition argument.
-/
def exactAliceLocalConditional
    {n : ℕ} (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (i : SourceRemainingCoordinate D) (x : X)
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  if exactAliceLocalMass D Q i x = 0 then
    if r = base then 1 else 0
  else
    (∑ y : Y, Q (i, x, y, r)) /
      exactAliceLocalMass D Q i x

/--
The exact bob local conditional construction used in the quantum parallel-repetition argument.
-/
def exactBobLocalConditional
    {n : ℕ} (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (i : SourceRemainingCoordinate D) (y : Y)
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  if exactBobLocalMass D Q i y = 0 then
    if r = base then 1 else 0
  else
    (∑ x : X, Q (i, x, y, r)) /
      exactBobLocalMass D Q i y

theorem exactAliceLocalConditional_nonneg
    {n : ℕ} (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (nonnegative : ∀ t, 0 ≤ Q t)
    (i : SourceRemainingCoordinate D) (x : X)
    (r : ExactHistoryFlag X Y A B D) :
    0 ≤ exactAliceLocalConditional D base Q i x r := by
  unfold exactAliceLocalConditional
  split_ifs with hmass hbase
  · exact zero_le_one
  · exact le_rfl
  · exact div_nonneg
      (Finset.sum_nonneg (fun y _ => nonnegative (i, x, y, r)))
      (exactAliceLocalMass_nonneg D Q nonnegative i x)

theorem exactBobLocalConditional_nonneg
    {n : ℕ} (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (nonnegative : ∀ t, 0 ≤ Q t)
    (i : SourceRemainingCoordinate D) (y : Y)
    (r : ExactHistoryFlag X Y A B D) :
    0 ≤ exactBobLocalConditional D base Q i y r := by
  unfold exactBobLocalConditional
  split_ifs with hmass hbase
  · exact zero_le_one
  · exact le_rfl
  · exact div_nonneg
      (Finset.sum_nonneg (fun x _ => nonnegative (i, x, y, r)))
      (exactBobLocalMass_nonneg D Q nonnegative i y)

theorem exactAliceLocalMass_zero_apply
    {n : ℕ} (D : Finset (Fin n))
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (nonnegative : ∀ t, 0 ≤ Q t)
    (i : SourceRemainingCoordinate D) (x : X)
    (y : Y) (r : ExactHistoryFlag X Y A B D)
    (zero : exactAliceLocalMass D Q i x = 0) :
    Q (i, x, y, r) = 0 := by
  change
    (∑ r : ExactHistoryFlag X Y A B D,
      ∑ y : Y, Q (i, x, y, r)) = 0 at zero
  have hr : (∑ y : Y, Q (i, x, y, r)) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun r _ => Finset.sum_nonneg
        (fun y _ => nonnegative (i, x, y, r)))).mp
          zero r (Finset.mem_univ r)
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun y _ => nonnegative (i, x, y, r))).mp
      hr y (Finset.mem_univ y)

theorem exactBobLocalMass_zero_apply
    {n : ℕ} (D : Finset (Fin n))
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (nonnegative : ∀ t, 0 ≤ Q t)
    (i : SourceRemainingCoordinate D) (x : X)
    (y : Y) (r : ExactHistoryFlag X Y A B D)
    (zero : exactBobLocalMass D Q i y = 0) :
    Q (i, x, y, r) = 0 := by
  change
    (∑ r : ExactHistoryFlag X Y A B D,
      ∑ x : X, Q (i, x, y, r)) = 0 at zero
  have hr : (∑ x : X, Q (i, x, y, r)) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun r _ => Finset.sum_nonneg
        (fun x _ => nonnegative (i, x, y, r)))).mp
          zero r (Finset.mem_univ r)
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun x _ => nonnegative (i, x, y, r))).mp
      hr x (Finset.mem_univ x)

theorem exactAliceLocalConditional_zero_apply
    {n : ℕ} (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (nonnegative : ∀ t, 0 ≤ Q t)
    (i : SourceRemainingCoordinate D) (x : X)
    (y : Y) (r : ExactHistoryFlag X Y A B D)
    (zero : exactAliceLocalConditional D base Q i x r = 0) :
    Q (i, x, y, r) = 0 := by
  by_cases hmass : exactAliceLocalMass D Q i x = 0
  · exact exactAliceLocalMass_zero_apply
      D Q nonnegative i x y r hmass
  · unfold exactAliceLocalConditional at zero
    rw [ite_eq_right hmass] at zero
    have hfiber : (∑ y : Y, Q (i, x, y, r)) = 0 :=
      (div_eq_zero_iff.mp zero).resolve_right hmass
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun y _ => nonnegative (i, x, y, r))).mp
        hfiber y (Finset.mem_univ y)

theorem exactBobLocalConditional_zero_apply
    {n : ℕ} (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (nonnegative : ∀ t, 0 ≤ Q t)
    (i : SourceRemainingCoordinate D) (x : X)
    (y : Y) (r : ExactHistoryFlag X Y A B D)
    (zero : exactBobLocalConditional D base Q i y r = 0) :
    Q (i, x, y, r) = 0 := by
  by_cases hmass : exactBobLocalMass D Q i y = 0
  · exact exactBobLocalMass_zero_apply
      D Q nonnegative i x y r hmass
  · unfold exactBobLocalConditional at zero
    rw [ite_eq_right hmass] at zero
    have hfiber : (∑ x : X, Q (i, x, y, r)) = 0 :=
      (div_eq_zero_iff.mp zero).resolve_right hmass
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _ => nonnegative (i, x, y, r))).mp
        hfiber x (Finset.mem_univ x)

theorem exactAliceLocalConditional_sum
    {n : ℕ} (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (i : SourceRemainingCoordinate D) (x : X) :
    (∑ r : ExactHistoryFlag X Y A B D,
      exactAliceLocalConditional D base Q i x r) = 1 := by
  unfold exactAliceLocalConditional
  split_ifs with hmass
  · simp only [sum_ite_eq', mem_univ, ↓reduceIte]
  · rw [← Finset.sum_div]
    exact div_self hmass

theorem exactBobLocalConditional_sum
    {n : ℕ} (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (i : SourceRemainingCoordinate D) (y : Y) :
    (∑ r : ExactHistoryFlag X Y A B D,
      exactBobLocalConditional D base Q i y r) = 1 := by
  unfold exactBobLocalConditional
  split_ifs with hmass
  · simp only [sum_ite_eq', mem_univ, ↓reduceIte]
  · rw [← Finset.sum_div]
    exact div_self hmass

/--
The exact locally sampleable ja construction used in the quantum parallel-repetition argument.
-/
def exactLocallySampleableJA
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (t : ExactLocallySampleableTuple X Y A B D) : ℝ :=
  G.questionWeight t.2.1 t.2.2.1 *
    exactAliceLocalConditional D base
      (exactLocallySampleableLaw G n S D)
      t.1 t.2.1 t.2.2.2 /
    (Fintype.card (SourceRemainingCoordinate D) : ℝ)

/--
The exact locally sampleable jb construction used in the quantum parallel-repetition argument.
-/
def exactLocallySampleableJB
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (t : ExactLocallySampleableTuple X Y A B D) : ℝ :=
  G.questionWeight t.2.1 t.2.2.1 *
    exactBobLocalConditional D base
      (exactLocallySampleableLaw G n S D)
      t.1 t.2.2.1 t.2.2.2 /
    (Fintype.card (SourceRemainingCoordinate D) : ℝ)

theorem exactLocallySampleableJA_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (t : ExactLocallySampleableTuple X Y A B D) :
    0 ≤ exactLocallySampleableJA G n S D base t := by
  unfold exactLocallySampleableJA
  exact div_nonneg
    (mul_nonneg (G.weight_nonneg t.2.1 t.2.2.1)
      (exactAliceLocalConditional_nonneg D base
        (exactLocallySampleableLaw G n S D)
        (exactLocallySampleableLaw_nonneg G n S D positive)
        t.1 t.2.1 t.2.2.2))
    (Nat.cast_nonneg _)

theorem exactLocallySampleableJB_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (t : ExactLocallySampleableTuple X Y A B D) :
    0 ≤ exactLocallySampleableJB G n S D base t := by
  unfold exactLocallySampleableJB
  exact div_nonneg
    (mul_nonneg (G.weight_nonneg t.2.1 t.2.2.1)
      (exactBobLocalConditional_nonneg D base
        (exactLocallySampleableLaw G n S D)
        (exactLocallySampleableLaw_nonneg G n S D positive)
        t.1 t.2.2.1 t.2.2.2))
    (Nat.cast_nonneg _)

theorem exactRemainingCoordinate_card_pos
    {n : ℕ} (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card) :
    0 < Fintype.card (SourceRemainingCoordinate D) := by
  simpa only [Fintype.card_coe, card_pos] using remaining

theorem exactLocallySampleableJA_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (base : ExactHistoryFlag X Y A B D) :
    (∑ t : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableJA G n S D base t) = 1 := by
  have hcard :
      (Fintype.card (SourceRemainingCoordinate D) : ℝ) ≠ 0 := by
    exact_mod_cast
      (Nat.ne_of_gt (exactRemainingCoordinate_card_pos D remaining))
  calc
    (∑ t : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableJA G n S D base t) =
      (∑ i : SourceRemainingCoordinate D,
        ∑ x : X, ∑ y : Y,
          G.questionWeight x y *
            (∑ r : ExactHistoryFlag X Y A B D,
              exactAliceLocalConditional D base
                (exactLocallySampleableLaw G n S D) i x r)) /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ) := by
      simp only [exactLocallySampleableJA,
        Fintype.sum_prod_type]
      simp_rw [← Finset.sum_div]
      refine congrArg₂ (· / ·) ?_ rfl
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
    _ = (∑ i : SourceRemainingCoordinate D,
        ∑ x : X, ∑ y : Y, G.questionWeight x y) /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ) := by
      simp_rw [exactAliceLocalConditional_sum, mul_one]
    _ = 1 := by
      simp_rw [G.weight_normalized]
      simp only [Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one]
      exact div_self hcard

theorem exactLocallySampleableJB_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (base : ExactHistoryFlag X Y A B D) :
    (∑ t : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableJB G n S D base t) = 1 := by
  have hcard :
      (Fintype.card (SourceRemainingCoordinate D) : ℝ) ≠ 0 := by
    exact_mod_cast
      (Nat.ne_of_gt (exactRemainingCoordinate_card_pos D remaining))
  calc
    (∑ t : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableJB G n S D base t) =
      (∑ i : SourceRemainingCoordinate D,
        ∑ x : X, ∑ y : Y,
          G.questionWeight x y *
            (∑ r : ExactHistoryFlag X Y A B D,
              exactBobLocalConditional D base
                (exactLocallySampleableLaw G n S D) i y r)) /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ) := by
      simp only [exactLocallySampleableJB,
        Fintype.sum_prod_type]
      simp_rw [← Finset.sum_div]
      refine congrArg₂ (· / ·) ?_ rfl
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
    _ = (∑ i : SourceRemainingCoordinate D,
        ∑ x : X, ∑ y : Y, G.questionWeight x y) /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ) := by
      simp_rw [exactBobLocalConditional_sum, mul_one]
    _ = 1 := by
      simp_rw [G.weight_normalized]
      simp only [Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one]
      exact div_self hcard

theorem exactLocallySampleableLaw_absolute_continuous_JA
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (t : ExactLocallySampleableTuple X Y A B D) :
    exactLocallySampleableJA G n S D base t = 0 →
      exactLocallySampleableLaw G n S D t = 0 := by
  rcases t with ⟨i, x, y, r⟩
  intro zero
  have hcard :
      (Fintype.card (SourceRemainingCoordinate D) : ℝ) ≠ 0 := by
    exact_mod_cast
      (Nat.ne_of_gt (exactRemainingCoordinate_card_pos D remaining))
  change
    G.questionWeight x y *
      exactAliceLocalConditional D base
        (exactLocallySampleableLaw G n S D) i x r /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ) = 0 at zero
  have hproduct :
      G.questionWeight x y *
        exactAliceLocalConditional D base
          (exactLocallySampleableLaw G n S D) i x r = 0 :=
    (div_eq_zero_iff.mp zero).resolve_right hcard
  rcases mul_eq_zero.mp hproduct with hquestion | hconditional
  · exact exactLocallySampleableLaw_eq_zero_of_question_zero
      G n S D i x y r hquestion
  · exact exactAliceLocalConditional_zero_apply D base
      (exactLocallySampleableLaw G n S D)
      (exactLocallySampleableLaw_nonneg G n S D positive)
      i x y r hconditional

theorem exactLocallySampleableLaw_absolute_continuous_JB
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (t : ExactLocallySampleableTuple X Y A B D) :
    exactLocallySampleableJB G n S D base t = 0 →
      exactLocallySampleableLaw G n S D t = 0 := by
  rcases t with ⟨i, x, y, r⟩
  intro zero
  have hcard :
      (Fintype.card (SourceRemainingCoordinate D) : ℝ) ≠ 0 := by
    exact_mod_cast
      (Nat.ne_of_gt (exactRemainingCoordinate_card_pos D remaining))
  change
    G.questionWeight x y *
      exactBobLocalConditional D base
        (exactLocallySampleableLaw G n S D) i y r /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ) = 0 at zero
  have hproduct :
      G.questionWeight x y *
        exactBobLocalConditional D base
          (exactLocallySampleableLaw G n S D) i y r = 0 :=
    (div_eq_zero_iff.mp zero).resolve_right hcard
  rcases mul_eq_zero.mp hproduct with hquestion | hconditional
  · exact exactLocallySampleableLaw_eq_zero_of_question_zero
      G n S D i x y r hquestion
  · exact exactBobLocalConditional_zero_apply D base
      (exactLocallySampleableLaw G n S D)
      (exactLocallySampleableLaw_nonneg G n S D positive)
      i x y r hconditional

theorem exactLocallySampleableJA_pinsker
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    finiteTotalVariation
        (exactLocallySampleableLaw G n S D)
        (exactLocallySampleableJA G n S D base) ≤
      Real.sqrt
        (finiteRelativeEntropy
          (exactLocallySampleableLaw G n S D)
          (exactLocallySampleableJA G n S D base) / 2) := by
  exact finite_pinsker_sqrt_of_absolute_continuity
    (exactLocallySampleableLaw G n S D)
    (exactLocallySampleableJA G n S D base)
    (exactLocallySampleableLaw_nonneg G n S D positive)
    (exactLocallySampleableJA_nonneg G n S D positive base)
    (exactLocallySampleableLaw_absolute_continuous_JA
      G n S D remaining positive base)
    (exactLocallySampleableLaw_sum
      G n S D remaining positive)
    (exactLocallySampleableJA_sum G n S D remaining base)

theorem exactLocallySampleableJB_pinsker
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    finiteTotalVariation
        (exactLocallySampleableLaw G n S D)
        (exactLocallySampleableJB G n S D base) ≤
      Real.sqrt
        (finiteRelativeEntropy
          (exactLocallySampleableLaw G n S D)
          (exactLocallySampleableJB G n S D base) / 2) := by
  exact finite_pinsker_sqrt_of_absolute_continuity
    (exactLocallySampleableLaw G n S D)
    (exactLocallySampleableJB G n S D base)
    (exactLocallySampleableLaw_nonneg G n S D positive)
    (exactLocallySampleableJB_nonneg G n S D positive base)
    (exactLocallySampleableLaw_absolute_continuous_JB
      G n S D remaining positive base)
    (exactLocallySampleableLaw_sum
      G n S D remaining positive)
    (exactLocallySampleableJB_sum G n S D remaining base)

/-- The type used to represent exact local sampler index in the exact sampling construction. -/
abbrev ExactLocalSamplerIndex
    (X Y : Type*)
    {n : ℕ} (D : Finset (Fin n)) :=
  (SourceRemainingCoordinate D × X) ⊕
    (SourceRemainingCoordinate D × Y)

/--
The exact local conditional family construction used in the quantum parallel-repetition
argument.
-/
def exactLocalConditionalFamily
    {n : ℕ} (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (k : ExactLocalSamplerIndex X Y D)
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  match k with
  | .inl (i, x) => exactAliceLocalConditional D base Q i x r
  | .inr (i, y) => exactBobLocalConditional D base Q i y r

theorem exactLocalConditionalFamily_nonneg
    {n : ℕ} (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (nonnegative : ∀ t, 0 ≤ Q t)
    (k : ExactLocalSamplerIndex X Y D)
    (r : ExactHistoryFlag X Y A B D) :
    0 ≤ exactLocalConditionalFamily D base Q k r := by
  rcases k with ⟨i, x⟩ | ⟨i, y⟩
  · exact exactAliceLocalConditional_nonneg
      D base Q nonnegative i x r
  · exact exactBobLocalConditional_nonneg
      D base Q nonnegative i y r

theorem exactLocalConditionalFamily_sum
    {n : ℕ} (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (k : ExactLocalSamplerIndex X Y D) :
    (∑ r : ExactHistoryFlag X Y A B D,
      exactLocalConditionalFamily D base Q k r) = 1 := by
  rcases k with ⟨i, x⟩ | ⟨i, y⟩
  · exact exactAliceLocalConditional_sum D base Q i x
  · exact exactBobLocalConditional_sum D base Q i y

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The probability weight for exact conditional question. -/
def exactConditionalQuestionWeight
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y)
    (xs : Fin n → X) (ys : Fin n → Y) : ℝ :=
  exactFiberQuestionWeight
      G n D seed history x y xs ys /
    exactFiberQuestionMass G n D seed history x y

theorem exactFiberQuestionMass_eq_jointQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y) :
    exactFiberQuestionMass G n D seed history x y =
      exactJointQuestionMass G n D seed history x y := by
  classical
  unfold exactFiberQuestionMass
    exactFiberQuestionWeight
    exactJointQuestionMass
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro xs _
  apply Finset.sum_congr rfl
  intro ys _
  simp only [Game.repeat_questionWeight, exactRevealCode_compatible_iff, exactPriorQuestionWeight]

private def exactJointAliceQuestionFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) (y : Y) : Matrix S.Alice S.Alice ℂ :=
  ∑ xs : Fin n → X,
    (exactFiberAliceMarginal
      G n D seed history x y xs /
      exactFiberQuestionMass G n D seed history x y) •
    conditionedAliceEffect G n S D answer xs

private def exactJointBobQuestionFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (x : X) (y : Y) : Matrix S.Bob S.Bob ℂ :=
  ∑ ys : Fin n → Y,
    (exactFiberBobMarginal
      G n D seed history x y ys /
      exactFiberQuestionMass G n D seed history x y) •
    conditionedBobEffect G n S D answer ys

/-- The spectral filter for exact joint alice coordinate. -/
def exactJointAliceCoordinateFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) (y : Y) (a : A) : Matrix S.Alice S.Alice ℂ :=
  ∑ xs : Fin n → X,
    (exactFiberAliceMarginal
      G n D seed history x y xs /
      exactFiberQuestionMass G n D seed history x y) •
    conditionedAliceCoordinateEffect
      G n S D answer xs seed.coordinate.val a

/-- The spectral filter for exact joint bob coordinate. -/
def exactJointBobCoordinateFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (x : X) (y : Y) (b : B) : Matrix S.Bob S.Bob ℂ :=
  ∑ ys : Fin n → Y,
    (exactFiberBobMarginal
      G n D seed history x y ys /
      exactFiberQuestionMass G n D seed history x y) •
    conditionedBobCoordinateEffect
      G n S D answer ys seed.coordinate.val b

theorem exactFiber_born_of_rank_one
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y)
    (nonzero : exactFiberQuestionMass
      G n D seed history x y ≠ 0)
    (EA : (Fin n → X) → Matrix S.Alice S.Alice ℂ)
    (EB : (Fin n → Y) → Matrix S.Bob S.Bob ℂ) :
    bornTracePairing S.state.matrix
        (∑ xs : Fin n → X,
          (exactFiberAliceMarginal
            G n D seed history x y xs /
            exactFiberQuestionMass
              G n D seed history x y) • EA xs)
        (∑ ys : Fin n → Y,
          (exactFiberBobMarginal
            G n D seed history x y ys /
            exactFiberQuestionMass
              G n D seed history x y) • EB ys) =
      ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
        exactConditionalQuestionWeight
          G n D seed history x y xs ys *
          bornTracePairing S.state.matrix (EA xs) (EB ys) := by
  classical
  simp only [map_sum, LinearMap.sum_apply,
    map_smul, LinearMap.smul_apply, smul_eq_mul,
    exactConditionalQuestionWeight]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro xs _
  apply Finset.sum_congr rfl
  intro ys _
  have hrank := exactFiberQuestionWeight_mul_mass
    G n D seed history x y xs ys
  have hborn := congrArg
    (fun z : ℝ => z *
      bornTracePairing S.state.matrix (EA xs) (EB ys)) hrank
  field_simp [nonzero]
  linarith [hborn]

theorem exactJointQuestionFilter_born
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (aliceAnswer : {j : Fin n // j ∈ D} → A)
    (bobAnswer : {j : Fin n // j ∈ D} → B)
    (x : X) (y : Y)
    (nonzero : exactFiberQuestionMass
      G n D seed history x y ≠ 0) :
    bornTracePairing S.state.matrix
        (exactJointAliceQuestionFilter
          G n S D seed history aliceAnswer x y)
        (exactJointBobQuestionFilter
          G n S D seed history bobAnswer x y) =
      ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
        exactConditionalQuestionWeight
          G n D seed history x y xs ys *
        bornTracePairing S.state.matrix
          (conditionedAliceEffect G n S D aliceAnswer xs)
          (conditionedBobEffect G n S D bobAnswer ys) := by
  exact exactFiber_born_of_rank_one
    G n S D seed history x y nonzero
    (conditionedAliceEffect G n S D aliceAnswer)
    (conditionedBobEffect G n S D bobAnswer)

theorem exactJointCoordinateFilter_born
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (aliceAnswer : {j : Fin n // j ∈ D} → A)
    (bobAnswer : {j : Fin n // j ∈ D} → B)
    (x : X) (y : Y) (a : A) (b : B)
    (nonzero : exactFiberQuestionMass
      G n D seed history x y ≠ 0) :
    bornTracePairing S.state.matrix
        (exactJointAliceCoordinateFilter
          G n S D seed history aliceAnswer x y a)
        (exactJointBobCoordinateFilter
          G n S D seed history bobAnswer x y b) =
      ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
        exactConditionalQuestionWeight
          G n D seed history x y xs ys *
        bornTracePairing S.state.matrix
          (conditionedAliceCoordinateEffect
            G n S D aliceAnswer xs seed.coordinate.val a)
          (conditionedBobCoordinateEffect
            G n S D bobAnswer ys seed.coordinate.val b) := by
  exact exactFiber_born_of_rank_one
    G n S D seed history x y nonzero
    (fun xs => conditionedAliceCoordinateEffect
      G n S D aliceAnswer xs seed.coordinate.val a)
    (fun ys => conditionedBobCoordinateEffect
      G n S D bobAnswer ys seed.coordinate.val b)

/-- The total probability mass of exact joint conditional winning. -/
def exactJointConditionalWinningMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (aliceAnswer : {j : Fin n // j ∈ D} → A)
    (bobAnswer : {j : Fin n // j ∈ D} → B)
    (x : X) (y : Y) : ℝ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true then
      bornTracePairing S.state.matrix
        (exactJointAliceCoordinateFilter
          G n S D seed history aliceAnswer x y a)
        (exactJointBobCoordinateFilter
          G n S D seed history bobAnswer x y b)
    else 0

theorem exactJointConditionalWinningMass_born
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (aliceAnswer : {j : Fin n // j ∈ D} → A)
    (bobAnswer : {j : Fin n // j ∈ D} → B)
    (x : X) (y : Y)
    (nonzero : exactFiberQuestionMass
      G n D seed history x y ≠ 0) :
    exactJointConditionalWinningMass
        G n S D seed history aliceAnswer bobAnswer x y =
      ∑ a : A, ∑ b : B,
        if G.predicate x y a b = true then
          ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
            exactConditionalQuestionWeight
              G n D seed history x y xs ys *
            bornTracePairing S.state.matrix
              (conditionedAliceCoordinateEffect
                G n S D aliceAnswer xs seed.coordinate.val a)
              (conditionedBobCoordinateEffect
                G n S D bobAnswer ys seed.coordinate.val b)
        else 0 := by
  classical
  unfold exactJointConditionalWinningMass
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · exact exactJointCoordinateFilter_born
      G n S D seed history aliceAnswer bobAnswer x y a b nonzero
  · rfl

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactFiberQuestionWeight_sum_bobQuestion
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (xs : Fin n → X) (ys : Fin n → Y) :
    (∑ y : Y,
      exactFiberQuestionWeight
        G n D seed history x y xs ys) =
      if exactRevealCode D seed (xs, ys) = history ∧
        xs seed.coordinate.val = x
      then exactPriorQuestionWeight G n (xs, ys)
      else 0 := by
  classical
  let y := ys seed.coordinate.val
  calc
    (∑ yy : Y,
      exactFiberQuestionWeight
        G n D seed history x yy xs ys) =
      exactFiberQuestionWeight
        G n D seed history x y xs ys := by
      apply Fintype.sum_eq_single y
      intro yy hyy
      unfold exactFiberQuestionWeight
      split_ifs with h
      · exact (hyy (show yy = y from h.2.2.2.2.symm)).elim
      · rfl
    _ = _ := by
      have hcompatible :
          (exactAliceQuestionCompatible
              D seed history x xs ∧
            exactBobQuestionCompatible
              D seed history y ys) ↔
            (exactRevealCode D seed (xs, ys) = history ∧
              xs seed.coordinate.val = x) := by
        simpa only [and_true, y] using
          (exactRevealCode_compatible_iff
            D seed history x y xs ys).symm
      simp only [exactFiberQuestionWeight, hcompatible, Game.repeat_questionWeight,
        exactPriorQuestionWeight]

theorem exactFiberQuestionWeight_sum_aliceQuestion
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (y : Y) (xs : Fin n → X) (ys : Fin n → Y) :
    (∑ x : X,
      exactFiberQuestionWeight
        G n D seed history x y xs ys) =
      if exactRevealCode D seed (xs, ys) = history ∧
        ys seed.coordinate.val = y
      then exactPriorQuestionWeight G n (xs, ys)
      else 0 := by
  classical
  let x := xs seed.coordinate.val
  calc
    (∑ xx : X,
      exactFiberQuestionWeight
        G n D seed history xx y xs ys) =
      exactFiberQuestionWeight
        G n D seed history x y xs ys := by
      apply Fintype.sum_eq_single x
      intro xx hxx
      unfold exactFiberQuestionWeight
      split_ifs with h
      · exact (hxx (show xx = x from h.1.2.2.2.symm)).elim
      · rfl
    _ = _ := by
      have hcompatible :
          (exactAliceQuestionCompatible
              D seed history x xs ∧
            exactBobQuestionCompatible
              D seed history y ys) ↔
            (exactRevealCode D seed (xs, ys) = history ∧
              ys seed.coordinate.val = y) := by
        simpa only [true_and, x] using
          (exactRevealCode_compatible_iff
            D seed history x y xs ys).symm
      simp only [exactFiberQuestionWeight, hcompatible, Game.repeat_questionWeight,
        exactPriorQuestionWeight]

theorem exactAliceQuestionMass_eq_sum_fiberMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) :
    exactAliceQuestionMass G n D seed history x =
      ∑ y : Y,
        exactFiberQuestionMass G n D seed history x y := by
  classical
  unfold exactAliceQuestionMass
  rw [Fintype.sum_prod_type]
  calc
    (∑ xs : Fin n → X, ∑ ys : Fin n → Y,
      if exactRevealCode D seed (xs, ys) = history ∧
        xs seed.coordinate.val = x
      then exactPriorQuestionWeight G n (xs, ys)
      else 0) =
      ∑ xs : Fin n → X, ∑ ys : Fin n → Y, ∑ y : Y,
        exactFiberQuestionWeight
          G n D seed history x y xs ys := by
      apply Finset.sum_congr rfl
      intro xs _
      apply Finset.sum_congr rfl
      intro ys _
      exact (exactFiberQuestionWeight_sum_bobQuestion
        G n D seed history x xs ys).symm
    _ = ∑ xs : Fin n → X, ∑ y : Y, ∑ ys : Fin n → Y,
        exactFiberQuestionWeight
          G n D seed history x y xs ys := by
      apply Finset.sum_congr rfl
      intro xs _
      rw [Finset.sum_comm]
    _ = ∑ y : Y, ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
        exactFiberQuestionWeight
          G n D seed history x y xs ys := by
      rw [Finset.sum_comm]
    _ = _ := by
      rfl

theorem exactBobQuestionMass_eq_sum_fiberMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (y : Y) :
    exactBobQuestionMass G n D seed history y =
      ∑ x : X,
        exactFiberQuestionMass G n D seed history x y := by
  classical
  unfold exactBobQuestionMass
  rw [Fintype.sum_prod_type]
  calc
    (∑ xs : Fin n → X, ∑ ys : Fin n → Y,
      if exactRevealCode D seed (xs, ys) = history ∧
        ys seed.coordinate.val = y
      then exactPriorQuestionWeight G n (xs, ys)
      else 0) =
      ∑ xs : Fin n → X, ∑ ys : Fin n → Y, ∑ x : X,
        exactFiberQuestionWeight
          G n D seed history x y xs ys := by
      apply Finset.sum_congr rfl
      intro xs _
      apply Finset.sum_congr rfl
      intro ys _
      exact (exactFiberQuestionWeight_sum_aliceQuestion
        G n D seed history y xs ys).symm
    _ = ∑ xs : Fin n → X, ∑ x : X, ∑ ys : Fin n → Y,
        exactFiberQuestionWeight
          G n D seed history x y xs ys := by
      apply Finset.sum_congr rfl
      intro xs _
      rw [Finset.sum_comm]
    _ = ∑ x : X, ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
        exactFiberQuestionWeight
          G n D seed history x y xs ys := by
      rw [Finset.sum_comm]
    _ = _ := by
      rfl

theorem exactCompatible_aliceMixed_coordinate_eq_or
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y y' : Y)
    (xs xs' : Fin n → X) (ys ys' : Fin n → Y)
    (ha : exactAliceQuestionCompatible
      D seed history x xs)
    (ha' : exactAliceQuestionCompatible
      D seed history x xs')
    (hb : exactBobQuestionCompatible
      D seed history y ys)
    (hb' : exactBobQuestionCompatible
      D seed history y' ys')
    (j : Fin n) :
    xs j = xs' j ∨ ys j = ys' j := by
  by_cases hj : j ∈ D
  · left
    exact (ha.1 ⟨j, hj⟩).trans (ha'.1 ⟨j, hj⟩).symm
  · let jr : SourceRemainingCoordinate D :=
      ⟨j, by simp only [mem_sdiff, mem_univ, hj, not_false_eq_true, and_self]⟩
    by_cases hcoordinate : jr = seed.coordinate
    · left
      have hval : j = seed.coordinate.val :=
        congrArg Subtype.val hcoordinate
      rw [hval]
      exact ha.2.2.2.trans ha'.2.2.2.symm
    · cases hbit : seed.partition jr with
      | false =>
          left
          have hleft :
              jr ∈ exactLeft
                seed.coordinate seed.partition := by
            simp only [exactLeft, ne_eq, univ_eq_attach, mem_filter, mem_attach, hcoordinate,
              not_false_eq_true, hbit, and_self]
          exact (ha.2.1 ⟨jr, hleft⟩).trans
            (ha'.2.1 ⟨jr, hleft⟩).symm
      | true =>
          right
          have hright :
              jr ∈ exactRight
                seed.coordinate seed.partition := by
            simp only [exactRight, ne_eq, univ_eq_attach, mem_filter, mem_attach, hcoordinate,
              not_false_eq_true, hbit, and_self]
          exact (hb.2.1 ⟨jr, hright⟩).trans
            (hb'.2.1 ⟨jr, hright⟩).symm

theorem exactQuestionWeight_aliceMixed_rectangle
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y y' : Y)
    (xs xs' : Fin n → X) (ys ys' : Fin n → Y)
    (ha : exactAliceQuestionCompatible
      D seed history x xs)
    (ha' : exactAliceQuestionCompatible
      D seed history x xs')
    (hb : exactBobQuestionCompatible
      D seed history y ys)
    (hb' : exactBobQuestionCompatible
      D seed history y' ys') :
    (G.repeat n).questionWeight xs ys *
        (G.repeat n).questionWeight xs' ys' =
      (G.repeat n).questionWeight xs ys' *
        (G.repeat n).questionWeight xs' ys := by
  simp only [Game.repeat_questionWeight]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rcases exactCompatible_aliceMixed_coordinate_eq_or
    D seed history x y y' xs xs' ys ys'
    ha ha' hb hb' j with hAlice | hBob
  · simp only [hAlice, mul_comm]
  · simp only [hBob]

theorem exactFiberQuestionWeight_aliceMixed_rectangle
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y y' : Y)
    (xs xs' : Fin n → X) (ys ys' : Fin n → Y) :
    exactFiberQuestionWeight
        G n D seed history x y xs ys *
      exactFiberQuestionWeight
        G n D seed history x y' xs' ys' =
    exactFiberQuestionWeight
        G n D seed history x y' xs ys' *
      exactFiberQuestionWeight
        G n D seed history x y xs' ys := by
  classical
  by_cases ha : exactAliceQuestionCompatible
      D seed history x xs <;>
    by_cases ha' : exactAliceQuestionCompatible
      D seed history x xs' <;>
    by_cases hb : exactBobQuestionCompatible
      D seed history y ys <;>
    by_cases hb' : exactBobQuestionCompatible
      D seed history y' ys' <;>
    simp [exactFiberQuestionWeight,
      ha, ha', hb, hb']
  simpa only [Game.repeat_questionWeight] using
    (exactQuestionWeight_aliceMixed_rectangle
      G n D seed history x y y' xs xs' ys ys'
      ha ha' hb hb')

theorem exactCompatible_bobMixed_coordinate_eq_or
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x x' : X) (y : Y)
    (xs xs' : Fin n → X) (ys ys' : Fin n → Y)
    (ha : exactAliceQuestionCompatible
      D seed history x xs)
    (ha' : exactAliceQuestionCompatible
      D seed history x' xs')
    (hb : exactBobQuestionCompatible
      D seed history y ys)
    (hb' : exactBobQuestionCompatible
      D seed history y ys')
    (j : Fin n) :
    xs j = xs' j ∨ ys j = ys' j := by
  by_cases hj : j ∈ D
  · left
    exact (ha.1 ⟨j, hj⟩).trans (ha'.1 ⟨j, hj⟩).symm
  · let jr : SourceRemainingCoordinate D :=
      ⟨j, by simp only [mem_sdiff, mem_univ, hj, not_false_eq_true, and_self]⟩
    by_cases hcoordinate : jr = seed.coordinate
    · right
      have hval : j = seed.coordinate.val :=
        congrArg Subtype.val hcoordinate
      rw [hval]
      exact hb.2.2.2.trans hb'.2.2.2.symm
    · cases hbit : seed.partition jr with
      | false =>
          left
          have hleft :
              jr ∈ exactLeft
                seed.coordinate seed.partition := by
            simp only [exactLeft, ne_eq, univ_eq_attach, mem_filter, mem_attach, hcoordinate,
              not_false_eq_true, hbit, and_self]
          exact (ha.2.1 ⟨jr, hleft⟩).trans
            (ha'.2.1 ⟨jr, hleft⟩).symm
      | true =>
          right
          have hright :
              jr ∈ exactRight
                seed.coordinate seed.partition := by
            simp only [exactRight, ne_eq, univ_eq_attach, mem_filter, mem_attach, hcoordinate,
              not_false_eq_true, hbit, and_self]
          exact (hb.2.1 ⟨jr, hright⟩).trans
            (hb'.2.1 ⟨jr, hright⟩).symm

theorem exactQuestionWeight_bobMixed_rectangle
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x x' : X) (y : Y)
    (xs xs' : Fin n → X) (ys ys' : Fin n → Y)
    (ha : exactAliceQuestionCompatible
      D seed history x xs)
    (ha' : exactAliceQuestionCompatible
      D seed history x' xs')
    (hb : exactBobQuestionCompatible
      D seed history y ys)
    (hb' : exactBobQuestionCompatible
      D seed history y ys') :
    (G.repeat n).questionWeight xs ys *
        (G.repeat n).questionWeight xs' ys' =
      (G.repeat n).questionWeight xs ys' *
        (G.repeat n).questionWeight xs' ys := by
  simp only [Game.repeat_questionWeight]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rcases exactCompatible_bobMixed_coordinate_eq_or
    D seed history x x' y xs xs' ys ys'
    ha ha' hb hb' j with hAlice | hBob
  · simp only [hAlice, mul_comm]
  · simp only [hBob]

theorem exactFiberQuestionWeight_bobMixed_rectangle
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x x' : X) (y : Y)
    (xs xs' : Fin n → X) (ys ys' : Fin n → Y) :
    exactFiberQuestionWeight
        G n D seed history x y xs ys *
      exactFiberQuestionWeight
        G n D seed history x' y xs' ys' =
    exactFiberQuestionWeight
        G n D seed history x y xs ys' *
      exactFiberQuestionWeight
        G n D seed history x' y xs' ys := by
  classical
  by_cases ha : exactAliceQuestionCompatible
      D seed history x xs <;>
    by_cases ha' : exactAliceQuestionCompatible
      D seed history x' xs' <;>
    by_cases hb : exactBobQuestionCompatible
      D seed history y ys <;>
    by_cases hb' : exactBobQuestionCompatible
      D seed history y ys' <;>
    simp [exactFiberQuestionWeight,
      ha, ha', hb, hb']
  simpa only [Game.repeat_questionWeight] using
    (exactQuestionWeight_bobMixed_rectangle
      G n D seed history x x' y xs xs' ys ys'
      ha ha' hb hb')

theorem exactMixedRowMarginal_mul_total
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (left right : ι → κ → ℝ)
    (rectangle : ∀ i i' j j',
      left i j * right i' j' = right i j' * left i' j)
    (i : ι) :
    (∑ j : κ, left i j) *
        (∑ i' : ι, ∑ j' : κ, right i' j') =
      (∑ j' : κ, right i j') *
        (∑ i' : ι, ∑ j : κ, left i' j) := by
  classical
  calc
    (∑ j : κ, left i j) *
        (∑ i' : ι, ∑ j' : κ, right i' j') =
      ∑ j : κ, ∑ i' : ι, ∑ j' : κ,
        left i j * right i' j' := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i' _
      rw [Finset.mul_sum]
    _ = ∑ j : κ, ∑ i' : ι, ∑ j' : κ,
        right i j' * left i' j := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i' _
      apply Finset.sum_congr rfl
      intro j' _
      exact rectangle i i' j j'
    _ = ∑ j : κ, ∑ i' : ι,
        (∑ j' : κ, right i j') * left i' j := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i' _
      rw [Finset.sum_mul]
    _ = ∑ i' : ι, ∑ j : κ,
        (∑ j' : κ, right i j') * left i' j := by
      rw [Finset.sum_comm]
    _ = (∑ j' : κ, right i j') *
        (∑ i' : ι, ∑ j : κ, left i' j) := by
      simp only [Finset.mul_sum]

theorem exactFiberAliceMarginal_mul_cross_mass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y y' : Y) (xs : Fin n → X) :
    exactFiberAliceMarginal
        G n D seed history x y xs *
      exactFiberQuestionMass
        G n D seed history x y' =
    exactFiberAliceMarginal
        G n D seed history x y' xs *
      exactFiberQuestionMass
        G n D seed history x y := by
  apply exactMixedRowMarginal_mul_total
    (exactFiberQuestionWeight G n D seed history x y)
    (exactFiberQuestionWeight G n D seed history x y')
  intro u v s t
  exact exactFiberQuestionWeight_aliceMixed_rectangle
    G n D seed history x y y' u v s t

theorem exactFiberBobMarginal_mul_cross_mass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x x' : X) (y : Y) (ys : Fin n → Y) :
    exactFiberBobMarginal
        G n D seed history x y ys *
      exactFiberQuestionMass
        G n D seed history x' y =
    exactFiberBobMarginal
        G n D seed history x' y ys *
      exactFiberQuestionMass
        G n D seed history x y := by
  classical
  have hcross := exactMixedRowMarginal_mul_total
    (fun yy xx => exactFiberQuestionWeight
      G n D seed history x y xx yy)
    (fun yy xx => exactFiberQuestionWeight
      G n D seed history x' y xx yy)
    (by
      intro u v s t
      simpa only [mul_comm] using
        (exactFiberQuestionWeight_bobMixed_rectangle
          G n D seed history x x' y s t u v)) ys
  change
    (∑ xs : Fin n → X,
      exactFiberQuestionWeight
        G n D seed history x y xs ys) *
      (∑ xx : Fin n → X, ∑ yy : Fin n → Y,
        exactFiberQuestionWeight
          G n D seed history x' y xx yy) =
    (∑ xs : Fin n → X,
      exactFiberQuestionWeight
        G n D seed history x' y xs ys) *
      (∑ xx : Fin n → X, ∑ yy : Fin n → Y,
        exactFiberQuestionWeight
          G n D seed history x y xx yy)
  calc
    _ =
      (∑ xs : Fin n → X,
        exactFiberQuestionWeight
          G n D seed history x y xs ys) *
      (∑ yy : Fin n → Y, ∑ xx : Fin n → X,
        exactFiberQuestionWeight
          G n D seed history x' y xx yy) := by
      rw [Finset.sum_comm]
    _ =
      (∑ xs : Fin n → X,
        exactFiberQuestionWeight
          G n D seed history x' y xs ys) *
      (∑ yy : Fin n → Y, ∑ xx : Fin n → X,
        exactFiberQuestionWeight
          G n D seed history x y xx yy) := hcross
    _ = _ := by
      rw [Finset.sum_comm]

theorem exactFiberQuestionWeight_nonneg
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y)
    (xs : Fin n → X) (ys : Fin n → Y) :
    0 ≤ exactFiberQuestionWeight
      G n D seed history x y xs ys := by
  unfold exactFiberQuestionWeight
  split
  · exact (G.repeat n).weight_nonneg xs ys
  · exact le_rfl

theorem exactFiberQuestionMass_nonneg
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y) :
    0 ≤ exactFiberQuestionMass
      G n D seed history x y := by
  unfold exactFiberQuestionMass
  exact Finset.sum_nonneg (fun xs _ =>
    Finset.sum_nonneg (fun ys _ =>
      exactFiberQuestionWeight_nonneg
        G n D seed history x y xs ys))

theorem exactAliceFiberNormalizedRow
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y) (xs : Fin n → X)
    (nonzero : exactFiberQuestionMass
      G n D seed history x y ≠ 0) :
    exactFiberAliceMarginal
        G n D seed history x y xs /
      exactFiberQuestionMass
        G n D seed history x y =
      (∑ yy : Y,
        exactFiberAliceMarginal
          G n D seed history x yy xs) /
      exactAliceQuestionMass
        G n D seed history x := by
  classical
  rw [exactAliceQuestionMass_eq_sum_fiberMass]
  have hypos : 0 < exactFiberQuestionMass
      G n D seed history x y :=
    lt_of_le_of_ne
      (exactFiberQuestionMass_nonneg
        G n D seed history x y) (Ne.symm nonzero)
  have hsum :
      (∑ yy : Y,
        exactFiberQuestionMass
          G n D seed history x yy) ≠ 0 := by
    apply ne_of_gt
    exact lt_of_lt_of_le hypos
      (Finset.single_le_sum
        (fun yy _ => exactFiberQuestionMass_nonneg
          G n D seed history x yy)
        (Finset.mem_univ y))
  apply (div_eq_div_iff nonzero hsum).mpr
  calc
    exactFiberAliceMarginal
        G n D seed history x y xs *
      (∑ yy : Y,
        exactFiberQuestionMass
          G n D seed history x yy) =
      ∑ yy : Y,
        exactFiberAliceMarginal
          G n D seed history x y xs *
        exactFiberQuestionMass
          G n D seed history x yy := by
      rw [Finset.mul_sum]
    _ = ∑ yy : Y,
        exactFiberAliceMarginal
          G n D seed history x yy xs *
        exactFiberQuestionMass
          G n D seed history x y := by
      apply Finset.sum_congr rfl
      intro yy _
      exact exactFiberAliceMarginal_mul_cross_mass
        G n D seed history x y yy xs
    _ = (∑ yy : Y,
        exactFiberAliceMarginal
          G n D seed history x yy xs) *
        exactFiberQuestionMass
          G n D seed history x y := by
      rw [Finset.sum_mul]

theorem exactBobFiberNormalizedColumn
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y) (ys : Fin n → Y)
    (nonzero : exactFiberQuestionMass
      G n D seed history x y ≠ 0) :
    exactFiberBobMarginal
        G n D seed history x y ys /
      exactFiberQuestionMass
        G n D seed history x y =
      (∑ xx : X,
        exactFiberBobMarginal
          G n D seed history xx y ys) /
      exactBobQuestionMass
        G n D seed history y := by
  classical
  rw [exactBobQuestionMass_eq_sum_fiberMass]
  have hxpos : 0 < exactFiberQuestionMass
      G n D seed history x y :=
    lt_of_le_of_ne
      (exactFiberQuestionMass_nonneg
        G n D seed history x y) (Ne.symm nonzero)
  have hsum :
      (∑ xx : X,
        exactFiberQuestionMass
          G n D seed history xx y) ≠ 0 := by
    apply ne_of_gt
    exact lt_of_lt_of_le hxpos
      (Finset.single_le_sum
        (fun xx _ => exactFiberQuestionMass_nonneg
          G n D seed history xx y)
        (Finset.mem_univ x))
  apply (div_eq_div_iff nonzero hsum).mpr
  calc
    exactFiberBobMarginal
        G n D seed history x y ys *
      (∑ xx : X,
        exactFiberQuestionMass
          G n D seed history xx y) =
      ∑ xx : X,
        exactFiberBobMarginal
          G n D seed history x y ys *
        exactFiberQuestionMass
          G n D seed history xx y := by
      rw [Finset.mul_sum]
    _ = ∑ xx : X,
        exactFiberBobMarginal
          G n D seed history xx y ys *
        exactFiberQuestionMass
          G n D seed history x y := by
      apply Finset.sum_congr rfl
      intro xx _
      exact exactFiberBobMarginal_mul_cross_mass
        G n D seed history x xx y ys
    _ = (∑ xx : X,
        exactFiberBobMarginal
          G n D seed history xx y ys) *
        exactFiberQuestionMass
          G n D seed history x y := by
      rw [Finset.sum_mul]

theorem exactAliceConditionalMatrix_eq_joint
    {d : Type*}
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y)
    (nonzero : exactFiberQuestionMass
      G n D seed history x y ≠ 0)
    (E : (Fin n → X) → Matrix d d ℂ) :
    (∑ q : ExactFullQuestion X Y n,
      if exactRevealCode D seed q = history ∧
        q.1 seed.coordinate.val = x
      then
        (exactPriorQuestionWeight G n q /
          exactAliceQuestionMass
            G n D seed history x) • E q.1
      else 0) =
      ∑ xs : Fin n → X,
        (exactFiberAliceMarginal
          G n D seed history x y xs /
          exactFiberQuestionMass
            G n D seed history x y) • E xs := by
  classical
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro xs _
  calc
    (∑ ys : Fin n → Y,
      if exactRevealCode D seed (xs, ys) = history ∧
        xs seed.coordinate.val = x
      then
        (exactPriorQuestionWeight G n (xs, ys) /
          exactAliceQuestionMass
            G n D seed history x) • E xs
      else 0) =
      (∑ ys : Fin n → Y,
        ((if exactRevealCode D seed (xs, ys) = history ∧
          xs seed.coordinate.val = x
        then exactPriorQuestionWeight G n (xs, ys)
        else 0) /
          exactAliceQuestionMass
            G n D seed history x) • E xs) := by
      apply Finset.sum_congr rfl
      intro ys _
      split_ifs <;> simp
    _ = ((∑ ys : Fin n → Y,
        if exactRevealCode D seed (xs, ys) = history ∧
          xs seed.coordinate.val = x
        then exactPriorQuestionWeight G n (xs, ys)
        else 0) /
          exactAliceQuestionMass
            G n D seed history x) • E xs := by
      rw [Finset.sum_div, Finset.sum_smul]
    _ = ((∑ yy : Y,
        exactFiberAliceMarginal
          G n D seed history x yy xs) /
          exactAliceQuestionMass
            G n D seed history x) • E xs := by
      congr 2
      calc
        (∑ ys : Fin n → Y,
          if exactRevealCode D seed (xs, ys) = history ∧
            xs seed.coordinate.val = x
          then exactPriorQuestionWeight G n (xs, ys)
          else 0) =
          ∑ ys : Fin n → Y, ∑ yy : Y,
            exactFiberQuestionWeight
              G n D seed history x yy xs ys := by
          apply Finset.sum_congr rfl
          intro ys _
          exact (exactFiberQuestionWeight_sum_bobQuestion
            G n D seed history x xs ys).symm
        _ = ∑ yy : Y, ∑ ys : Fin n → Y,
            exactFiberQuestionWeight
              G n D seed history x yy xs ys := by
          rw [Finset.sum_comm]
        _ = _ := by
          rfl
    _ = _ := by
      rw [← exactAliceFiberNormalizedRow
        G n D seed history x y xs nonzero]

theorem exactBobConditionalMatrix_eq_joint
    {d : Type*}
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y)
    (nonzero : exactFiberQuestionMass
      G n D seed history x y ≠ 0)
    (E : (Fin n → Y) → Matrix d d ℂ) :
    (∑ q : ExactFullQuestion X Y n,
      if exactRevealCode D seed q = history ∧
        q.2 seed.coordinate.val = y
      then
        (exactPriorQuestionWeight G n q /
          exactBobQuestionMass
            G n D seed history y) • E q.2
      else 0) =
      ∑ ys : Fin n → Y,
        (exactFiberBobMarginal
          G n D seed history x y ys /
          exactFiberQuestionMass
            G n D seed history x y) • E ys := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ys _
  calc
    (∑ xs : Fin n → X,
      if exactRevealCode D seed (xs, ys) = history ∧
        ys seed.coordinate.val = y
      then
        (exactPriorQuestionWeight G n (xs, ys) /
          exactBobQuestionMass
            G n D seed history y) • E ys
      else 0) =
      (∑ xs : Fin n → X,
        ((if exactRevealCode D seed (xs, ys) = history ∧
          ys seed.coordinate.val = y
        then exactPriorQuestionWeight G n (xs, ys)
        else 0) /
          exactBobQuestionMass
            G n D seed history y) • E ys) := by
      apply Finset.sum_congr rfl
      intro xs _
      split_ifs <;> simp
    _ = ((∑ xs : Fin n → X,
        if exactRevealCode D seed (xs, ys) = history ∧
          ys seed.coordinate.val = y
        then exactPriorQuestionWeight G n (xs, ys)
        else 0) /
          exactBobQuestionMass
            G n D seed history y) • E ys := by
      rw [Finset.sum_div, Finset.sum_smul]
    _ = ((∑ xx : X,
        exactFiberBobMarginal
          G n D seed history xx y ys) /
          exactBobQuestionMass
            G n D seed history y) • E ys := by
      congr 2
      calc
        (∑ xs : Fin n → X,
          if exactRevealCode D seed (xs, ys) = history ∧
            ys seed.coordinate.val = y
          then exactPriorQuestionWeight G n (xs, ys)
          else 0) =
          ∑ xs : Fin n → X, ∑ xx : X,
            exactFiberQuestionWeight
              G n D seed history xx y xs ys := by
          apply Finset.sum_congr rfl
          intro xs _
          exact (exactFiberQuestionWeight_sum_aliceQuestion
            G n D seed history y xs ys).symm
        _ = ∑ xx : X, ∑ xs : Fin n → X,
            exactFiberQuestionWeight
              G n D seed history xx y xs ys := by
          rw [Finset.sum_comm]
        _ = _ := by
          rfl
    _ = _ := by
      rw [← exactBobFiberNormalizedColumn
        G n D seed history x y ys nonzero]

theorem exactAliceQuestionFilter_eq_joint
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) (y : Y)
    (nonzero : exactFiberQuestionMass
      G n D seed history x y ≠ 0) :
    exactAliceQuestionFilter
        G n S D seed history answer x =
      exactJointAliceQuestionFilter
        G n S D seed history answer x y := by
  exact exactAliceConditionalMatrix_eq_joint
    G n D seed history x y nonzero
    (conditionedAliceEffect G n S D answer)

theorem exactBobQuestionFilter_eq_joint
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (x : X) (y : Y)
    (nonzero : exactFiberQuestionMass
      G n D seed history x y ≠ 0) :
    exactBobQuestionFilter
        G n S D seed history answer y =
      exactJointBobQuestionFilter
        G n S D seed history answer x y := by
  exact exactBobConditionalMatrix_eq_joint
    G n D seed history x y nonzero
    (conditionedBobEffect G n S D answer)

theorem exactAliceCoordinateFilter_eq_joint
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) (y : Y) (a : A)
    (nonzero : exactFiberQuestionMass
      G n D seed history x y ≠ 0) :
    exactAliceCoordinateFilter
        G n S D seed history answer x a =
      exactJointAliceCoordinateFilter
        G n S D seed history answer x y a := by
  exact exactAliceConditionalMatrix_eq_joint
    G n D seed history x y nonzero
    (fun xs => conditionedAliceCoordinateEffect
      G n S D answer xs seed.coordinate.val a)

theorem exactBobCoordinateFilter_eq_joint
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (x : X) (y : Y) (b : B)
    (nonzero : exactFiberQuestionMass
      G n D seed history x y ≠ 0) :
    exactBobCoordinateFilter
        G n S D seed history answer y b =
      exactJointBobCoordinateFilter
        G n S D seed history answer x y b := by
  exact exactBobConditionalMatrix_eq_joint
    G n D seed history x y nonzero
    (fun ys => conditionedBobCoordinateEffect
      G n S D answer ys seed.coordinate.val b)

theorem exactSourceEquationTen
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (aliceAnswer : {j : Fin n // j ∈ D} → A)
    (bobAnswer : {j : Fin n // j ∈ D} → B)
    (x : X) (y : Y)
    (nonzero : exactFiberQuestionMass
      G n D seed history x y ≠ 0) :
    bornTracePairing S.state.matrix
        (exactAliceQuestionFilter
          G n S D seed history aliceAnswer x)
        (exactBobQuestionFilter
          G n S D seed history bobAnswer y) =
      ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
        exactConditionalQuestionWeight
          G n D seed history x y xs ys *
        bornTracePairing S.state.matrix
          (conditionedAliceEffect G n S D aliceAnswer xs)
          (conditionedBobEffect G n S D bobAnswer ys) := by
  rw [exactAliceQuestionFilter_eq_joint
    G n S D seed history aliceAnswer x y nonzero,
    exactBobQuestionFilter_eq_joint
    G n S D seed history bobAnswer x y nonzero]
  exact exactJointQuestionFilter_born
    G n S D seed history aliceAnswer bobAnswer x y nonzero

end

end QuantumParallelRepetition

end
