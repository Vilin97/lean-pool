/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.ConcreteClosure
import LeanPool.Wallace.CountableDisjointization
import LeanPool.Wallace.FusionSchedule
import LeanPool.Wallace.BoundedIndependentMap

/-!
# The concrete countable block schedule around one nonzero vector

For one nonzero vector `x`, only codes whose fresh coordinates lie in its dependency closure
matter to the local fusion.  They form a countable type.  This module disjointizes their fixed
almost-disjoint labels, selects the unique active code at each block label, and defines the
finite independent set presented to bounded deletion at that stage.
-/

open Set

namespace Wallace
namespace ConcreteLocalSetup

noncomputable section

open TriangularPreprocess
open ConcreteData
open ConcreteClosure
open FiniteCombinatorics

variable (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) (M : ℕ → ℕ)

/-- Codes whose prescribed basis coordinate belongs to the local dependency closure of `x`. -/
abbrev RelevantCode (x : ContinuumFreeGroup) :=
  {a : ContinuumIndex // codeIndex a ∈ closure N hN M x}

theorem relevantCode_countable (x : ContinuumFreeGroup) :
    Countable (RelevantCode N hN M x) := by
  apply Countable.to_subtype
  exact countable_preimage_of_injective codeIndex (closure_countable N hN M x)

private theorem relevantLabels_pairwise (x : ContinuumFreeGroup) :
    Pairwise fun a b : RelevantCode N hN M x ↦
      (label a.1 ∩ label b.1).Finite := by
  intro a b hab
  apply label_inter_finite
  intro heq
  apply hab
  exact Subtype.ext heq

/-- Pairwise disjoint labels obtained by deleting finitely many points from each relevant
almost-disjoint label. -/
def refinedLabel (x : ContinuumFreeGroup) : RelevantCode N hN M x → Set ℕ := by
  letI : Countable (RelevantCode N hN M x) := relevantCode_countable N hN M x
  exact Classical.choose
    (exists_disjoint_refinement_countable
      (fun a : RelevantCode N hN M x ↦ label a.1)
      (relevantLabels_pairwise N hN M x))

theorem refinedLabel_pairwise (x : ContinuumFreeGroup) :
    Pairwise fun a b : RelevantCode N hN M x ↦
      Disjoint (refinedLabel N hN M x a) (refinedLabel N hN M x b) := by
  letI : Countable (RelevantCode N hN M x) := relevantCode_countable N hN M x
  exact (Classical.choose_spec
    (exists_disjoint_refinement_countable
      (fun a : RelevantCode N hN M x ↦ label a.1)
      (relevantLabels_pairwise N hN M x))).1

theorem label_diff_refinedLabel_finite
    (x : ContinuumFreeGroup) (a : RelevantCode N hN M x) :
    (label a.1 \ refinedLabel N hN M x a).Finite := by
  letI : Countable (RelevantCode N hN M x) := relevantCode_countable N hN M x
  exact (Classical.choose_spec
    (exists_disjoint_refinement_countable
      (fun a : RelevantCode N hN M x ↦ label a.1)
      (relevantLabels_pairwise N hN M x))).2 a |>.2

theorem refinedLabel_unique (x : ContinuumFreeGroup) {l : ℕ}
    {a b : RelevantCode N hN M x}
    (ha : l ∈ refinedLabel N hN M x a)
    (hb : l ∈ refinedLabel N hN M x b) : a = b := by
  by_contra hab
  exact Set.disjoint_left.mp (refinedLabel_pairwise N hN M x hab) ha hb

/-- The unique relevant code scheduled at label `l`, if there is one. -/
def activeCode (x : ContinuumFreeGroup) (l : ℕ) :
    Option (RelevantCode N hN M x) := by
  classical
  exact if h : ∃ a, l ∈ refinedLabel N hN M x a then
    some (Classical.choose h) else none

theorem activeCode_eq_some_of_mem (x : ContinuumFreeGroup) (l : ℕ)
    (a : RelevantCode N hN M x) (ha : l ∈ refinedLabel N hN M x a) :
    activeCode N hN M x l = some a := by
  classical
  unfold activeCode
  split
  · rename_i h
    congr 1
    exact refinedLabel_unique N hN M x (Classical.choose_spec h) ha
  · rename_i h
    exact (h ⟨a, ha⟩).elim

/-! ## Restriction to the countable local free group -/

/-- Inclusion of the free group on the closure coordinates into the ambient free group. -/
def closureInclusion (x : ContinuumFreeGroup) :
    (closure N hN M x →₀ ℤ) →+ ContinuumFreeGroup :=
  by
    classical
    exact Finsupp.embDomain.addMonoidHom
      (.subtype (closure N hN M x : ContinuumIndex → Prop))

theorem closureInclusion_apply (x : ContinuumFreeGroup)
    (z : closure N hN M x →₀ ℤ) :
    closureInclusion N hN M x z =
      Finsupp.embDomain
        (.subtype (closure N hN M x : ContinuumIndex → Prop)) z := by
  classical
  rfl

theorem closureInclusion_injective (x : ContinuumFreeGroup) :
    Function.Injective (closureInclusion N hN M x) := by
  classical
  intro y z h
  apply Finsupp.embDomain_injective
    (.subtype (closure N hN M x : ContinuumIndex → Prop))
  change Finsupp.embDomain
    (.subtype (closure N hN M x : ContinuumIndex → Prop)) y =
      Finsupp.embDomain
        (.subtype (closure N hN M x : ContinuumIndex → Prop)) z at h
  exact h

/-- The shifted prepared value, restricted to the local closure. -/
def localDifference (x : ContinuumFreeGroup)
    (a : RelevantCode N hN M x) (n : ℕ) : closure N hN M x →₀ ℤ :=
  by
    classical
    exact Finsupp.subtypeDomain (closure N hN M x)
      (prepared N hN M a.1 n - codeBasisVector a.1)

private theorem difference_support_subset_closure
    (x : ContinuumFreeGroup) (a : RelevantCode N hN M x) (n : ℕ) :
    ∀ i ∈ (prepared N hN M a.1 n - codeBasisVector a.1).support,
      i ∈ closure N hN M x := by
  intro i hi
  by_contra hiD
  have hprep0 : prepared N hN M a.1 n i = 0 := by
    by_contra hne
    apply hiD
    exact prepared_support_mem_closure N hN M x a.1 a.2 n i
      (Finsupp.mem_support_iff.mpr hne)
  have hbasis0 : codeBasisVector a.1 i = 0 := by
    by_cases hai : codeIndex a.1 = i
    · apply (hiD (hai ▸ a.2)).elim
    · simp [codeBasisVector, hai]
  have hne :
      (prepared N hN M a.1 n - codeBasisVector a.1) i ≠ 0 :=
    Finsupp.mem_support_iff.mp hi
  exact hne (by simp [hprep0, hbasis0])

theorem closureInclusion_localDifference
    (x : ContinuumFreeGroup) (a : RelevantCode N hN M x) (n : ℕ) :
    closureInclusion N hN M x (localDifference N hN M x a n) =
      prepared N hN M a.1 n - codeBasisVector a.1 := by
  classical
  letI : DecidablePred (closure N hN M x : ContinuumIndex → Prop) :=
    fun _ ↦ Classical.propDecidable _
  rw [closureInclusion_apply]
  change Finsupp.embDomain
    (.subtype (closure N hN M x : ContinuumIndex → Prop))
      (Finsupp.subtypeDomain (closure N hN M x)
        (prepared N hN M a.1 n - codeBasisVector a.1)) = _
  exact
    (Finsupp.extendDomain_eq_embDomain_subtype
      (P := (closure N hN M x : ContinuumIndex → Prop))
      (Finsupp.subtypeDomain (closure N hN M x)
        (prepared N hN M a.1 n - codeBasisVector a.1))).symm.trans
      (Finsupp.extendDomain_subtypeDomain
        (prepared N hN M a.1 n - codeBasisVector a.1)
        (difference_support_subset_closure N hN M x a n))

theorem localDifference_injective
    (x : ContinuumFreeGroup) (a : RelevantCode N hN M x) :
    Function.Injective (localDifference N hN M x a) := by
  intro m n hmn
  apply preparedDifference_injective N hN M a.1
  change prepared N hN M a.1 m - codeBasisVector a.1 =
    prepared N hN M a.1 n - codeBasisVector a.1
  rw [← closureInclusion_localDifference N hN M x a m,
    ← closureInclusion_localDifference N hN M x a n, hmn]

/-- The independent shifted set in one block, now inside the countable local group. -/
def localDifferenceBlock (x : ContinuumFreeGroup)
    (a : RelevantCode N hN M x) (l : ℕ) :
    Finset (closure N hN M x →₀ ℤ) :=
  (blockPositions N hN l).image (localDifference N hN M x a)

theorem localDifferenceBlock_card
    (x : ContinuumFreeGroup) (a : RelevantCode N hN M x) (l : ℕ) :
    (localDifferenceBlock N hN M x a l).card = N l := by
  rw [localDifferenceBlock,
    Finset.card_image_iff.mpr (localDifference_injective N hN M x a).injOn,
    blockPositions_card]

theorem localDifferenceBlock_image_inclusion
    (x : ContinuumFreeGroup) (a : RelevantCode N hN M x) (l : ℕ) :
    (localDifferenceBlock N hN M x a l).image (closureInclusion N hN M x) =
      differenceBlock N hN M a.1 l := by
  rw [localDifferenceBlock, differenceBlock, Finset.image_image]
  apply Finset.image_congr
  intro n hn
  exact closureInclusion_localDifference N hN M x a n

theorem localDifferenceBlock_boundedIndependent
    (x : ContinuumFreeGroup) (a : RelevantCode N hN M x) (l : ℕ) :
    BoundedIndependent (M l) (localDifferenceBlock N hN M x a l) := by
  apply boundedIndependent_of_image (closureInclusion N hN M x)
    (closureInclusion_injective N hN M x)
  rw [localDifferenceBlock_image_inclusion]
  exact differenceBlock_boundedIndependent N hN M a.1 l

/-- The active finite set inside the local free group. -/
def localActiveBlock (x : ContinuumFreeGroup) (l : ℕ) :
    Finset (closure N hN M x →₀ ℤ) :=
  match activeCode N hN M x l with
  | none => ∅
  | some a => localDifferenceBlock N hN M x a l

theorem localActiveBlock_eq_of_mem (x : ContinuumFreeGroup) (l : ℕ)
    (a : RelevantCode N hN M x) (ha : l ∈ refinedLabel N hN M x a) :
    localActiveBlock N hN M x l = localDifferenceBlock N hN M x a l := by
  simp [localActiveBlock, activeCode_eq_some_of_mem N hN M x l a ha]

theorem localActiveBlock_boundedIndependent (x : ContinuumFreeGroup) (l : ℕ) :
    BoundedIndependent (M l) (localActiveBlock N hN M x l) := by
  unfold localActiveBlock
  split
  · simp [BoundedIndependent]
  · rename_i a hactive
    exact localDifferenceBlock_boundedIndependent N hN M x a l

theorem localActiveBlock_card_le (x : ContinuumFreeGroup) (l : ℕ) :
    (localActiveBlock N hN M x l).card ≤ N l := by
  unfold localActiveBlock
  split
  · simp
  · rename_i a hactive
    rw [localDifferenceBlock_card]

end

end ConcreteLocalSetup
end Wallace
