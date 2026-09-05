/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.BlockFilters

/-!
# Disjointizing a countable almost-disjoint family

The block fusion uses a countable subfamily of the fixed almost-disjoint family.  This module
orders any countable index type by an injection into `ℕ` and applies the standard predecessor
deletion.  Each label loses only finitely many points.
-/

open Set

namespace Wallace

noncomputable section

open AlmostDisjoint

universe u v

/-- Every countable almost-disjoint family has a pairwise disjoint refinement modulo finite
sets.  Unlike an enumeration by a surjection, this statement also handles finite and empty
index types without duplicate indices. -/
theorem exists_disjoint_refinement_countable
    {ι : Type u} {α : Type v} [Countable ι]
    (family : ι → Set α)
    (had : Pairwise fun i j ↦ (family i ∩ family j).Finite) :
    ∃ refined : ι → Set α,
      (Pairwise fun i j ↦ Disjoint (refined i) (refined j)) ∧
        ∀ i, refined i ⊆ family i ∧ (family i \ refined i).Finite := by
  let rank : ι → ℕ := Classical.choose (exists_injective_nat ι)
  have hrank : Function.Injective rank := Classical.choose_spec (exists_injective_nat ι)
  let : LinearOrder ι := LinearOrder.lift' rank hrank
  have hpred (i : ι) : (Set.Iio i).Finite := by
    have heq : Set.Iio i = rank ⁻¹' Set.Iio (rank i) := by
      ext j
      rfl
    rw [heq]
    exact (Set.finite_Iio (rank i)).preimage hrank.injOn
  refine ⟨disjointize family, pairwise_disjoint_disjointize family, ?_⟩
  intro i
  exact ⟨disjointize_subset family i, disjointize_loss_finite family had i (hpred i)⟩

/-! ## Scheduling the relevant Wallace codes -/

namespace LocalCodeSchedule

open BlockData TriangularPreprocess

/-- Codes whose distinguished coordinate belongs to a given coordinate set. -/
abbrev RelevantCode (index : ContinuumIndex ↪ ContinuumIndex) (D : Set ContinuumIndex) :=
  {a : ContinuumIndex // index a ∈ D}

private theorem relevantCode_countable (index : ContinuumIndex ↪ ContinuumIndex)
    (D : Set ContinuumIndex) (hD : D.Countable) : Countable (RelevantCode index D) := by
  apply Countable.to_subtype
  exact hD.preimage index.injective

private theorem relevantLabels_pairwise (index : ContinuumIndex ↪ ContinuumIndex)
    (D : Set ContinuumIndex) :
    Pairwise fun a b : RelevantCode index D ↦ (label a.1 ∩ label b.1).Finite := by
  intro a b hab
  apply label_inter_finite
  exact fun heq ↦ hab (Subtype.ext heq)

/-- Pairwise-disjoint refinements of the labels of all codes relevant to `D`. -/
def refinedLabel (index : ContinuumIndex ↪ ContinuumIndex)
    (D : Set ContinuumIndex) (hD : D.Countable) : RelevantCode index D → Set ℕ := by
  let : Countable (RelevantCode index D) := relevantCode_countable index D hD
  exact Classical.choose
    (exists_disjoint_refinement_countable
      (fun a : RelevantCode index D ↦ label a.1) (relevantLabels_pairwise index D))

theorem refinedLabel_pairwise (index : ContinuumIndex ↪ ContinuumIndex)
    (D : Set ContinuumIndex) (hD : D.Countable) :
    Pairwise fun a b : RelevantCode index D ↦
      Disjoint (refinedLabel index D hD a) (refinedLabel index D hD b) := by
  let : Countable (RelevantCode index D) := relevantCode_countable index D hD
  exact (Classical.choose_spec
    (exists_disjoint_refinement_countable
      (fun a : RelevantCode index D ↦ label a.1) (relevantLabels_pairwise index D))).1

theorem label_diff_refinedLabel_finite (index : ContinuumIndex ↪ ContinuumIndex)
    (D : Set ContinuumIndex) (hD : D.Countable) (a : RelevantCode index D) :
    (label a.1 \ refinedLabel index D hD a).Finite := by
  let : Countable (RelevantCode index D) := relevantCode_countable index D hD
  exact (Classical.choose_spec
    (exists_disjoint_refinement_countable
      (fun a : RelevantCode index D ↦ label a.1) (relevantLabels_pairwise index D))).2 a |>.2

private theorem refinedLabel_unique (index : ContinuumIndex ↪ ContinuumIndex)
    (D : Set ContinuumIndex) (hD : D.Countable) {l : ℕ}
    {a b : RelevantCode index D} (ha : l ∈ refinedLabel index D hD a)
    (hb : l ∈ refinedLabel index D hD b) : a = b := by
  by_contra hab
  exact Set.disjoint_left.mp (refinedLabel_pairwise index D hD hab) ha hb

/-- The unique relevant code scheduled at a label, when one exists. -/
def activeCode (index : ContinuumIndex ↪ ContinuumIndex)
    (D : Set ContinuumIndex) (hD : D.Countable) (l : ℕ) :
    Option (RelevantCode index D) := by
  classical
  exact if h : ∃ a, l ∈ refinedLabel index D hD a then some (Classical.choose h) else none

theorem activeCode_eq_some_of_mem (index : ContinuumIndex ↪ ContinuumIndex)
    (D : Set ContinuumIndex) (hD : D.Countable) (l : ℕ)
    (a : RelevantCode index D) (ha : l ∈ refinedLabel index D hD a) :
    activeCode index D hD l = some a := by
  classical
  unfold activeCode
  split
  · rename_i h
    congr 1
    exact refinedLabel_unique index D hD (Classical.choose_spec h) ha
  · rename_i h
    exact (h ⟨a, ha⟩).elim

end LocalCodeSchedule

end

end Wallace
