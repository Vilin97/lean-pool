/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyPhysicalTailPrefix

/-!
# Finite overlap stopping geometry

The maximal intervals removed by literal overlap pruning cover exactly
the high-overlap set. Inside each such interval at most `M` covering
intervals are strict ancestors. These statements are deterministic and
use only the actual finite laminar family.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyStoppingExtraction KrauseLaceyGenerationLayers

attribute [local instance] Classical.propDecidable

/-- The inclusion-maximal members of the finite interval family `A`. -/
noncomputable def maximalIntervals (A : Finset RealInterval) : Finset RealInterval :=
  A.filter fun I ↦ ∀ J ∈ A, I.carrier ⊆ J.carrier → J = I

theorem maximalIntervals_subset (A : Finset RealInterval) : maximalIntervals A ⊆ A :=
  Finset.filter_subset _ _

theorem exists_maximalInterval_containing {A : Finset RealInterval} {I : RealInterval}
    (hI : I ∈ A) : ∃ J ∈ maximalIntervals A, I.carrier ⊆ J.carrier := by
  let F := A.filter fun J ↦ I.carrier ⊆ J.carrier
  obtain ⟨J, hJ, hmax⟩ := F.exists_max_image RealInterval.length
    ⟨I, Finset.mem_filter.mpr ⟨hI, Subset.rfl⟩⟩
  have hj := Finset.mem_filter.mp hJ
  refine ⟨J, Finset.mem_filter.mpr ⟨hj.1, ?_⟩, hj.2⟩
  intro K hK hJK
  exact (interval_eq_of_carrier_subset_of_length_le hJK
    (hmax K (Finset.mem_filter.mpr ⟨hK, hj.2.trans hJK⟩))).symm

theorem maximalIntervals_pairwiseDisjoint {A : Finset RealInterval}
    (hlam : Set.Pairwise (↑A : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier) :
    Set.Pairwise (↑(maximalIntervals A) : Set RealInterval)
      (Disjoint on fun I : RealInterval ↦ I.carrier) := by
  intro I hI J hJ hne
  have hi := Finset.mem_filter.mp hI
  have hj := Finset.mem_filter.mp hJ
  rcases hlam hi.1 hj.1 hne with h | h | h
  · exact (hne (hi.2 J hj.1 h).symm).elim
  · exact (hne (hj.2 I hi.1 h)).elim
  · exact h

/-- The inclusion-maximal intervals removed by pruning at overlap threshold `M`. -/
noncomputable def overlapStoppingIntervals (A : Finset RealInterval) (M : ℕ) :=
  maximalIntervals (A \ overlapPrunedFamily A M)

theorem overlapStoppingIntervals_subset (A : Finset RealInterval) (M : ℕ) :
    overlapStoppingIntervals A M ⊆ A :=
  (maximalIntervals_subset _).trans Finset.sdiff_subset

theorem overlapStoppingIntervals_subset_highOverlap
    {A : Finset RealInterval} {M : ℕ} {I : RealInterval}
    (hI : I ∈ overlapStoppingIntervals A M) :
    I.carrier ⊆ {x | M < overlapCount A x} := by
  have hi := Finset.mem_sdiff.mp (maximalIntervals_subset _ hI)
  exact removed_interval_subset_highOverlap hi.1 hi.2

theorem highOverlap_subset_biUnion_overlapStoppingIntervals
    (A : Finset RealInterval) (M : ℕ)
    (hlam : Set.Pairwise (↑A : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier) :
    {x | M < overlapCount A x} ⊆ ⋃ I ∈ overlapStoppingIntervals A M, I.carrier := by
  intro x hx
  change M < overlapCount A x at hx
  let F := A.filter fun I ↦ x ∈ I.carrier
  have hF : F.Nonempty := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hx)
  obtain ⟨I, hI, hmin⟩ := F.exists_min_image RealInterval.length hF
  have hi := Finset.mem_filter.mp hI
  have hcover (J : RealInterval) (hJ : J ∈ F) : I.carrier ⊆ J.carrier := by
    have hj := Finset.mem_filter.mp hJ
    by_cases he : I = J
    · exact he ▸ Subset.rfl
    rcases hlam hi.1 hj.1 he with h | h | hd
    · exact h
    · exact (interval_eq_of_carrier_subset_of_length_le h (hmin J hJ)) ▸ Subset.rfl
    · exact (Set.disjoint_left.mp hd hi.2 hj.2).elim
  have hremoved : I ∉ overlapPrunedFamily A M := by
    intro hp
    obtain ⟨y, hy, hlow⟩ := (Finset.mem_filter.mp hp).2
    have hfsub : F ⊆ A.filter (fun J ↦ y ∈ J.carrier) := by
      intro J hJ
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hJ).1, hcover J hJ hy⟩
    have hc := Finset.card_le_card hfsub
    change overlapCount A x ≤ overlapCount A y at hc
    omega
  obtain ⟨J, hJ, hIJ⟩ := exists_maximalInterval_containing
    (Finset.mem_sdiff.mpr ⟨hi.1, hremoved⟩)
  exact Set.mem_iUnion.mpr ⟨J, Set.mem_iUnion.mpr ⟨hJ, hIJ hi.2⟩⟩

theorem highOverlap_eq_biUnion_overlapStoppingIntervals
    (A : Finset RealInterval) (M : ℕ)
    (hlam : Set.Pairwise (↑A : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier) :
    {x | M < overlapCount A x} = ⋃ I ∈ overlapStoppingIntervals A M, I.carrier := by
  apply Subset.antisymm (highOverlap_subset_biUnion_overlapStoppingIntervals A M hlam)
  intro x hx
  obtain ⟨I, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hI, hx⟩ := Set.mem_iUnion.mp hx
  exact overlapStoppingIntervals_subset_highOverlap hI hx

theorem overlapStoppingIntervals_pairwiseDisjoint
    (A : Finset RealInterval) (M : ℕ)
    (hlam : Set.Pairwise (↑A : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier) :
    Set.Pairwise (↑(overlapStoppingIntervals A M) : Set RealInterval)
      (Disjoint on fun I : RealInterval ↦ I.carrier) :=
  maximalIntervals_pairwiseDisjoint (fun _I hI _J hJ hne ↦
    hlam (Finset.mem_sdiff.mp hI).1 (Finset.mem_sdiff.mp hJ).1 hne)

/-- A maximal removed interval has at most `M` strict covering ancestors.
The smallest strict ancestor, if any, must survive the pruning and
provides the low-overlap witness for the whole ancestor chain. -/
theorem strictAncestors_card_le_of_mem_overlapStoppingIntervals
    {A : Finset RealInterval} {M : ℕ} {I : RealInterval}
    (hlam : Set.Pairwise (↑A : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hI : I ∈ overlapStoppingIntervals A M) :
    (A.filter fun J ↦ I.carrier ⊆ J.carrier ∧ J ≠ I).card ≤ M := by
  let F := A.filter fun J ↦ I.carrier ⊆ J.carrier ∧ J ≠ I
  change F.card ≤ M
  by_cases he : F = ∅
  · simp [he]
  obtain ⟨J, hJ, hmin⟩ := F.exists_min_image RealInterval.length
    (Finset.nonempty_iff_ne_empty.mpr he)
  have hj := Finset.mem_filter.mp hJ
  have hJpruned : J ∈ overlapPrunedFamily A M := by
    by_contra hn
    have heq := (Finset.mem_filter.mp hI).2 J (Finset.mem_sdiff.mpr ⟨hj.1, hn⟩) hj.2.1
    exact hj.2.2 heq
  obtain ⟨y, hyJ, hlow⟩ := (Finset.mem_filter.mp hJpruned).2
  have hsub : F ⊆ A.filter (fun K ↦ y ∈ K.carrier) := by
    intro K hK
    have hk := Finset.mem_filter.mp hK
    refine Finset.mem_filter.mpr ⟨hk.1, ?_⟩
    by_cases heq : J = K
    · exact heq ▸ hyJ
    rcases hlam hj.1 hk.1 heq with h | h | hd
    · exact h hyJ
    · have heq := interval_eq_of_carrier_subset_of_length_le h (hmin K hK)
      exact heq ▸ hyJ
    · exact (Set.disjoint_left.mp hd
        (hj.2.1 ⟨I.left_lt_right, le_rfl⟩) (hk.2.1 ⟨I.left_lt_right, le_rfl⟩)).elim
  exact (Finset.card_le_card hsub).trans hlow

/-- The local counting function loses at most one block of ancestors. -/
theorem overlapCount_le_descendants_add_of_mem_overlapStoppingIntervals
    {A : Finset RealInterval} {M : ℕ} {I : RealInterval}
    (hlam : Set.Pairwise (↑A : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hI : I ∈ overlapStoppingIntervals A M) {x : ℝ} (hx : x ∈ I.carrier) :
    overlapCount A x ≤ overlapCount (A.filter fun J ↦ J.carrier ⊆ I.carrier) x + M := by
  let D := (A.filter fun J ↦ J.carrier ⊆ I.carrier).filter fun J ↦ x ∈ J.carrier
  let O := A.filter fun J ↦ I.carrier ⊆ J.carrier ∧ J ≠ I
  have hsub : A.filter (fun J ↦ x ∈ J.carrier) ⊆ D ∪ O := by
    intro J hJ
    have hj := Finset.mem_filter.mp hJ
    by_cases he : J = I
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hj.1, he ▸ Subset.rfl⟩, hj.2⟩
    rcases hlam hj.1 (overlapStoppingIntervals_subset A M hI) he with h | h | hd
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hj.1, h⟩, hj.2⟩
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hj.1, h, he⟩)
    · exact (Set.disjoint_left.mp hd hj.2 hx).elim
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (strictAncestors_card_le_of_mem_overlapStoppingIntervals hlam hI) _))


end KrauseLaceyBadScale
end QuadraticCarleson
