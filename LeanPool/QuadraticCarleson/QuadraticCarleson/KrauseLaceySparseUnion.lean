/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyStoppingExtraction

/-!
# Sparse unions over disjoint spatial branches

The recursive Krause--Lacey stopping proof produces one sparse family inside
each pairwise-disjoint stopping child.  This file proves that their union is
sparse with exactly the same density.  The proof transports the individual
major subsets through the unique branch containing each interval.
-/

open Function MeasureTheory Set

namespace QuadraticCarleson


/-- A nondegenerate real interval has a point in its carrier. -/
theorem RealInterval.carrier_nonempty (I : RealInterval) : I.carrier.Nonempty := by
  exact Set.nonempty_Ioc.mpr I.left_lt_right

/-- Sparse families living in pairwise-disjoint spatial regions can be
united without changing the sparse density. -/
theorem IsSparse.iUnion_of_disjoint_carriers
    {ι : Type*} [Nonempty ι] {η : ℝ}
    (F : ι → Set RealInterval) (U : ι → Set ℝ)
    (hU : (Set.univ : Set ι).PairwiseDisjoint U)
    (hFU : ∀ i, ∀ I ∈ F i, I.carrier ⊆ U i)
    (hS : ∀ i, IsSparse η (F i)) :
    IsSparse η (⋃ i, F i) := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  have hη : 0 < η := (hS i₀).1
  have hη1 : η < 1 := (hS i₀).2.1
  have hex : ∀ i, ∃ E : {I : RealInterval // I ∈ F i} → Set ℝ,
      (∀ I, MeasurableSet (E I)) ∧
        (∀ I, E I ⊆ I.1.carrier) ∧
          (Pairwise fun I J ↦ Disjoint (E I) (E J)) ∧
            ∀ I, η * I.1.length ≤ (volume (E I)).toReal :=
    fun i ↦ (hS i).2.2
  choose E hEmeas hEsub hEdisj hEmass using hex
  let idx (I : {I : RealInterval // I ∈ ⋃ i, F i}) : ι :=
    Classical.choose (Set.mem_iUnion.mp I.2)
  have hidx_mem (I : {I : RealInterval // I ∈ ⋃ i, F i}) : I.1 ∈ F (idx I) :=
    Classical.choose_spec (Set.mem_iUnion.mp I.2)
  let Eambient (i : ι) (I : RealInterval) : Set ℝ :=
    if hI : I ∈ F i then E i ⟨I, hI⟩ else ∅
  have hEambient (i : ι) (I : RealInterval) (hI : I ∈ F i) :
      Eambient i I = E i ⟨I, hI⟩ := by
    simp only [Eambient, dif_pos hI]
  let E' (I : {I : RealInterval // I ∈ ⋃ i, F i}) : Set ℝ :=
    Eambient (idx I) I.1
  refine ⟨hη, hη1, E', ?_, ?_, ?_, ?_⟩
  · intro I
    change MeasurableSet (Eambient (idx I) I.1)
    rw [hEambient (idx I) I.1 (hidx_mem I)]
    exact hEmeas (idx I) ⟨I.1, hidx_mem I⟩
  · intro I
    change Eambient (idx I) I.1 ⊆ I.1.carrier
    rw [hEambient (idx I) I.1 (hidx_mem I)]
    exact hEsub (idx I) ⟨I.1, hidx_mem I⟩
  · intro I J hIJ
    by_cases hij : idx I = idx J
    · have hJmem : J.1 ∈ F (idx I) := by simpa only [hij] using hidx_mem J
      change Disjoint (Eambient (idx I) I.1) (Eambient (idx J) J.1)
      rw [hEambient (idx I) I.1 (hidx_mem I)]
      rw [← hij, hEambient (idx I) J.1 hJmem]
      apply hEdisj (idx I)
      intro hsub
      apply hIJ
      apply Subtype.ext
      exact congrArg
        (fun K : {K : RealInterval // K ∈ F (idx I)} ↦ K.1) hsub
    · have hEI : E' I ⊆ U (idx I) := by
        change Eambient (idx I) I.1 ⊆ U (idx I)
        rw [hEambient (idx I) I.1 (hidx_mem I)]
        exact (hEsub (idx I) ⟨I.1, hidx_mem I⟩).trans
          (hFU (idx I) I.1 (hidx_mem I))
      have hEJ : E' J ⊆ U (idx J) := by
        change Eambient (idx J) J.1 ⊆ U (idx J)
        rw [hEambient (idx J) J.1 (hidx_mem J)]
        exact (hEsub (idx J) ⟨J.1, hidx_mem J⟩).trans
          (hFU (idx J) J.1 (hidx_mem J))
      exact (hU (Set.mem_univ (idx I)) (Set.mem_univ (idx J)) hij).mono hEI hEJ
  · intro I
    change η * I.1.length ≤ (volume (Eambient (idx I) I.1)).toReal
    rw [hEambient (idx I) I.1 (hidx_mem I)]
    exact hEmass (idx I) ⟨I.1, hidx_mem I⟩


end QuadraticCarleson
