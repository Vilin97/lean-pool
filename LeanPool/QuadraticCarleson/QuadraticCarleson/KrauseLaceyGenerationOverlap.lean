/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyGenerationLayers

/-!
# Minimal generations and actual spatial overlap

An interval that survives `n` minimal-layer removals contains an actual
inclusion chain of `n + 1` distinct members of the original family. The
smallest member has positive length, so even an almost-everywhere bound
on spatial overlap bounds the number of nonempty generations.

This statement does not compare physical scales of two generation labels.
In particular, it does not assert a scale gap in an unbalanced tree.
-/

@[expose] public section

open Function MeasureTheory Set

namespace QuadraticCarleson
namespace KrauseLaceyGenerationLayers

open KrauseLaceyStoppingExtraction


private theorem length_le_of_carrier_subset {I J : RealInterval}
    (h : I.carrier ⊆ J.carrier) : I.length ≤ J.length := by
  have he := (Ioc_subset_Ioc_iff I.left_lt_right).mp h
  dsimp [RealInterval.length]
  linarith [he.1, he.2]

/-- Survival through `n` removals produces an actual chain of `n + 1`
distinct intervals, with the given interval as its largest member and
an actual nondegenerate interval as its smallest member. No laminarity
hypothesis is needed for this direction. -/
theorem exists_chain_of_mem_remainingIntervals
    {S : Finset RealInterval} {n : ℕ} {I : RealInterval}
    (hI : I ∈ remainingIntervals S n) :
    ∃ C : Finset RealInterval,
      C ⊆ S ∧ C.card = n + 1 ∧ I ∈ C ∧
      (∀ J ∈ C, J.carrier ⊆ I.carrier) ∧
      (∀ J ∈ C, ∀ K ∈ C, J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier) ∧
      ∃ K ∈ C, ∀ J ∈ C, K.carrier ⊆ J.carrier := by
  classical
  induction n generalizing I with
  | zero =>
      refine ⟨{I}, ?_, by simp, by simp, ?_, ?_, I, by simp, ?_⟩
      · simpa [remainingIntervals] using hI
      · intro J hJ
        rw [Finset.mem_singleton.mp hJ]
      · intro J hJ K hK
        have hJeq := Finset.mem_singleton.mp hJ
        have hKeq := Finset.mem_singleton.mp hK
        subst J
        subst K
        exact Or.inl Subset.rfl
      · intro J hJ
        rw [Finset.mem_singleton.mp hJ]
  | succ n ih =>
      have hrem := Finset.mem_sdiff.mp hI
      have hex : ∃ J ∈ remainingIntervals S n,
          J.carrier ⊆ I.carrier ∧ J ≠ I := by
        by_contra hnone
        apply hrem.2
        apply mem_minimalLayer_iff.mpr
        refine ⟨hrem.1, ?_⟩
        intro J hJ hsub
        by_contra hne
        exact hnone ⟨J, hJ, hsub, hne⟩
      obtain ⟨J, hJ, hJI, hne⟩ := hex
      obtain ⟨C, hCS, hcard, hJC, hCJ, hchain, K, hKC, hK⟩ := ih hJ
      have hIC : I ∉ C := by
        intro hIC
        exact hne (interval_eq_of_carrier_subset_of_length_le hJI
          (length_le_of_carrier_subset (hCJ I hIC)))
      refine ⟨insert I C, Finset.insert_subset_iff.mpr
        ⟨remainingIntervals_subset S n hrem.1, hCS⟩, ?_,
        Finset.mem_insert_self _ _, ?_, ?_, K, Finset.mem_insert_of_mem hKC, ?_⟩
      · rw [Finset.card_insert_of_notMem hIC, hcard]
      · intro L hL
        rcases Finset.mem_insert.mp hL with rfl | hL
        · exact Subset.rfl
        · exact (hCJ L hL).trans hJI
      · intro L hL M hM
        rcases Finset.mem_insert.mp hL with rfl | hLC
        · rcases Finset.mem_insert.mp hM with rfl | hMC
          · exact Or.inl Subset.rfl
          · exact Or.inr ((hCJ M hMC).trans hJI)
        · rcases Finset.mem_insert.mp hM with rfl | hMC
          · exact Or.inl ((hCJ L hLC).trans hJI)
          · exact hchain L hLC M hMC
      · intro L hL
        rcases Finset.mem_insert.mp hL with rfl | hL
        · exact (hK J hJC).trans hJI
        · exact hK L hL

/-- The chain statement for the actual minimal-generation family. -/
theorem exists_chain_of_mem_generation
    {S : Finset RealInterval} {n : ℕ} {I : RealInterval}
    (hI : I ∈ generation S n) :
    ∃ C : Finset RealInterval,
      C ⊆ S ∧ C.card = n + 1 ∧ I ∈ C ∧
      (∀ J ∈ C, J.carrier ⊆ I.carrier) ∧
      (∀ J ∈ C, ∀ K ∈ C, J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier) ∧
      ∃ K ∈ C, ∀ J ∈ C, K.carrier ⊆ J.carrier :=
  exists_chain_of_mem_remainingIntervals (minimalLayer_subset _ hI)

/-- The literal number of parent intervals covering a point. -/
noncomputable def overlapCount (S : Finset RealInterval) (x : ℝ) : ℕ := by
  classical
  exact (S.filter fun I ↦ x ∈ I.carrier).card

/-- Survival at depth `n` forces overlap at least `n + 1` on an entire
nondegenerate member of the original family, not merely at one point. -/
theorem exists_interval_overlapCount_gt_of_mem_remainingIntervals
    {S : Finset RealInterval} {n : ℕ} {I : RealInterval}
    (hI : I ∈ remainingIntervals S n) :
    ∃ K ∈ S, K.carrier ⊆ I.carrier ∧
      ∀ x ∈ K.carrier, n < overlapCount S x := by
  classical
  obtain ⟨C, hCS, hcard, _, hCI, _, K, hKC, hK⟩ :=
    exists_chain_of_mem_remainingIntervals hI
  refine ⟨K, hCS hKC, hCI K hKC, ?_⟩
  intro x hx
  have hsub : C ⊆ S.filter (fun J ↦ x ∈ J.carrier) := by
    intro J hJ
    exact Finset.mem_filter.mpr ⟨hCS hJ, hK J hJ hx⟩
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  exact lt_of_lt_of_le (Nat.lt_succ_self n) hle

theorem exists_interval_overlapCount_gt_of_mem_generation
    {S : Finset RealInterval} {n : ℕ} {I : RealInterval}
    (hI : I ∈ generation S n) :
    ∃ K ∈ S, K.carrier ⊆ I.carrier ∧
      ∀ x ∈ K.carrier, n < overlapCount S x :=
  exists_interval_overlapCount_gt_of_mem_remainingIntervals (minimalLayer_subset _ hI)

/-- An almost-everywhere spatial-overlap cap already exhausts the actual
minimal-layer construction after at most that many layers. -/
theorem remainingIntervals_eq_empty_of_ae_overlapCount_le
    (S : Finset RealInterval) {M n : ℕ}
    (hbound : ∀ᵐ x ∂volume, overlapCount S x ≤ M) (hMn : M ≤ n) :
    remainingIntervals S n = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro I hI
  obtain ⟨K, _, _, hK⟩ := exists_interval_overlapCount_gt_of_mem_remainingIntervals hI
  have hvol : volume K.carrier ≠ 0 := by
    rw [RealInterval.volume_carrier]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr K.length_pos)
  obtain ⟨x, hx, hxb⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol
    (ae_restrict_of_ae hbound)
  exact (not_lt_of_ge (hxb.trans hMn)) (hK x hx)

theorem generation_eq_empty_of_ae_overlapCount_le
    (S : Finset RealInterval) {M n : ℕ}
    (hbound : ∀ᵐ x ∂volume, overlapCount S x ≤ M) (hMn : M ≤ n) :
    generation S n = ∅ := by
  classical
  rw [generation, remainingIntervals_eq_empty_of_ae_overlapCount_le S hbound hMn]
  simp [minimalLayer]

theorem generation_eq_empty_of_overlapCount_le
    (S : Finset RealInterval) {M n : ℕ}
    (hbound : ∀ x, overlapCount S x ≤ M) (hMn : M ≤ n) :
    generation S n = ∅ :=
  generation_eq_empty_of_ae_overlapCount_le S (Filter.Eventually.of_forall hbound) hMn

/-- Under an overlap cap, every source interval belongs to one of the
first `M` actual minimal generations. -/
theorem exists_generation_lt_of_mem_of_ae_overlapCount_le
    {S : Finset RealInterval} {M : ℕ} {I : RealInterval}
    (hbound : ∀ᵐ x ∂volume, overlapCount S x ≤ M) (hI : I ∈ S) :
    ∃ n < M, I ∈ generation S n := by
  obtain ⟨n, _, hn⟩ := exists_generation_of_mem hI
  refine ⟨n, ?_, hn⟩
  by_contra hnot
  rw [generation_eq_empty_of_ae_overlapCount_le S hbound (by omega : M ≤ n)] at hn
  exact Finset.notMem_empty I hn

/-- A finite prefix of an eventually zero sequence is exactly its prefix
truncated at the vanishing threshold. -/
theorem sum_range_eq_sum_range_min_of_eq_zero
    {α : Type*} [AddCommMonoid α] (v : ℕ → α) (M n : ℕ)
    (hzero : ∀ i, M ≤ i → v i = 0) :
    (∑ i ∈ Finset.range n, v i) = ∑ i ∈ Finset.range (min n M), v i := by
  symm
  apply Finset.sum_subset (Finset.range_mono (min_le_left n M))
  intro i hin hout
  apply hzero
  simp only [Finset.mem_range] at hin hout
  omega

/-- The actual generation prefixes truncate exactly at an almost-everywhere
spatial-overlap cap. The summands may depend on both the layer and interval. -/
theorem sum_generations_eq_sum_generations_min_of_ae_overlapCount_le
    {α : Type*} [AddCommMonoid α] (S : Finset RealInterval) (v : ℕ → RealInterval → α)
    (M n : ℕ) (hbound : ∀ᵐ x ∂volume, overlapCount S x ≤ M) :
    (∑ i ∈ Finset.range n, ∑ I ∈ generation S i, v i I) =
      ∑ i ∈ Finset.range (min n M), ∑ I ∈ generation S i, v i I := by
  apply sum_range_eq_sum_range_min_of_eq_zero
  intro i hi
  rw [generation_eq_empty_of_ae_overlapCount_le S hbound hi]
  exact Finset.sum_empty


end KrauseLaceyGenerationLayers
end QuadraticCarleson
