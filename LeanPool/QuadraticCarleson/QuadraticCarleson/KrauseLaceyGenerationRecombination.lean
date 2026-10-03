/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyGenerationLayers

/-!
# Exact recombination of the actual minimal generations
-/

@[expose] public section

namespace QuadraticCarleson.KrauseLaceyGenerationLayers

attribute [local instance] Classical.propDecidable

/-- The unique minimal-generation label of an interval in a finite family. -/
noncomputable def generationIndex (S : Finset RealInterval) (I : RealInterval) : ℕ :=
  if hI : I ∈ S then Classical.choose (exists_generation_of_mem hI) else 0

theorem generationIndex_spec {S : Finset RealInterval} {I : RealInterval} (hI : I ∈ S) :
    generationIndex S I < S.card ∧ I ∈ generation S (generationIndex S I) := by
  simp only [generationIndex, dite_eq_left hI]
  exact Classical.choose_spec (exists_generation_of_mem hI)

theorem generationIndex_eq_of_mem {S : Finset RealInterval} {I : RealInterval} {n : ℕ}
    (hI : I ∈ generation S n) : generationIndex S I = n := by
  have hi := generationIndex_spec (generation_subset S n hI)
  by_contra hn
  exact Finset.disjoint_left.mp (generations_disjoint S hn) hi.2 hI

theorem generation_eq_filter_index (S : Finset RealInterval) (n : ℕ) :
    generation S n = S.filter (fun I ↦ generationIndex S I = n) := by
  ext I
  simp only [Finset.mem_filter]
  constructor
  · intro hI
    exact ⟨generation_subset S n hI, generationIndex_eq_of_mem hI⟩
  · rintro ⟨hI, hindex⟩
    have h := (generationIndex_spec hI).2
    rwa [hindex] at h

/-- Weighting the genuine generations is exactly weighting each genuine
interval by its unique generation coefficient. -/
theorem sum_smul_generations_eq
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (S : Finset RealInterval) (v : RealInterval → E) (c : ℕ → ℝ) :
    (∑ n ∈ Finset.range S.card, c n • ∑ I ∈ generation S n, v I) =
      ∑ I ∈ S, c (generationIndex S I) • v I := by
  simp_rw [Finset.smul_sum, generation_eq_filter_index]
  have hreplace :
      (∑ n ∈ Finset.range S.card,
        ∑ I ∈ S.filter (fun I ↦ generationIndex S I = n), c n • v I) =
      ∑ n ∈ Finset.range S.card,
        ∑ I ∈ S.filter (fun I ↦ generationIndex S I = n),
          c (generationIndex S I) • v I := by
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro I hI
    rw [(Finset.mem_filter.mp hI).2]
  rw [hreplace]
  exact Finset.sum_fiberwise_of_maps_to
    (fun I hI ↦ Finset.mem_range.mpr (generationIndex_spec hI).1) _

/-- The exact prefix recombination does not require the prefix length to
exhaust all generations. -/
theorem sum_smul_generations_range_eq
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (S : Finset RealInterval) (v : RealInterval → E) (c : ℕ → ℝ) (M : ℕ) :
    (∑ n ∈ Finset.range M, c n • ∑ I ∈ generation S n, v I) =
      ∑ I ∈ S, (if generationIndex S I < M then c (generationIndex S I) else 0) • v I := by
  simp_rw [Finset.smul_sum, generation_eq_filter_index]
  calc
    _ = ∑ n ∈ Finset.range M,
        ∑ I ∈ S.filter (fun I ↦ generationIndex S I = n),
          c (generationIndex S I) • v I := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro I hI
      rw [(Finset.mem_filter.mp hI).2]
    _ = ∑ I ∈ S.filter (fun I ↦ generationIndex S I ∈ Finset.range M),
        c (generationIndex S I) • v I := Finset.sum_fiberwise_eq_sum_filter _ _ _ _
    _ = _ := by
      simp only [Finset.mem_range, Finset.sum_filter, ite_smul, zero_smul]


end QuadraticCarleson.KrauseLaceyGenerationLayers
