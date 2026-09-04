/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import Mathlib.Data.Set.Countable

/-!
# Countable closure under triangular dependencies

For a code `c`, `dependency c` is the countable set of basis coordinates occurring in its
prepared sequence.  Because code indices are injective, closing a countable set under all codes
whose indices it contains still takes only countably many new coordinates at each finite stage.
-/

open Set

universe u v

namespace Wallace

noncomputable section

variable {I : Type u} {Code : Type v}

/-- One closure step under a family of countable dependencies. -/
def dependencyClosureStep (index : Code ↪ I) (dependency : Code → Set I)
    (D : Set I) : Set I :=
  D ∪ ⋃ c, ⋃ (_h : index c ∈ D), dependency c

/-- Finite stages of the dependency closure. -/
def dependencyClosureStages (index : Code ↪ I) (dependency : Code → Set I)
    (D₀ : Set I) : ℕ → Set I
  | 0 => D₀
  | n + 1 => dependencyClosureStep index dependency (dependencyClosureStages index dependency D₀ n)

/-- Closure after all finite stages. -/
def dependencyClosure (index : Code ↪ I) (dependency : Code → Set I)
    (D₀ : Set I) : Set I :=
  ⋃ n, dependencyClosureStages index dependency D₀ n

theorem subset_dependencyClosure (index : Code ↪ I) (dependency : Code → Set I)
    (D₀ : Set I) : D₀ ⊆ dependencyClosure index dependency D₀ := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨0, hx⟩

/-- The closure is closed under every dependency whose code index it contains. -/
theorem dependency_subset_closure_of_index_mem
    (index : Code ↪ I) (dependency : Code → Set I) (D₀ : Set I)
    {c : Code} (hc : index c ∈ dependencyClosure index dependency D₀) :
    dependency c ⊆ dependencyClosure index dependency D₀ := by
  obtain ⟨n, hcn⟩ := Set.mem_iUnion.mp hc
  intro x hx
  refine Set.mem_iUnion.mpr ⟨n + 1, ?_⟩
  exact Or.inr (Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hcn, hx⟩⟩)

theorem countable_preimage_of_injective
    (index : Code ↪ I) {D : Set I} (hD : D.Countable) :
    {c : Code | index c ∈ D}.Countable := by
  exact hD.preimage index.injective

/-- A countable set remains countable after one dependency-closure step. -/
theorem countable_dependencyClosureStep
    (index : Code ↪ I) (dependency : Code → Set I)
    (hdep : ∀ c, (dependency c).Countable)
    {D : Set I} (hD : D.Countable) :
    (dependencyClosureStep index dependency D).Countable := by
  apply hD.union
  have hcodes : {c : Code | index c ∈ D}.Countable :=
    countable_preimage_of_injective index hD
  exact hcodes.biUnion fun c _hc ↦ hdep c

/-- Closing a countable set under countable triangular dependencies is countable. -/
theorem countable_dependencyClosure
    (index : Code ↪ I) (dependency : Code → Set I)
    (hdep : ∀ c, (dependency c).Countable)
    {D₀ : Set I} (hD₀ : D₀.Countable) :
    (dependencyClosure index dependency D₀).Countable := by
  apply Set.countable_iUnion
  intro n
  induction n with
  | zero => exact hD₀
  | succ n ih => exact countable_dependencyClosureStep index dependency hdep ih

end

end Wallace
