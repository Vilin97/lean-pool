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
  letI : LinearOrder ι := LinearOrder.lift' rank hrank
  have hpred (i : ι) : (Set.Iio i).Finite := by
    have heq : Set.Iio i = rank ⁻¹' Set.Iio (rank i) := by
      ext j
      rfl
    rw [heq]
    exact (Set.finite_Iio (rank i)).preimage hrank.injOn
  refine ⟨disjointize family, pairwise_disjoint_disjointize family, ?_⟩
  intro i
  exact ⟨disjointize_subset family i, disjointize_loss_finite family had i (hpred i)⟩

end

end Wallace
