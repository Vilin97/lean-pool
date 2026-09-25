/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
module

/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

public import LeanPool.RearrangementNumber.NonMRR.Catalogue
public import LeanPool.RearrangementNumber.NonMRR.LowerBound

/-!
# The cardinal conclusion for the concrete slalom relation

This is the analytic/combinatorial reduction of the manuscript, including the
classical bounding-number lower bound. The category comparison needed for
the topological cardinal `nonM` is proved in `NonMRR.CategoryBound`.
-/

@[expose] public section

open Cardinal

namespace NonMRR

/-- The norm of the specific bounded-slalom relation used in the construction. -/
noncomputable def blockSlalomNumber : Cardinal :=
  (slalomRelation blockCapacity blockCapacity_pos).norm

/-- Every rearranging family has size at least the norm of the block slaloms. -/
theorem blockSlalomNumber_le_cardinal_of_isRearranging
    {P : Set (Equiv.Perm ℕ)} (hP : IsRearranging P) : blockSlalomNumber ≤ #P := by
  have hbP := boundingNumber_le_cardinal_of_isRearranging hP
  calc
    blockSlalomNumber ≤ boundingNumber * #P :=
      walshCatalogue.slalom_norm_le_bounding_mul_cardinal blockCapacity_pos
        blockTolerance_summable blockTolerance_nonneg hP
    _ ≤ #P * #P := mul_le_mul_left hbP _
    _ = #P := Cardinal.mul_eq_self (aleph0_le_cardinal_of_isRearranging hP)

/-- A family smaller than the block-slalom norm preserves some conditional series. -/
theorem exists_preserved_series_of_cardinal_lt_blockSlalomNumber
    {P : Set (Equiv.Perm ℕ)} (hP : #P < blockSlalomNumber) :
    ∃ a : ConditionalSeries, ∀ π ∈ P,
      HasSum (a.term ∘ π) a.sum (SummationFilter.conditional ℕ) := by
  have h : ¬ IsRearranging P := fun hr ↦
    (not_le_of_gt hP) (blockSlalomNumber_le_cardinal_of_isRearranging hr)
  simpa only [IsRearranging, Rearranges, not_forall, not_exists, not_and,
    Classical.not_not] using h

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
