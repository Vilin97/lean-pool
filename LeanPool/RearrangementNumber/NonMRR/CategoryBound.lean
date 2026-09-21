/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import LeanPool.RearrangementNumber.NonMRR.SlalomCoding
import LeanPool.RearrangementNumber.NonMRR.GapBounding
import LeanPool.RearrangementNumber.NonMRR.CategoryReduction
import LeanPool.RearrangementNumber.NonMRR.CategoryTransfer
import LeanPool.RearrangementNumber.NonMRR.SlalomBound

/-!
# The lower bound by the real meagre-ideal uniformity

The proof constructs a nonmeagre set of real numbers of cardinality at most
that of any rearranging family. All block, coding and category ingredients
are instantiated by the constructions in the preceding modules.
-/

open Cardinal

namespace NonMRR

/-- The category lower bound for the concrete slalom relation. -/
theorem nonM_le_bounding_mul_blockSlalomNumber :
    nonM ≤ boundingNumber * blockSlalomNumber := by
  obtain ⟨Φ, hΦ, hΦcard⟩ :=
    (slalomRelation blockCapacity blockCapacity_pos).exists_dominating_of_norm
  obtain ⟨F, hFcard, hF⟩ :=
    slalom_cover_to_strong_coincidence blockCapacity blockCapacity_pos Φ hΦ
  obtain ⟨B, hBcard, hBmono, hBgap⟩ := exists_gap_unbounded_family
  calc
    nonM ≤ nonMeagreCardinal (ℕ → Bool) := nonM_le_nonMeagreCardinal_bool
    _ ≤ #B * #F := nonMeagreCardinal_le_product_of_gap_and_coincidence
      ⟨hBmono, hBgap⟩ hF
    _ ≤ boundingNumber * #Φ := mul_le_mul' hBcard hFcard
    _ = boundingNumber * blockSlalomNumber := by rw [hΦcard]; rfl

/-- Every rearranging family has cardinality at least `nonM`, with `nonM`
defined using the actual meagre ideal on the real line. -/
theorem nonM_le_cardinal_of_isRearranging {P : Set (Equiv.Perm ℕ)}
    (hP : IsRearranging P) : nonM ≤ #P := by
  calc
    nonM ≤ boundingNumber * blockSlalomNumber := nonM_le_bounding_mul_blockSlalomNumber
    _ ≤ #P * #P := mul_le_mul'
      (boundingNumber_le_cardinal_of_isRearranging hP)
      (blockSlalomNumber_le_cardinal_of_isRearranging hP)
    _ = #P := Cardinal.mul_eq_self (aleph0_le_cardinal_of_isRearranging hP)

/-- The simultaneous witnessing formulation of the lower bound. -/
theorem exists_preserved_series_of_cardinal_lt_nonM
    {P : Set (Equiv.Perm ℕ)} (hP : #P < nonM) :
    ∃ a : ConditionalSeries, ∀ π ∈ P,
      HasSum (a.term ∘ π) a.sum (SummationFilter.conditional ℕ) := by
  have h : ¬ IsRearranging P := fun hr ↦
    (not_le_of_gt hP) (nonM_le_cardinal_of_isRearranging hr)
  simpa only [IsRearranging, Rearranges, not_forall, not_exists, not_and,
    Classical.not_not] using h

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
