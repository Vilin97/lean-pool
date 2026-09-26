/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ComplexityDecrease

/-!
# API checks for the complexity of formal expressions

These certificates separate the complexity and its reduction step from three nearby wrong
readings: relevant values indexed with multiplicity rather than by distinct factors, a reduction
that carries the unselected factors over unchanged rather than doubling them, and one that deletes
the selected factor outright rather than lowering its exponent by one.
-/

universe v

public noncomputable section

namespace Tests

open Berarducci Berarducci.FormalExpression

variable {K : Type v} [Field K]

/-- The relevant values are indexed by the distinct factors: adjoining another copy of a factor
already present leaves them unchanged. -/
theorem relevantValues_cons_of_mem {w : FormalExpression K} (hw : w ≠ 0)
    {y : SeriesWithOrdinalValueAboveOne K} (hy : y ∈ w) :
    relevantValues (y ::ₘ w) Multiset.cons_ne_zero = relevantValues w hw := by
  refine relevantValues_congr Multiset.cons_ne_zero hw (selected_cons_of_mem hw hy) fun z _ ↦ ?_
  rw [Multiset.mem_cons]
  exact ⟨fun h ↦ h.elim (fun hz ↦ hz ▸ hy) id, Or.inr⟩

open Classical in
/-- The reduction doubles the unselected exponents rather than carrying them over. -/
theorem count_reduced_eq_two_mul {w : FormalExpression K} {hw : w ≠ 0}
    {y : SeriesWithOrdinalValueAboveOne K} (hy : y ≠ selected w hw) :
    Multiset.count y (reduced w hw 0) = 2 * Multiset.count y w :=
  count_reduced_of_ne hy (Multiset.notMem_zero y)

open Classical in
/-- The reduction lowers the selected exponent by exactly one, so a selected factor of exponent
above one survives it. -/
theorem count_selected_reduced_add_one {w : FormalExpression K} (hw : w ≠ 0)
    (hk : 1 < selectedExponent w hw) :
    Multiset.count (selected w hw) (reduced w hw 0) + 1 = selectedExponent w hw := by
  rw [count_selected_reduced (Multiset.notMem_zero _)]
  omega

end Tests
