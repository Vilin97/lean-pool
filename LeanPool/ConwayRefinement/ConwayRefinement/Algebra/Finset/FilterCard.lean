/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Data.Finset.Card

/-!
# Cardinalities of strict upper filters

Raising a weight threshold past a member of a finite set strictly decreases the number of
members above the threshold. This supplies the induction measure for partial-derivative identities.
-/

public section

namespace ConwayRefinement

/-- Raising the weight threshold to a larger member strictly decreases the upper filter's size. -/
theorem card_filter_above_lt {ι η : Type*} [LinearOrder η]
    (wt : ι → η) (s : Finset ι) {i j : ι} (hj : j ∈ s) (hij : wt i < wt j) :
    (s.filter fun v ↦ wt j < wt v).card < (s.filter fun v ↦ wt i < wt v).card := by
  classical
  refine Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨fun v hv ↦ ?_, fun heq ↦ ?_⟩)
  · obtain ⟨hv, hlt⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨hv, hij.trans hlt⟩
  · have hjmem : j ∈ s.filter fun v ↦ wt i < wt v := Finset.mem_filter.mpr ⟨hj, hij⟩
    rw [← heq, Finset.mem_filter] at hjmem
    exact lt_irrefl _ hjmem.2

end ConwayRefinement
