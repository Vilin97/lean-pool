/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ConvolutionList

/-!
# API checks for the multi-factor convolution formula

These certificates separate the formula from two nearby wrong readings: an empty product that
would contribute at every cutoff rather than only at zero, and an index set that would not
constrain its exponent lists. A third check records that the exponent lists are positional, so
their length is the number of factors.
-/

public noncomputable section

namespace Tests

open scoped HahnSeries

/-- The empty product contributes only at cutoff zero. -/
theorem convolutionIndexList_nil_one :
    Berarducci.convolutionIndexList ([] : List ℚ⟦ℝ⟧) 1 = ∅ := by
  rw [Berarducci.convolutionIndexList_nil, if_neg one_ne_zero]

/-- Reading the formula at the empty list computes the germ of one away from zero. -/
theorem germAt_one_at_one : Berarducci.germAt (1 : ℚ⟦ℝ⟧) 1 = 0 := by
  have h := Berarducci.germAt_listProd ([] : List ℚ⟦ℝ⟧) 1
  rw [List.prod_nil, convolutionIndexList_nil_one, Finset.sum_empty] at h
  exact h

/-- Exponent lists in the index set are constrained: one that does not sum to the cutoff is
absent. -/
theorem notMem_convolutionIndexList_of_sum_ne
    (l : List ℚ⟦ℝ⟧) (γ : ℝ) (f : List ℝ) (h : f.sum ≠ γ) :
    f ∉ Berarducci.convolutionIndexList l γ :=
  fun hf ↦ h (Berarducci.sum_of_mem_convolutionIndexList l γ hf)

/-- Exponent lists are positional: their length is the number of factors. -/
theorem length_eq_of_mem_convolutionIndexList
    (l : List ℚ⟦ℝ⟧) (γ : ℝ) (f : List ℝ)
    (hf : f ∈ Berarducci.convolutionIndexList l γ) :
    f.length = l.length :=
  Berarducci.length_of_mem_convolutionIndexList l γ hf

end Tests
