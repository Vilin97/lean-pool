/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Tests.Fixtures.ApproachZero
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Convolution

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.SupportSupremum
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IsLUB

/-!
# API checks for the convolution index

The index set of Berarducci's convolution formula is built from the closed supports of the two
factors, not from the supports themselves. These certificates exhibit a series whose closed
support strictly contains its support, and an exponent that the index set therefore contains
although it lies in neither support.
-/

public noncomputable section

namespace Tests

open scoped HahnSeries

private theorem isLUB_approachZero_support : IsLUB approachZero.support 0 := by
  have h := (HahnSeries.Nonpositive.supportSup_eq_coe_iff.mp approachZero_supportSup).2
  rwa [coe_approachZeroNonpositive] at h

private theorem zero_mem_closure_approachZero_support :
    (0 : ℝ) ∈ closure approachZero.support := by
  refine isLUB_approachZero_support.mem_closure (HahnSeries.support_nonempty_iff.mpr ?_)
  intro hzero
  exact approachZero_ne_zero (Subtype.ext (by rw [coe_approachZeroNonpositive, hzero]; rfl))

/-- The closed support of `approachZero` strictly contains its support. -/
theorem closure_approachZero_support_ne :
    closure approachZero.support ≠ approachZero.support :=
  fun h ↦ zero_not_mem_approachZero_support (h ▸ zero_mem_closure_approachZero_support)

/-- The convolution index is computed from the closed supports: it contains an exponent lying in
the support of neither factor. -/
theorem zero_mem_convolutionIndex_approachZero :
    (0 : ℝ) ∈ Berarducci.convolutionIndex approachZero approachZero 0 ∧
      (0 : ℝ) ∉ approachZero.support :=
  ⟨Berarducci.mem_convolutionIndex.mpr
      ⟨zero_mem_closure_approachZero_support, by
        simpa using zero_mem_closure_approachZero_support⟩,
    zero_not_mem_approachZero_support⟩

end Tests
