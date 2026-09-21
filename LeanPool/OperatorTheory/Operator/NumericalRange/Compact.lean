/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Numerical range — compactness in finite dimension

`W(A)` is the image of the unit sphere under the continuous map `x ↦ ⟪x, A x⟫_ℂ`. When `E` is
finite-dimensional the unit sphere is compact, so `W(A)` is compact, in particular closed.

## Main declarations

* `numericalRange_eq_image` — `numericalRange A = (fun x => ⟪x, A x⟫_ℂ) '' sphere 0 1`.
* `isCompact_numericalRange`, `isClosed_numericalRange` — for `[FiniteDimensional ℂ E]`.

In infinite dimension `W(A)` need not be closed (the unilateral shift has `W(S)` the open unit
disk), which is why `spectrum_subset_closure_numericalRange` carries a closure; see
`spectrum_subset_numericalRange` for the finite-dimensional statement without it.
-/
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.FiniteDimension
import LeanPool.OperatorTheory.Operator.NumericalRange.Basic

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The numerical range is the image of the unit sphere under `x ↦ ⟪x, A x⟫_ℂ`. -/
theorem numericalRange_eq_image (A : E →L[ℂ] E) :
    numericalRange A = (fun x => ⟪x, A x⟫_ℂ) '' Metric.sphere (0 : E) 1 := by
  ext z
  simp only [mem_numericalRange, Set.mem_image, mem_sphere_zero_iff_norm]

/-- In finite dimension the numerical range is compact: the continuous image of the unit sphere. -/
theorem isCompact_numericalRange [FiniteDimensional ℂ E] (A : E →L[ℂ] E) :
    IsCompact (numericalRange A) := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  rw [numericalRange_eq_image]
  exact (isCompact_sphere (0 : E) 1).image (continuous_id.inner A.continuous)

/-- In finite dimension the numerical range is closed. -/
theorem isClosed_numericalRange [FiniteDimensional ℂ E] (A : E →L[ℂ] E) :
    IsClosed (numericalRange A) :=
  (isCompact_numericalRange A).isClosed
/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
