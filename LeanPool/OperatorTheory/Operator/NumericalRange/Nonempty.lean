/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import Mathlib.Analysis.Normed.Module.Normalize
import LeanPool.OperatorTheory.Operator.NumericalRange.Basic

/-!
# Nonemptiness of the numerical range

The numerical range is nonempty exactly when the underlying inner-product
space is nontrivial.  Thus the only empty numerical ranges are those on a
subsingleton space.
-/

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The numerical range is nonempty exactly when the underlying space is
nontrivial. -/
theorem numericalRange_nonempty_iff_nontrivial (A : E →L[ℂ] E) :
    (numericalRange A).Nonempty ↔ Nontrivial E := by
  constructor
  · rintro ⟨z, x, hx, _hz⟩
    rw [nontrivial_iff_exists_ne (0 : E)]
    refine ⟨x, ?_⟩
    intro hzero
    subst x
    norm_num at hx
  · intro hE
    obtain ⟨x, hx⟩ := (nontrivial_iff_exists_ne (0 : E)).mp hE
    let u : E := NormedSpace.normalize x
    have hu : ‖u‖ = 1 := NormedSpace.norm_normalize hx
    exact ⟨⟪u, A u⟫_ℂ, (mem_numericalRange A _).2 ⟨u, hu, rfl⟩⟩

/-- On a nontrivial space, every bounded operator has nonempty numerical
range. -/
theorem nonempty_numericalRange [Nontrivial E] (A : E →L[ℂ] E) :
    (numericalRange A).Nonempty :=
  (numericalRange_nonempty_iff_nontrivial A).2 inferInstance

/-- The numerical range is empty exactly on a subsingleton space. -/
theorem numericalRange_eq_empty_iff_subsingleton (A : E →L[ℂ] E) :
    numericalRange A = ∅ ↔ Subsingleton E := by
  rw [← Set.not_nonempty_iff_eq_empty, numericalRange_nonempty_iff_nontrivial,
    not_nontrivial_iff_subsingleton]

/-- Closing the numerical range does not change its nonemptiness
characterization. -/
theorem closure_numericalRange_nonempty_iff_nontrivial (A : E →L[ℂ] E) :
    (closure (numericalRange A)).Nonempty ↔ Nontrivial E :=
  closure_nonempty_iff.trans (numericalRange_nonempty_iff_nontrivial A)

/-- The closed numerical range is empty exactly on a subsingleton space. -/
theorem closure_numericalRange_eq_empty_iff_subsingleton (A : E →L[ℂ] E) :
    closure (numericalRange A) = ∅ ↔ Subsingleton E := by
  rw [← Set.not_nonempty_iff_eq_empty,
    closure_numericalRange_nonempty_iff_nontrivial,
    not_nontrivial_iff_subsingleton]

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
