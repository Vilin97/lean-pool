/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
module

public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.UniformSpace.Real

/-!
# Noncompact

Supporting results for the classification of compact one-dimensional manifolds.
-/

public section

namespace OneMfld

open Set

/-- `[0, ∞) ⊆ ℝ` is not compact. -/
lemma not_isCompact_Ici_zero_real : ¬ IsCompact (Ici (0 : ℝ)) := by
  intro h
  exact not_bddAbove_Ici (0 : ℝ) h.bddAbove

/-- `NNReal` (the nonnegative reals with the induced topology) is not a compact space. -/
theorem not_compactSpace_NNReal : ¬ CompactSpace NNReal := by
  intro h
  have hImage := isCompact_univ.image NNReal.continuous_coe
  rw [Set.image_univ, NNReal.range_coe] at hImage
  exact not_isCompact_Ici_zero_real hImage

end OneMfld
