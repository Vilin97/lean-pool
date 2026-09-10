/-
Copyright (c) 2026 AddCombi contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AddCombi contributors
-/

module

public import Mathlib.Algebra.Notation.Indicator

/-!
# Indicator notation
-/

public section

/-- Indicator-function notation with an explicit codomain. -/
scoped[Indicator] notation3 "𝟭_[" s ", " R "]" => Set.indicator s fun _ ↦ (1 : R)

open scoped Indicator

/-- Indicator-function notation with an inferred codomain. -/
scoped[Indicator] notation3 "𝟭_[" s "]" => 𝟭_[s, _]
