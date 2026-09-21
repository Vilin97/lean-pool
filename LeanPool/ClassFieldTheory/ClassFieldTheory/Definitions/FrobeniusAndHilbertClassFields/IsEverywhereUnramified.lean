/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsUnramifiedAtFinitePlaces
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
/-!
# Unramifiedness at every place
-/

namespace ClassFieldTheory

universe u v

/-- A number-field extension is unramified at all finite and infinite places. -/
def IsEverywhereUnramified
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] : Prop :=
  IsUnramifiedAtFinitePlaces K L ∧ IsUnramifiedAtInfinitePlaces K L

end ClassFieldTheory
