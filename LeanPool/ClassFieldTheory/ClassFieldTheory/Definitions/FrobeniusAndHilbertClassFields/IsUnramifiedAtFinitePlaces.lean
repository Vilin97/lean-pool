/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.Unramified.Locus
/-!
# Unramifiedness at all finite places
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTheory

universe u v

/-- A number-field extension is unramified at every finite prime of the base. -/
def IsUnramifiedAtFinitePlaces
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 K),
    Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal

end ClassFieldTheory
