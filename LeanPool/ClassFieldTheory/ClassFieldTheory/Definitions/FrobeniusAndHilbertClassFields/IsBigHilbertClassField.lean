/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsUnramifiedAtFinitePlaces
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension
/-!
# Big Hilbert class fields
-/

namespace ClassFieldTheory

universe u

/-- A big Hilbert class field is a finite-prime-unramified finite abelian
extension containing every finite abelian extension unramified at the finite
places.  Ramification at real places is allowed. -/
def IsBigHilbertClassField
    {K : Type u} [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) : Prop :=
  IsUnramifiedAtFinitePlaces K E ∧
    ∀ F : FiniteAbelianExtension K,
      IsUnramifiedAtFinitePlaces K F → Nonempty (F →ₐ[K] E)

end ClassFieldTheory
