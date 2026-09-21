/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.IsFieldNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.NormTheorems.IsEverywhereLocalNorm
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.FieldTheory.Galois.Basic
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.MathlibNormInterface
/-!
# The cyclic Hasse norm theorem

This module states the local-to-global norm principle for a finite cyclic
Galois extension `L / K` of number fields.  For a unit `x` of `K`, the
conclusion identifies membership in the global field-norm subgroup with the
condition of being a norm after base change to every finite and infinite
completion of `K`.
-/

open scoped NumberField

namespace ClassFieldTheory

/-- For a finite cyclic number-field extension, a unit is a global norm if
and only if it is a norm at every completion. -/
theorem cyclicHasseNormTheorem
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]
    (x : Kˣ) :
    IsFieldNorm K L x ↔ IsEverywhereLocalNorm K L x := by
  exact GlobalClassFieldTheory.ClassFieldAxiom.cyclicHasseNormTheorem K L x

end ClassFieldTheory
