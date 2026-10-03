/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianReciprocityData
public import Mathlib.GroupTheory.QuotientGroup.Basic
/-!
# The quotient induced by a finite Artin map

This is the specific isomorphism induced by the Artin map in
`FiniteAbelianReciprocityData`, not an arbitrarily chosen isomorphism.
-/

@[expose] public section

open scoped NumberField

noncomputable
section

namespace ClassFieldTheory

universe u v

/-- The first-isomorphism-theorem map induced by a finite Artin map. -/
def finiteAbelianReciprocityQuotientEquiv
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    (D : FiniteAbelianReciprocityData K L) :
    (RayClassGroup D.modulus ⧸ D.artin.ker) ≃* (L ≃ₐ[K] L) :=
  QuotientGroup.quotientKerEquivOfSurjective D.artin D.artin_surjective

end ClassFieldTheory
