/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianReciprocityQuotientEquiv
/-!
# Quotient form of finite abelian global reciprocity

The kernel of a finite ray-class Artin map is exactly the relation that must
be divided out to obtain the Galois group.  The modulus and Frobenius
normalization are carried by `FiniteAbelianReciprocityData`.
-/

@[expose] public section

open scoped NumberField

noncomputable
section

namespace ClassFieldTheory

universe u v

/-- A finite Artin map induces an isomorphism from its ray-class quotient to
the finite abelian Galois group. -/
theorem finiteAbelianGlobalReciprocity_quotient
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    (D : FiniteAbelianReciprocityData K L) :
    Nonempty
      ((RayClassGroup D.modulus ⧸ D.artin.ker) ≃* (L ≃ₐ[K] L)) := by
  exact ⟨finiteAbelianReciprocityQuotientEquiv K L D⟩

end ClassFieldTheory
