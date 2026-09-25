/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianReciprocityQuotientEquiv
/-!
# Evaluation of the finite Artin quotient isomorphism

The induced isomorphism maps the class of a ray class to its Artin value.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The quotient isomorphism evaluates to the original Artin map. -/
theorem finiteAbelianReciprocityQuotientEquiv_mk
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    (D : FiniteAbelianReciprocityData K L)
    (x : RayClassGroup D.modulus) :
    finiteAbelianReciprocityQuotientEquiv K L D
        (QuotientGroup.mk' D.artin.ker x) = D.artin x := by
  rfl

end ClassFieldTheory
