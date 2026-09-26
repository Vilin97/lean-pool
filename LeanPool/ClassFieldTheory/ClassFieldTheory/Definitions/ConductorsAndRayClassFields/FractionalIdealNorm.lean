/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.FractionalIdealNormExponentMap
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.NumberFieldFractionalIdealFactorization
/-!
# Relative norm of nonzero fractional ideals

The norm sends a finite-prime factor upstairs to the prime below it, with
exponent multiplied by the inertia degree. Prime factorization extends this
rule to a multiplicative map on all nonzero fractional ideals.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable
section

namespace ClassFieldTheory

universe u v

/-- The relative norm of nonzero fractional ideals of number fields,
defined by its inertia-degree-weighted action on prime exponents. -/
def fractionalIdealNorm
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] :
    NumberFieldFractionalIdealGroup L →*
      NumberFieldFractionalIdealGroup K :=
  (NumberFieldFractionalIdealGroup.factorizationEquiv
      (K := K)).toMonoidHom.comp
    ((fractionalIdealNormExponentMap K L).toMultiplicative.comp
      (NumberFieldFractionalIdealGroup.factorizationEquiv
        (K := L)).symm.toMonoidHom)

end ClassFieldTheory
