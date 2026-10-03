/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsUnramifiedOutsideModulus
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt
/-!
# Finite abelian global reciprocity data

The interface is ideal-theoretic: a ray-class Artin map is normalized by
arithmetic Frobenius away from its modulus.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTheory

universe u v

/-- Finite abelian global-reciprocity data in ideal-theoretic form. -/
structure FiniteAbelianReciprocityData
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] where
  /-- A modulus through which the finite Artin map factors. -/
  modulus : RayClassModulus K
  /-- The extension is unramified away from the modulus. -/
  unramifiedOutsideModulus : IsUnramifiedOutsideModulus K L modulus
  /-- The finite Artin map on the ray class group. -/
  artin : RayClassGroup modulus →* (L ≃ₐ[K] L)
  /-- The finite Artin map is onto. -/
  artin_surjective : Function.Surjective artin
  /-- A prime class maps to arithmetic Frobenius. -/
  artin_frobenius :
    ∀ (v : HeightOneSpectrum (𝓞 K))
      (hv : v ∉ modulus.finitePart.support)
      (w : HeightOneSpectrum (𝓞 L)),
      w.asIdeal.LiesOver v.asIdeal →
        artin (rayClassOfFinitePrime modulus v hv) =
          arithmeticFrobeniusAt (K := K) w

end ClassFieldTheory
