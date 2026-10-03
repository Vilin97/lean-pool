/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsUnramifiedOutsideModulus
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension
/-!
# Class fields attached to ray class subgroups
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTheory

universe u

/-- A finite abelian class field realizing a subgroup of a ray class group.

The Artin map has exactly the prescribed kernel and is normalized on prime
classes by arithmetic Frobenius. -/
structure RayClassSubgroupRealization
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) (H : Subgroup (RayClassGroup m)) where
  /-- The corresponding finite abelian extension. -/
  extension : FiniteAbelianExtension K
  /-- The extension is unramified away from the modulus. -/
  unramifiedOutsideModulus :
    IsUnramifiedOutsideModulus K extension m
  /-- The Artin map attached to the extension. -/
  artin : RayClassGroup m →* (extension ≃ₐ[K] extension)
  /-- The Artin map is onto. -/
  artin_surjective : Function.Surjective artin
  /-- The prescribed subgroup is exactly the Artin kernel. -/
  artin_ker : artin.ker = H
  /-- A prime class maps to arithmetic Frobenius. -/
  artin_frobenius :
    ∀ (v : HeightOneSpectrum (𝓞 K))
      (hv : v ∉ m.finitePart.support)
      (w : HeightOneSpectrum (𝓞 extension)),
      w.asIdeal.LiesOver v.asIdeal →
        artin (rayClassOfFinitePrime m v hv) =
          arithmeticFrobeniusAt (K := K) w

end ClassFieldTheory
