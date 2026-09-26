/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassModulus
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.RingTheory.Unramified.Locus
/-!
# Unramifiedness outside the support of a ray modulus
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTheory

universe u v

/-- A number-field extension is unramified away from the finite primes and
real places occurring in a ray modulus.  Only the support of the finite part
is used; this predicate does not bound conductor exponents. -/
def IsUnramifiedOutsideModulus
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    (m : RayClassModulus K) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 K), v ∉ m.finitePart.support →
      Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal) ∧
    ∀ (v : InfinitePlace K) (hv : v.IsReal),
      (⟨v, hv⟩ : RayClassRealPlace K) ∉ m.infinitePart →
        v.IsUnramifiedIn L

end ClassFieldTheory
