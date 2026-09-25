/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
/-!
# Norm of a fractional-ideal exponent vector

A finite prime of an extension contracts to a finite prime of the base.
The norm sends its exponent to the prime below, multiplied by the inertia
degree. The resulting map on finitely supported exponent vectors is additive.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable
section

namespace ClassFieldTheory

universe u v

open scoped Classical in
/-- The finite prime below a finite prime in an extension of number fields. -/
def fractionalIdealNormPrimeBelow
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (W : HeightOneSpectrum (𝓞 L)) :
    HeightOneSpectrum (𝓞 K) where
  asIdeal := W.asIdeal.under (𝓞 K)
  isPrime := inferInstance
  ne_bot :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (M := W.asIdeal.under (𝓞 K)) inferInstance
      (RingOfIntegers.not_isField K)

open scoped Classical in
/-- The relative ideal norm on formal finite-prime exponent vectors. The
coefficient at an upstairs prime is transferred to its contracted prime and
multiplied by the inertia degree. -/
def fractionalIdealNormExponentMap
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    :
    (HeightOneSpectrum (𝓞 L) →₀ ℤ) →+
      (HeightOneSpectrum (𝓞 K) →₀ ℤ) :=
  Finsupp.liftAddHom fun W =>
    (Finsupp.singleAddHom (fractionalIdealNormPrimeBelow K L W)).comp
      (AddMonoidHom.mulLeft (W.asIdeal.inertiaDeg (𝓞 K) : ℤ))

end ClassFieldTheory
