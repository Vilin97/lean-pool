/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import LeanPool.Stafford38.Stafford38.Characteristic.BaseRelativePoisson
public import LeanPool.Stafford38.Stafford38.Characteristic.PostScalarExtensionPoisson


/-!
# Minimal-prime assembly for base-relative Poisson closure

This file isolates the commutative-algebra end of the remaining Gabber input.
To prove base-relative Poisson closure of a radical, it is enough to prove the
required bracket membership in every minimal prime over the original ideal.
No integrability statement for those minimal primes is asserted here.
-/

@[expose] public section

namespace Stafford38.Characteristic.MinimalPrimePoisson

open Stafford38.Characteristic
open Stafford38.Characteristic.BaseRelativePoisson
open Stafford38.Characteristic.PostScalarExtensionPoisson
open Stafford38.Geometry.CoisotropicTranslation

noncomputable section

variable {k : Type*} [Field k] {n : ℕ}

/-- Componentwise membership in every minimal prime assembles to the exact
base-relative Poisson condition on the radical.  This is the final elementary
commutative-algebra step after the genuine Gabber integrability input. -/
theorem radical_isBaseRelativePoisson_of_minimalPrimes
    (J : Ideal (SymbolRing k n))
    (h : ∀ P ∈ J.minimalPrimes,
      ∀ f : MvPolynomial (Fin n) k, baseLift f ∈ J.radical →
        ∀ g ∈ J.radical, poissonBracket (baseLift f) g ∈ P) :
    IsBaseRelativePoisson J.radical := by
  intro f hf g hg
  rw [← J.sInf_minimalPrimes]
  exact Ideal.mem_sInf.mpr fun P hP => h P hP f hf g hg

/-- Componentwise involutivity is the natural sufficient hypothesis for the
minimal-prime assembly above.  The only commutative-algebra input is that the
radical is contained in every prime over the original ideal. -/
theorem radical_isBaseRelativePoisson_of_minimalPrimes_isInvolutive
    (J : Ideal (SymbolRing k n))
    (h : ∀ P ∈ J.minimalPrimes, IsInvolutive P) :
    IsBaseRelativePoisson J.radical := by
  apply radical_isBaseRelativePoisson_of_minimalPrimes J
  intro P hP f hf g hg
  have hprime : P.IsPrime := hP.1.1
  have hradical : J.radical ≤ P := hprime.radical_le_iff.mpr hP.1.2
  exact h P hP (baseLift f) (hradical hf) g (hradical hg)


end

end Stafford38.Characteristic.MinimalPrimePoisson
