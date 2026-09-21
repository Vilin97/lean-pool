/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Spectrum.Prime.Defs

/-!
# Constant or transcendental coordinates on an affine component

For a prime component over an algebraically closed field, a coordinate is
either constant on the component or transcendental in its function field.
Together with existence of a minimal prime over every proper affine ideal,
this gives the component split used before the divisorial-boundary
construction.
-/

namespace Stafford38.Geometry.AffineComponentCoordinateSplit

open Polynomial

noncomputable section

universe u

variable {k : Type u} [Field k] {m : ℕ}

/-- The image of an affine coordinate in the fraction field of a prime
component. -/
def componentCoordinate
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (i : Fin m) :
    FractionRing
      (MvPolynomial (Fin m) k ⧸ P.asIdeal) :=
  algebraMap
      (MvPolynomial (Fin m) k ⧸ P.asIdeal)
      (FractionRing (MvPolynomial (Fin m) k ⧸ P.asIdeal))
    (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i))

/-- On a prime affine component over an algebraically closed field, a
coordinate is either represented by a ground-field constant or is
transcendental in the component function field. -/
theorem coordinate_constant_or_transcendental
    [IsAlgClosed k]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (i : Fin m) :
    (∃ c : k, MvPolynomial.X i - MvPolynomial.C c ∈ P.asIdeal) ∨
      Transcendental k (componentCoordinate P i) := by
  classical
  by_cases htr : Transcendental k (componentCoordinate P i)
  · exact Or.inr htr
  · left
    have halg : IsAlgebraic k (componentCoordinate P i) := by
      simpa only [Transcendental, not_not] using htr
    have hint : IsIntegral k (componentCoordinate P i) :=
      isAlgebraic_iff_isIntegral.mp halg
    let p := minpoly k (componentCoordinate P i)
    have hpmonic : p.leadingCoeff = 1 := minpoly.monic hint
    have hpdegree : p.degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)
    have hroot : aeval (componentCoordinate P i) p = 0 :=
      minpoly.aeval k (componentCoordinate P i)
    rw [eq_X_add_C_of_degree_eq_one hpdegree, hpmonic, Polynomial.C_1,
      one_mul, aeval_add, aeval_X, aeval_C, add_eq_zero_iff_eq_neg] at hroot
    let c : k := -p.coeff 0
    refine ⟨c, ?_⟩
    have hfield :
        algebraMap k
            (FractionRing (MvPolynomial (Fin m) k ⧸ P.asIdeal)) c =
          componentCoordinate P i := by
      simpa only [c, map_neg] using hroot.symm
    have hquotient :
        algebraMap k (MvPolynomial (Fin m) k ⧸ P.asIdeal) c =
          Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i) := by
      apply IsFractionRing.injective
        (MvPolynomial (Fin m) k ⧸ P.asIdeal)
        (FractionRing (MvPolynomial (Fin m) k ⧸ P.asIdeal))
      change algebraMap k
          (FractionRing (MvPolynomial (Fin m) k ⧸ P.asIdeal)) c =
        componentCoordinate P i
      exact hfield
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [map_sub, ← MvPolynomial.algebraMap_eq,
      Ideal.Quotient.mk_algebraMap]
    exact sub_eq_zero.mpr hquotient.symm

/-- Every proper affine ideal has a minimal-prime component on which the
distinguished coordinate is either constant or transcendental in the
component function field.  Radicality is not needed for this component
selection theorem. -/
theorem exists_minimalPrime_coordinate_constant_or_transcendental
    [IsAlgClosed k]
    (I : Ideal (MvPolynomial (Fin m) k)) (hproper : I ≠ ⊤) (i : Fin m) :
    ∃ P : PrimeSpectrum (MvPolynomial (Fin m) k),
      P.asIdeal ∈ I.minimalPrimes ∧
      I ≤ P.asIdeal ∧
      ((∃ c : k, MvPolynomial.X i - MvPolynomial.C c ∈ P.asIdeal) ∨
        Transcendental k (componentCoordinate P i)) := by
  classical
  let P₀ : I.minimalPrimes := Classical.choice (I.nonempty_minimalPrimes hproper)
  let P : PrimeSpectrum (MvPolynomial (Fin m) k) :=
    ⟨P₀.1, P₀.2.isPrime⟩
  exact ⟨P, P₀.2, P₀.2.le, coordinate_constant_or_transcendental P i⟩


end

end Stafford38.Geometry.AffineComponentCoordinateSplit
