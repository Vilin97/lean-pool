/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Rational
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteIdeleArtin
import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.RationalCyclotomicField
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
/-!
# Unramified finite places of rational cyclotomic levels

This file connects the cyclotomic ramification-index formula over `ℤ`
to the finite-place completions used by the global Artin map.  A rational
prime outside the conductor is unramified at the actual chosen extension
of its normalized finite-place absolute value.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

local instance (q : Nat.Primes) : Fact q.1.Prime :=
  ⟨q.2⟩

/-- The height-one prime of `𝓞 ℚ` indexed by `q` lies over the principal
prime ideal `(q)` of `ℤ`. -/
theorem rationalPrime_liesOver_integerSpan
    (q : Nat.Primes) :
    (RayClass.rationalPrime q).asIdeal.LiesOver
      (Ideal.span {(q.1 : ℤ)}) := by
  constructor
  change
    Ideal.span {(q.1 : ℤ)} =
      (RayClass.rationalPrime q).asIdeal.comap
        (algebraMap ℤ (𝓞 ℚ))
  rw [← RayClass.natGenerator_rationalPrime q,
    Rat.HeightOneSpectrum.span_natGenerator]
  have hAlgebraMap :
      (algebraMap ℤ (𝓞 ℚ)) =
        (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm.toRingHom :=
    Subsingleton.elim _ _
  rw [hAlgebraMap]
  exact Ideal.map_comap_of_equiv _

/-- The centre of the chosen finite-place extension in a rational
cyclotomic level is algebraically unramified away from the level. -/
theorem rationalCyclotomicLevel_isUnramifiedAt_chosenFinitePlaceCentre
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) :
    Algebra.IsUnramifiedAt (𝓞 ℚ)
      (finitePlaceExtensionCentre
        (K := ℚ)
        (L := KummerTheory.rationalCyclotomicLevel m)
        (RayClass.rationalPrime q)
        (chosenFinitePlaceExtension
          (L := KummerTheory.rationalCyclotomicLevel m)
          (RayClass.rationalPrime q))).asIdeal := by
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    RayClass.rationalPrime q
  let L :=
    KummerTheory.rationalCyclotomicLevel m
  let W :=
    finitePlaceExtensionCentre
      (K := ℚ) (L := L) v
      (chosenFinitePlaceExtension (L := L) v)
  change Algebra.IsUnramifiedAt (𝓞 ℚ) W.asIdeal
  let hWv : W.asIdeal.LiesOver v.asIdeal :=
    finitePlaceExtensionCentre_liesOver
      (K := ℚ) (L := L) v
      (chosenFinitePlaceExtension (L := L) v)
  let hvq :
      v.asIdeal.LiesOver (Ideal.span {(q.1 : ℤ)}) := by
    dsimp only [v]
    exact rationalPrime_liesOver_integerSpan q
  let hWq :
      W.asIdeal.LiesOver (Ideal.span {(q.1 : ℤ)}) :=
    Ideal.LiesOver.trans W.asIdeal v.asIdeal
      (Ideal.span {(q.1 : ℤ)})
  have hAbsolute :
      W.asIdeal.ramificationIdx ℤ = 1 :=
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd
      q.1 L W.asIdeal hq
  have hTower :
      W.asIdeal.ramificationIdx ℤ =
        v.asIdeal.ramificationIdx ℤ *
          W.asIdeal.ramificationIdx (𝓞 ℚ) :=
    Ideal.ramificationIdx_tower
      (R := ℤ) v.asIdeal W.asIdeal
  have hRelative :
      W.asIdeal.ramificationIdx (𝓞 ℚ) = 1 :=
    Nat.eq_one_of_mul_eq_one_left
      (hTower.symm.trans hAbsolute)
  exact Ideal.ramificationIdx_eq_one_iff.mp hRelative

/-- A rational cyclotomic level is unramified at every chosen finite
place whose underlying rational prime does not divide the level. -/
theorem rationalCyclotomicLevel_chosenFinitePlaceIsUnramified
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) :
    ChosenFinitePlaceIsUnramified
      (K := ℚ)
      (L := KummerTheory.rationalCyclotomicLevel m)
      (RayClass.rationalPrime q) := by
  apply chosenFinitePlaceIsUnramified_of_isUnramifiedAt
  exact
    rationalCyclotomicLevel_isUnramifiedAt_chosenFinitePlaceCentre
      m q hq

end Reciprocity
end GlobalClassFieldTheory
