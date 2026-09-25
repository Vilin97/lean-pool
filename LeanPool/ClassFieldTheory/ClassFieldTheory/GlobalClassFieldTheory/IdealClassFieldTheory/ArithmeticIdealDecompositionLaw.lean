/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.ArithmeticIdealArtin
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.IdealDecompositionLaw
/-!
# Arithmetic ideal Artin symbols and unramified decomposition

This module states the order calculation in the unramified
decomposition law with arithmetic Frobenius normalization.
The underlying ideal-class quotient is unchanged by inversion of the
reciprocity map, while the image of an ordinary prime ideal is the
genuine arithmetic Frobenius automorphism.
-/

@[expose] public section

open scoped NumberField
noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open NumberField IsDedekindDomain

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

open scoped Classical in
open GlobalClassFields renaming
  orderOf_arithmeticFinitePlacePrimeArtin_eq_finitePlaceLocalDegree_of_chosenUnramified →
    orderOf_primeArtin_eq_localDegree_of_unramified in
/-- At an unramified prime outside a defining modulus, the arithmetic
ideal Artin symbol has order equal to the common inertia degree of the
primes above it. -/
theorem
    orderOf_arithmeticIdealArtin_prime_eq_inertiaDegree_of_chosenUnramified
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support)
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    orderOf
        (arithmeticIdealArtinGaloisMap
          (K := K) (L := L) m hm
          (RayClass.primeToModulusIdeal m v hv)) =
      Ideal.inertiaDegIn v.asIdeal (𝓞 L) := by
  rw [
    arithmeticIdealArtinGaloisMap_primeIdeal_eq_arithmeticFinitePlacePrimeArtin,
    orderOf_primeArtin_eq_localDegree_of_unramified
        (K := K) (L := L) v hunram]
  exact
    finitePlaceLocalDegree_eq_inertiaDegree_of_chosenUnramified
      (K := K) (L := L) v hunram

open scoped Classical in
/-- The arithmetic Artin symbol of a power of an unramified prime is
trivial exactly when the common inertia degree divides the exponent. -/
theorem
    arithmeticIdealArtin_prime_pow_eq_one_iff_inertiaDegree_dvd
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support)
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v)
    (n : ℕ) :
    arithmeticIdealArtinGaloisMap
          (K := K) (L := L) m hm
          ((RayClass.primeToModulusIdeal m v hv) ^ n) =
        1 ↔
      Ideal.inertiaDegIn v.asIdeal (𝓞 L) ∣ n := by
  rw [
    map_pow,
    ← orderOf_dvd_iff_pow_eq_one,
    orderOf_arithmeticIdealArtin_prime_eq_inertiaDegree_of_chosenUnramified
      (K := K) (L := L) m hm v hv hunram]

open scoped Classical in
/-- Full unramified decomposition law expressed through the genuine
arithmetic ideal Artin symbol.  The prime factors are distinct, every
factor has degree equal to the order of arithmetic Frobenius, and the
number of factors is the global degree divided by that order. -/
theorem unramifiedPrime_arithmeticIdealDecompositionLaw
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support)
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    let f :=
      orderOf
        (arithmeticIdealArtinGaloisMap
          (K := K) (L := L) m hm
          (RayClass.primeToModulusIdeal m v hv))
    Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal =
        ∏ P ∈ v.asIdeal.primesOver (𝓞 L), P ∧
      (∀ P : Ideal (𝓞 L),
        P ∈ v.asIdeal.primesOver (𝓞 L) →
          P.inertiaDeg (𝓞 K) = f) ∧
      (v.asIdeal.primesOver (𝓞 L)).ncard =
        Module.finrank K L / f := by
  dsimp only
  refine
    ⟨unramifiedPrime_idealMap_eq_product_primesOver
        (K := K) (L := L) v hunram, ?_, ?_⟩
  · intro P hP
    rw [
      orderOf_arithmeticIdealArtin_prime_eq_inertiaDegree_of_chosenUnramified
        (K := K) (L := L) m hm v hv hunram]
    exact
      primeAbove_inertiaDegree_eq_common
        (K := K) (L := L) v P hP
  · rw [
      orderOf_arithmeticIdealArtin_prime_eq_inertiaDegree_of_chosenUnramified
        (K := K) (L := L) m hm v hv hunram]
    exact
      unramifiedPrime_numberOfPrimes_eq_extensionDegree_div_inertiaDegree
        (K := K) (L := L) v hunram

end IdealClassFieldTheory
end GlobalClassFieldTheory
