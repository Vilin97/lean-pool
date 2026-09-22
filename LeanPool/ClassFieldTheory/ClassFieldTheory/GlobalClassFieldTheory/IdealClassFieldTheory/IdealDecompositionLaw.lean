/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassPrimeIdele
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.UnramifiedPrimeArtin
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldUnramifiedMaximality
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtinCompatibility
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Basic
/-!
# The ideal-theoretic unramified decomposition law

This file identifies the ideal Artin symbol of a prime with the genuine
global and local Frobenius automorphism.  For an unramified prime it then
combines this identification with the Dedekind-domain fundamental identity
to give the complete decomposition law:

* the order of the prime class modulo the defining ideal group;
* the order of the actual Frobenius automorphism;
* the common inertia degree of the primes above it; and
* the number of primes above it

are related by the global ideal decomposition law.
-/

open scoped NumberField BigOperators

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open NumberField IsDedekindDomain
open HilbertRamification

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

attribute [local instance] idealArtinKernelNormal

open scoped Classical in
/-- The actual idèlic and ideal-theoretic Artin maps form the
commutative square of the ideal formulation of global reciprocity.

For every idèle prime to the defining modulus, applying the ideal
Artin map to its fractional ideal gives its genuine global Artin
automorphism. -/
theorem idealArtinGaloisMap_primeToIdealMap_eq_globalArtin
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (a : RayClass.idelePrimeToModulusSubgroup m) :
    idealArtinGaloisMap (K := K) (L := L) m hm
        (RayClass.primeToIdealMap m a) =
      Reciprocity.globalArtinMonoidHom
        (K := K) (L := L) (a : IdeleGroup K) := by
  rw [idealArtinGaloisMap_apply]
  rw [GlobalClassFields.idealArtinMap_primeToIdealMap]
  change
    Reciprocity.globalNormResidueMonoidHom K L
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)
            (a : IdeleGroup K)) =
      Reciprocity.globalArtinMonoidHom
        (K := K) (L := L) (a : IdeleGroup K)
  exact
    DFunLike.congr_fun
      (Reciprocity.globalNormResidueMonoidHom_comp_ideleClassQuotient_eq_globalArtin
          (K := K) (L := L))
      (a : IdeleGroup K)

open scoped Classical in
/-- The Galois-valued ideal Artin map sends a prime ideal outside a
defining modulus to the actual global prime Artin element.  The latter
is, by finite-place local-global compatibility, the genuine chosen
local Frobenius value of a normalized order-one element. -/
theorem idealArtinGaloisMap_primeIdeal_eq_finitePlacePrimeArtin
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    idealArtinGaloisMap (K := K) (L := L) m hm
        (RayClass.primeToModulusIdeal m v hv) =
      GlobalClassFields.finitePlacePrimeArtin
        (K := K) (L := L) v := by
  rw [← GlobalClassFields.primeToIdealMap_finitePrimeIdele m v hv]
  exact
    idealArtinGaloisMap_primeToIdealMap_eq_globalArtin
      (K := K) (L := L) m hm
      ⟨IdeleGroup.finitePrimeIdele v,
        GlobalClassFields.finitePrimeIdele_mem_idelePrimeToModulusSubgroup
            m v hv⟩

open scoped Classical in
/-- Direct local form of the prime-ideal Artin identification: the
ideal Artin symbol is the chosen finite-place Artin value of the
normalized order-one local element. -/
theorem idealArtinGaloisMap_primeIdeal_eq_chosenFinitePlaceArtin
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    idealArtinGaloisMap (K := K) (L := L) m hm
        (RayClass.primeToModulusIdeal m v hv) =
      Reciprocity.chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v
        (FiniteIdeleGroup.chosenLocalOrderSection v 1) := by
  rw [
    idealArtinGaloisMap_primeIdeal_eq_finitePlacePrimeArtin,
    GlobalClassFields.finitePlacePrimeArtin_eq_chosenFinitePlaceArtin]

open scoped Classical in
/-- The actual ideal class-field equivalence sends the class of a prime
ideal to the genuine finite-place Frobenius automorphism. -/
theorem idealClassQuotientEquivGaloisGroup_primeIdeal
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    idealClassQuotientEquivGaloisGroup
        (K := K) (L := L) m hm
        (QuotientGroup.mk'
          (idealArtinKernel m
            ((_root_.ideleClassNorm K L).range) hm)
          (RayClass.primeToModulusIdeal m v hv)) =
      GlobalClassFields.finitePlacePrimeArtin
        (K := K) (L := L) v := by
  rw [
    idealClassQuotientEquivGaloisGroup_mk,
    idealArtinGaloisMap_primeIdeal_eq_finitePlacePrimeArtin]

open scoped Classical in
/-- Completed unramifiedness at the chosen place gives ramification
index one in the integral Dedekind extension. -/
theorem ramificationIndex_eq_one_of_chosenFinitePlaceUnramified
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    Ideal.ramificationIdxIn v.asIdeal (𝓞 L) = 1 := by
  let w :=
    _root_.chosenFinitePlaceExtension (L := L) v
  let W :=
    _root_.finitePlaceExtensionCentre
      (K := K) (L := L) v w
  let : Finite (L ≃ₐ[K] L) :=
    IsGaloisGroup.finite (L ≃ₐ[K] L) K L
  let :
      IsGaloisGroup
        (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing
      (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  let : W.asIdeal.LiesOver v.asIdeal :=
    _root_.finitePlaceExtensionCentre_liesOver
      (K := K) (L := L) v w
  have hUnramifiedAt :
      Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal :=
    _root_.isUnramifiedAt_of_chosenFinitePlaceIsUnramified
      (K := K) (L := L) v hunram
  let : Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal :=
    hUnramifiedAt
  rw [
    Ideal.ramificationIdxIn_eq_ramificationIdx
      v.asIdeal W.asIdeal (L ≃ₐ[K] L)]
  exact Ideal.ramificationIdx_eq_one W.asIdeal (𝓞 K)

open scoped Classical in
/-- At an unramified finite place, the chosen completion degree equals
the common ideal-theoretic inertia degree of the primes above it. -/
theorem finitePlaceLocalDegree_eq_inertiaDegree_of_chosenUnramified
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    _root_.finitePlaceLocalDegree
        (K := K) (L := L) v =
      Ideal.inertiaDegIn v.asIdeal (𝓞 L) := by
  let w :=
    _root_.chosenFinitePlaceExtension (L := L) v
  let W :=
    _root_.finitePlaceExtensionCentre
      (K := K) (L := L) v w
  let : Finite (L ≃ₐ[K] L) :=
    IsGaloisGroup.finite (L ≃ₐ[K] L) K L
  let :
      IsGaloisGroup
        (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing
      (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  let : W.asIdeal.LiesOver v.asIdeal :=
    _root_.finitePlaceExtensionCentre_liesOver
      (K := K) (L := L) v w
  let := _root_.finitePlaceMulAction K L
  have hGroup :
      _root_.finitePlaceDecompositionGroup
          (K := K) (L := L) v =
        MulAction.stabilizer (L ≃ₐ[K] L) W := by
    unfold _root_.finitePlaceDecompositionGroup
    exact
      _root_.absoluteValueDecompositionGroup_eq_finitePlaceStabilizer
        (K := K) (L := L) v w
  have hUnder :
      W.asIdeal.under (𝓞 K) = v.asIdeal := by
    have hBelow :=
      _root_.finitePlaceBelow_finitePlaceExtensionCentre
        (K := K) (L := L) v w
    have h :=
      congrArg HeightOneSpectrum.asIdeal hBelow
    simpa only [_root_.finitePlaceBelow_asIdeal] using h
  have hRamification :
      Ideal.ramificationIdxIn v.asIdeal (𝓞 L) = 1 :=
    ramificationIndex_eq_one_of_chosenFinitePlaceUnramified
      (K := K) (L := L) v hunram
  calc
    _root_.finitePlaceLocalDegree
        (K := K) (L := L) v =
        Nat.card
          (_root_.finitePlaceDecompositionGroup
            (K := K) (L := L) v) :=
      (_root_.finitePlaceDecompositionGroup_card_eq_localDegree
        (K := K) (L := L) v).symm
    _ =
        Nat.card
          (MulAction.stabilizer (L ≃ₐ[K] L) W) := by
      rw [hGroup]
    _ = finiteLogPlaceLocalDegree K L W :=
      finitePlace_stabilizer_card_eq_localDegree K L W
    _ =
        Ideal.ramificationIdxIn v.asIdeal (𝓞 L) *
          Ideal.inertiaDegIn v.asIdeal (𝓞 L) := by
      simp only [finiteLogPlaceLocalDegree, hUnder]
    _ = Ideal.inertiaDegIn v.asIdeal (𝓞 L) := by
      rw [hRamification, one_mul]

open scoped Classical in
/-- For an unramified prime, the order of its class modulo the ideal
Artin kernel is the common inertia degree.  Equivalently, it is the
order of the genuine global/local Frobenius automorphism. -/
theorem orderOf_idealPrimeClass_eq_inertiaDegree_of_chosenUnramified
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
        (QuotientGroup.mk'
          (idealArtinKernel m
            ((_root_.ideleClassNorm K L).range) hm)
          (RayClass.primeToModulusIdeal m v hv)) =
      Ideal.inertiaDegIn v.asIdeal (𝓞 L) := by
  calc
    orderOf
        (QuotientGroup.mk'
          (idealArtinKernel m
            ((_root_.ideleClassNorm K L).range) hm)
          (RayClass.primeToModulusIdeal m v hv)) =
        orderOf
          (idealClassQuotientEquivGaloisGroup
            (K := K) (L := L) m hm
            (QuotientGroup.mk'
              (idealArtinKernel m
                ((_root_.ideleClassNorm K L).range) hm)
              (RayClass.primeToModulusIdeal m v hv))) :=
      ((idealClassQuotientEquivGaloisGroup
        (K := K) (L := L) m hm).orderOf_eq _).symm
    _ =
        orderOf
          (GlobalClassFields.finitePlacePrimeArtin
            (K := K) (L := L) v) := by
      rw [idealClassQuotientEquivGaloisGroup_primeIdeal]
    _ =
        _root_.finitePlaceLocalDegree
          (K := K) (L := L) v :=
      GlobalClassFields.orderOf_finitePlacePrimeArtin_eq_finitePlaceLocalDegree_of_chosenUnramified
          (K := K) (L := L) v hunram
    _ =
        Ideal.inertiaDegIn v.asIdeal (𝓞 L) :=
      finitePlaceLocalDegree_eq_inertiaDegree_of_chosenUnramified
        (K := K) (L := L) v hunram

open scoped Classical in
/-- The ideal Artin kernel detects precisely the multiples of the
unramified inertia degree among powers of the prime ideal. -/
theorem unramifiedPrime_pow_mem_idealArtinKernel_iff_inertiaDegree_dvd
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
    (RayClass.primeToModulusIdeal m v hv) ^ n ∈
        idealArtinKernel m
          ((_root_.ideleClassNorm K L).range) hm ↔
      Ideal.inertiaDegIn v.asIdeal (𝓞 L) ∣ n := by
  rw [
    primeIdeal_pow_mem_idealArtinKernel_iff_orderOf_dvd,
    orderOf_idealPrimeClass_eq_inertiaDegree_of_chosenUnramified
      (K := K) (L := L) m hm v hv hunram]

open scoped Classical in
/-- In an unramified Galois extension, the number of primes above `v`
is the extension degree divided by their common inertia degree. -/
theorem unramifiedPrime_numberOfPrimes_eq_extensionDegree_div_inertiaDegree
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    (v.asIdeal.primesOver (𝓞 L)).ncard =
      Module.finrank K L /
        Ideal.inertiaDegIn v.asIdeal (𝓞 L) := by
  let : Finite (L ≃ₐ[K] L) :=
    IsGaloisGroup.finite (L ≃ₐ[K] L) K L
  let :
      IsGaloisGroup
        (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing
      (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  have hRamification :
      Ideal.ramificationIdxIn v.asIdeal (𝓞 L) = 1 :=
    ramificationIndex_eq_one_of_chosenFinitePlaceUnramified
      (K := K) (L := L) v hunram
  simpa only [IsGalois.card_aut_eq_finrank] using
    (Dedekind.dedekindRamification_unramified_numberOfPrimes_eq_degree_div_inertiaDegree
        (A := 𝓞 K) (B := 𝓞 L)
        v.asIdeal v.ne_bot (L ≃ₐ[K] L) hRamification)

open scoped Classical in
/-- In an unramified Galois extension, the extended base prime is the
product of the distinct primes above it: every exponent is one. -/
theorem unramifiedPrime_idealMap_eq_product_primesOver
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal =
      ∏ P ∈ v.asIdeal.primesOver (𝓞 L), P := by
  let : Finite (L ≃ₐ[K] L) :=
    IsGaloisGroup.finite (L ≃ₐ[K] L) K L
  let :
      IsGaloisGroup
        (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing
      (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  have hRamification :
      Ideal.ramificationIdxIn v.asIdeal (𝓞 L) = 1 :=
    ramificationIndex_eq_one_of_chosenFinitePlaceUnramified
      (K := K) (L := L) v hunram
  simpa only [hRamification, pow_one] using
    (Dedekind.dedekindRamification_galois_prime_decomposition
      (A := 𝓞 K) (B := 𝓞 L)
      v.asIdeal v.ne_bot (L ≃ₐ[K] L))

open scoped Classical in
/-- Every prime above an unramified base prime has the common inertia
degree `inertiaDegIn v (𝓞 L)`. -/
theorem primeAbove_inertiaDegree_eq_common
    (v : HeightOneSpectrum (𝓞 K))
    (P : Ideal (𝓞 L))
    (hP : P ∈ v.asIdeal.primesOver (𝓞 L)) :
    P.inertiaDeg (𝓞 K) =
      Ideal.inertiaDegIn v.asIdeal (𝓞 L) := by
  let : Finite (L ≃ₐ[K] L) :=
    IsGaloisGroup.finite (L ≃ₐ[K] L) K L
  let :
      IsGaloisGroup
        (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing
      (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  let : P.IsPrime := hP.1
  let : P.LiesOver v.asIdeal := hP.2
  exact
    (Ideal.inertiaDegIn_eq_inertiaDeg
      v.asIdeal P (L ≃ₐ[K] L)).symm

open scoped Classical in
/-- The number of prime factors above an unramified prime is the
extension degree divided by the order of its ideal class modulo the
defining ideal group. -/
theorem unramifiedPrime_numberOfPrimes_eq_extensionDegree_div_idealClassOrder
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support)
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    (v.asIdeal.primesOver (𝓞 L)).ncard =
      Module.finrank K L /
        orderOf
          (QuotientGroup.mk'
            (idealArtinKernel m
              ((_root_.ideleClassNorm K L).range) hm)
            (RayClass.primeToModulusIdeal m v hv)) := by
  rw [
    orderOf_idealPrimeClass_eq_inertiaDegree_of_chosenUnramified
      (K := K) (L := L) m hm v hv hunram]
  exact
    unramifiedPrime_numberOfPrimes_eq_extensionDegree_div_inertiaDegree
      (K := K) (L := L) v hunram

open scoped Classical in
/-- Full ideal-theoretic decomposition law for an unramified prime.

The prime factors are distinct, all have inertia degree equal to the
order of the prime class modulo the defining ideal group, and their
number is the global degree divided by that order. -/
theorem unramifiedPrime_idealDecompositionLaw
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
        (QuotientGroup.mk'
          (idealArtinKernel m
            ((_root_.ideleClassNorm K L).range) hm)
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
      orderOf_idealPrimeClass_eq_inertiaDegree_of_chosenUnramified
        (K := K) (L := L) m hm v hv hunram]
    exact
      primeAbove_inertiaDegree_eq_common
        (K := K) (L := L) v P hP
  · exact
      unramifiedPrime_numberOfPrimes_eq_extensionDegree_div_idealClassOrder
        (K := K) (L := L) m hm v hv hunram

section SmallHilbertPrimeSplitting

variable {K : Type} [Field K] [NumberField K]

open scoped Classical in
/-- Under actual reciprocity for the selected small Hilbert class
field, its genuine prime Frobenius automorphism is the ordinary ideal
class of the corresponding prime. -/
theorem
    smallHilbertClassFieldGaloisEquivClassGroup_finitePlacePrimeArtin
    (v : HeightOneSpectrum (𝓞 K)) :
    GlobalClassFields.smallHilbertClassFieldGaloisEquivClassGroupOverOriginal
          (K := K)
          (GlobalClassFields.finitePlacePrimeArtin
            (K := K)
            (L := GlobalClassFields.smallHilbertClassField K) v) =
      ClassGroup.mk K (FractionalIdealGroup.prime v) := by
  rw [GlobalClassFields.finitePlacePrimeArtin]
  rw [
    ← DFunLike.congr_fun
      (Reciprocity.globalNormResidueMonoidHom_comp_ideleClassQuotient_eq_globalArtin
          (K := K)
          (L := GlobalClassFields.smallHilbertClassField K))
      (IdeleGroup.finitePrimeIdele v)]
  rw [MonoidHom.comp_apply]
  rw [
    GlobalClassFields.smallHilbertClassFieldGaloisEquivClassGroupOverOriginal_idele,
    IdeleGroup.idealClass_finitePrimeIdele]

open scoped Classical in
/-- Every finite place is unramified in the selected small Hilbert
class field, in the completed chosen-place formulation used by the
local Artin map. -/
theorem smallHilbertClassField_chosenFinitePlaceIsUnramified
    (v : HeightOneSpectrum (𝓞 K)) :
    _root_.ChosenFinitePlaceIsUnramified
      (K := K)
      (L := GlobalClassFields.smallHilbertClassField K) v := by
  let w :=
    _root_.chosenFinitePlaceExtension
      (L := GlobalClassFields.smallHilbertClassField K) v
  let W :=
    _root_.finitePlaceExtensionCentre
      (K := K)
      (L := GlobalClassFields.smallHilbertClassField K) v w
  apply
    _root_.chosenFinitePlaceIsUnramified_of_isUnramifiedAt
      (K := K)
      (L := GlobalClassFields.smallHilbertClassField K) v
  exact
    GlobalClassFields.smallHilbertClassField_isUnramifiedAtFinitePlaces
      K W

open scoped Classical in
/-- A prime of the original number field actually splits completely
in the selected small Hilbert class field exactly when its prime ideal
is principal. -/
theorem finitePlaceSplitsCompletelyInSmallHilbertClassField_iff_principal
    (v : HeightOneSpectrum (𝓞 K)) :
    _root_.FinitePlaceSplitsCompletely
          (K := K)
          (L := GlobalClassFields.smallHilbertClassField K) v ↔
      FractionalIdealGroup.prime v ∈
        (toPrincipalIdeal (𝓞 K) K).range := by
  let e :=
    GlobalClassFields.smallHilbertClassFieldGaloisEquivClassGroupOverOriginal
        (K := K)
  have hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K)
        (L := GlobalClassFields.smallHilbertClassField K) v :=
    smallHilbertClassField_chosenFinitePlaceIsUnramified
      (K := K) v
  have hFrobenius :
      GlobalClassFields.finitePlacePrimeArtin
            (K := K)
            (L := GlobalClassFields.smallHilbertClassField K) v =
          1 ↔
        ClassGroup.mk K (FractionalIdealGroup.prime v) =
          1 := by
    constructor
    · intro h
      calc
        ClassGroup.mk K (FractionalIdealGroup.prime v) =
            e
              (GlobalClassFields.finitePlacePrimeArtin
                (K := K)
                (L := GlobalClassFields.smallHilbertClassField K) v) := by
          rw [
            smallHilbertClassFieldGaloisEquivClassGroup_finitePlacePrimeArtin]
        _ = e 1 := congrArg e h
        _ = 1 := e.map_one
    · intro h
      apply e.injective
      rw [
        smallHilbertClassFieldGaloisEquivClassGroup_finitePlacePrimeArtin,
        h, e.map_one]
  rw [
    ← GlobalClassFields.finitePlacePrimeArtin_eq_one_iff_splitsCompletely_of_chosenUnramified
        (K := K)
        (L := GlobalClassFields.smallHilbertClassField K) v hunram,
    hFrobenius]
  exact
    IdeleGroup.classGroup_mk_eq_one_iff
      (FractionalIdealGroup.prime v)

end SmallHilbertPrimeSplitting

end IdealClassFieldTheory
end GlobalClassFieldTheory
