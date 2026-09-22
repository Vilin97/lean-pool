/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerAlgEquivNaturality
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianLocalConductorComparison
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidue
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicFinitePlaceArtin
import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.RayClassComparison
import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.RationalCyclotomicCharacterEquiv
/-!
# Rational cyclotomic ray norm groups

For a positive integer `m`, the genuine idèle-class norm range of the
actual cyclotomic level `ℚ(μ_m)` is the rational ray congruence subgroup
modulo `(m)`.

The local input is the cyclotomic higher-unit calculation: at a rational prime
`q`, an
`m.factorization q`-th higher unit has trivial Artin action on every
prime-power cyclotomic part.  On the `q`-primary part this is the actual
multiplicative Lubin--Tate norm theorem; on every other primary part it is
the unramified Artin formula together with valuation zero.  The finite
cyclotomic character then detects that the full local Artin symbol is
trivial.
-/

open scoped NNReal NumberField ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open LubinTate

open scoped Classical in
local instance localPrimesInstance1 (q : Nat.Primes) : Fact q.1.Prime :=
  ⟨q.2⟩

attribute [local instance] localPrimesInstance1

attribute [local instance]
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional
  rationalCyclotomicPrincipalPrimeLevelIsAbelianGalois

section FinitePlaceLocalCalculation

attribute [local instance]
  rationalFinitePlaceBaseNontriviallyNormedField
  rationalFinitePlaceBaseLocallyCompactSpace
  rationalFinitePlaceBaseIsUltrametricDist
  rationalFinitePlaceBaseValued
  rationalFinitePlaceBaseValuativeRel
  rationalFinitePlaceBaseValuationIsNontrivial
  rationalFinitePlaceBaseValuationCompatible
  rationalFinitePlaceBaseValuativeRelIsNontrivial
  rationalFinitePlaceBaseIsValuativeTopology
  rationalFinitePlaceBaseIsNonarchimedeanLocalField

open scoped Classical in
private theorem
    rationalRayNorm_integerUnitsMap_mem_higherPrincipalUnits_iff
    (q : Nat.Primes) (n : ℕ)
    (u : 𝒪[RationalCyclotomicPrincipalPrimeCompletion q]ˣ) :
    Units.mapEquiv
          (((rationalFinitePlaceCompletionIntegerRingEquivPadicInt q).trans
            (padicIntEquivValuationSubring q.1)).toMulEquiv) u ∈
        higherPrincipalUnitGroup
          (padicLocalField q.1).toCompleteDVF n ↔
      u ∈ principalUnits
        (RationalCyclotomicPrincipalPrimeCompletion q) n := by
  let F := RationalCyclotomicPrincipalPrimeCompletion q
  let eO :
      𝒪[F] ≃+* (padicLocalField q.1).valuationSubring :=
    (rationalFinitePlaceCompletionIntegerRingEquivPadicInt q).trans
      (padicIntEquivValuationSubring q.1)
  change
    eO (u : 𝒪[F]) - 1 ∈
        (padicLocalField q.1).toCompleteDVF.maximalIdeal ^ n ↔
      (u : 𝒪[F]) - 1 ∈
        (IsLocalRing.maximalIdeal 𝒪[F]) ^ n
  simpa only [map_sub, map_one] using
    (ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff
      eO n ((u : 𝒪[F]) - 1))

open scoped Classical in
private theorem rationalRayNorm_fieldUnitsMap_integerUnits
    (q : Nat.Primes)
    (u : 𝒪[RationalCyclotomicPrincipalPrimeCompletion q]ˣ) :
    Units.map
        (rationalFinitePlaceCompletionRingEquivPadic q).toMonoidHom
        (IsNonarchimedeanLocalField.integerUnitsToFieldUnits
          (RationalCyclotomicPrincipalPrimeCompletion q) u) =
      CompleteDVF.valuationSubringUnitsToFieldUnits
        (padicLocalField q.1).toCompleteDVF
        (Units.mapEquiv
          (((rationalFinitePlaceCompletionIntegerRingEquivPadicInt q).trans
            (padicIntEquivValuationSubring q.1)).toMulEquiv) u) := by
  let F := RationalCyclotomicPrincipalPrimeCompletion q
  let eK := rationalFinitePlaceCompletionRingEquivPadic q
  let eO :
      𝒪[F] ≃+* (padicLocalField q.1).valuationSubring :=
    (rationalFinitePlaceCompletionIntegerRingEquivPadicInt q).trans
      (padicIntEquivValuationSubring q.1)
  apply Units.ext
  change
    eK (algebraMap 𝒪[F] F
        ((u : 𝒪[F]ˣ) : 𝒪[F])) =
      algebraMap (padicLocalField q.1).valuationSubring ℚ_[q.1]
        (eO ((u : 𝒪[F]ˣ) : 𝒪[F]))
  calc
    eK (algebraMap 𝒪[F] F
        ((u : 𝒪[F]ˣ) : 𝒪[F])) =
      algebraMap ℤ_[q.1] ℚ_[q.1]
        ((rationalFinitePlaceCompletionIntegerRingEquivPadicInt q)
          ((u : 𝒪[F]ˣ) : 𝒪[F])) :=
      rationalFinitePlaceCompletionIntegerRingEquivPadicInt_coe
        q ((u : 𝒪[F]ˣ) : 𝒪[F])
    _ =
      algebraMap (padicLocalField q.1).valuationSubring ℚ_[q.1]
        (padicIntEquivValuationSubring q.1
          ((rationalFinitePlaceCompletionIntegerRingEquivPadicInt q)
            ((u : 𝒪[F]ˣ) : 𝒪[F]))) := by
        change
          (((rationalFinitePlaceCompletionIntegerRingEquivPadicInt q)
              ((u : 𝒪[F]ˣ) : 𝒪[F]) : ℤ_[q.1]) : ℚ_[q.1]) =
            ((padicIntEquivValuationSubring q.1
              ((rationalFinitePlaceCompletionIntegerRingEquivPadicInt q)
                ((u : 𝒪[F]ˣ) : 𝒪[F])) :
                (padicDVRValuation q.1).valuationSubring) : ℚ_[q.1])
        exact
          (padicIntEquivValuationSubring_coe q.1
            ((rationalFinitePlaceCompletionIntegerRingEquivPadicInt q)
              ((u : 𝒪[F]ˣ) : 𝒪[F]))).symm
    _ =
      algebraMap (padicLocalField q.1).valuationSubring ℚ_[q.1]
        (eO ((u : 𝒪[F]ˣ) : 𝒪[F])) :=
      rfl

open scoped Classical in
/-- The canonical rational-completion equivalence transports the
topology-first principal-unit subgroup to the packaged higher-principal-unit
subgroup in the standard `q`-adic field. -/
theorem
    rationalFinitePlaceFieldPrincipalUnits_map_eq_padicHigherPrincipalUnits
    (q : Nat.Primes) (n : ℕ) :
    let vQ :=
      HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)
    let eK :=
      rationalFinitePlaceCompletionRingEquivPadic q
    (fieldPrincipalUnits vQ.Completion n).map
        (Units.map eK.toMonoidHom) =
      (higherPrincipalUnitGroup
        (padicLocalField q.1).toCompleteDVF n).map
        (CompleteDVF.valuationSubringUnitsToFieldUnits
          (padicLocalField q.1).toCompleteDVF) := by
  let vQ :=
    HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)
  let eO :
      𝒪[vQ.Completion] ≃+*
        (padicLocalField q.1).valuationSubring :=
    (rationalFinitePlaceCompletionIntegerRingEquivPadicInt q).trans
      (padicIntEquivValuationSubring q.1)
  let eU :
      𝒪[vQ.Completion]ˣ ≃*
        (padicLocalField q.1).valuationSubringˣ :=
    Units.mapEquiv eO.toMulEquiv
  let jQ : 𝒪[vQ.Completion]ˣ →* vQ.Completionˣ :=
    IsNonarchimedeanLocalField.integerUnitsToFieldUnits vQ.Completion
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    change
      z ∈
        (principalUnits vQ.Completion n).map jQ at hz
    obtain ⟨u, hu, rfl⟩ := hz
    refine
      ⟨eU u,
        (rationalRayNorm_integerUnitsMap_mem_higherPrincipalUnits_iff
          q n u).2 hu,
        ?_⟩
    exact (rationalRayNorm_fieldUnitsMap_integerUnits q u).symm
  · rintro ⟨u, hu, rfl⟩
    let z : 𝒪[vQ.Completion]ˣ := eU.symm u
    have hzu :
        eU z = u :=
      eU.apply_symm_apply u
    refine
      ⟨jQ z, ⟨z, ?_, rfl⟩, ?_⟩
    · apply
      (rationalRayNorm_integerUnitsMap_mem_higherPrincipalUnits_iff
          q n z).1
      exact hzu.symm ▸ hu
    · exact
        (rationalRayNorm_fieldUnitsMap_integerUnits q z).trans
          (congrArg
            (CompleteDVF.valuationSubringUnitsToFieldUnits
              (padicLocalField q.1).toCompleteDVF)
            hzu)

section PrimePowerCalculation

attribute [local instance]
  rationalCyclotomicPrincipalPrimePadicLevelFiniteDimensional

open scoped Classical in
noncomputable local instance
    rationalCyclotomicRayNormPadicLevelIsAbelianGalois
    (q : Nat.Primes) (n : ℕ) :
    IsAbelianGalois ℚ_[q.1]
      (RationalCyclotomicPrincipalPrimePadicLevel q n) :=
  standardLubinTateLevelField_isAbelianGalois
    (padicLocalField q.1)
    (padicMultiplicativeLubinTateSeries_isUniformizer q.1) n

attribute [local instance] rationalCyclotomicRayNormPadicLevelIsAbelianGalois

open scoped Classical in
/-- A rational higher unit has trivial local Artin image in the standard
multiplicative Lubin--Tate level.  This is the purely `q`-adic part of the
prime-power argument; the semilinear transport to the localized global
cyclotomic field is handled separately below. -/
private theorem rationalPrimePowerPadicAbelianLocalArtin_eq_one
    (q : Nat.Primes) (n : ℕ)
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ)
    (hx :
      x ∈ RayClass.localHigherUnitGroup
        (RayClass.rationalPrime q) (n + 1)) :
    abelianLocalArtinMonoidHom ℚ_[q.1]
        (RationalCyclotomicPrincipalPrimePadicLevel q n)
        (Units.map
          (rationalFinitePlaceCompletionRingEquivPadic q).toMonoidHom
          ((finitePlaceCompletionUnitsContinuousMulEquiv
            (RayClass.rationalPrime q)).symm x)) = 1 := by
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    RayClass.rationalPrime q
  let vQ := HeightOneSpectrum.adicAbv ℚ v
  let eK := rationalFinitePlaceCompletionRingEquivPadic q
  let eC :
      vQ.Completionˣ ≃ₜ* (v.adicCompletion ℚ)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  let localInput : vQ.Completionˣ := eC.symm x
  let T := RationalCyclotomicPrincipalPrimePadicLevel q n
  have hxMap :
      x ∈
        (fieldPrincipalUnits vQ.Completion (n + 1)).map
          eC.toMonoidHom := by
    rw [
      GlobalClassFields.finitePlaceFieldPrincipalUnits_map_eq_localHigherUnitGroup
          (K := ℚ) v (n + 1)]
    exact hx
  have hlocalInput :
      localInput ∈
        fieldPrincipalUnits vQ.Completion (n + 1) := by
    obtain ⟨y, hy, hyx⟩ := hxMap
    have hylocal : y = localInput := by
      have hyx' : eC y = x := hyx
      apply eC.injective
      exact hyx'.trans (eC.apply_symm_apply x).symm
    rw [← hylocal]
    exact hy
  have hxMapped :
      Units.map eK.toMonoidHom localInput ∈
        (higherPrincipalUnitGroup
          (padicLocalField q.1).toCompleteDVF (n + 1)).map
          (CompleteDVF.valuationSubringUnitsToFieldUnits
            (padicLocalField q.1).toCompleteDVF) := by
    rw [←
      rationalFinitePlaceFieldPrincipalUnits_map_eq_padicHigherPrincipalUnits
        q (n + 1)]
    exact ⟨localInput, hlocalInput, rfl⟩
  obtain ⟨u, hu, hux⟩ := hxMapped
  have hPadic :
      abelianLocalArtinMonoidHom ℚ_[q.1] T
          (Units.map eK.toMonoidHom localInput) = 1 := by
    rw [← hux]
    simpa only [standardLubinTateUnitFactorFieldUnit] using
      (padicMultiplicativeAbelianLocalArtin_eq_one_of_mem_higherPrincipalUnitGroup
        q.1 n u hu)
  simpa only [T, eK, localInput, eC, vQ, v] using hPadic

open scoped Classical in
/-- The chosen ramified finite-place Artin value, with the cyclotomic level
and its instance arguments frozen behind a named boundary. -/
private noncomputable def rationalPrimePowerChosenFinitePlaceArtinValue
    (q : Nat.Primes) (n : ℕ)
    (x :
      ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    KummerTheory.rationalCyclotomicLevel
          (rationalCyclotomicPrincipalPrimeModulus q n) ≃ₐ[ℚ]
        KummerTheory.rationalCyclotomicLevel
          (rationalCyclotomicPrincipalPrimeModulus q n) :=
  chosenFinitePlaceArtinMonoidHom
    (K := ℚ)
    (L :=
      KummerTheory.rationalCyclotomicLevel
        (rationalCyclotomicPrincipalPrimeModulus q n))
    (RayClass.rationalPrime q) x

open scoped Classical in
/-- The standard `q`-adic calculation evaluated on the canonical input used
by the finite-place Artin construction. -/
private theorem rationalPrimePowerFinitePlaceLocalInputPadicArtin_eq_one
    (q : Nat.Primes) (n : ℕ)
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ)
    (hx :
      x ∈ RayClass.localHigherUnitGroup
        (RayClass.rationalPrime q) (n + 1)) :
    abelianLocalArtinMonoidHom ℚ_[q.1]
        (RationalCyclotomicPrincipalPrimePadicLevel q n)
        (Units.map
          (rationalFinitePlaceCompletionRingEquivPadic q).toMonoidHom
          (finitePlaceLocalArtinInput
            (RayClass.rationalPrime q) x)) = 1 := by
  change
    abelianLocalArtinMonoidHom ℚ_[q.1]
        (RationalCyclotomicPrincipalPrimePadicLevel q n)
        (Units.map
          (rationalFinitePlaceCompletionRingEquivPadic q).toMonoidHom
          ((finitePlaceCompletionUnitsContinuousMulEquiv
            (RayClass.rationalPrime q)).symm x)) = 1
  exact rationalPrimePowerPadicAbelianLocalArtin_eq_one q n x hx

open scoped Classical in
/-- The normalized local calculation, transported through the decomposition
group inclusion.  This bridge contains no semilinear instance search. -/
private theorem rationalPrimePowerFinitePlaceArtinOfExtension_eq_one
    (q : Nat.Primes) (n : ℕ)
    (x :
      ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ)
    (hx :
      x ∈ RayClass.localHigherUnitGroup
        (RayClass.rationalPrime q) (n + 1)) :
    finitePlaceArtinMonoidHomOfExtension
        (K := ℚ)
        (L := KummerTheory.rationalCyclotomicLevel
          (rationalCyclotomicPrincipalPrimeModulus q n))
        (RayClass.rationalPrime q)
        (rationalCyclotomicChosenFinitePlaceExtension
          (rationalCyclotomicPrincipalPrimeModulus q n)
          (RayClass.rationalPrime q)) x = 1 := by
  exact
    rationalCyclotomicPrincipalPrime_finitePlaceArtinOfExtension_eq_one_of_padic
      q n x
      (rationalPrimePowerFinitePlaceLocalInputPadicArtin_eq_one q n x hx)

open scoped Classical in
/-- The local semilinear calculation for a ramified prime-power level.  Its
statement only exposes the named global Artin value. -/
private theorem
    rationalPrimePowerChosenFinitePlaceArtinValue_eq_one_of_mem_localHigherUnitGroup
    (q : Nat.Primes) (n : ℕ)
    (x :
      ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ)
    (hx :
      x ∈ RayClass.localHigherUnitGroup
        (RayClass.rationalPrime q) (n + 1)) :
    rationalPrimePowerChosenFinitePlaceArtinValue q n x = 1 := by
  simpa only [rationalPrimePowerChosenFinitePlaceArtinValue,
    chosenFinitePlaceArtinMonoidHom,
    rationalCyclotomicChosenFinitePlaceExtension] using
    rationalPrimePowerFinitePlaceArtinOfExtension_eq_one q n x hx

open scoped Classical in
/-- A principal unit of depth `n + 1` has trivial chosen finite-place
Artin symbol in the genuine `q ^ (n + 1)`-st rational cyclotomic level. -/
theorem
    rationalPrimePowerChosenFinitePlaceArtin_eq_one_of_mem_localHigherUnitGroup
    (q : Nat.Primes) (n : ℕ)
    (x :
      ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ)
    (hx :
      x ∈ RayClass.localHigherUnitGroup
        (RayClass.rationalPrime q) (n + 1)) :
    chosenFinitePlaceArtinMonoidHom
        (K := ℚ)
        (L :=
          KummerTheory.rationalCyclotomicLevel
            (rationalCyclotomicPrincipalPrimeModulus q n))
        (RayClass.rationalPrime q) x =
      1 := by
  simpa only [rationalPrimePowerChosenFinitePlaceArtinValue] using
    rationalPrimePowerChosenFinitePlaceArtinValue_eq_one_of_mem_localHigherUnitGroup
      q n x hx

open scoped Classical in
/-- The positive-depth form of the prime-power calculation.  Eliminating
the successor before introducing a cyclotomic level avoids transporting its
dependent field and instance data later in the full-level coordinate proof. -/
private theorem
    rationalPrimePowerChosenFinitePlaceArtin_eq_one_of_mem_localHigherUnitGroup_pos
    (q : Nat.Primes) (k : ℕ) (hk : k ≠ 0)
    (mp : ℕ+) (hmp : (mp : ℕ) = q.1 ^ k)
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ)
    (hx :
      x ∈ RayClass.localHigherUnitGroup
        (RayClass.rationalPrime q) k) :
    chosenFinitePlaceArtinMonoidHom
        (K := ℚ)
        (L := KummerTheory.rationalCyclotomicLevel mp)
        (RayClass.rationalPrime q) x = 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hlevel :
      mp = rationalCyclotomicPrincipalPrimeModulus q n := by
    apply Subtype.ext
    exact hmp
  subst mp
  exact
    rationalPrimePowerChosenFinitePlaceArtin_eq_one_of_mem_localHigherUnitGroup
      q n x hx

open scoped Classical in
/-- A valuation-zero input away from a named cyclotomic level has trivial
chosen Artin value.  Keeping the level as a positive-natural variable makes
the instance owner identical on both sides of the imported calculation. -/
private theorem rationalCyclotomicRayNormAwayChosenFinitePlaceArtin_eq_one
    (mp : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (mp : ℕ))
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ)
    (hzero : rationalCyclotomicArtinLocalExponent q x = 0) :
    chosenFinitePlaceArtinMonoidHom
        (K := ℚ)
        (L := KummerTheory.rationalCyclotomicLevel mp)
        (RayClass.rationalPrime q) x = 1 := by
  exact
    chosenFinitePlaceArtinMonoidHom_eq_one_of_not_dvd_of_localExponent_eq_zero
      mp q hq x hzero

end PrimePowerCalculation

open scoped Classical in
/-- Membership in a rational local higher-unit group forces the normalized
cyclotomic Artin exponent to vanish.  This boundary keeps the completion and
valuation expansion out of the full cyclotomic-coordinate calculation. -/
private theorem
    rationalCyclotomicRayNormLocalExponent_eq_zero_of_mem_localHigherUnitGroup
    (q : Nat.Primes) (n : ℕ)
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ)
    (hx :
      x ∈ RayClass.localHigherUnitGroup
        (RayClass.rationalPrime q) n) :
    rationalCyclotomicArtinLocalExponent q x = 0 := by
  change
    IsNonarchimedeanLocalField.valuationMap
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        (Additive.ofMul
          ((finitePlaceCompletionUnitsContinuousMulEquiv
            (RayClass.rationalPrime q)).symm x)) =
      0
  exact
    _root_.GlobalClassFieldTheory.GlobalClassFields.finitePlaceCompletion_valuationMap_eq_zero_of_mem_localHigherUnitGroup
      (K := ℚ) (RayClass.rationalPrime q) n x hx

open scoped Classical in
/-- The rational ray-class higher-unit group at `q` consists of actual
local norms from the chosen completion of the genuine cyclotomic level. -/
theorem
    rationalCyclotomicLevel_localHigherUnitGroup_le_chosenLocalNorm
    (m : ℕ+) (q : Nat.Primes) :
    RayClass.localHigherUnitGroup
        (RayClass.rationalPrime q)
        (RayClass.rationalFiniteModulus (m : ℕ)
          (RayClass.rationalPrime q)) ≤
      _root_.chosenFinitePlaceLocalNormSubgroup
        (K := ℚ)
        (L := KummerTheory.rationalCyclotomicLevel m)
        (RayClass.rationalPrime q) := by
  intro x hxMod
  rw [← chosenFinitePlaceArtinMonoidHom_ker,
    MonoidHom.mem_ker]
  have hx :
      x ∈ RayClass.localHigherUnitGroup
        (RayClass.rationalPrime q)
        ((m : ℕ).factorization q.1) := by
    simpa only [RayClass.rationalFiniteModulus_apply,
      RayClass.natGenerator_rationalPrime] using hxMod
  let L := KummerTheory.rationalCyclotomicLevel m
  let : IsCyclotomicExtension {(m : ℕ)} ℚ L := by
    simpa only [L] using
      KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension m
  let : FiniteDimensional ℚ L :=
    rationalCyclotomicLevelFiniteDimensional m
  let : IsAbelianGalois ℚ L :=
    rationalCyclotomicLevelIsAbelianGalois m
  let σ : Gal(L / ℚ) :=
    chosenFinitePlaceArtinMonoidHom
      (K := ℚ) (L := L) (RayClass.rationalPrime q) x
  apply
    (IsCyclotomicExtension.Rat.galEquivZMod
      (m : ℕ) L).injective
  apply Units.ext
  let e :=
    ZMod.equivPi (n := (m : ℕ)) m.2.ne'
  apply e.injective
  funext r
  have hrPrime : r.1.Prime :=
    Nat.prime_of_mem_primeFactors r.2
  let p : Nat.Primes := ⟨r.1, hrPrime⟩
  let k := (m : ℕ).factorization p.1
  have hpDvd :
      p.1 ∣ (m : ℕ) :=
    Nat.dvd_of_mem_primeFactors r.2
  have hkNe : k ≠ 0 :=
    (p.2.factorization_pos_of_dvd m.ne_zero hpDvd).ne'
  have hpow : p.1 ^ k ∣ (m : ℕ) :=
    (p.2.pow_dvd_iff_le_factorization m.2.ne').2 le_rfl
  let mp : ℕ+ :=
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩
  let P := KummerTheory.rationalCyclotomicLevel mp
  have hmp : (mp : ℕ) = p.1 ^ k := rfl
  have hAwayDvd (hpq : p ≠ q) : ¬ q.1 ∣ (mp : ℕ) := by
    change ¬ q.1 ∣ p.1 ^ k
    have hqNotDvdP : ¬ q.1 ∣ p.1 := by
      intro hqp
      rcases (Nat.dvd_prime p.2).1 hqp with hqOne | hqpEq
      · exact q.2.ne_one hqOne
      · exact hpq (Subtype.ext hqpEq.symm)
    have hqCoprimeP : Nat.Coprime q.1 p.1 :=
      q.2.coprime_iff_not_dvd.mpr hqNotDvdP
    exact q.2.coprime_iff_not_dvd.mp (hqCoprimeP.pow_right k)
  let : NumberField P :=
    KummerTheory.rationalCyclotomicLevel_numberField mp
  let : IsCyclotomicExtension {p.1 ^ k} ℚ P := by
    rw [← hmp]
    simpa only [P] using
      KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension mp
  let : FiniteDimensional ℚ P :=
    rationalCyclotomicLevelFiniteDimensional mp
  let : IsAbelianGalois ℚ P :=
    rationalCyclotomicLevelIsAbelianGalois mp
  let χ : Gal(P / ℚ) ≃* (ZMod (p.1 ^ k))ˣ :=
    IsCyclotomicExtension.Rat.galEquivZMod
      (p.1 ^ k) P
  have hFL : P ≤ L := by
    simpa only [P] using
      (KummerTheory.rationalCyclotomicLevel_mono
        (m := mp) (n := m) hpow)
  let algFL : Algebra P L :=
    RingHom.toAlgebra
      (IntermediateField.inclusion hFL).toRingHom
  let : SMul P L :=
    @Algebra.toSMul P L _ _ algFL
  let : Algebra P L := algFL
  let : IsScalarTower ℚ P L :=
    IsScalarTower.of_algHom (IntermediateField.inclusion hFL)
  have hrestrict :
      σ.restrictNormal P =
        chosenFinitePlaceArtinMonoidHom
          (K := ℚ)
          (L := KummerTheory.rationalCyclotomicLevel mp)
          (RayClass.rationalPrime q) x := by
    change
      (AlgEquiv.restrictNormalHom
          (KummerTheory.rationalCyclotomicLevel mp))
          (chosenFinitePlaceArtinMonoidHom
            (K := ℚ) (L := L) (RayClass.rationalPrime q) x) =
        chosenFinitePlaceArtinMonoidHom
          (K := ℚ)
          (L := KummerTheory.rationalCyclotomicLevel mp)
          (RayClass.rationalPrime q) x
    exact
      DFunLike.congr_fun
        (chosenFinitePlaceArtinMonoidHom_restrict_tower
          (K := ℚ) (L := L)
          (E := KummerTheory.rationalCyclotomicLevel mp)
          (RayClass.rationalPrime q))
        x
  have hcharacterRestrict :
      χ (σ.restrictNormal P) =
        χ (chosenFinitePlaceArtinMonoidHom
            (K := ℚ)
            (L := KummerTheory.rationalCyclotomicLevel mp)
            (RayClass.rationalPrime q) x) :=
    congrArg χ hrestrict
  have hprojection :
      ZMod.unitsMap hpow
          (IsCyclotomicExtension.Rat.galEquivZMod
            (m : ℕ) L σ) =
        χ (σ.restrictNormal P) :=
    (IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply
      (m : ℕ) L P
      hpow σ).symm
  have hcoordinate :
      ZMod.unitsMap hpow
          (IsCyclotomicExtension.Rat.galEquivZMod
            (m : ℕ) L σ) =
        1 := by
    refine hprojection.trans ?_
    by_cases hpq : p = q
    · subst q
      have hArtinF :
          chosenFinitePlaceArtinMonoidHom
              (K := ℚ)
              (L := KummerTheory.rationalCyclotomicLevel mp)
              (RayClass.rationalPrime p) x = 1 := by
        exact
          rationalPrimePowerChosenFinitePlaceArtin_eq_one_of_mem_localHigherUnitGroup_pos
            p k hkNe mp hmp x hx
      have hArtinCharacter :
          χ (chosenFinitePlaceArtinMonoidHom
                (K := ℚ)
                (L := KummerTheory.rationalCyclotomicLevel mp)
                (RayClass.rationalPrime p) x) = 1 := by
        calc
          χ (chosenFinitePlaceArtinMonoidHom
              (K := ℚ)
              (L := KummerTheory.rationalCyclotomicLevel mp)
              (RayClass.rationalPrime p) x) =
              χ 1 := congrArg χ hArtinF
          _ = 1 := χ.map_one
      exact hcharacterRestrict.trans hArtinCharacter
    · have hzero : rationalCyclotomicArtinLocalExponent q x = 0 :=
        rationalCyclotomicRayNormLocalExponent_eq_zero_of_mem_localHigherUnitGroup
          q ((m : ℕ).factorization q.1) x hx
      have hArtinF :
          chosenFinitePlaceArtinMonoidHom
              (K := ℚ)
              (L := KummerTheory.rationalCyclotomicLevel mp)
              (RayClass.rationalPrime q) x = 1 := by
        exact
          rationalCyclotomicRayNormAwayChosenFinitePlaceArtin_eq_one
            mp q (hAwayDvd hpq) x hzero
      have hArtinCharacter :
          χ (chosenFinitePlaceArtinMonoidHom
                (K := ℚ)
                (L := KummerTheory.rationalCyclotomicLevel mp)
                (RayClass.rationalPrime q) x) = 1 := by
        calc
          χ (chosenFinitePlaceArtinMonoidHom
              (K := ℚ)
              (L := KummerTheory.rationalCyclotomicLevel mp)
              (RayClass.rationalPrime q) x) =
              χ 1 := congrArg χ hArtinF
          _ = 1 := χ.map_one
      exact hcharacterRestrict.trans hArtinCharacter
  have heval (z : ZMod (m : ℕ)) :
      e z r =
        ZMod.castHom hpow (ZMod (p.1 ^ k)) z := by
    change
      ((Pi.evalRingHom
          (fun s : (m : ℕ).primeFactors =>
            ZMod (s.1 ^ (m : ℕ).factorization s.1)) r).comp
        e.toRingHom) z =
          ZMod.castHom hpow (ZMod (p.1 ^ k)) z
    exact RingHom.congr_fun (Subsingleton.elim _ _) z
  rw [map_one, heval, heval]
  simpa only [p, k, ZMod.unitsMap_val,
    ZMod.castHom_apply, map_one, Units.val_one] using
    congrArg
      (fun u : (ZMod (p.1 ^ k))ˣ =>
        (u : ZMod (p.1 ^ k)))
      hcoordinate

end FinitePlaceLocalCalculation

open scoped Classical in
/-- At every finite rational place, the local higher-unit group prescribed
by `(m)` lies in the chosen local norm subgroup of `ℚ(μ_m)`. -/
theorem rationalCyclotomicLevel_rationalModulus_localNorm
    (m : ℕ+)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    RayClass.localHigherUnitGroup v
        (RayClass.rationalFiniteModulus (m : ℕ) v) ≤
      _root_.chosenFinitePlaceLocalNormSubgroup
        (K := ℚ)
        (L := KummerTheory.rationalCyclotomicLevel m) v := by
  let q : Nat.Primes :=
    Rat.HeightOneSpectrum.primesEquiv
      (R := 𝓞 ℚ) v
  have hv :
      RayClass.rationalPrime q = v := by
    change
      (Rat.HeightOneSpectrum.primesEquiv
        (R := 𝓞 ℚ)).symm
          ((Rat.HeightOneSpectrum.primesEquiv
            (R := 𝓞 ℚ)) v) =
        v
    exact
      (Rat.HeightOneSpectrum.primesEquiv
        (R := 𝓞 ℚ)).symm_apply_apply v
  rw [← hv]
  exact
    rationalCyclotomicLevel_localHigherUnitGroup_le_chosenLocalNorm m q

open scoped Classical in
/-- The rational ray congruence subgroup modulo `(m)` is contained in the
genuine idèle-class norm range from the actual cyclotomic level `ℚ(μ_m)`. -/
theorem
    rationalCongruenceSubgroup_le_rationalCyclotomicLevelIdeleClassNormRange
    (m : ℕ) (hm : m ≠ 0) :
    let mp : ℕ+ := ⟨m, Nat.pos_of_ne_zero hm⟩
    RayClass.Modulus.congruenceSubgroup
        (RayClass.rationalModulus m) ≤
      (_root_.ideleClassNorm ℚ
        (KummerTheory.rationalCyclotomicLevel mp)).range := by
  dsimp only
  let mp : ℕ+ := ⟨m, Nat.pos_of_ne_zero hm⟩
  let L := KummerTheory.rationalCyclotomicLevel mp
  have hlocal :
      ∀ v : HeightOneSpectrum (𝓞 ℚ),
        RayClass.localHigherUnitGroup v
            (RayClass.rationalFiniteModulus m v) ≤
          _root_.chosenFinitePlaceLocalNormSubgroup
            (K := ℚ) (L := L) v := by
    intro v
    change
      RayClass.localHigherUnitGroup v
          (RayClass.rationalFiniteModulus (mp : ℕ) v) ≤
        _root_.chosenFinitePlaceLocalNormSubgroup
          (K := ℚ)
          (L := KummerTheory.rationalCyclotomicLevel mp) v
    exact rationalCyclotomicLevel_rationalModulus_localNorm mp v
  have hfinite :
      GlobalClassFields.ideleClassNormDefiningModulus
          (K := ℚ) (L := L) ≤
        RayClass.rationalFiniteModulus m :=
    GlobalClassFields.ideleClassNormDefiningModulus_le_of_localHigherUnitGroup_le
        (K := ℚ) (L := L)
        (RayClass.rationalFiniteModulus m) hlocal
  have hmodulus :
      RayClass.Modulus.narrowOfFinite
          (GlobalClassFields.ideleClassNormDefiningModulus
            (K := ℚ) (L := L)) ≤
        RayClass.rationalModulus m := by
    refine ⟨hfinite, ?_⟩
    change
      (Finset.univ : Finset (RayClass.RealPlace ℚ)) ⊆
        Finset.univ
    exact fun _ h => h
  exact
    (GlobalClassFields.rayClassCongruenceSubgroup_antitone
      (K := ℚ) hmodulus).trans
      (GlobalClassFields.ideleClassNormDefiningModulus_isDefiningModulus
          (K := ℚ) (L := L))

open scoped Classical in
/-- The genuine idèle-class norm range from the actual finite cyclotomic
level is exactly the rational ray congruence subgroup modulo `(m)`. -/
theorem
    rationalCyclotomicLevel_ideleClassNorm_range_eq_rationalCongruenceSubgroup
    (m : ℕ) (hm : m ≠ 0) :
    let mp : ℕ+ := ⟨m, Nat.pos_of_ne_zero hm⟩
    (_root_.ideleClassNorm ℚ
      (KummerTheory.rationalCyclotomicLevel mp)).range =
      RayClass.Modulus.congruenceSubgroup
        (RayClass.rationalModulus m) := by
  dsimp only
  let : NeZero m := ⟨hm⟩
  let mp : ℕ+ := ⟨m, Nat.pos_of_ne_zero hm⟩
  let L := KummerTheory.rationalCyclotomicLevel mp
  let : IsCyclotomicExtension {m} ℚ
      (KummerTheory.rationalCyclotomicLevel
        ⟨m, Nat.pos_of_ne_zero hm⟩) :=
    KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
      ⟨m, Nat.pos_of_ne_zero hm⟩
  let H :=
    RayClass.Modulus.congruenceSubgroup
      (RayClass.rationalModulus m)
  let N :=
    (_root_.ideleClassNorm ℚ L).range
  have hHN : H ≤ N := by
    simpa only [H, N, L, mp] using
      rationalCongruenceSubgroup_le_rationalCyclotomicLevelIdeleClassNormRange
        m hm
  have hindex : H.index = N.index := by
    calc
      H.index =
          Nat.card
            (IdeleClassGroup ℚ ⧸
              RayClass.Modulus.congruenceSubgroup
                (RayClass.rationalModulus m)) := by
        rw [Subgroup.index_eq_card]
      _ = m.totient :=
        KroneckerWeber.rationalRayClassFieldQuotient_card_eq_totient m hm
      _ = Module.finrank ℚ L := by
        simpa only [L, mp] using
          (IsCyclotomicExtension.Rat.finrank m L).symm
      _ = N.index := by
        simpa only [N] using
          (ideleClassNorm_index_eq_finrank_abelian ℚ L).symm
  apply le_antisymm
  · by_contra hNH
    have hne : H ≠ N := by
      intro hEq
      exact hNH hEq.symm.le
    have hstrict : H < N :=
      lt_of_le_of_ne hHN hne
    have hindexStrict :=
      Subgroup.index_strictAnti hstrict
    rw [hindex] at hindexStrict
    exact (Nat.lt_irrefl _ hindexStrict)
  · exact hHN

open scoped Classical in
/-- The standard cyclotomic field `CyclotomicField m ℚ` has the same
actual idèle-class norm range, namely the rational ray congruence subgroup
modulo `(m)`. -/
theorem
    rationalCyclotomicField_ideleClassNorm_range_eq_rationalCongruenceSubgroup
    (m : ℕ) (hm : m ≠ 0) :
    (_root_.ideleClassNorm ℚ
      (CyclotomicField m ℚ)).range =
      RayClass.Modulus.congruenceSubgroup
        (RayClass.rationalModulus m) := by
  let mp : ℕ+ := ⟨m, Nat.pos_of_ne_zero hm⟩
  let L := KummerTheory.rationalCyclotomicLevel mp
  let C := CyclotomicField m ℚ
  let : NeZero m := ⟨hm⟩
  let : IsCyclotomicExtension {m} ℚ
      (KummerTheory.rationalCyclotomicLevel
        ⟨m, Nat.pos_of_ne_zero hm⟩) :=
    KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
      ⟨m, Nat.pos_of_ne_zero hm⟩
  let : IsCyclotomicExtension {m} ℚ C :=
    CyclotomicField.isCyclotomicExtension m ℚ
  let e : L ≃ₐ[ℚ] C :=
    IsCyclotomicExtension.algEquiv {m} ℚ L C
  calc
    (_root_.ideleClassNorm ℚ C).range =
        (_root_.ideleClassNorm ℚ L).range := by
      simpa only [ordinaryIdeleClassNorm_range_eq_relative] using
        (ideleClassNorm_range_algEquiv
          (K := ℚ) e)
    _ =
        RayClass.Modulus.congruenceSubgroup
          (RayClass.rationalModulus m) := by
      simpa only [L, mp] using
        rationalCyclotomicLevel_ideleClassNorm_range_eq_rationalCongruenceSubgroup
          m hm

end Reciprocity
end GlobalClassFieldTheory
