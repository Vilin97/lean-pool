/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.RatFuncInfinityLocalization
import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantFieldInfinityBase
import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteFieldPolynomialDifferent
import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.Algebra.Polynomial.GroupRingAction
import Mathlib.FieldTheory.Galois.Basic

/-!
# The different of a finite coefficient extension at infinity

For a finite Galois extension `S / C`, the infinity valuation ring over `S`
is the localization of the reciprocal polynomial ring `S[X]` at the image of
the reciprocal-origin complement from `C[X]`.  The key denominator argument
uses the product of all Galois conjugates of a polynomial.

This localization description transports finiteness and formal
unramifiedness from `C[X] → S[X]`.  Consequently the local different of the
coefficient extension at infinity is the unit ideal.
-/

open scoped Polynomial TensorProduct nonZeroDivisors

namespace BGS.HasseWeil

open BGS.CorvajaZannier

noncomputable section

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

variable (C S : Type*) [Field C] [Field S]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance finiteFieldInfinityDifferentDecidableEqC : DecidableEq C :=
  Classical.decEq C
local instance finiteFieldInfinityDifferentDecidableEqS : DecidableEq S :=
  Classical.decEq S
local instance finiteFieldInfinityDifferentDecidableEqRatFuncC :
    DecidableEq (RatFunc C) := Classical.decEq (RatFunc C)
local instance finiteFieldInfinityDifferentDecidableEqRatFuncS :
    DecidableEq (RatFunc S) := Classical.decEq (RatFunc S)

local instance finiteFieldInfinityDifferentCoefficientPolynomialAlgebra :
    Algebra C[X] S[X] :=
  Polynomial.algebra C S

local instance finiteFieldInfinityDifferentReciprocalPolynomialAlgebra :
    Algebra S[X] (RatFuncInfinityIntegers S) :=
  ratFuncInfinityReciprocalPolynomialAlgebra S

local instance finiteFieldInfinityDifferentCoefficientOriginPrime :
    (Ideal.span ({Polynomial.X} : Set C[X])).IsPrime :=
  (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X

local instance finiteFieldInfinityDifferentExtensionOriginPrime :
    (Ideal.span ({Polynomial.X} : Set S[X])).IsPrime :=
  (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X

omit [FiniteDimensional C S] [IsGalois C S] in
private theorem coefficientPrimeCompl_le_reciprocalPrimeCompl :
    Algebra.algebraMapSubmonoid S[X]
        (Ideal.span ({Polynomial.X} : Set C[X])).primeCompl ≤
      (Ideal.span ({Polynomial.X} : Set S[X])).primeCompl := by
  rintro _ ⟨p, hp, rfl⟩
  intro hmap
  change p ∉ Ideal.span ({Polynomial.X} : Set C[X]) at hp
  apply hp
  rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff]
  apply (algebraMap C S).injective
  have hzero :
      (algebraMap C[X] S[X] p).coeff 0 = 0 :=
    Polynomial.X_dvd_iff.mp (Ideal.mem_span_singleton.mp hmap)
  simpa [Polynomial.algebraMap_def] using hzero

private theorem exists_coefficient_multiple_of_not_mem_reciprocalOrigin
    (p : S[X])
    (hp : p ∉ Ideal.span ({Polynomial.X} : Set S[X])) :
    ∃ m : C[X],
      m ∉ Ideal.span ({Polynomial.X} : Set C[X]) ∧
        p ∣ algebraMap C[X] S[X] m := by
  let G := S ≃ₐ[C] S
  let P : S[X] := ∏ g : G, g • p
  have hp0 : p.coeff 0 ≠ 0 := by
    intro hp0
    apply hp
    rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff]
    exact hp0
  have hPfixed (g : G) : g • P = P := by
    exact Finset.smul_prod_perm p g
  have hcoeffRange (n : ℕ) :
      P.coeff n ∈ Set.range (algebraMap C S) := by
    rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro g
    have hcoeffFixed :=
      congrArg (fun q : S[X] => q.coeff n) (hPfixed g)
    simp only [Polynomial.smul_eq_map, Polynomial.coeff_map] at hcoeffFixed
    change g • P.coeff n = P.coeff n at hcoeffFixed
    calc
      g (P.coeff n) = g • P.coeff n :=
        (AlgEquiv.smul_def g (P.coeff n)).symm
      _ = P.coeff n := hcoeffFixed
  have hPrange :
      P ∈ (Polynomial.mapRingHom (algebraMap C S)).range := by
    rw [Polynomial.mem_map_range]
    exact hcoeffRange
  obtain ⟨m, hm⟩ := hPrange
  have hp_dvd_P : p ∣ P := by
    have h := Finset.dvd_prod_of_mem (fun g : G => g • p)
      (Finset.mem_univ (1 : G))
    change p ∣ ∏ g : G, g • p
    simpa using h
  have hP0 : P.coeff 0 ≠ 0 := by
    change (∏ g : G, g • p).coeff 0 ≠ 0
    rw [Polynomial.coeff_zero_prod]
    exact Finset.prod_ne_zero_iff.mpr fun g _ => by
      rw [show (g • p).coeff 0 = g • p.coeff 0 by
        simp [Polynomial.smul_eq_map]]
      exact (smul_ne_zero_iff_ne g).2 hp0
  have hm0map : algebraMap C S (m.coeff 0) = P.coeff 0 := by
    have := congrArg (fun q : S[X] => q.coeff 0) hm
    simpa using this
  have hm0 : m.coeff 0 ≠ 0 := by
    intro hm0
    apply hP0
    rw [← hm0map, hm0, map_zero]
  refine ⟨m, ?_, ?_⟩
  · intro hmOrigin
    exact hm0 (Polynomial.X_dvd_iff.mp
      (Ideal.mem_span_singleton.mp hmOrigin))
  · change p ∣ Polynomial.map (algebraMap C S) m
    have hm' : Polynomial.map (algebraMap C S) m = P := hm
    rw [hm']
    exact hp_dvd_P

/-- The infinity valuation ring over `S` is already obtained by localizing
`S[X]` at the image of the reciprocal-origin complement from `C[X]`. -/
theorem ratFuncInfinityIntegers_isLocalization_coefficientPrimeCompl :
    IsLocalization
      (Algebra.algebraMapSubmonoid S[X]
        (Ideal.span ({Polynomial.X} : Set C[X])).primeCompl)
      (RatFuncInfinityIntegers S) := by
  let M := Algebra.algebraMapSubmonoid S[X]
    (Ideal.span ({Polynomial.X} : Set C[X])).primeCompl
  let N := (Ideal.span ({Polynomial.X} : Set S[X])).primeCompl
  have hMN : M ≤ N :=
    coefficientPrimeCompl_le_reciprocalPrimeCompl C S
  have hdiv : ∀ p ∈ N, ∃ m ∈ M, p ∣ m := by
    intro p hp
    obtain ⟨m, hmOrigin, hp_dvd⟩ :=
      exists_coefficient_multiple_of_not_mem_reciprocalOrigin C S p hp
    exact ⟨algebraMap C[X] S[X] m, ⟨m, hmOrigin, rfl⟩, hp_dvd⟩
  exact (IsLocalization.iff_of_le_of_exists_dvd
    (M := M) N hMN hdiv).mpr
      (ratFuncInfinityIntegers_isLocalization_reciprocal S)

section Corollaries

local instance finiteFieldInfinityDifferentBaseReciprocalPolynomialAlgebra :
    Algebra C[X] (RatFuncInfinityIntegers C) :=
  ratFuncInfinityReciprocalPolynomialAlgebra C

local instance finiteFieldInfinityDifferentCoefficientAlgebra :
    Algebra (RatFuncInfinityIntegers C) (RatFuncInfinityIntegers S) :=
  RingHom.toAlgebra (ratFuncInfinityIntegersRingHom C S)

local instance (priority := low)
    finiteFieldInfinityDifferentBasePolynomialExtensionAlgebra :
    Algebra C[X] (RatFuncInfinityIntegers S) :=
  RingHom.toAlgebra
    ((algebraMap S[X] (RatFuncInfinityIntegers S)).comp
      (algebraMap C[X] S[X]))

local instance finiteFieldInfinityDifferentCoefficientPolynomialTower :
    IsScalarTower C[X] S[X] (RatFuncInfinityIntegers S) :=
  IsScalarTower.of_algebraMap_eq'
    (RingHom.algebraMap_toAlgebra _)

omit [FiniteDimensional C S] [IsGalois C S] in
private theorem ratFuncCoefficientAlgHom_reciprocalPolynomialRingHom
    (p : C[X]) :
    ratFuncCoefficientAlgHom C S
        (((reciprocalPolynomialRingHom C p :
          RatFuncInfinityIntegers C) : RatFunc C)) =
      ((reciprocalPolynomialRingHom S (algebraMap C[X] S[X] p) :
          RatFuncInfinityIntegers S) : RatFunc S) := by
  rw [reciprocalPolynomialRingHom_coe,
    reciprocalPolynomialRingHom_coe]
  change (ratFuncCoefficientAlgHom C S).toRingHom
      (Polynomial.eval₂ RatFunc.C (1 / RatFunc.X) p) = _
  rw [Polynomial.hom_eval₂]
  have hX : ratFuncCoefficientAlgHom C S RatFunc.X = RatFunc.X := by
    have h := ratFuncCoefficientAlgHom_algebraMap C S Polynomial.X
    simpa using h
  have hcoeff :
      (ratFuncCoefficientAlgHom C S).toRingHom.comp RatFunc.C =
        RatFunc.C.comp (algebraMap C S) := by
    ext c
    change ratFuncCoefficientAlgHom C S
        (algebraMap C (RatFunc C) c) =
      algebraMap S (RatFunc S) (algebraMap C S c)
    rw [(ratFuncCoefficientAlgHom C S).commutes]
    exact IsScalarTower.algebraMap_apply C S (RatFunc S) c
  have hrecip : (ratFuncCoefficientAlgHom C S).toRingHom
      (1 / RatFunc.X) = 1 / RatFunc.X := by
    rw [one_div, map_inv₀]
    have hX' : (ratFuncCoefficientAlgHom C S).toRingHom RatFunc.X =
        RatFunc.X := hX
    simpa [hX']
  rw [hcoeff, hrecip]
  change Polynomial.eval₂ (RatFunc.C.comp (algebraMap C S))
      (1 / RatFunc.X) p =
    Polynomial.eval₂ RatFunc.C (1 / RatFunc.X)
      (Polynomial.map (algebraMap C S) p)
  rw [Polynomial.eval₂_map]

omit [FiniteDimensional C S] [IsGalois C S] in
private theorem reciprocalPolynomialAlgebraMap_commutes (p : C[X]) :
    algebraMap (RatFuncInfinityIntegers C) (RatFuncInfinityIntegers S)
        (algebraMap C[X] (RatFuncInfinityIntegers C) p) =
      algebraMap C[X] (RatFuncInfinityIntegers S) p := by
  simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
  apply Subtype.ext
  exact ratFuncCoefficientAlgHom_reciprocalPolynomialRingHom C S p

local instance finiteFieldInfinityDifferentBasePolynomialCoefficientTower :
    IsScalarTower C[X] (RatFuncInfinityIntegers C)
      (RatFuncInfinityIntegers S) :=
  IsScalarTower.of_algebraMap_eq fun p =>
    (reciprocalPolynomialAlgebraMap_commutes C S p).symm

local instance finiteFieldInfinityDifferentCoefficientPolynomialModuleFinite :
    Module.Finite C[X] S[X] := by
  letI : Module.Finite C[X] (C[X] ⊗[C] S) :=
    Module.Finite.base_change C C[X] S
  exact Module.Finite.equiv
    (Algebra.IsPushout.equiv C C[X] S S[X]).toLinearEquiv

/-- The coefficient extension of infinity valuation rings is finite. -/
theorem ratFuncInfinityIntegers_coefficient_moduleFinite :
    Module.Finite (RatFuncInfinityIntegers C)
      (RatFuncInfinityIntegers S) := by
  letI : IsLocalization
      (Ideal.span ({Polynomial.X} : Set C[X])).primeCompl
      (RatFuncInfinityIntegers C) :=
    ratFuncInfinityIntegers_isLocalization_reciprocal C
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid S[X]
        (Ideal.span ({Polynomial.X} : Set C[X])).primeCompl)
      (RatFuncInfinityIntegers S) :=
    ratFuncInfinityIntegers_isLocalization_coefficientPrimeCompl C S
  exact Module.Finite.of_isLocalization C[X] S[X]
    (Ideal.span ({Polynomial.X} : Set C[X])).primeCompl

local instance finiteFieldInfinityDifferentCoefficientModuleFinite :
    Module.Finite (RatFuncInfinityIntegers C)
      (RatFuncInfinityIntegers S) :=
  ratFuncInfinityIntegers_coefficient_moduleFinite C S

local instance finiteFieldInfinityDifferentCoefficientIsTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers C)
      (RatFuncInfinityIntegers S) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  exact ratFuncInfinityIntegersRingHom_injective C S

/-- The coefficient extension of infinity valuation rings is formally
unramified. -/
theorem ratFuncInfinityIntegers_coefficient_formallyUnramified :
    Algebra.FormallyUnramified (RatFuncInfinityIntegers C)
      (RatFuncInfinityIntegers S) := by
  letI : IsLocalization
      (Ideal.span ({Polynomial.X} : Set C[X])).primeCompl
      (RatFuncInfinityIntegers C) :=
    ratFuncInfinityIntegers_isLocalization_reciprocal C
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid S[X]
        (Ideal.span ({Polynomial.X} : Set C[X])).primeCompl)
      (RatFuncInfinityIntegers S) :=
    ratFuncInfinityIntegers_isLocalization_coefficientPrimeCompl C S
  letI : IsLocalization
      (Submonoid.map (algebraMap C[X] S[X])
        (Ideal.span ({Polynomial.X} : Set C[X])).primeCompl)
      (RatFuncInfinityIntegers S) := by
    simpa only [Algebra.algebraMapSubmonoid] using
      ratFuncInfinityIntegers_isLocalization_coefficientPrimeCompl C S
  letI : Algebra.FormallyUnramified C[X] S[X] :=
    coefficientPolynomial_formallyUnramified C S
  exact Algebra.FormallyUnramified.localization_map
    (R := C[X]) (S := S[X])
    (Rₘ := RatFuncInfinityIntegers C)
    (Sₘ := RatFuncInfinityIntegers S)
    (Ideal.span ({Polynomial.X} : Set C[X])).primeCompl

/-- A finite Galois coefficient extension has unit different at the infinity
valuation ring. -/
theorem ratFuncInfinityIntegers_coefficient_differentIdeal_eq_top :
    differentIdeal (RatFuncInfinityIntegers C)
      (RatFuncInfinityIntegers S) = ⊤ := by
  let A := RatFuncInfinityIntegers C
  let B := RatFuncInfinityIntegers S
  letI : Algebra.FormallyUnramified A B :=
    ratFuncInfinityIntegers_coefficient_formallyUnramified C S
  letI : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed B A (FractionRing B)
  letI : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) :=
    isAlgebraic_of_isFractionRing A B ..
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization A (FractionRing A)
      (FractionRing B) B
  letI : FiniteDimensional (FractionRing A) (FractionRing B) :=
    Module.Finite.of_isLocalization A B A⁰
  letI : Algebra.FormallyUnramified B (FractionRing B) :=
    Algebra.FormallyUnramified.of_isLocalization B⁰
  letI : Algebra.FormallyUnramified A (FractionRing B) :=
    Algebra.FormallyUnramified.comp A B (FractionRing B)
  letI : Algebra.FormallyUnramified (FractionRing A) (FractionRing B) :=
    Algebra.FormallyUnramified.localization_base A⁰
  letI : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    Algebra.FormallyUnramified.isSeparable
      (FractionRing A) (FractionRing B)
  by_contra htop
  obtain ⟨P, hPmax, hdiffP⟩ :=
    Ideal.exists_le_maximal (differentIdeal A B) htop
  letI : P.IsPrime := hPmax.isPrime
  have hunram : Algebra.IsUnramifiedAt A P := by
    exact Algebra.formallyUnramified_iff_forall.mp
      (show Algebra.FormallyUnramified A B from inferInstance)
      ⟨P, hPmax.isPrime⟩
  exact (not_dvd_differentIdeal_iff.mpr hunram)
    (Ideal.dvd_iff_le.mpr hdiffP)

end Corollaries

end

end BGS.HasseWeil
