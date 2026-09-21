/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantTensorResidue
import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionInfinityNormalization
import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointLeadingCoefficient

/-!
# Infinity places in an exact constant extension

This file localizes the reciprocal affine normalizations used by the exact
constant-extension model.  A height-one prime of

`S ⊗[C] integralClosure C[X] N`

above the reciprocal origin gives actual places above infinity in both the
extended function field and the original function field.  Their residue
degrees satisfy the usual division-by-gcd formula.
-/

open scoped Polynomial TensorProduct nonZeroDivisors

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier IsDedekindDomain


section ReciprocalFractionField

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]

@[reducible] private noncomputable def canonicalRatFuncPolynomialAlgebra :
    Algebra K[X] (RatFunc K) := inferInstance

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
private theorem canonicalRatFuncPolynomialFractionRing :
    letI := canonicalRatFuncPolynomialAlgebra K
    IsFractionRing K[X] (RatFunc K) := by
  letI := canonicalRatFuncPolynomialAlgebra K
  infer_instance

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
private theorem canonicalRatFuncPolynomialAlgebraMap_injective :
    Function.Injective
      (@algebraMap K[X] (RatFunc K) _ _
        (canonicalRatFuncPolynomialAlgebra K)) := by
  letI := canonicalRatFuncPolynomialAlgebra K
  exact RatFunc.algebraMap_injective K

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
private theorem canonicalRatFunc_div_surjective (z : RatFunc K) :
    ∃ p q : K[X], q ≠ 0 ∧ z =
      @algebraMap K[X] (RatFunc K) _ _
          (canonicalRatFuncPolynomialAlgebra K) p /
        @algebraMap K[X] (RatFunc K) _ _
          (canonicalRatFuncPolynomialAlgebra K) q := by
  letI := canonicalRatFuncPolynomialAlgebra K
  letI : IsFractionRing K[X] (RatFunc K) :=
    canonicalRatFuncPolynomialFractionRing K
  obtain ⟨p, q, hq, h⟩ := IsFractionRing.div_surjective K[X] z
  exact ⟨p, q, nonZeroDivisors.ne_zero hq, h.symm⟩

local instance reciprocalRatFuncPolynomialAlgebra :
    Algebra K[X] (RatFunc K) :=
  ratFuncExtensionReciprocalPolynomialAlgebra K (RatFunc K)

local instance reciprocalRatFuncPolynomialSMul : SMul K[X] (RatFunc K) :=
  Algebra.toSMul

local instance reciprocalRatFuncPolynomialModule : Module K[X] (RatFunc K) :=
  Algebra.toModule

local instance reciprocalRatFuncPolynomialFaithful :
    FaithfulSMul K[X] (RatFunc K) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro p q hpq
  apply reciprocalPolynomialRingHom_injective K
  apply Subtype.ext
  exact hpq

private theorem reciprocalRatFunc_algebraMap_eq_eval (p : K[X]) :
    algebraMap K[X] (RatFunc K) p =
      Polynomial.eval₂ RatFunc.C (1 / RatFunc.X) p := by
  change algebraMap (RatFuncInfinityIntegers K) (RatFunc K)
    (reciprocalPolynomialRingHom K p) = _
  change (((reciprocalPolynomialRingHom K p :
    RatFuncInfinityIntegers K) : RatFunc K)) = _
  rw [reciprocalPolynomialRingHom_coe]

/-- The reciprocal polynomial embedding `K[X] → K(X)`, sending the
polynomial variable to `X⁻¹`, still has `K(X)` as its fraction field. -/
theorem ratFunc_isFractionRing_reciprocalPolynomial :
    IsFractionRing K[X] (RatFunc K) := by
  apply IsFractionRing.of_field K[X] (RatFunc K)
  intro z
  obtain ⟨p, q, hq0, hz⟩ := canonicalRatFunc_div_surjective K z
  let x := p.reverse * Polynomial.X ^ q.natDegree
  let y := q.reverse * Polynomial.X ^ p.natDegree
  refine ⟨x, y, ?_⟩
  rw [reciprocalRatFunc_algebraMap_eq_eval K x,
    reciprocalRatFunc_algebraMap_eq_eval K y]
  dsimp only [x, y]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X]
  have hp := eval_reciprocal_reverse_mul_X_pow K p
  have hq := eval_reciprocal_reverse_mul_X_pow K q
  let can : K[X] →+* RatFunc K :=
    @algebraMap K[X] (RatFunc K) _ _
      (canonicalRatFuncPolynomialAlgebra K)
  have hcanq : can q ≠ 0 := by
    simpa [can] using
      (canonicalRatFuncPolynomialAlgebraMap_injective K).ne hq0
  have hevalq :
      Polynomial.eval₂ RatFunc.C (1 / RatFunc.X) q.reverse ≠ 0 := by
    intro hzero
    apply hcanq
    rw [← hq, hzero, zero_mul]
  calc
    z = can p / can q := hz
    _ = (Polynomial.eval₂ RatFunc.C (1 / RatFunc.X) p.reverse *
          (1 / RatFunc.X) ^ q.natDegree) /
        (Polynomial.eval₂ RatFunc.C (1 / RatFunc.X) q.reverse *
          (1 / RatFunc.X) ^ p.natDegree) := by
      rw [← hp, ← hq]
      field_simp [RatFunc.X_ne_zero, hevalq]
      simp [RatFunc.X_ne_zero]

end ReciprocalFractionField

section LocalizationHelpers

private noncomputable def heightOneResidueFieldRingEquiv
    {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (q : HeightOneSpectrum A) :
    q.asIdeal.ResidueField ≃+*
      (HeightOneSpectrum.equivOfRingEquiv e q).asIdeal.ResidueField :=
  Ideal.residueFieldRingEquiv q.asIdeal
    (HeightOneSpectrum.equivOfRingEquiv e q).asIdeal e
    (by
      change q.asIdeal = (q.asIdeal.comap e.symm).comap e
      exact (Ideal.comap_of_equiv e).symm)

private theorem mappedPrimeCompl_disjoint_of_under_eq
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] (q : Ideal A)
    (hq : q.under R = p) :
    Disjoint
      ((Algebra.algebraMapSubmonoid A p.primeCompl : Submonoid A) : Set A)
      (q : Set A) := by
  rw [Set.disjoint_left]
  intro x hxM hxq
  obtain ⟨r, hr, rfl⟩ := hxM
  exact hr (hq ▸ hxq)

private theorem localizationMap_liesOver_maximalIdeal
    (R V A B : Type*)
    [CommRing R] [CommRing V] [CommRing A] [CommRing B]
    [Algebra R V] [Algebra R A] [Algebra R B]
    [Algebra V B] [Algebra A B]
    [IsScalarTower R V B] [IsScalarTower R A B]
    (p : Ideal R) [p.IsPrime]
    [IsLocalization p.primeCompl V] [IsLocalRing V]
    (q : Ideal A) (hqPrime : q.IsPrime) (hqUnder : q.under R = p)
    [IsLocalization (Algebra.algebraMapSubmonoid A p.primeCompl) B] :
    (Ideal.map (algebraMap A B) q).LiesOver
      (IsLocalRing.maximalIdeal V) := by
  let M := Algebra.algebraMapSubmonoid A p.primeCompl
  have hdisj : Disjoint (M : Set A) (q : Set A) :=
    mappedPrimeCompl_disjoint_of_under_eq R A p q hqUnder
  let Q := Ideal.map (algebraMap A B) q
  have hQA : Q.under A = q :=
    IsLocalization.under_map_of_isPrime_disjoint M B hqPrime hdisj
  rw [Ideal.liesOver_iff]
  apply (IsLocalization.orderEmbedding p.primeCompl V).injective
  calc
    (IsLocalRing.maximalIdeal V).under R = p :=
      IsLocalization.AtPrime.under_maximalIdeal V p
    _ = q.under R := hqUnder.symm
    _ = Q.under R :=
      (congrArg (Ideal.under R) hQA).symm.trans (Ideal.under_under Q)
    _ = (Q.under V).under R := Ideal.under_under Q |>.symm

private noncomputable def localizationResidueFieldAlgEquiv
    (K A B : Type*)
    [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra A B]
    [IsScalarTower K A B]
    (M : Submonoid A) [IsLocalization M B]
    (q : Ideal A) [q.IsPrime]
    (hdisj : Disjoint (M : Set A) (q : Set A)) :
    let Q := Ideal.map (algebraMap A B) q
    letI : Q.IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint M B q inferInstance hdisj
    q.ResidueField ≃ₐ[K] Q.ResidueField := by
  let Q := Ideal.map (algebraMap A B) q
  letI hQPrime : Q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M B q inferInstance hdisj
  have hcomap : q = Q.under A :=
    (IsLocalization.under_map_of_isPrime_disjoint M B inferInstance hdisj).symm
  let f : A →ₐ[K] B := IsScalarTower.toAlgHom K A B
  let rf : q.ResidueField →ₐ[K] Q.ResidueField :=
    Ideal.ResidueField.mapₐ q Q f hcomap
  apply AlgEquiv.ofBijective rf
  exact (RingHom.surjectiveOnStalks_of_isLocalization M B)
    |>.residueFieldMap_bijective q Q hcomap

private noncomputable def localizationResidueFieldRingEquiv
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B]
    (q : Ideal A) [q.IsPrime]
    (hdisj : Disjoint (M : Set A) (q : Set A)) :
    let Q := Ideal.map (algebraMap A B) q
    letI : Q.IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint M B q inferInstance hdisj
    q.ResidueField ≃+* Q.ResidueField := by
  let Q := Ideal.map (algebraMap A B) q
  letI hQPrime : Q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M B q inferInstance hdisj
  have hcomap : q = Q.under A :=
    (IsLocalization.under_map_of_isPrime_disjoint M B inferInstance hdisj).symm
  let f : q.ResidueField →+* Q.ResidueField :=
    Ideal.ResidueField.map q Q (algebraMap A B) hcomap
  apply RingEquiv.ofBijective f
  exact (RingHom.surjectiveOnStalks_of_isLocalization M B)
    |>.residueFieldMap_bijective q Q hcomap

private theorem finrank_eq_of_finite_ringEquiv
    (K E F : Type*) [Field K] [Fintype K]
    [Field E] [Field F] [Algebra K E] [Algebra K F]
    [Finite E] [Finite F] (e : E ≃+* F) :
    Module.finrank K E = Module.finrank K F := by
  letI : Fintype E := Fintype.ofFinite E
  letI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card E = Fintype.card F :=
    Fintype.card_congr e.toEquiv
  rw [Module.card_eq_pow_finrank (K := K) (V := E),
    Module.card_eq_pow_finrank (K := K) (V := F)] at hcard
  exact Nat.pow_right_injective
    (show 2 ≤ Fintype.card K from Fintype.one_lt_card) hcard

private theorem actualInfinityPlaceResidueField_finite
    (K L : Type*) [Field K] [Field L]
    [DecidableEq K] [DecidableEq (RatFunc K)]
    [Fintype K] [Algebra (RatFunc K) L]
    [FiniteDimensional (RatFunc K) L]
    [Algebra.IsSeparable (RatFunc K) L]
    (P : FiniteExtensionInfinityPlace K L) :
    Finite P.1.ResidueField := by
  letI : Algebra K (RatFuncInfinityIntegers K) :=
    (ratFuncInfinityConstantRingHom K).toAlgebra
  letI : IsScalarTower K (RatFuncInfinityIntegers K) (RatFunc K) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
    IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)
  let p := (ratFuncInfinityPlace K).asIdeal
  letI : Finite p.ResidueField :=
    Finite.of_injective (ratFuncInfinityPlaceResidueEquiv K)
      (ratFuncInfinityPlaceResidueEquiv K).injective
  letI : P.1.LiesOver p := by
    simpa [p] using Ideal.primesOver.liesOver
      (ratFuncInfinityPlace K).asIdeal P
  letI := Localization.AtPrime.algebraOfLiesOver p P.1
  let _ : IsScalarTower (RatFuncInfinityIntegers K) (Localization.AtPrime p)
      (Localization.AtPrime P.1) := inferInstance
  letI : Algebra.QuasiFiniteAt (RatFuncInfinityIntegers K) P.1 :=
    inferInstance
  letI : Module.Finite p.ResidueField P.1.ResidueField := inferInstance
  exact Module.finite_of_finite p.ResidueField

end LocalizationHelpers

section TensorReciprocalNormalization

/-- Extending polynomial coefficients carries the reciprocal origin back to
the reciprocal origin. -/
theorem coefficientPolynomial_under_span_X
    (C S : Type*) [Field C] [Field S] [Algebra C S] :
    letI : Algebra C[X] S[X] := Polynomial.algebra C S
    (Ideal.span ({Polynomial.X} : Set S[X])).under C[X] =
      Ideal.span ({Polynomial.X} : Set C[X]) := by
  letI : Algebra C[X] S[X] := Polynomial.algebra C S
  ext p
  change algebraMap C[X] S[X] p ∈
      Ideal.span ({Polynomial.X} : Set S[X]) ↔
    p ∈ Ideal.span ({Polynomial.X} : Set C[X])
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  rw [Polynomial.X_dvd_iff, Polynomial.X_dvd_iff]
  simp

/-- In the polynomial-cancellation model, coefficient extension of a
polynomial acts as the right pure tensor of its old action. -/
theorem polynomialTensorCancel_algebraMap_coefficient
    (C S A : Type*) [Field C] [Field S] [CommRing A]
    [Algebra C S] [Algebra C[X] A]
    [Algebra C A] [IsScalarTower C C[X] A]
    (p : C[X]) :
    letI : Algebra C[X] S[X] := Polynomial.algebra C S
    letI : Algebra S[X] (S ⊗[C] A) :=
      polynomialTensorCancelTargetPolynomialExtensionAlgebra C S A
    algebraMap S[X] (S ⊗[C] A) (algebraMap C[X] S[X] p) =
      (1 : S) ⊗ₜ[C] algebraMap C[X] A p := by
  letI : Algebra C[X] S[X] := Polynomial.algebra C S
  letI : Algebra S[X] (S ⊗[C] A) :=
    polynomialTensorCancelTargetPolynomialExtensionAlgebra C S A
  let e := polynomialTensorCancelOverCoefficientPolynomial C S A
  have hsource :
      (algebraMap C[X] S[X] p) ⊗ₜ[C[X]] (1 : A) =
        (1 : S[X]) ⊗ₜ[C[X]] (algebraMap C[X] A p) :=
    Algebra.TensorProduct.tmul_one_eq_one_tmul p
  calc
    algebraMap S[X] (S ⊗[C] A) (algebraMap C[X] S[X] p) =
        e ((algebraMap C[X] S[X] p) ⊗ₜ[C[X]] (1 : A)) :=
      (e.commutes (algebraMap C[X] S[X] p)).symm
    _ = e ((1 : S[X]) ⊗ₜ[C[X]] (algebraMap C[X] A p)) :=
      congrArg e hsource
    _ = (1 : S) ⊗ₜ[C] algebraMap C[X] A p := by
      rw [polynomialTensorCancelOverCoefficientPolynomial_apply,
        polynomialTensorCancel_tmul]
      simp

variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Fintype C] [Finite S]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance infinityBridgeDecidableEqBase : DecidableEq C := Classical.decEq C
local instance infinityBridgeDecidableEqConstants : DecidableEq S := Classical.decEq S
local instance infinityBridgeDecidableEqRatFuncBase : DecidableEq (RatFunc C) :=
  Classical.decEq (RatFunc C)
local instance infinityBridgeDecidableEqRatFuncConstants : DecidableEq (RatFunc S) :=
  Classical.decEq (RatFunc S)

local instance infinityBridgeBaseConstantAlgebra : Algebra C N :=
  RingHom.toAlgebra ((algebraMap (RatFunc C) N).comp
    (algebraMap C (RatFunc C)))

local instance infinityBridgeBaseReciprocalPolynomialAlgebra : Algebra C[X] N :=
  ratFuncExtensionReciprocalPolynomialAlgebra C N

local instance infinityBridgeBaseConstantPolynomialTower :
    IsScalarTower C C[X] N := by
  exact IsScalarTower.of_algebraMap_eq' (by
    ext c
    change algebraMap (RatFunc C) N (algebraMap C (RatFunc C) c) =
      algebraMap (RatFunc C) N
        (((reciprocalPolynomialRingHom C (Polynomial.C c) :
          RatFuncInfinityIntegers C) : RatFunc C))
    rw [reciprocalPolynomialRingHom_coe]
    simp)

local instance infinityBridgeOldNormalizationConstantAlgebra :
    Algebra C (integralClosure C[X] N) :=
  RingHom.toAlgebra
    ((algebraMap C[X] (integralClosure C[X] N)).comp
      (algebraMap C C[X]))

local instance infinityBridgeOldNormalizationConstantPolynomialTower :
    IsScalarTower C C[X] (integralClosure C[X] N) :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance infinityBridgeTensorPolynomialAlgebra :
    Algebra S[X] (S ⊗[C] integralClosure C[X] N) :=
  polynomialTensorCancelTargetPolynomialExtensionAlgebra C S
    (integralClosure C[X] N)

local instance infinityBridgeTensorConstantAlgebra :
    Algebra S (S ⊗[C] integralClosure C[X] N) :=
  Algebra.TensorProduct.leftAlgebra

local instance infinityBridgeTensorOldNormalizationAlgebra :
    Algebra (integralClosure C[X] N)
      (S ⊗[C] integralClosure C[X] N) :=
  Algebra.TensorProduct.rightAlgebra

/-- Contract a reciprocal tensor-normalization prime to the old reciprocal
normalization. -/
def exactConstantExtensionInfinityDownstairsIdeal
    (q : HeightOneSpectrum (S ⊗[C] integralClosure C[X] N)) :
    Ideal (integralClosure C[X] N) :=
  q.asIdeal.comap
    (Algebra.TensorProduct.includeRight
      (R := C) (A := S) (B := integralClosure C[X] N)).toRingHom

omit [Fintype C] [Finite S]
    [FiniteDimensional (RatFunc C) N] [Algebra.IsSeparable (RatFunc C) N]
    [FiniteDimensional C S] [IsGalois C S] in
@[simp]
theorem exactConstantExtensionInfinityDownstairsIdeal_eq
    (q : HeightOneSpectrum (S ⊗[C] integralClosure C[X] N)) :
    exactConstantExtensionInfinityDownstairsIdeal C S N q =
      q.asIdeal.comap
        (Algebra.TensorProduct.includeRight
          (R := C) (A := S) (B := integralClosure C[X] N)).toRingHom :=
  rfl

omit [Fintype C] [Finite S]
    [FiniteDimensional (RatFunc C) N] [Algebra.IsSeparable (RatFunc C) N]
    [FiniteDimensional C S] [IsGalois C S] in
/-- A tensor-normalization prime above the reciprocal origin contracts to a
prime above the reciprocal origin in the old normalization. -/
theorem exactConstantExtensionInfinityDownstairsIdeal_under
    (q : HeightOneSpectrum (S ⊗[C] integralClosure C[X] N))
    (hqOrigin : q.asIdeal.under S[X] =
      Ideal.span ({Polynomial.X} : Set S[X])) :
    (exactConstantExtensionInfinityDownstairsIdeal C S N q).under C[X] =
      Ideal.span ({Polynomial.X} : Set C[X]) := by
  let p := exactConstantExtensionInfinityDownstairsIdeal C S N q
  let oS := Ideal.span ({Polynomial.X} : Set S[X])
  let oC := Ideal.span ({Polynomial.X} : Set C[X])
  letI : Algebra C[X] S[X] := Polynomial.algebra C S
  ext r
  change
    (1 : S) ⊗ₜ[C]
        algebraMap C[X] (integralClosure C[X] N) r ∈ q.asIdeal ↔
      r ∈ oC
  rw [← polynomialTensorCancel_algebraMap_coefficient C S
    (integralClosure C[X] N) r]
  change algebraMap C[X] S[X] r ∈ q.asIdeal.under S[X] ↔ r ∈ oC
  rw [hqOrigin]
  exact SetLike.ext_iff.mp (coefficientPolynomial_under_span_X C S) r

local instance infinityBridgeBaseInfinityPolynomialAlgebra :
    Algebra C[X] (RatFuncInfinityIntegers C) :=
  ratFuncInfinityReciprocalPolynomialAlgebra C

local instance infinityBridgeBaseInfinityConstantAlgebra :
    Algebra C (RatFuncInfinityIntegers C) :=
  (ratFuncInfinityConstantRingHom C).toAlgebra

local instance infinityBridgeBaseOriginPrime :
    (Ideal.span ({Polynomial.X} : Set C[X])).IsPrime :=
  (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X

local instance infinityBridgeBaseInfinityLocalization :
    IsLocalization
      (Ideal.span ({Polynomial.X} : Set C[X])).primeCompl
      (RatFuncInfinityIntegers C) :=
  ratFuncInfinityIntegers_isLocalization_reciprocal C

local instance infinityBridgeOldNormalizationInfinityAlgebra :
    Algebra (integralClosure C[X] N) (RatFuncInfinityIntegralClosure C N) :=
  ratFuncInfinityReciprocalIntegralClosureAlgebra C N

local instance infinityBridgeOldNormalizationInfinitySMul :
    SMul (integralClosure C[X] N) (RatFuncInfinityIntegralClosure C N) :=
  Algebra.toSMul

local instance infinityBridgeOldNormalizationInfinityLocalization :
    IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure C[X] N)
        (Ideal.span ({Polynomial.X} : Set C[X])).primeCompl)
      (RatFuncInfinityIntegralClosure C N) :=
  ratFuncInfinityIntegralClosure_isLocalization_reciprocal C N

local instance infinityBridgeBasePolynomialInfinityAlgebra :
    Algebra C[X] (RatFuncInfinityIntegralClosure C N) :=
  RingHom.toAlgebra
    ((algebraMap (RatFuncInfinityIntegers C)
      (RatFuncInfinityIntegralClosure C N)).comp
        (algebraMap C[X] (RatFuncInfinityIntegers C)))

local instance infinityBridgeInfinityConstantAlgebra :
    Algebra C (RatFuncInfinityIntegralClosure C N) :=
  RingHom.toAlgebra
    ((algebraMap (RatFuncInfinityIntegers C)
      (RatFuncInfinityIntegralClosure C N)).comp
        (algebraMap C (RatFuncInfinityIntegers C)))

local instance infinityBridgeOldNormalizationInfinityConstantTower :
    IsScalarTower C (integralClosure C[X] N)
      (RatFuncInfinityIntegralClosure C N) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    apply Subtype.ext
    change algebraMap (RatFunc C) N (algebraMap C (RatFunc C) c) =
      algebraMap (RatFunc C) N
        (((reciprocalPolynomialRingHom C (Polynomial.C c) :
          RatFuncInfinityIntegers C) : RatFunc C))
    rw [reciprocalPolynomialRingHom_coe]
    simp

local instance infinityBridgeBasePolynomialInfinityTower :
    IsScalarTower C[X] (RatFuncInfinityIntegers C)
      (RatFuncInfinityIntegralClosure C N) :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance infinityBridgeOldNormalizationInfinityTower :
    IsScalarTower C[X] (integralClosure C[X] N)
      (RatFuncInfinityIntegralClosure C N) :=
  IsScalarTower.of_algebraMap_eq fun p => by
    apply Subtype.ext
    rfl

/-- The contraction of a reciprocal tensor prime, localized at the old
reciprocal origin, is an actual place of `N` above infinity. -/
noncomputable def exactConstantExtensionDownstairsInfinityPlace
    (q : HeightOneSpectrum (S ⊗[C] integralClosure C[X] N))
    (hqOrigin : q.asIdeal.under S[X] =
      Ideal.span ({Polynomial.X} : Set S[X])) :
    FiniteExtensionInfinityPlace C N := by
  let A := integralClosure C[X] N
  let B := RatFuncInfinityIntegralClosure C N
  let o := Ideal.span ({Polynomial.X} : Set C[X])
  let p := exactConstantExtensionInfinityDownstairsIdeal C S N q
  let M := Algebra.algebraMapSubmonoid A o.primeCompl
  have hpPrime : p.IsPrime := by
    exact Ideal.comap_isPrime
      (f := (Algebra.TensorProduct.includeRight
        (R := C) (A := S) (B := integralClosure C[X] N)).toRingHom)
      (K := q.asIdeal)
  have hpUnder : p.under C[X] = o :=
    exactConstantExtensionInfinityDownstairsIdeal_under C S N q hqOrigin
  have hdisj : Disjoint (M : Set A) (p : Set A) := by
    letI : o.IsPrime := infinityBridgeBaseOriginPrime C
    exact mappedPrimeCompl_disjoint_of_under_eq C[X] A o p hpUnder
  let P := Ideal.map (algebraMap A B) p
  letI : p.IsPrime := hpPrime
  letI : P.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M B p hpPrime hdisj
  have hOver : P.LiesOver (ratFuncInfinityPlace C).asIdeal := by
    exact localizationMap_liesOver_maximalIdeal C[X]
      (RatFuncInfinityIntegers C) A B o p hpPrime hpUnder
  exact ⟨P, inferInstance, hOver⟩

omit [Fintype C] [Finite S]
    [FiniteDimensional (RatFunc C) N] [Algebra.IsSeparable (RatFunc C) N]
    [FiniteDimensional C S] [IsGalois C S] in
@[simp]
theorem exactConstantExtensionDownstairsInfinityPlace_asIdeal
    (q : HeightOneSpectrum (S ⊗[C] integralClosure C[X] N))
    (hqOrigin : q.asIdeal.under S[X] =
      Ideal.span ({Polynomial.X} : Set S[X])) :
    (exactConstantExtensionDownstairsInfinityPlace
      C S N q hqOrigin).1 =
      Ideal.map
        (algebraMap (integralClosure C[X] N)
          (RatFuncInfinityIntegralClosure C N))
        (exactConstantExtensionInfinityDownstairsIdeal C S N q) :=
  rfl

/-- Localization at the reciprocal origin does not change the residue field
of the contracted downstairs prime. -/
noncomputable def exactConstantExtensionDownstairsResidueFieldAlgEquiv
    (q : HeightOneSpectrum (S ⊗[C] integralClosure C[X] N))
    (hqOrigin : q.asIdeal.under S[X] =
      Ideal.span ({Polynomial.X} : Set S[X])) :
    let i := (Algebra.TensorProduct.includeRight
      (R := C) (A := S) (B := integralClosure C[X] N)).toRingHom
    let p := exactConstantExtensionInfinityDownstairsIdeal C S N q
    letI : p.IsPrime := Ideal.comap_isPrime (f := i) (K := q.asIdeal)
    p.ResidueField ≃ₐ[C]
      (exactConstantExtensionDownstairsInfinityPlace
        C S N q hqOrigin).1.ResidueField := by
  let A := integralClosure C[X] N
  let B := RatFuncInfinityIntegralClosure C N
  let o := Ideal.span ({Polynomial.X} : Set C[X])
  let p := exactConstantExtensionInfinityDownstairsIdeal C S N q
  let M := Algebra.algebraMapSubmonoid A o.primeCompl
  have hpPrime : p.IsPrime := by
    exact Ideal.comap_isPrime
      (f := (Algebra.TensorProduct.includeRight
        (R := C) (A := S) (B := integralClosure C[X] N)).toRingHom)
      (K := q.asIdeal)
  letI : p.IsPrime := hpPrime
  have hpUnder : p.under C[X] = o :=
    exactConstantExtensionInfinityDownstairsIdeal_under C S N q hqOrigin
  have hdisj : Disjoint (M : Set A) (p : Set A) :=
    mappedPrimeCompl_disjoint_of_under_eq C[X] A o p hpUnder
  let P := Ideal.map (algebraMap A B) p
  letI : P.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M B p hpPrime hdisj
  change p.ResidueField ≃ₐ[C]
    P.ResidueField
  exact localizationResidueFieldAlgEquiv C A B M p hdisj

variable (hExact : algebraicClosure C N =
  (⊥ : IntermediateField C N))

/-- Localizing the corresponding prime in the reciprocal affine
normalization of the exact constant extension produces an actual upstairs
place above infinity. -/
noncomputable def exactConstantExtensionUpstairsInfinityPlace
    (q : HeightOneSpectrum (S ⊗[C] integralClosure C[X] N))
    (hqOrigin : q.asIdeal.under S[X] =
      Ideal.span ({Polynomial.X} : Set S[X])) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    FiniteExtensionInfinityPlace S (ExactConstantExtension C N S) := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  letI : Algebra S[X] (ExactConstantExtension C N S) :=
    ratFuncExtensionReciprocalPolynomialAlgebra S
      (ExactConstantExtension C N S)
  let R := S ⊗[C] integralClosure C[X] N
  let A := integralClosure S[X] (ExactConstantExtension C N S)
  let V := RatFuncInfinityIntegers S
  let B := RatFuncInfinityIntegralClosure S (ExactConstantExtension C N S)
  let o := Ideal.span ({Polynomial.X} : Set S[X])
  let e := exactConstantExtensionInfinityAffineNormalizationAlgEquiv
    C S N hExact
  let qA : HeightOneSpectrum A := heightOneSpectrumEquivOfAlgEquiv e q
  have hqAOrigin : qA.asIdeal.under S[X] = o := by
    calc
      qA.asIdeal.under S[X] = q.asIdeal.under S[X] := by
        ext p
        change e.symm (algebraMap S[X] A p) ∈ q.asIdeal ↔
          algebraMap S[X] R p ∈ q.asIdeal
        rw [e.symm.commutes]
      _ = o := hqOrigin
  letI : Algebra S[X] V := ratFuncInfinityReciprocalPolynomialAlgebra S
  letI : o.IsPrime :=
    (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X
  letI : IsLocalization o.primeCompl V :=
    ratFuncInfinityIntegers_isLocalization_reciprocal S
  letI : Algebra A B :=
    ratFuncInfinityReciprocalIntegralClosureAlgebra S
      (ExactConstantExtension C N S)
  letI : SMul A B := Algebra.toSMul
  letI : IsLocalization (Algebra.algebraMapSubmonoid A o.primeCompl) B :=
    ratFuncInfinityIntegralClosure_isLocalization_reciprocal S
      (ExactConstantExtension C N S)
  letI : Algebra S[X] B :=
    RingHom.toAlgebra
      ((algebraMap V B).comp (algebraMap S[X] V))
  letI : IsScalarTower S[X] V B :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower S[X] A B :=
    IsScalarTower.of_algebraMap_eq fun p => by
      apply Subtype.ext
      rfl
  let M := Algebra.algebraMapSubmonoid A o.primeCompl
  have hdisj : Disjoint (M : Set A) (qA.asIdeal : Set A) :=
    mappedPrimeCompl_disjoint_of_under_eq S[X] A o qA.asIdeal hqAOrigin
  let Q := Ideal.map (algebraMap A B) qA.asIdeal
  letI : Q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M B qA.asIdeal qA.isPrime hdisj
  have hOver : Q.LiesOver (ratFuncInfinityPlace S).asIdeal := by
    exact localizationMap_liesOver_maximalIdeal S[X] V A B o
      qA.asIdeal qA.isPrime hqAOrigin
  exact ⟨Q, inferInstance, hOver⟩

/-- The reciprocal affine prime and the corresponding actual upstairs
infinity place have canonically ring-equivalent residue fields. -/
noncomputable def exactConstantExtensionUpstairsResidueFieldRingEquiv
    (q : HeightOneSpectrum (S ⊗[C] integralClosure C[X] N))
    (hqOrigin : q.asIdeal.under S[X] =
      Ideal.span ({Polynomial.X} : Set S[X])) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    q.asIdeal.ResidueField ≃+*
      (exactConstantExtensionUpstairsInfinityPlace
        C S N hExact q hqOrigin).1.ResidueField := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  letI : Algebra S[X] (ExactConstantExtension C N S) :=
    ratFuncExtensionReciprocalPolynomialAlgebra S
      (ExactConstantExtension C N S)
  let R := S ⊗[C] integralClosure C[X] N
  let A := integralClosure S[X] (ExactConstantExtension C N S)
  let V := RatFuncInfinityIntegers S
  let B := RatFuncInfinityIntegralClosure S (ExactConstantExtension C N S)
  let o := Ideal.span ({Polynomial.X} : Set S[X])
  let e := exactConstantExtensionInfinityAffineNormalizationAlgEquiv
    C S N hExact
  let qA : HeightOneSpectrum A := heightOneSpectrumEquivOfAlgEquiv e q
  have hqAOrigin : qA.asIdeal.under S[X] = o := by
    calc
      qA.asIdeal.under S[X] = q.asIdeal.under S[X] := by
        ext p
        change e.symm (algebraMap S[X] A p) ∈ q.asIdeal ↔
          algebraMap S[X] R p ∈ q.asIdeal
        rw [e.symm.commutes]
      _ = o := hqOrigin
  let affineResidue : q.asIdeal.ResidueField ≃+*
      qA.asIdeal.ResidueField :=
    heightOneResidueFieldRingEquiv e.toRingEquiv q
  letI : Algebra S[X] V := ratFuncInfinityReciprocalPolynomialAlgebra S
  letI : o.IsPrime :=
    (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X
  letI : IsLocalization o.primeCompl V :=
    ratFuncInfinityIntegers_isLocalization_reciprocal S
  letI : Algebra A B :=
    ratFuncInfinityReciprocalIntegralClosureAlgebra S
      (ExactConstantExtension C N S)
  letI : SMul A B := Algebra.toSMul
  letI : IsLocalization (Algebra.algebraMapSubmonoid A o.primeCompl) B :=
    ratFuncInfinityIntegralClosure_isLocalization_reciprocal S
      (ExactConstantExtension C N S)
  letI : Algebra S[X] B :=
    RingHom.toAlgebra ((algebraMap V B).comp (algebraMap S[X] V))
  letI : IsScalarTower S[X] V B :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower S[X] A B :=
    IsScalarTower.of_algebraMap_eq fun p => by
      apply Subtype.ext
      rfl
  let M := Algebra.algebraMapSubmonoid A o.primeCompl
  have hdisj : Disjoint (M : Set A) (qA.asIdeal : Set A) :=
    mappedPrimeCompl_disjoint_of_under_eq S[X] A o qA.asIdeal hqAOrigin
  let Q := Ideal.map (algebraMap A B) qA.asIdeal
  letI : Q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M B qA.asIdeal qA.isPrime hdisj
  let localResidue : qA.asIdeal.ResidueField ≃+* Q.ResidueField :=
    localizationResidueFieldRingEquiv A B M qA.asIdeal hdisj
  change q.asIdeal.ResidueField ≃+* Q.ResidueField
  exact affineResidue.trans localResidue

/-- The residue field of the actual upstairs infinity place is finite. -/
theorem exactConstantExtensionUpstairsInfinityResidueField_finite
    (q : HeightOneSpectrum (S ⊗[C] integralClosure C[X] N))
    (hqOrigin : q.asIdeal.under S[X] =
      Ideal.span ({Polynomial.X} : Set S[X])) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    Finite (exactConstantExtensionUpstairsInfinityPlace
      C S N hExact q hqOrigin).1.ResidueField := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  letI : SMul (RatFunc S) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  letI : Module (RatFunc S) (ExactConstantExtension C N S) :=
    Algebra.toModule
  letI : FiniteDimensional (RatFunc S) (ExactConstantExtension C N S) :=
    finiteDimensional_over_extendedRatFunc C S N hExact
  letI : Algebra.IsSeparable (RatFunc S) (ExactConstantExtension C N S) :=
    isSeparable_over_extendedRatFunc C S N hExact
  letI : Fintype S := Fintype.ofFinite S
  exact actualInfinityPlaceResidueField_finite S
    (ExactConstantExtension C N S)
    (exactConstantExtensionUpstairsInfinityPlace
      C S N hExact q hqOrigin)

include hExact

/-- The residue field of the reciprocal tensor-normalization prime is finite. -/
theorem exactConstantExtensionInfinityTensorResidueField_finite
    (q : HeightOneSpectrum (S ⊗[C] integralClosure C[X] N))
    (hqOrigin : q.asIdeal.under S[X] =
      Ideal.span ({Polynomial.X} : Set S[X])) :
    Finite q.asIdeal.ResidueField := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  letI : Finite
      (exactConstantExtensionUpstairsInfinityPlace
        C S N hExact q hqOrigin).1.ResidueField :=
    exactConstantExtensionUpstairsInfinityResidueField_finite
      C S N hExact q hqOrigin
  let e := exactConstantExtensionUpstairsResidueFieldRingEquiv
    C S N hExact q hqOrigin
  exact Finite.of_injective e e.injective

/-- A reciprocal tensor-normalization height-one prime above the origin is
maximal; no maximality hypothesis is left to the residue calculation. -/
theorem exactConstantExtensionInfinityTensorIdeal_isMaximal
    (q : HeightOneSpectrum (S ⊗[C] integralClosure C[X] N))
    (hqOrigin : q.asIdeal.under S[X] =
      Ideal.span ({Polynomial.X} : Set S[X])) :
    q.asIdeal.IsMaximal := by
  letI : Finite q.asIdeal.ResidueField :=
    exactConstantExtensionInfinityTensorResidueField_finite
      C S N hExact q hqOrigin
  letI : Finite
      (HasQuotient.Quotient
        (S ⊗[C] integralClosure C[X] N) q.asIdeal) :=
    Finite.of_injective
      (algebraMap
        (HasQuotient.Quotient
          (S ⊗[C] integralClosure C[X] N) q.asIdeal)
        q.asIdeal.ResidueField)
      q.asIdeal.injective_algebraMap_quotient_residueField
  exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient q.asIdeal).mpr
    (Finite.isField_of_domain
      (HasQuotient.Quotient
        (S ⊗[C] integralClosure C[X] N) q.asIdeal))

omit [Finite S] [FiniteDimensional C S] [IsGalois C S] hExact in
/-- The residue field of the contracted downstairs reciprocal prime is finite. -/
theorem exactConstantExtensionInfinityDownstairsResidueField_finite
    (q : HeightOneSpectrum (S ⊗[C] integralClosure C[X] N))
    (hqOrigin : q.asIdeal.under S[X] =
      Ideal.span ({Polynomial.X} : Set S[X])) :
    let p := exactConstantExtensionInfinityDownstairsIdeal C S N q
    let i := (Algebra.TensorProduct.includeRight
      (R := C) (A := S) (B := integralClosure C[X] N)).toRingHom
    letI : p.IsPrime := Ideal.comap_isPrime (f := i) (K := q.asIdeal)
    Finite p.ResidueField := by
  let p := exactConstantExtensionInfinityDownstairsIdeal C S N q
  let i := (Algebra.TensorProduct.includeRight
    (R := C) (A := S) (B := integralClosure C[X] N)).toRingHom
  letI : p.IsPrime := Ideal.comap_isPrime (f := i) (K := q.asIdeal)
  let P := exactConstantExtensionDownstairsInfinityPlace C S N q hqOrigin
  letI : Finite P.1.ResidueField :=
    actualInfinityPlaceResidueField_finite C N P
  let e := exactConstantExtensionDownstairsResidueFieldAlgEquiv
    C S N q hqOrigin
  exact Finite.of_injective e e.injective

omit [Field C] [Field N] [Fintype C]
    [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
    [Algebra.IsSeparable (RatFunc C) N] hExact in
private theorem constantTensorResidue_finrank_over_constants_eq_div_gcd
    (C R S : Type*)
    [Field C] [CommRing R] [Field S]
    [Algebra C R] [Algebra C S]
    [Finite C] [Finite S]
    (q : Ideal (S ⊗[C] R)) [q.IsMaximal]
    [Finite ((q.comap (Algebra.TensorProduct.includeRight
      (R := C) (A := S) (B := R)).toRingHom).ResidueField)]
    [Finite q.ResidueField] :
    let p := q.comap (Algebra.TensorProduct.includeRight
      (R := C) (A := S) (B := R)).toRingHom
    Module.finrank S q.ResidueField =
      Module.finrank C p.ResidueField /
        Nat.gcd (Module.finrank C S)
          (Module.finrank C p.ResidueField) := by
  let p := q.comap (Algebra.TensorProduct.includeRight
    (R := C) (A := S) (B := R)).toRingHom
  let m := Module.finrank C S
  let n := Module.finrank C p.ResidueField
  let d := Nat.gcd m n
  let l := Nat.lcm m n
  let r := Module.finrank S q.ResidueField
  have htotal : Module.finrank C q.ResidueField = l :=
    constantTensorResidue_finrank_eq_lcm C R S q
  have hmr : m * r = l := by
    exact (Module.finrank_mul_finrank C S q.ResidueField).trans htotal
  have hdr : d * r = n := by
    apply Nat.mul_left_cancel
      (Module.finrank_pos (R := C) (M := S))
    calc
      m * (d * r) = d * (m * r) := by ac_rfl
      _ = d * l := by rw [hmr]
      _ = m * n := Nat.gcd_mul_lcm m n
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left n
    (Module.finrank_pos (R := C) (M := S))
  change r = n / d
  symm
  apply Nat.div_eq_of_eq_mul_left hdpos
  simpa [mul_comm] using hdr.symm

/-- Exact extension of constants changes the degree of an actual infinity
place by the standard division-by-gcd formula. -/
theorem exactConstantExtensionInfinityPlace_degree_eq_div_gcd
    (q : HeightOneSpectrum (S ⊗[C] integralClosure C[X] N))
    (hqOrigin : q.asIdeal.under S[X] =
      Ideal.span ({Polynomial.X} : Set S[X])) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    finiteExtensionPlaceDegree S (ExactConstantExtension C N S)
        (.inr (exactConstantExtensionUpstairsInfinityPlace
          C S N hExact q hqOrigin)) =
      finiteExtensionPlaceDegree C N
          (.inr (exactConstantExtensionDownstairsInfinityPlace
            C S N q hqOrigin)) /
        Nat.gcd (Module.finrank C S)
          (finiteExtensionPlaceDegree C N
            (.inr (exactConstantExtensionDownstairsInfinityPlace
              C S N q hqOrigin))) := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  letI : SMul (RatFunc S) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  letI : Module (RatFunc S) (ExactConstantExtension C N S) :=
    Algebra.toModule
  letI : FiniteDimensional (RatFunc S) (ExactConstantExtension C N S) :=
    finiteDimensional_over_extendedRatFunc C S N hExact
  letI : Algebra.IsSeparable (RatFunc S) (ExactConstantExtension C N S) :=
    isSeparable_over_extendedRatFunc C S N hExact
  letI : Fintype S := Fintype.ofFinite S
  let p := exactConstantExtensionInfinityDownstairsIdeal C S N q
  let i := (Algebra.TensorProduct.includeRight
    (R := C) (A := S) (B := integralClosure C[X] N)).toRingHom
  letI : p.IsPrime := Ideal.comap_isPrime (f := i) (K := q.asIdeal)
  letI : Finite p.ResidueField :=
    exactConstantExtensionInfinityDownstairsResidueField_finite
      C S N q hqOrigin
  letI : Finite
      (q.asIdeal.comap (Algebra.TensorProduct.includeRight
        (R := C) (A := S) (B := integralClosure C[X] N)).toRingHom).ResidueField := by
    change Finite p.ResidueField
    infer_instance
  letI : Finite q.asIdeal.ResidueField :=
    exactConstantExtensionInfinityTensorResidueField_finite
      C S N hExact q hqOrigin
  letI : q.asIdeal.IsMaximal :=
    exactConstantExtensionInfinityTensorIdeal_isMaximal
      C S N hExact q hqOrigin
  let Q := exactConstantExtensionUpstairsInfinityPlace
    C S N hExact q hqOrigin
  let P := exactConstantExtensionDownstairsInfinityPlace
    C S N q hqOrigin
  letI : Finite Q.1.ResidueField :=
    exactConstantExtensionUpstairsInfinityResidueField_finite
      C S N hExact q hqOrigin
  letI : Finite P.1.ResidueField :=
    actualInfinityPlaceResidueField_finite C N P
  have hUp : Module.finrank S q.asIdeal.ResidueField =
      Module.finrank S Q.1.ResidueField :=
    finrank_eq_of_finite_ringEquiv S q.asIdeal.ResidueField
      Q.1.ResidueField
      (exactConstantExtensionUpstairsResidueFieldRingEquiv
        C S N hExact q hqOrigin)
  have hDown : Module.finrank C p.ResidueField =
      Module.finrank C P.1.ResidueField :=
    (exactConstantExtensionDownstairsResidueFieldAlgEquiv
      C S N q hqOrigin).toLinearEquiv.finrank_eq
  rw [finiteExtensionInfinityPlace_degree_eq_finrank_residueField S
      (ExactConstantExtension C N S) Q,
    finiteExtensionInfinityPlace_degree_eq_finrank_residueField C N P]
  calc
    Module.finrank S Q.1.ResidueField =
        Module.finrank S q.asIdeal.ResidueField := hUp.symm
    _ = Module.finrank C p.ResidueField /
          Nat.gcd (Module.finrank C S)
            (Module.finrank C p.ResidueField) :=
      constantTensorResidue_finrank_over_constants_eq_div_gcd
        C (integralClosure C[X] N) S q.asIdeal
    _ = Module.finrank C P.1.ResidueField /
          Nat.gcd (Module.finrank C S)
            (Module.finrank C P.1.ResidueField) := by rw [hDown]

/-- If the downstairs infinity-place degree divides the extension degree of
the constants, the corresponding upstairs infinity place has degree one. -/
theorem exactConstantExtensionInfinityPlace_degree_eq_one_of_dvd
    (q : HeightOneSpectrum (S ⊗[C] integralClosure C[X] N))
    (hqOrigin : q.asIdeal.under S[X] =
      Ideal.span ({Polynomial.X} : Set S[X]))
    (hdiv : finiteExtensionPlaceDegree C N
        (.inr (exactConstantExtensionDownstairsInfinityPlace
          C S N q hqOrigin)) ∣ Module.finrank C S) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    finiteExtensionPlaceDegree S (ExactConstantExtension C N S)
      (.inr (exactConstantExtensionUpstairsInfinityPlace
        C S N hExact q hqOrigin)) = 1 := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  rw [exactConstantExtensionInfinityPlace_degree_eq_div_gcd
    C S N hExact q hqOrigin]
  rw [Nat.gcd_eq_right_iff_dvd.mpr hdiv]
  let P := exactConstantExtensionDownstairsInfinityPlace
    C S N q hqOrigin
  letI : Finite P.1.ResidueField :=
    actualInfinityPlaceResidueField_finite C N P
  let _ : DistribMulAction (RatFuncInfinityIntegralClosure C N)
      (RatFuncInfinityIntegralClosure C N) :=
    (Algebra.toModule : Module (RatFuncInfinityIntegralClosure C N)
      (RatFuncInfinityIntegralClosure C N)).toDistribMulAction
  apply Nat.div_self
  rw [finiteExtensionInfinityPlace_degree_eq_finrank_residueField C N P]
  exact Module.finrank_pos

end TensorReciprocalNormalization

end


end BGS.HasseWeil
