/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import Mathlib.RingTheory.Localization.AtPrime.Extension
public import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantExtensionInfinityPlaceBridge
public import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantExtensionPlaceSplittingMultiplicity

/-!
# Splitting multiplicity at infinity in an exact extension of constants

This file identifies the reciprocal-normalization presentation of the places
at infinity with the actual places over the original constant field.  It then
proves that an exact extension of constants is unramified at those places.

The comparison is noncircular: reciprocal affine normalizations are first
compared over `C[X]`, and only then localized to the valuation ring at
infinity.
-/

@[expose] public section

open scoped Polynomial TensorProduct nonZeroDivisors

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier IsDedekindDomain


variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Fintype C] [Finite S]
  [DecidableEq C] [DecidableEq S]
  [DecidableEq (RatFunc C)] [DecidableEq (RatFunc S)]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance (priority := 10000) infinitySplittingDecidableEqBase :
    DecidableEq C := infinityBridgeDecidableEqConstants C

local instance (priority := 10000) infinitySplittingDecidableEqRatFuncBase :
    DecidableEq (RatFunc C) := infinityBridgeDecidableEqRatFuncConstants C

local instance (priority := 10000) infinitySplittingDecidableEqConstants :
    DecidableEq S := infinityBridgeDecidableEqConstants S

local instance (priority := 10000) infinitySplittingDecidableEqRatFuncConstants :
    DecidableEq (RatFunc S) := infinityBridgeDecidableEqRatFuncConstants S

@[reducible] local instance infinitySplittingBaseConstantAlgebra : Algebra C N :=
  infinityConstantAlgebra C N

@[reducible] local instance infinitySplittingBaseReciprocalPolynomialAlgebra :
    Algebra C[X] N :=
  infinityReciprocalPolynomialAlgebra C N

local instance infinitySplittingBaseConstantReciprocalPolynomialTower :
    IsScalarTower C C[X] N :=
  infinityReciprocalPolynomialTower C N

local instance infinitySplittingBaseRatFuncTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance infinitySplittingOldNormalizationConstantAlgebra :
    Algebra C (integralClosure C[X] N) :=
  RingHom.toAlgebra
    ((algebraMap C[X] (integralClosure C[X] N)).comp
      (algebraMap C C[X]))

local instance infinitySplittingOldNormalizationConstantPolynomialTower :
    IsScalarTower C C[X] (integralClosure C[X] N) :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance infinitySplittingCoefficientPolynomialAlgebra :
    Algebra C[X] S[X] :=
  Polynomial.algebra C S

local instance infinitySplittingCoefficientPolynomialSMul :
    SMul C[X] S[X] := Algebra.toSMul

local instance infinitySplittingCoefficientPolynomialModule :
    Module C[X] S[X] := Algebra.toModule

local instance infinitySplittingCOriginPrime :
    (Ideal.span ({Polynomial.X} : Set C[X])).IsPrime :=
  (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X

local instance infinitySplittingSOriginPrime :
    (Ideal.span ({Polynomial.X} : Set S[X])).IsPrime :=
  (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X

variable (hExact : algebraicClosure C N =
  (⊥ : IntermediateField C N))

/-- The reciprocal `C[X]`-action on the exact constant extension. -/
@[reducible] noncomputable def exactConstantExtensionCReciprocalPolynomialAlgebra :
    Algebra C[X] (ExactConstantExtension C N S) :=
  RingHom.toAlgebra
    ((Algebra.TensorProduct.includeRight
      (R := C) (A := S) (B := N)).toRingHom.comp
        (algebraMap C[X] N))

@[reducible] local instance infinitySplittingExactCPolynomialAlgebra :
    Algebra C[X] (ExactConstantExtension C N S) :=
  exactConstantExtensionCReciprocalPolynomialAlgebra C S N

@[reducible] local instance infinitySplittingExactSPolynomialAlgebra :
    Algebra S[X] (ExactConstantExtension C N S) :=
  polynomialTensorCancelTargetPolynomialExtensionAlgebra C S N

local instance infinitySplittingExactCPolynomialSMul :
    SMul C[X] (ExactConstantExtension C N S) := Algebra.toSMul

local instance infinitySplittingExactCPolynomialModule :
    Module C[X] (ExactConstantExtension C N S) := Algebra.toModule

local instance infinitySplittingExactSPolynomialSMul :
    SMul S[X] (ExactConstantExtension C N S) := Algebra.toSMul

@[reducible] local instance infinitySplittingPresentedSPolynomialAlgebra :
    Algebra S[X] (TensorProduct C S (integralClosure C[X] N)) :=
  polynomialTensorCancelTargetPolynomialExtensionAlgebra C S
    (integralClosure C[X] N)

@[reducible] local instance infinitySplittingPresentedCPolynomialAlgebra :
    Algebra C[X] (TensorProduct C S (integralClosure C[X] N)) :=
  RingHom.toAlgebra
    ((Algebra.TensorProduct.includeRight
      (R := C) (A := S) (B := integralClosure C[X] N)).toRingHom.comp
        (algebraMap C[X] (integralClosure C[X] N)))

local instance infinitySplittingPresentedSPolynomialSMul :
    SMul S[X] (TensorProduct C S (integralClosure C[X] N)) := Algebra.toSMul

local instance infinitySplittingPresentedCPolynomialSMul :
    SMul C[X] (TensorProduct C S (integralClosure C[X] N)) := Algebra.toSMul

omit [Fintype C] [Finite S] [DecidableEq C] [DecidableEq S] [DecidableEq (RatFunc C)]
  [DecidableEq (RatFunc S)] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N] [FiniteDimensional C S] [IsGalois C S] in
/-- The reciprocal polynomial actions on the exact constant extension form
the expected scalar tower. -/
theorem exactConstantExtensionReciprocalPolynomialTower :
    IsScalarTower C[X] S[X] (ExactConstantExtension C N S) := by
  apply IsScalarTower.of_algebraMap_eq
  intro p
  rw [polynomialTensorCancel_algebraMap_coefficient C S N p]
  rfl

/-- Integral closure is unchanged when the integral coefficient extension
`C[X] -> S[X]` is inserted into the reciprocal normalization. -/
noncomputable def exactConstantExtensionReciprocalIntegralClosureTowerEquiv :
    integralClosure C[X] (ExactConstantExtension C N S) ≃+*
      @integralClosure S[X] (ExactConstantExtension C N S) _ _
        (polynomialTensorCancelTargetPolynomialExtensionAlgebra C S N) := by
  letI : IsScalarTower C[X] S[X] (ExactConstantExtension C N S) :=
    exactConstantExtensionReciprocalPolynomialTower C S N
  exact integralClosureRingEquivOfIntegralTower C[X] S[X]
    (ExactConstantExtension C N S)

/-- The presented reciprocal normalization is the normalization of the exact
constant extension over the original reciprocal polynomial ring `C[X]`. -/
noncomputable def exactConstantExtensionPresentedToCReciprocalNormalizationRingEquiv :
    TensorProduct C S (integralClosure C[X] N) ≃+*
      integralClosure C[X] (ExactConstantExtension C N S) := by
  letI : IsScalarTower C[X] S[X] (ExactConstantExtension C N S) :=
    exactConstantExtensionReciprocalPolynomialTower C S N
  let eS := finiteFieldReciprocalNormalizationAlgEquiv C S N
  let eC := exactConstantExtensionReciprocalIntegralClosureTowerEquiv C S N
  exact eS.toRingEquiv.trans eC.symm

omit [Fintype C] [Finite S] [FiniteDimensional C S] [IsGalois C S] in
/-- Coefficient extension commutes with evaluation in the reciprocal
coordinate. -/
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

/-- The reciprocal polynomial algebra map is the composite through the
rational-function field. -/
theorem ratFuncExtensionReciprocalPolynomialAlgebra_map
    (K L : Type*) [Field K] [Field L]
    [DecidableEq K] [DecidableEq (RatFunc K)]
    [Algebra (RatFunc K) L] (p : K[X]) :
    letI : Algebra K[X] L :=
      ratFuncExtensionReciprocalPolynomialAlgebra K L
    algebraMap K[X] L p = algebraMap (RatFunc K) L
      (((reciprocalPolynomialRingHom K p :
        RatFuncInfinityIntegers K) : RatFunc K)) := by
  let : Algebra K[X] L :=
    ratFuncExtensionReciprocalPolynomialAlgebra K L
  change algebraMap (RatFuncInfinityIntegers K) L
      (reciprocalPolynomialRingHom K p) = _
  exact IsScalarTower.algebraMap_apply
    (RatFuncInfinityIntegers K) (RatFunc K) L _

omit [Fintype C] [Finite S] [DecidableEq C] [DecidableEq (RatFunc C)]
  [FiniteDimensional (RatFunc C) N] [Algebra.IsSeparable (RatFunc C) N] in
/-- Version of reciprocal polynomial compatibility elaborated with the
instances used in this file. -/
private theorem exactConstantExtensionSReciprocalPolynomialAlgebra_eq :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    polynomialTensorCancelTargetPolynomialExtensionAlgebra C S N =
      ratFuncExtensionReciprocalPolynomialAlgebra S
        (ExactConstantExtension C N S) := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  apply Algebra.algebra_ext
  intro p
  change Polynomial.aeval
      (polynomialTensorCancelEvaluationPoint C S N) p =
    algebraMap (RatFunc S) (ExactConstantExtension C N S)
      (((reciprocalPolynomialRingHom S p :
        RatFuncInfinityIntegers S) : RatFunc S))
  rw [reciprocalPolynomialRingHom_coe, Polynomial.hom_eval₂]
  have hcoeff :
      (algebraMap (RatFunc S)
          (ExactConstantExtension C N S)).comp RatFunc.C =
        algebraMap S (ExactConstantExtension C N S) := by
    ext s
    exact (ratFuncToExactConstantExtension C S N hExact).commutes s
  rw [hcoeff]
  change Polynomial.eval₂
      (algebraMap S (ExactConstantExtension C N S))
        (polynomialTensorCancelEvaluationPoint C S N) p =
    Polynomial.eval₂
      (algebraMap S (ExactConstantExtension C N S))
        (ratFuncToExactConstantExtension C S N hExact
          (1 / RatFunc.X)) p
  rw [ratFuncToExactConstantExtension_reciprocal_X C S N hExact]

omit [Fintype C] [Finite S] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N] in
/-- The transported reciprocal `C[X]`-action is the actual action induced by
the canonical embedding of `C(X)` into the exact constant extension. -/
theorem exactConstantExtensionCReciprocalPolynomialAlgebra_eq :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    exactConstantExtensionCReciprocalPolynomialAlgebra C S N =
      ratFuncExtensionReciprocalPolynomialAlgebra C
        (ExactConstantExtension C N S) := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : Algebra (RatFunc C) (RatFunc S) :=
    ratFuncCoefficientAlgebra C S
  let : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : Algebra C[X] (ExactConstantExtension C N S) :=
    exactConstantExtensionCReciprocalPolynomialAlgebra C S N
  let : Algebra S[X] (ExactConstantExtension C N S) :=
    infinitySplittingExactSPolynomialAlgebra C S N
  let : SMul C[X] (ExactConstantExtension C N S) :=
    infinitySplittingExactCPolynomialSMul C S N
  let : SMul S[X] (ExactConstantExtension C N S) :=
    infinitySplittingExactSPolynomialSMul C S N
  let : IsScalarTower C[X] S[X] (ExactConstantExtension C N S) :=
    exactConstantExtensionReciprocalPolynomialTower C S N
  apply Algebra.algebra_ext
  intro p
  let pS := algebraMap C[X] S[X] p
  let yC := ((reciprocalPolynomialRingHom C p :
    RatFuncInfinityIntegers C) : RatFunc C)
  let yS := ((reciprocalPolynomialRingHom S pS :
    RatFuncInfinityIntegers S) : RatFunc S)
  have hSAlg := exactConstantExtensionSReciprocalPolynomialAlgebra_eq
    C S N hExact
  have hRat := rationalBase_algebraMap_eq C S N hExact
  calc
    algebraMap C[X] (ExactConstantExtension C N S) p =
        algebraMap S[X] (ExactConstantExtension C N S) pS :=
      IsScalarTower.algebraMap_apply C[X] S[X]
        (ExactConstantExtension C N S) p
    _ = @algebraMap S[X] (ExactConstantExtension C N S) _ _
        (ratFuncExtensionReciprocalPolynomialAlgebra S
          (ExactConstantExtension C N S)) pS := by
      change @algebraMap S[X] (ExactConstantExtension C N S) _ _
          (polynomialTensorCancelTargetPolynomialExtensionAlgebra C S N) pS = _
      exact DFunLike.congr_fun
        (congrArg (fun a : Algebra S[X] (ExactConstantExtension C N S) =>
          @algebraMap S[X] (ExactConstantExtension C N S) _ _ a) hSAlg) pS
    _ = algebraMap (RatFunc S) (ExactConstantExtension C N S) yS :=
      ratFuncExtensionReciprocalPolynomialAlgebra_map S
        (ExactConstantExtension C N S) pS
    _ = algebraMap (RatFunc S) (ExactConstantExtension C N S)
        (algebraMap (RatFunc C) (RatFunc S) yC) := by
      congr 1
      exact (ratFuncCoefficientAlgHom_reciprocalPolynomialRingHom C S p).symm
    _ = algebraMap (RatFunc C) (ExactConstantExtension C N S) yC := by
      exact (DFunLike.congr_fun hRat yC).symm
    _ = @algebraMap C[X] (ExactConstantExtension C N S) _ _
        (ratFuncExtensionReciprocalPolynomialAlgebra C
          (ExactConstantExtension C N S)) p :=
      (ratFuncExtensionReciprocalPolynomialAlgebra_map C
        (ExactConstantExtension C N S) p).symm

/-- Replace the transported reciprocal polynomial action by the definitionally
actual action induced from `C(X)`. -/
noncomputable def exactConstantExtensionCReciprocalNormalizationRingEquiv :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    @integralClosure C[X] (ExactConstantExtension C N S) _ _
        (exactConstantExtensionCReciprocalPolynomialAlgebra C S N) ≃+*
      @integralClosure C[X] (ExactConstantExtension C N S) _ _
        (ratFuncExtensionReciprocalPolynomialAlgebra C
          (ExactConstantExtension C N S)) := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  rw [exactConstantExtensionCReciprocalPolynomialAlgebra_eq C S N hExact]

/-- Localization at the reciprocal origin identifies affine primes with the
actual places of the exact constant extension above `C`-infinity. -/
noncomputable def exactConstantExtensionCReciprocalPrimesEquivInfinityPlace :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra C[X] (ExactConstantExtension C N S) :=
      ratFuncExtensionReciprocalPolynomialAlgebra C
        (ExactConstantExtension C N S)
    (Ideal.span ({Polynomial.X} : Set C[X])).primesOver
        (integralClosure C[X] (ExactConstantExtension C N S)) ≃
      FiniteExtensionInfinityPlace C (ExactConstantExtension C N S) := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toModule
  letI : FiniteDimensional (RatFunc C)
      (ExactConstantExtension C N S) :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc
      C S N hExact
  letI : Algebra.IsSeparable (RatFunc C)
      (ExactConstantExtension C N S) :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  letI : Algebra C[X] (ExactConstantExtension C N S) :=
    ratFuncExtensionReciprocalPolynomialAlgebra C
      (ExactConstantExtension C N S)
  letI : SMul C[X] (ExactConstantExtension C N S) :=
    Algebra.toSMul
  letI : Module C[X] (ExactConstantExtension C N S) :=
    Algebra.toModule
  letI : Algebra C[X] (RatFunc C) :=
    ratFuncExtensionReciprocalPolynomialAlgebra C (RatFunc C)
  letI : SMul C[X] (RatFunc C) := Algebra.toSMul
  letI : IsScalarTower C[X] (RatFunc C)
      (ExactConstantExtension C N S) :=
    IsScalarTower.of_algebraMap_eq fun p => by
      calc
        algebraMap C[X] (ExactConstantExtension C N S) p =
            algebraMap (RatFunc C) (ExactConstantExtension C N S)
              (((reciprocalPolynomialRingHom C p :
                RatFuncInfinityIntegers C) : RatFunc C)) :=
          ratFuncExtensionReciprocalPolynomialAlgebra_map C
            (ExactConstantExtension C N S) p
        _ = algebraMap (RatFunc C) (ExactConstantExtension C N S)
            (algebraMap C[X] (RatFunc C) p) := by
          rw [ratFuncExtensionReciprocalPolynomialAlgebra_map C (RatFunc C) p]
          exact congrArg (algebraMap (RatFunc C)
            (ExactConstantExtension C N S))
              (Algebra.algebraMap_self_apply _).symm
  letI : IsFractionRing C[X] (RatFunc C) :=
    ratFunc_isFractionRing_reciprocalPolynomial C
  let A := integralClosure C[X] (ExactConstantExtension C N S)
  let V := RatFuncInfinityIntegers C
  let B := RatFuncInfinityIntegralClosure C
    (ExactConstantExtension C N S)
  let o := Ideal.span ({Polynomial.X} : Set C[X])
  letI : Algebra C[X] V := ratFuncInfinityReciprocalPolynomialAlgebra C
  letI : o.IsPrime :=
    (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X
  letI : IsLocalization o.primeCompl V :=
    ratFuncInfinityIntegers_isLocalization_reciprocal C
  letI : Algebra A B :=
    ratFuncInfinityReciprocalIntegralClosureAlgebra C
      (ExactConstantExtension C N S)
  letI : SMul A B := Algebra.toSMul
  letI : IsLocalization (Algebra.algebraMapSubmonoid A o.primeCompl) B :=
    ratFuncInfinityIntegralClosure_isLocalization_reciprocal C
      (ExactConstantExtension C N S)
  letI : Algebra C[X] B :=
    RingHom.toAlgebra ((algebraMap V B).comp (algebraMap C[X] V))
  letI : IsScalarTower C[X] V B :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower C[X] A B :=
    IsScalarTower.of_algebraMap_eq fun p => by
      apply Subtype.ext
      rfl
  letI : IsDedekindDomain A :=
    IsIntegralClosure.isDedekindDomain C[X] (RatFunc C)
      (ExactConstantExtension C N S) A
  letI : Module C[X] A := Algebra.toModule
  letI : Module.IsTorsionFree C[X]
      (ExactConstantExtension C N S) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    intro x y hxy
    apply IsFractionRing.injective C[X] (RatFunc C)
    apply (algebraMap (RatFunc C)
      (ExactConstantExtension C N S)).injective
    simpa only [IsScalarTower.algebraMap_apply C[X] (RatFunc C)
      (ExactConstantExtension C N S)] using hxy
  letI : IsScalarTower C[X] A (ExactConstantExtension C N S) := by
    infer_instance
  letI : Module.IsTorsionFree C[X] A :=
    IsIntegralClosure.isTorsionFree C[X]
      (ExactConstantExtension C N S)
  have ho : o ≠ ⊥ := by
    exact fun h => Polynomial.X_ne_zero (Ideal.span_singleton_eq_bot.mp h)
  change o.primesOver A ≃
    (IsLocalRing.maximalIdeal V).primesOver B
  exact (IsDedekindDomain.primesOverEquivPrimesOver o V B ho).toEquiv

omit [Fintype C] [Finite S] [DecidableEq C] [DecidableEq S] [DecidableEq (RatFunc C)]
  [DecidableEq (RatFunc S)] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N] [FiniteDimensional C S] [IsGalois C S] in
private theorem exactConstantExtensionPresentedReciprocalPolynomialTower :
    IsScalarTower C[X] S[X]
      (S ⊗[C] integralClosure C[X] N) := by
  apply IsScalarTower.of_algebraMap_eq
  intro p
  rw [polynomialTensorCancel_algebraMap_coefficient C S
    (integralClosure C[X] N) p]
  rfl

/-- The old reciprocal normalization maps into the reciprocal normalization
of the exact constant extension through the right tensor factor. -/
private noncomputable def exactConstantExtensionOldToCReciprocalNormalizationMap :
    integralClosure C[X] N →ₐ[C[X]]
      integralClosure C[X] (ExactConstantExtension C N S) := by
  letI : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionAlgebra C N S
  letI : SMul N (ExactConstantExtension C N S) := Algebra.toSMul
  letI : IsScalarTower C[X] N (ExactConstantExtension C N S) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact (IsScalarTower.toAlgHom C[X] N
    (ExactConstantExtension C N S)).mapIntegralClosure

omit [DecidableEq C] [DecidableEq S] [DecidableEq (RatFunc C)] [DecidableEq (RatFunc S)]
  [FiniteDimensional (RatFunc C) N] [Algebra.IsSeparable (RatFunc C) N]
  [FiniteDimensional C S] in
/-- The normalization equivalence carries the old normalization embedded in
the right tensor factor to its canonical map into the exact extension. -/
private theorem
    exactConstantExtensionPresentedToCReciprocalNormalizationRingEquiv_includeRight
    (x : integralClosure C[X] N) :
    exactConstantExtensionPresentedToCReciprocalNormalizationRingEquiv
        C S N
        (Algebra.TensorProduct.includeRight
          (R := C) (A := S) (B := integralClosure C[X] N) x) =
      exactConstantExtensionOldToCReciprocalNormalizationMap C S N x := by
  apply Subtype.ext
  change ((finiteFieldReciprocalNormalizationAlgEquiv C S N
      (Algebra.TensorProduct.includeRight
        (R := C) (A := S) (B := integralClosure C[X] N) x) :
        integralClosure S[X] (ExactConstantExtension C N S)) :
      ExactConstantExtension C N S) =
    (1 : S) ⊗ₜ[C] (x : N)
  simp only [finiteFieldReciprocalNormalizationAlgEquiv,
    AlgEquiv.trans_apply,
    Algebra.TensorProduct.includeRight_apply,
    polynomialTensorCancelOverCoefficientPolynomial_symm_apply,
    polynomialTensorCancel_symm_tmul,
    finiteFieldPolynomialIntegralClosureBaseChangeAlgEquiv,
    polynomialIntegralClosureBaseChangeAlgEquiv,
    AlgEquiv.ofBijective_apply,
    AlgEquiv.coe_mapIntegralClosure]
  rw [polynomialTensorCancelOverCoefficientPolynomial_apply]
  change polynomialTensorCancel C S N
      (Polynomial.C 1 ⊗ₜ[C[X]] (x : N)) =
    (1 : S) ⊗ₜ[C] (x : N)
  rw [polynomialTensorCancel_tmul]
  simp

omit [Fintype C] [Finite S] [DecidableEq C] [DecidableEq S] [DecidableEq (RatFunc C)]
  [DecidableEq (RatFunc S)] [FiniteDimensional C S] [IsGalois C S] in
/-- The reciprocal origin is the unique prime of `S[X]` above the reciprocal
origin of `C[X]`. -/
theorem primeUnderReciprocalOrigin_eq_origin
    (p : Ideal S[X]) [p.IsPrime]
    (hunder : p.under C[X] =
      Ideal.span ({Polynomial.X} : Set C[X])) :
    p = Ideal.span ({Polynomial.X} : Set S[X]) := by
  let oS := Ideal.span ({Polynomial.X} : Set S[X])
  have hXC : (Polynomial.X : C[X]) ∈ p.under C[X] := by
    rw [hunder]
    exact Ideal.subset_span (Set.mem_singleton Polynomial.X)
  have hXS : (Polynomial.X : S[X]) ∈ p := by
    change algebraMap C[X] S[X] (Polynomial.X : C[X]) ∈ p at hXC
    simpa using hXC
  have hle : oS ≤ p := by
    rw [Ideal.span_le]
    exact Set.singleton_subset_iff.mpr hXS
  have hoPrime : oS.IsPrime := by
    exact (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr
      Polynomial.prime_X
  have hoNeBot : oS ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact Polynomial.X_ne_zero
  exact ((hoPrime.isMaximal hoNeBot).eq_of_le
    (inferInstance : p.IsPrime).ne_top hle).symm

omit [DecidableEq C] [DecidableEq S] [DecidableEq (RatFunc C)] [DecidableEq (RatFunc S)]
  [FiniteDimensional (RatFunc C) N] [Algebra.IsSeparable (RatFunc C) N]
  [FiniteDimensional C S] in
private theorem
    exactConstantExtensionPresentedToCReciprocalNormalizationRingEquiv_commutes
    (p : C[X]) :
    exactConstantExtensionPresentedToCReciprocalNormalizationRingEquiv C S N
        (algebraMap C[X] (S ⊗[C] integralClosure C[X] N) p) =
      algebraMap C[X]
        (integralClosure C[X] (ExactConstantExtension C N S)) p := by
  let : IsScalarTower C[X] S[X] (ExactConstantExtension C N S) :=
    exactConstantExtensionReciprocalPolynomialTower C S N
  let eS := finiteFieldReciprocalNormalizationAlgEquiv C S N
  let eC := exactConstantExtensionReciprocalIntegralClosureTowerEquiv C S N
  change eC.symm (eS
    (algebraMap C[X] (S ⊗[C] integralClosure C[X] N) p)) = _
  rw [show algebraMap C[X] (S ⊗[C] integralClosure C[X] N) p =
      algebraMap S[X] (S ⊗[C] integralClosure C[X] N)
        (algebraMap C[X] S[X] p) by
    rw [polynomialTensorCancel_algebraMap_coefficient C S
      (integralClosure C[X] N) p]
    rfl]
  rw [eS.commutes]
  apply Subtype.ext
  change algebraMap S[X] (ExactConstantExtension C N S)
      (algebraMap C[X] S[X] p) =
    algebraMap C[X] (ExactConstantExtension C N S) p
  rw [polynomialTensorCancel_algebraMap_coefficient C S N p]
  rfl

/-- The reciprocal normalization equivalence transports height-one primes. -/
noncomputable def
    exactConstantExtensionPresentedToCReciprocalNormalizationHeightOneEquiv :
    HeightOneSpectrum (S ⊗[C] integralClosure C[X] N) ≃
      HeightOneSpectrum
        (integralClosure C[X] (ExactConstantExtension C N S)) :=
  HeightOneSpectrum.equivOfRingEquiv
    (exactConstantExtensionPresentedToCReciprocalNormalizationRingEquiv C S N)

/-- The reciprocal normalization equivalence preserves contraction to `C[X]`. -/
theorem
    exactConstantExtensionPresentedToCReciprocalNormalizationHeightOneEquiv_under
    (q : HeightOneSpectrum (S ⊗[C] integralClosure C[X] N)) :
    ((exactConstantExtensionPresentedToCReciprocalNormalizationHeightOneEquiv
        C S N) q).asIdeal.under C[X] =
      q.asIdeal.under C[X] := by
  let e := exactConstantExtensionPresentedToCReciprocalNormalizationRingEquiv
    C S N
  ext p
  change e.symm
      (algebraMap C[X]
        (integralClosure C[X] (ExactConstantExtension C N S)) p) ∈
      q.asIdeal ↔
    algebraMap C[X] (S ⊗[C] integralClosure C[X] N) p ∈ q.asIdeal
  rw [←
    exactConstantExtensionPresentedToCReciprocalNormalizationRingEquiv_commutes
      C S N p]
  simp only [e, RingEquiv.symm_apply_apply]

/-- Presented infinity places correspond to height-one primes above the reciprocal origin. -/
noncomputable def
    exactConstantExtensionPresentedInfinityHeightOneEquiv :
    ExactConstantExtensionPresentedInfinityPlace C S N ≃
      {q : HeightOneSpectrum
          (integralClosure C[X] (ExactConstantExtension C N S)) //
        q.asIdeal.under C[X] =
          Ideal.span ({Polynomial.X} : Set C[X])} := by
  letI : IsScalarTower C[X] S[X]
      (S ⊗[C] integralClosure C[X] N) :=
    by exact exactConstantExtensionPresentedReciprocalPolynomialTower C S N
  let e :=
    exactConstantExtensionPresentedToCReciprocalNormalizationHeightOneEquiv
      C S N
  apply e.subtypeEquiv
  intro q
  constructor
  · intro hq
    rw [
      exactConstantExtensionPresentedToCReciprocalNormalizationHeightOneEquiv_under
        C S N q]
    calc
      q.asIdeal.under C[X] =
          (q.asIdeal.under S[X]).under C[X] :=
        (Ideal.under_under q.asIdeal).symm
      _ = (Ideal.span ({Polynomial.X} : Set S[X])).under C[X] := by
        rw [hq]
      _ = Ideal.span ({Polynomial.X} : Set C[X]) :=
        coefficientPolynomial_under_span_X C S
  · intro hq
    have hqC : q.asIdeal.under C[X] =
        Ideal.span ({Polynomial.X} : Set C[X]) := by
      rw [←
        exactConstantExtensionPresentedToCReciprocalNormalizationHeightOneEquiv_under
          C S N q]
      exact hq
    let p := q.asIdeal.under S[X]
    let : q.asIdeal.IsPrime := q.isPrime
    let : p.IsPrime := inferInstance
    apply primeUnderReciprocalOrigin_eq_origin C S p
    calc
      p.under C[X] = q.asIdeal.under C[X] := Ideal.under_under q.asIdeal
      _ = Ideal.span ({Polynomial.X} : Set C[X]) := hqC

/-- Height-one primes above the reciprocal origin identify with its prime fiber. -/
noncomputable def
    exactConstantExtensionCReciprocalHeightOneEquivPrimesOver :
    {q : HeightOneSpectrum
        (integralClosure C[X] (ExactConstantExtension C N S)) //
      q.asIdeal.under C[X] =
        Ideal.span ({Polynomial.X} : Set C[X])} ≃
      (Ideal.span ({Polynomial.X} : Set C[X])).primesOver
        (integralClosure C[X] (ExactConstantExtension C N S)) := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  exact
    { toFun := fun q => ⟨q.1.asIdeal, q.1.isPrime, ⟨q.2.symm⟩⟩
      invFun := fun P => by
        let oC := Ideal.span ({Polynomial.X} : Set C[X])
        have hNX : algebraMap C[X] N (Polynomial.X : C[X]) ≠ 0 := by
          let : DecidableEq C := infinityBridgeDecidableEqConstants C
          let : DecidableEq (RatFunc C) :=
            infinityBridgeDecidableEqRatFuncConstants C
          have hNX' : @algebraMap C[X] N _ _
              (ratFuncExtensionReciprocalPolynomialAlgebra C N)
                (Polynomial.X : C[X]) ≠ 0 := by
            rw [ratFuncExtensionReciprocalPolynomialAlgebra_map C N]
            rw [reciprocalPolynomialRingHom_X]
            change algebraMap (RatFunc C) N (1 / RatFunc.X) ≠ 0
            intro hzero
            have hzero' : (1 / RatFunc.X : RatFunc C) = 0 := by
              apply (algebraMap (RatFunc C) N).injective
              simpa only [map_zero] using hzero
            exact (one_div_ne_zero RatFunc.X_ne_zero) hzero'
          change @algebraMap C[X] N _ _
            (infinitySplittingBaseReciprocalPolynomialAlgebra C N)
              (Polynomial.X : C[X]) ≠ 0
          unfold infinitySplittingBaseReciprocalPolynomialAlgebra
          unfold infinityReciprocalPolynomialAlgebra
          exact hNX'
        have hEX : algebraMap C[X] (ExactConstantExtension C N S)
            (Polynomial.X : C[X]) ≠ 0 := by
          change Algebra.TensorProduct.includeRight
            (R := C) (A := S) (B := N)
              (algebraMap C[X] N (Polynomial.X : C[X])) ≠ 0
          let f := Algebra.TensorProduct.includeRight
            (R := C) (A := S) (B := N)
          intro hx
          apply hNX
          apply f.injective
          exact hx.trans (map_zero f).symm
        have hAX : algebraMap C[X]
            (integralClosure C[X] (ExactConstantExtension C N S))
              (Polynomial.X : C[X]) ≠ 0 := by
          intro hzero
          apply hEX
          exact congrArg Subtype.val hzero
        letI : P.1.LiesOver oC := P.2.2
        have hXmem : algebraMap C[X]
            (integralClosure C[X] (ExactConstantExtension C N S))
              (Polynomial.X : C[X]) ∈ P.1 :=
          (Ideal.mem_of_liesOver P.1 oC Polynomial.X).mp
            (Ideal.mem_span_singleton_self Polynomial.X)
        have hPNeBot : P.1 ≠ ⊥ := by
          intro hbot
          apply hAX
          rw [hbot] at hXmem
          change algebraMap C[X]
            (integralClosure C[X] (ExactConstantExtension C N S))
              (Polynomial.X : C[X]) = 0 at hXmem
          exact hXmem
        let q : HeightOneSpectrum
            (integralClosure C[X] (ExactConstantExtension C N S)) :=
          ⟨P.1, P.2.1, hPNeBot⟩
        refine ⟨q, ?_⟩
        exact (Ideal.over_def P.1 oC).symm
      left_inv := by
        intro q
        apply Subtype.ext
        apply HeightOneSpectrum.ext
        rfl
      right_inv := by
        intro P
        apply Subtype.ext
        rfl }

/-- Presented infinity places, before changing the transported reciprocal
action to the actual one, are precisely the affine primes above `(X)`. -/
noncomputable def
    exactConstantExtensionPresentedInfinityPlaceEquivCReciprocalPrimes :
    ExactConstantExtensionPresentedInfinityPlace C S N ≃
      (Ideal.span ({Polynomial.X} : Set C[X])).primesOver
        (integralClosure C[X] (ExactConstantExtension C N S)) :=
  (exactConstantExtensionPresentedInfinityHeightOneEquiv C S N).trans
    (exactConstantExtensionCReciprocalHeightOneEquivPrimesOver
      C S N)

/-- Contracting the transported reciprocal affine prime to the old
normalization recovers the contraction used in the presented downstairs
place. -/
private theorem
    exactConstantExtensionPresentedInfinityPlaceEquivCReciprocalPrimes_under_old
    (q : ExactConstantExtensionPresentedInfinityPlace C S N) :
    letI : Algebra (integralClosure C[X] N)
        (integralClosure C[X] (ExactConstantExtension C N S)) :=
      (exactConstantExtensionOldToCReciprocalNormalizationMap C S N).toAlgebra
    ((exactConstantExtensionPresentedInfinityPlaceEquivCReciprocalPrimes
        C S N q).1).under (integralClosure C[X] N) =
      exactConstantExtensionInfinityDownstairsIdeal C S N q.1 := by
  let e := exactConstantExtensionPresentedToCReciprocalNormalizationRingEquiv
    C S N
  let f := exactConstantExtensionOldToCReciprocalNormalizationMap C S N
  let : Algebra (integralClosure C[X] N)
      (integralClosure C[X] (ExactConstantExtension C N S)) :=
    f.toAlgebra
  ext x
  change e.symm (f x) ∈ q.1.asIdeal ↔
    Algebra.TensorProduct.includeRight
      (R := C) (A := S) (B := integralClosure C[X] N) x ∈
        q.1.asIdeal
  have hx : e.symm (f x) =
      Algebra.TensorProduct.includeRight
        (R := C) (A := S) (B := integralClosure C[X] N) x := by
    apply e.injective
    rw [e.apply_symm_apply,
      exactConstantExtensionPresentedToCReciprocalNormalizationRingEquiv_includeRight]
  rw [hx]

/-- Changing from the transported reciprocal action to the actual action does
not change the affine prime fiber. -/
private noncomputable def integralClosureAlgHomOfAlgebraEq
    (R L A : Type*) [CommRing R] [Field L] [CommRing A] [Algebra R A]
    (a b : Algebra R L) (h : a = b)
    (f : A →ₐ[R] @integralClosure R L _ _ a) :
    A →ₐ[R] @integralClosure R L _ _ b := by
  rw [← h]
  exact f

private noncomputable def primesOverEquivOfAlgebraEq
    (R L : Type*) [CommRing R] [Field L]
    (a b : Algebra R L) (h : a = b) (p : Ideal R) :
    @Ideal.primesOver R _ p (@integralClosure R L _ _ a) _ _ ≃
      @Ideal.primesOver R _ p (@integralClosure R L _ _ b) _ _ := by
  rw [h]

private theorem primesOverEquivOfAlgebraEq_under
    (R L A : Type*) [CommRing R] [Field L] [CommRing A] [Algebra R A]
    (a b : Algebra R L) (h : a = b) (p : Ideal R)
    (f : A →ₐ[R] @integralClosure R L _ _ a)
    (P : @Ideal.primesOver R _ p (@integralClosure R L _ _ a) _ _) :
    let g := integralClosureAlgHomOfAlgebraEq R L A a b h f
    letI : Algebra A (@integralClosure R L _ _ a) := f.toAlgebra
    letI : Algebra A (@integralClosure R L _ _ b) := g.toAlgebra
    ((primesOverEquivOfAlgebraEq R L a b h p P).1).under A =
      P.1.under A := by
  subst b
  rfl

/-- The prime fiber over the reciprocal origin is preserved by identifying the two polynomial
actions. -/
noncomputable def
    exactConstantExtensionCReciprocalPrimesEquivActual :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    @Ideal.primesOver C[X] _
        (Ideal.span ({Polynomial.X} : Set C[X]))
        (@integralClosure C[X] (ExactConstantExtension C N S) _ _
          (exactConstantExtensionCReciprocalPolynomialAlgebra C S N)) _ _ ≃
      @Ideal.primesOver C[X] _
        (Ideal.span ({Polynomial.X} : Set C[X]))
        (@integralClosure C[X] (ExactConstantExtension C N S) _ _
          (ratFuncExtensionReciprocalPolynomialAlgebra C
            (ExactConstantExtension C N S))) _ _ := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  rw [exactConstantExtensionCReciprocalPolynomialAlgebra_eq C S N hExact]

/-- The reciprocal-normalization presentation of infinity places is exactly
the actual infinity-place type of the exact constant extension over `C`. -/
noncomputable def exactConstantExtensionPresentedInfinityPlaceEquiv :
    ExactConstantExtensionPresentedInfinityPlace C S N ≃
      letI : Field (ExactConstantExtension C N S) :=
        exactConstantExtensionField C N S hExact
      letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
        exactConstantExtensionBaseAlgebra C (RatFunc C) N S
      FiniteExtensionInfinityPlace C (ExactConstantExtension C N S) :=
  (exactConstantExtensionPresentedInfinityPlaceEquivCReciprocalPrimes
      C S N).trans
    ((exactConstantExtensionCReciprocalPrimesEquivActual
        C S N hExact).trans
      (exactConstantExtensionCReciprocalPrimesEquivInfinityPlace
        C S N hExact))

omit [DecidableEq C] [DecidableEq (RatFunc C)] in
/-- The reciprocal presentation equivalence respects restriction to the
original function field. -/
@[simp]
theorem exactConstantExtensionPresentedInfinityPlaceEquiv_under
    (q : ExactConstantExtensionPresentedInfinityPlace C S N) :
    letI : DecidableEq C := infinityBridgeDecidableEqConstants C
    letI : DecidableEq (RatFunc C) :=
      infinityBridgeDecidableEqRatFuncConstants C
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : FiniteDimensional (RatFunc C)
        (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc
        C S N hExact
    letI : Algebra.IsSeparable (RatFunc C)
        (ExactConstantExtension C N S) :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : Algebra N (ExactConstantExtension C N S) :=
      exactConstantExtensionAlgebra C N S
    letI : SMul N (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module N (ExactConstantExtension C N S) := Algebra.toModule
    letI : IsScalarTower (RatFunc C) N
        (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseTower C (RatFunc C) N S
    infinityPlaceUnder C N (ExactConstantExtension C N S)
        (exactConstantExtensionPresentedInfinityPlaceEquiv
          C S N hExact q) =
      exactConstantExtensionDownstairsInfinityPlace C S N q.1 q.2 := by
  let : DecidableEq C := infinityBridgeDecidableEqConstants C
  let : DecidableEq (RatFunc C) :=
    infinityBridgeDecidableEqRatFuncConstants C
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : FiniteDimensional (RatFunc C)
      (ExactConstantExtension C N S) :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc
      C S N hExact
  let : Algebra.IsSeparable (RatFunc C)
      (ExactConstantExtension C N S) :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionAlgebra C N S
  let : SMul N (ExactConstantExtension C N S) := Algebra.toSMul
  let : Module N (ExactConstantExtension C N S) := Algebra.toModule
  let : IsScalarTower (RatFunc C) N
      (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  apply Subtype.ext
  rw [infinityPlaceUnder_asIdeal,
    exactConstantExtensionDownstairsInfinityPlace_asIdeal]
  let E := ExactConstantExtension C N S
  let : Algebra C[X] E :=
    ratFuncExtensionReciprocalPolynomialAlgebra C E
  let A₀ := integralClosure C[X] N
  let B₀ := RatFuncInfinityIntegralClosure C N
  let A := integralClosure C[X] E
  let B := RatFuncInfinityIntegralClosure C E
  let P := (exactConstantExtensionCReciprocalPrimesEquivActual
    C S N hExact)
      (exactConstantExtensionPresentedInfinityPlaceEquivCReciprocalPrimes
        C S N q)
  let a := exactConstantExtensionCReciprocalPolynomialAlgebra C S N
  let b := ratFuncExtensionReciprocalPolynomialAlgebra C E
  let h : a = b :=
    exactConstantExtensionCReciprocalPolynomialAlgebra_eq C S N hExact
  let f₀ := exactConstantExtensionOldToCReciprocalNormalizationMap C S N
  let g := integralClosureAlgHomOfAlgebraEq C[X] E A₀ a b h f₀
  let : Algebra A B :=
    ratFuncInfinityReciprocalIntegralClosureAlgebra C E
  let : SMul A B := Algebra.toSMul
  let : Algebra A₀ B₀ :=
    ratFuncInfinityReciprocalIntegralClosureAlgebra C N
  let : SMul A₀ B₀ := Algebra.toSMul
  let : Algebra A₀ A :=
    g.toAlgebra
  let : SMul A₀ A := Algebra.toSMul
  let : Algebra B₀ B :=
    (infinityIntegralClosureMap C N E).toAlgebra
  let : SMul B₀ B := Algebra.toSMul
  change (Ideal.map (algebraMap A B) P.1).under
      B₀ =
    Ideal.map
      (algebraMap A₀ B₀)
      (exactConstantExtensionInfinityDownstairsIdeal C S N q.1)
  have hAffine : P.1.under A₀ =
      exactConstantExtensionInfinityDownstairsIdeal C S N q.1 := by
    let P₀ :=
      exactConstantExtensionPresentedInfinityPlaceEquivCReciprocalPrimes
        C S N q
    have hTransport : P.1.under A₀ = P₀.1.under A₀ := by
      exact primesOverEquivOfAlgebraEq_under
        C[X] E A₀ a b h
        (Ideal.span ({Polynomial.X} : Set C[X])) f₀ P₀
    have hOld :=
      exactConstantExtensionPresentedInfinityPlaceEquivCReciprocalPrimes_under_old
        C S N q
    exact hTransport.trans hOld
  let : Algebra A₀ B :=
    RingHom.toAlgebra
      ((algebraMap B₀ B).comp (algebraMap A₀ B₀))
  let : SMul A₀ B := Algebra.toSMul
  let : IsScalarTower A₀ B₀ B :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A₀ A B :=
    IsScalarTower.of_algebraMap_eq fun x => by
      apply Subtype.ext
      rfl
  have hMax :
      (Ideal.map (algebraMap A₀ B₀) (P.1.under A₀)).IsMaximal := by
    rw [hAffine]
    change (exactConstantExtensionDownstairsInfinityPlace
      C S N q.1 q.2).1.IsMaximal
    infer_instance
  have hNe : Ideal.map (algebraMap A B) P.1 ≠ ⊤ := by
    change (exactConstantExtensionPresentedInfinityPlaceEquiv
      C S N hExact q).1 ≠ ⊤
    exact (exactConstantExtensionPresentedInfinityPlaceEquiv
      C S N hExact q).2.1.ne_top
  rw [Ideal.under_map_eq_map_under P.1 hMax hNe, hAffine]

/-- The residue field of a presented reciprocal prime is the residue field of
the corresponding actual `C`-infinity place. -/
noncomputable def exactConstantExtensionPresentedInfinityResidueFieldRingEquiv
    (q : ExactConstantExtensionPresentedInfinityPlace C S N) :
    letI : DecidableEq C := infinityBridgeDecidableEqConstants C
    letI : DecidableEq (RatFunc C) :=
      infinityBridgeDecidableEqRatFuncConstants C
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    q.1.asIdeal.ResidueField ≃+*
      (exactConstantExtensionPresentedInfinityPlaceEquiv
        C S N hExact q).1.ResidueField := by
  letI : DecidableEq C := infinityBridgeDecidableEqConstants C
  letI : DecidableEq (RatFunc C) :=
    infinityBridgeDecidableEqRatFuncConstants C
  let E := ExactConstantExtension C N S
  letI : Field E := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) E :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let e₀ :=
    exactConstantExtensionPresentedToCReciprocalNormalizationRingEquiv
      C S N
  let e₁ := exactConstantExtensionCReciprocalNormalizationRingEquiv
    C S N hExact
  let e := e₀.trans e₁
  let qA : IsDedekindDomain.HeightOneSpectrum
      (@integralClosure C[X] E _ _
        (ratFuncExtensionReciprocalPolynomialAlgebra C E)) :=
    IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv e q.1
  let P := (exactConstantExtensionCReciprocalPrimesEquivActual
    C S N hExact)
      (exactConstantExtensionPresentedInfinityPlaceEquivCReciprocalPrimes
        C S N q)
  have hqA : qA.asIdeal = P.1 := by
    rfl
  let affineResidue : q.1.asIdeal.ResidueField ≃+*
      qA.asIdeal.ResidueField :=
    heightOneResidueFieldRingEquiv e q.1
  letI : Algebra C[X] E :=
    ratFuncExtensionReciprocalPolynomialAlgebra C E
  let A := integralClosure C[X] E
  let idealResidue : qA.asIdeal.ResidueField ≃+* P.1.ResidueField :=
    Ideal.residueFieldRingEquiv qA.asIdeal P.1 (RingEquiv.refl A)
      (by
        change qA.asIdeal = P.1.comap (RingHom.id A)
        rw [Ideal.comap_id, hqA])
  let affineResidue' : q.1.asIdeal.ResidueField ≃+* P.1.ResidueField :=
    affineResidue.trans idealResidue
  let B := RatFuncInfinityIntegralClosure C E
  let o := Ideal.span ({Polynomial.X} : Set C[X])
  letI : Algebra A B :=
    ratFuncInfinityReciprocalIntegralClosureAlgebra C E
  letI : SMul A B := Algebra.toSMul
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid A o.primeCompl) B :=
    ratFuncInfinityIntegralClosure_isLocalization_reciprocal C E
  let M := Algebra.algebraMapSubmonoid A o.primeCompl
  have hPUnder : P.1.under C[X] = o := P.2.2.over.symm
  have hdisj : Disjoint (M : Set A) (P.1 : Set A) :=
    mappedPrimeCompl_disjoint_of_under_eq
      C[X] A o P.1 hPUnder
  let Q := Ideal.map (algebraMap A B) P.1
  letI : Q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M B P.1 P.2.1 hdisj
  let localResidue : P.1.ResidueField ≃+* Q.ResidueField :=
    localizationResidueFieldRingEquiv A B M P.1 hdisj
  change q.1.asIdeal.ResidueField ≃+* Q.ResidueField
  exact affineResidue'.trans localResidue

section InfinityRamification


private theorem infinitySplitting_eq_of_algebraMap_sub_mem_prime
    (K R : Type*) [Field K] [CommRing R] [Algebra K R]
    (P : Ideal R) [P.IsPrime] (a b : K)
    (h : algebraMap K R a - algebraMap K R b ∈ P) :
    a = b := by
  by_contra hab
  have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hunit : IsUnit (algebraMap K R (a - b)) :=
    (isUnit_iff_ne_zero.mpr hne).map (algebraMap K R)
  have hmem : algebraMap K R (a - b) ∈ P := by simpa using h
  exact (inferInstance : P.IsPrime).ne_top
    (P.eq_top_of_isUnit_mem hmem hunit)

private theorem
    infinitySplitting_constantQuotient_eq_one_imp_eq_one
    (C N S : Type*) [Field C] [Field N] [Field S]
    [Algebra C N] [Algebra C S]
    [FiniteDimensional C S] [IsGalois C S]
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (g : letI : Field (ExactConstantExtension C N S) :=
          exactConstantExtensionField C N S hExact
        letI : Algebra N (ExactConstantExtension C N S) :=
          exactConstantExtensionBaseAlgebra C N N S
        ExactConstantExtension C N S ≃ₐ[N]
          ExactConstantExtension C N S)
    (hg : letI : Field (ExactConstantExtension C N S) :=
          exactConstantExtensionField C N S hExact
        letI : Algebra N (ExactConstantExtension C N S) :=
          exactConstantExtensionBaseAlgebra C N N S
        exactConstantExtensionConstantQuotient C N N S hExact g = 1) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra N (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C N N S
    g = 1 := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C N N S
  have hker : g ∈
      (exactConstantExtensionConstantQuotient C N N S hExact).ker :=
    MonoidHom.mem_ker.mpr hg
  rw [exactConstantExtensionConstantQuotient_ker C N N S hExact] at hker
  obtain ⟨u, hu⟩ := hker
  have huOne : u = 1 := Subsingleton.elim _ _
  calc
    g = exactConstantExtensionFunctionAutHom C N N S u := hu.symm
    _ = exactConstantExtensionFunctionAutHom C N N S 1 :=
      congrArg (exactConstantExtensionFunctionAutHom C N N S) huOne
    _ = 1 := map_one (exactConstantExtensionFunctionAutHom C N N S)

@[reducible] local instance infinitySplittingInfinityBaseRatFuncAlgebra :
    Algebra (RatFuncInfinityIntegers C) (RatFunc C) :=
  RingHom.toAlgebra
    (SubringClass.subtype ((RatFunc.inftyValuation C).integer))

local instance infinitySplittingInfinityBaseRatFuncSMul :
    SMul (RatFuncInfinityIntegers C) (RatFunc C) := Algebra.toSMul

local instance infinitySplittingInfinityBaseRatFuncModule :
    Module (RatFuncInfinityIntegers C) (RatFunc C) := Algebra.toModule

@[reducible] local instance infinitySplittingInfinityBaseNAlgebra :
    Algebra (RatFuncInfinityIntegers C) N :=
  RingHom.toAlgebra
    ((algebraMap (RatFunc C) N).comp
      (algebraMap (RatFuncInfinityIntegers C) (RatFunc C)))

local instance infinitySplittingInfinityBaseNSMul :
    SMul (RatFuncInfinityIntegers C) N := Algebra.toSMul

local instance infinitySplittingInfinityBaseNModule :
    Module (RatFuncInfinityIntegers C) N := Algebra.toModule

local instance infinitySplittingInfinityBaseNTower :
    IsScalarTower (RatFuncInfinityIntegers C) (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

omit [Fintype C] [DecidableEq C] [DecidableEq S] [DecidableEq (RatFunc S)]
  [Algebra.IsSeparable (RatFunc C) N] in
/-- Galois action on the infinity normalization restricts to the expected
constant-field quotient action. -/
theorem exactConstantExtensionConstantQuotient_action_on_infinityNormalization :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : Algebra N (ExactConstantExtension C N S) :=
      exactConstantExtensionAlgebra C N S
    letI : SMul N (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module N (ExactConstantExtension C N S) := Algebra.toModule
    letI : IsScalarTower (RatFunc C) N
        (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseTower C (RatFunc C) N S
    letI : IsGalois N (ExactConstantExtension C N S) :=
      exactConstantExtension_isGalois C N N S hExact
    letI : Algebra (RatFuncInfinityIntegers C)
        (ExactConstantExtension C N S) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc C) (ExactConstantExtension C N S)).comp
          (algebraMap (RatFuncInfinityIntegers C) (RatFunc C)))
    letI : SMul (RatFuncInfinityIntegers C)
        (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module (RatFuncInfinityIntegers C)
        (ExactConstantExtension C N S) := Algebra.toModule
    letI : IsScalarTower (RatFuncInfinityIntegers C) (RatFunc C)
        (ExactConstantExtension C N S) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : Algebra S (RatFuncInfinityIntegralClosure C
        (ExactConstantExtension C N S)) :=
      exactConstantExtensionInfinityIntegralClosureConstantAlgebra
        C S N hExact
    letI : MulSemiringAction
        (ExactConstantExtension C N S ≃ₐ[N]
          ExactConstantExtension C N S)
        (RatFuncInfinityIntegralClosure C
          (ExactConstantExtension C N S)) :=
      infinityIntegralClosureGalAction C N (ExactConstantExtension C N S)
    ∀ (g : ExactConstantExtension C N S ≃ₐ[N]
      ExactConstantExtension C N S) (s : S),
    g • algebraMap S (RatFuncInfinityIntegralClosure C
        (ExactConstantExtension C N S)) s =
      algebraMap S (RatFuncInfinityIntegralClosure C
        (ExactConstantExtension C N S))
        (exactConstantExtensionConstantQuotient C N N S hExact g s) := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionAlgebra C N S
  let : SMul N (ExactConstantExtension C N S) := Algebra.toSMul
  let : Module N (ExactConstantExtension C N S) := Algebra.toModule
  let : IsScalarTower (RatFunc C) N
      (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  let : IsGalois N (ExactConstantExtension C N S) :=
    exactConstantExtension_isGalois C N N S hExact
  let : Algebra (RatFuncInfinityIntegers C)
      (ExactConstantExtension C N S) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc C) (ExactConstantExtension C N S)).comp
        (algebraMap (RatFuncInfinityIntegers C) (RatFunc C)))
  let : SMul (RatFuncInfinityIntegers C)
      (ExactConstantExtension C N S) := Algebra.toSMul
  let : Module (RatFuncInfinityIntegers C)
      (ExactConstantExtension C N S) := Algebra.toModule
  let : IsScalarTower (RatFuncInfinityIntegers C) (RatFunc C)
      (ExactConstantExtension C N S) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra S (RatFuncInfinityIntegralClosure C
      (ExactConstantExtension C N S)) :=
    exactConstantExtensionInfinityIntegralClosureConstantAlgebra
      C S N hExact
  let : MulSemiringAction
      (ExactConstantExtension C N S ≃ₐ[N]
        ExactConstantExtension C N S)
      (RatFuncInfinityIntegralClosure C
        (ExactConstantExtension C N S)) :=
    infinityIntegralClosureGalAction C N (ExactConstantExtension C N S)
  intro g s
  apply Subtype.ext
  calc
    ((g • algebraMap S (RatFuncInfinityIntegralClosure C
          (ExactConstantExtension C N S)) s :
        RatFuncInfinityIntegralClosure C
          (ExactConstantExtension C N S)) :
        ExactConstantExtension C N S) =
      g ((algebraMap S (RatFuncInfinityIntegralClosure C
          (ExactConstantExtension C N S)) s :
        RatFuncInfinityIntegralClosure C
          (ExactConstantExtension C N S)) :
        ExactConstantExtension C N S) := by
      exact algebraMap.smul'
        (B := RatFuncInfinityIntegralClosure C
          (ExactConstantExtension C N S))
        g
        (algebraMap S (RatFuncInfinityIntegralClosure C
          (ExactConstantExtension C N S)) s)
        (ExactConstantExtension C N S)
    _ = (Algebra.TensorProduct.includeLeft
          (R := C) (S := C) (A := S) (B := N))
        (exactConstantExtensionConstantQuotient C N N S hExact g s) := by
      change g ((Algebra.TensorProduct.includeLeft
        (R := C) (S := C) (A := S) (B := N)) s) = _
      exact exactConstantExtensionConstantQuotient_action_on_constants
        C N N S hExact g s
    _ = ((algebraMap S (RatFuncInfinityIntegralClosure C
          (ExactConstantExtension C N S))
        (exactConstantExtensionConstantQuotient C N N S hExact g s) :
        RatFuncInfinityIntegralClosure C
          (ExactConstantExtension C N S)) :
        ExactConstantExtension C N S) := rfl

omit [DecidableEq C] [DecidableEq S] [DecidableEq (RatFunc S)] in
/-- Every infinity place is unramified in an exact extension of constants. -/
theorem exactConstantExtensionInfinityPlace_ramificationIdx_eq_one
    (Q : letI : Field (ExactConstantExtension C N S) :=
          exactConstantExtensionField C N S hExact
        letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
          exactConstantExtensionBaseAlgebra C (RatFunc C) N S
        FiniteExtensionInfinityPlace C (ExactConstantExtension C N S)) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : Algebra N (ExactConstantExtension C N S) :=
      exactConstantExtensionAlgebra C N S
    letI : SMul N (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module N (ExactConstantExtension C N S) := Algebra.toModule
    letI : IsScalarTower (RatFunc C) N
        (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseTower C (RatFunc C) N S
    infinityPlaceRelativeRamificationIdx C N
      (ExactConstantExtension C N S) Q = 1 := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : FiniteDimensional (RatFunc C)
      (ExactConstantExtension C N S) :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc C)
      (ExactConstantExtension C N S) :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionAlgebra C N S
  let : SMul N (ExactConstantExtension C N S) := Algebra.toSMul
  let : Module N (ExactConstantExtension C N S) := Algebra.toModule
  let : IsScalarTower (RatFunc C) N
      (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  let : IsGalois N (ExactConstantExtension C N S) :=
    exactConstantExtension_isGalois C N N S hExact
  let : Algebra (RatFuncInfinityIntegers C)
      (ExactConstantExtension C N S) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc C) (ExactConstantExtension C N S)).comp
        (algebraMap (RatFuncInfinityIntegers C) (RatFunc C)))
  let : SMul (RatFuncInfinityIntegers C)
      (ExactConstantExtension C N S) := Algebra.toSMul
  let : Module (RatFuncInfinityIntegers C)
      (ExactConstantExtension C N S) := Algebra.toModule
  let : IsScalarTower (RatFuncInfinityIntegers C) (RatFunc C)
      (ExactConstantExtension C N S) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra S (RatFuncInfinityIntegralClosure C
      (ExactConstantExtension C N S)) :=
    exactConstantExtensionInfinityIntegralClosureConstantAlgebra
      C S N hExact
  let : MulSemiringAction
      (ExactConstantExtension C N S ≃ₐ[N]
        ExactConstantExtension C N S)
      (RatFuncInfinityIntegralClosure C
        (ExactConstantExtension C N S)) :=
    infinityIntegralClosureGalAction C N (ExactConstantExtension C N S)
  rw [← infinityPlaceInertiaGroup_card_eq_ramificationIdx C N
    (ExactConstantExtension C N S) Q]
  have hsubsingleton :
      Subsingleton (infinityPlaceInertiaGroup C N
        (ExactConstantExtension C N S) Q) := by
    constructor
    intro g h
    apply Subtype.ext
    have inertiaElement_eq_one
        (u : infinityPlaceInertiaGroup C N
          (ExactConstantExtension C N S) Q) : u.1 = 1 := by
      have hquot : exactConstantExtensionConstantQuotient
          C N N S hExact u.1 = 1 := by
        apply AlgEquiv.ext
        intro s
        have hinertia := AddSubgroup.mem_inertia.mp u.2
          (algebraMap S (RatFuncInfinityIntegralClosure C
            (ExactConstantExtension C N S)) s)
        rw [exactConstantExtensionConstantQuotient_action_on_infinityNormalization
          C S N hExact] at hinertia
        let : Q.1.IsPrime := Q.2.1
        exact infinitySplitting_eq_of_algebraMap_sub_mem_prime S
          (RatFuncInfinityIntegralClosure C
            (ExactConstantExtension C N S)) Q.1 _ _ hinertia
      exact infinitySplitting_constantQuotient_eq_one_imp_eq_one
        C N S hExact u.1 hquot
    have hgOne := inertiaElement_eq_one g
    have hhOne := inertiaElement_eq_one h
    exact hgOne.trans hhOne.symm
  let := hsubsingleton
  exact Nat.card_unique

end InfinityRamification

end

end BGS.HasseWeil
