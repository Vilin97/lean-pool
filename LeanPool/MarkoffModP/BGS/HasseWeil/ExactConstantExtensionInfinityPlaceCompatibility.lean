/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantExtensionInfinityPlaceSplittingMultiplicity
public import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionInfinityDifferent

/-!
# Compatibility of infinity places with exact constant extension

The reciprocal affine normalization of an exact constant extension may be
viewed either over the original constants or over the extended constants.
This module proves that these two presentations commute with localization at
infinity. Consequently, the explicit upstairs infinity prime contracts to the
explicit downstairs infinity prime under the canonical algebra on infinity
normalizations.
-/

@[expose] public section

open scoped Polynomial TensorProduct

namespace BGS.HasseWeil

open BGS.CorvajaZannier

noncomputable section


variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]
  [Fintype C] [Finite S]

local instance infinityPlaceCompatibilityBaseConstantAlgebra : Algebra C N :=
  infinityConstantAlgebra C N

local instance infinityPlaceCompatibilityBaseReciprocalPolynomialAlgebra :
    Algebra C[X] N := infinityReciprocalPolynomialAlgebra C N

local instance infinityPlaceCompatibilityBaseConstantReciprocalTower :
    IsScalarTower C C[X] N := infinityReciprocalPolynomialTower C N

local instance infinityPlaceCompatibilityOldNormalizationConstantAlgebra :
    Algebra C (integralClosure C[X] N) :=
  RingHom.toAlgebra
    ((algebraMap C[X] (integralClosure C[X] N)).comp
      (algebraMap C C[X]))

local instance
    infinityPlaceCompatibilityOldNormalizationConstantPolynomialTower :
    IsScalarTower C C[X] (integralClosure C[X] N) :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance infinityPlaceCompatibilityCoefficientPolynomialAlgebra :
    Algebra C[X] S[X] := Polynomial.algebra C S

local instance infinityPlaceCompatibilityCoefficientPolynomialSMul :
    SMul C[X] S[X] := Algebra.toSMul

local instance infinityPlaceCompatibilityCoefficientPolynomialModule :
    Module C[X] S[X] := Algebra.toModule

local instance (priority := 10000)
    infinityPlaceCompatibilityDecidableEqBaseRatFunc :
    DecidableEq (RatFunc C) := infinityBridgeDecidableEqRatFuncConstants C

local instance (priority := 10000)
    infinityPlaceCompatibilityDecidableEqExtendedRatFunc :
    DecidableEq (RatFunc S) := infinityBridgeDecidableEqRatFuncConstants S

local instance (priority := 10000) infinityPlaceCompatibilityDecidableEqBase :
    DecidableEq C := infinityBridgeDecidableEqConstants C

local instance (priority := 10000)
    infinityPlaceCompatibilityDecidableEqExtended :
    DecidableEq S := infinityBridgeDecidableEqConstants S

private theorem
    infinityPlaceCompatibility_integralClosureAlgEquivOfAlgebraEq_coe
    {R L T : Type*} [CommRing R] [Field L] [CommRing T] [Algebra R T]
    (a b : Algebra R L) (h : a = b)
    (e : T ≃ₐ[R] @integralClosure R L _ _ a) (x : T) :
    let e' : T ≃ₐ[R] @integralClosure R L _ _ b := by
      rw [← h]
      exact e
    ((e' x : @integralClosure R L _ _ b) : L) =
      ((e x : @integralClosure R L _ _ a) : L) := by
  subst b
  rfl

omit [FiniteDimensional (RatFunc C) N] [Algebra.IsSeparable (RatFunc C) N] in
/-- The reciprocal affine normalization equivalence sends the old
normalization embedded in the right tensor factor to the same element of the
ambient exact constant extension. -/
private theorem
    exactConstantExtensionInfinityAffineNormalization_includeRight_coe
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (x : integralClosure C[X] N) :
    let E := ExactConstantExtension C N S
    letI : Field E := exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) E :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : Algebra S[X]
        (S ⊗[C] integralClosure C[X] N) :=
      polynomialTensorCancelTargetPolynomialExtensionAlgebra C S
        (integralClosure C[X] N)
    letI : Algebra S[X] E :=
      ratFuncExtensionReciprocalPolynomialAlgebra S E
    ((exactConstantExtensionInfinityAffineNormalizationAlgEquiv
        C S N hExact)
      (Algebra.TensorProduct.includeRight
        (R := C) (A := S) (B := integralClosure C[X] N) x) : E) =
      Algebra.TensorProduct.includeRight (R := C) (A := S) (B := N) x.1 := by
  let E := ExactConstantExtension C N S
  let : Field E := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc S) E :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : Algebra S[X]
      (S ⊗[C] integralClosure C[X] N) :=
    polynomialTensorCancelTargetPolynomialExtensionAlgebra C S
      (integralClosure C[X] N)
  let : Algebra S[X] E :=
    ratFuncExtensionReciprocalPolynomialAlgebra S E
  let a := polynomialTensorCancelTargetPolynomialExtensionAlgebra C S N
  let b := ratFuncExtensionReciprocalPolynomialAlgebra S E
  let h : a = b :=
    exactConstantExtensionReciprocalPolynomialAlgebra_eq C S N hExact
  let y := Algebra.TensorProduct.includeRight
    (R := C) (A := S) (B := integralClosure C[X] N) x
  have hTransport :=
    infinityPlaceCompatibility_integralClosureAlgEquivOfAlgebraEq_coe
      a b h (finiteFieldReciprocalNormalizationAlgEquiv C S N) y
  have hFinite :
      (((finiteFieldReciprocalNormalizationAlgEquiv C S N) y :
          @integralClosure S[X] E _ _ a) : E) =
        (1 : S) ⊗ₜ[C] (x : N) := by
    dsimp only [y, a]
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
  have hExactTransport :
      ((exactConstantExtensionInfinityAffineNormalizationAlgEquiv
          C S N hExact y : @integralClosure S[X] E _ _ b) : E) =
        (((finiteFieldReciprocalNormalizationAlgEquiv C S N) y :
          @integralClosure S[X] E _ _ a) : E) := by
    simpa only [a, b, h,
      exactConstantExtensionInfinityAffineNormalizationAlgEquiv] using
        hTransport
  exact hExactTransport.trans hFinite

omit [FiniteDimensional (RatFunc C) N] [Algebra.IsSeparable (RatFunc C) N] in
/-- The affine-to-infinity localization square commutes on elements of the
old reciprocal normalization. -/
private theorem exactConstantExtensionInfinityAffineLocalizationSquare_coe
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (x : integralClosure C[X] N) :
    let E := ExactConstantExtension C N S
    letI : Field E := exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) E :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra N E := exactConstantExtensionAlgebra C N S
    letI : Algebra (RatFunc S) E :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : Algebra S[X] E :=
      ratFuncExtensionReciprocalPolynomialAlgebra S E
    let R0 := integralClosure C[X] N
    let AS := integralClosure S[X] E
    let R2 := RatFuncInfinityIntegralClosure C N
    let B := RatFuncInfinityIntegralClosure S E
    letI : Algebra S[X] (S ⊗[C] R0) :=
      polynomialTensorCancelTargetPolynomialExtensionAlgebra C S R0
    let eAff := exactConstantExtensionInfinityAffineNormalizationAlgEquiv
      C S N hExact
    letI : Algebra R0 R2 :=
      ratFuncInfinityReciprocalIntegralClosureAlgebra C N
    letI : Algebra AS B :=
      ratFuncInfinityReciprocalIntegralClosureAlgebra S E
    letI : Algebra R2 B :=
      exactConstantExtensionInfinityNormalizationAlgebra C S N hExact
    (((algebraMap R2 B) ((algebraMap R0 R2) x) : B) : E) =
      (((algebraMap AS B)
        (eAff (Algebra.TensorProduct.includeRight
          (R := C) (A := S) (B := R0) x)) : B) : E) := by
  dsimp only
  let E := ExactConstantExtension C N S
  let R0 := integralClosure C[X] N
  let R2 := RatFuncInfinityIntegralClosure C N
  let : Field E := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) E :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : Algebra N E := exactConstantExtensionAlgebra C N S
  let : Algebra (RatFunc S) E :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : Algebra S[X] E :=
    ratFuncExtensionReciprocalPolynomialAlgebra S E
  let AS := integralClosure S[X] E
  let : Algebra S[X] (S ⊗[C] R0) :=
    polynomialTensorCancelTargetPolynomialExtensionAlgebra C S R0
  let B := RatFuncInfinityIntegralClosure S E
  let eAff := exactConstantExtensionInfinityAffineNormalizationAlgEquiv
    C S N hExact
  let : Algebra R0 R2 :=
    ratFuncInfinityReciprocalIntegralClosureAlgebra C N
  let : Algebra AS B :=
    ratFuncInfinityReciprocalIntegralClosureAlgebra S E
  let : Algebra R2 B :=
    exactConstantExtensionInfinityNormalizationAlgebra C S N hExact
  calc
    (((algebraMap R2 B) ((algebraMap R0 R2) x) : B) : E) =
        algebraMap N E x.1 := by
      change
        (((algebraMap R2 B (algebraMap R0 R2 x) : B) : E)) =
          algebraMap N E ((algebraMap R0 R2 x : R2) : N)
      exact exactConstantExtensionInfinityNormalizationAlgebra_coe
        C S N hExact (algebraMap R0 R2 x)
    _ = Algebra.TensorProduct.includeRight
          (R := C) (A := S) (B := N) x.1 := rfl
    _ = ((eAff (Algebra.TensorProduct.includeRight
          (R := C) (A := S) (B := R0) x) : AS) : E) := by
      exact
        (exactConstantExtensionInfinityAffineNormalization_includeRight_coe
          C S N hExact x).symm
    _ = (((algebraMap AS B)
          (eAff (Algebra.TensorProduct.includeRight
            (R := C) (A := S) (B := R0) x)) : B) : E) := rfl

omit [FiniteDimensional (RatFunc C) N] [Algebra.IsSeparable (RatFunc C) N] in
/-- The extended reciprocal affine prime contracts to the reciprocal affine
prime obtained from the old normalization. -/
private theorem exactConstantExtensionInfinityAffinePrime_under
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (q : ExactConstantExtensionPresentedInfinityPlace C S N) :
    let E := ExactConstantExtension C N S
    letI : Field E := exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) E :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : Algebra S[X] E :=
      ratFuncExtensionReciprocalPolynomialAlgebra S E
    let R0 := integralClosure C[X] N
    let AS := integralClosure S[X] E
    letI : Algebra S[X] (S ⊗[C] R0) :=
      polynomialTensorCancelTargetPolynomialExtensionAlgebra C S R0
    let eAff := exactConstantExtensionInfinityAffineNormalizationAlgEquiv
      C S N hExact
    let qA : IsDedekindDomain.HeightOneSpectrum AS :=
      heightOneSpectrumEquivOfAlgEquiv eAff q.1
    let oldToAffine : R0 →+* AS :=
      eAff.toRingEquiv.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := C) (A := S) (B := R0)).toRingHom
    letI : Algebra R0 AS := oldToAffine.toAlgebra
    qA.asIdeal.under R0 =
      exactConstantExtensionInfinityDownstairsIdeal C S N q.1 := by
  dsimp only
  let E := ExactConstantExtension C N S
  let R0 := integralClosure C[X] N
  let : Field E := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc S) E :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : Algebra S[X] E :=
    ratFuncExtensionReciprocalPolynomialAlgebra S E
  let AS := integralClosure S[X] E
  let : Algebra S[X] (S ⊗[C] R0) :=
    polynomialTensorCancelTargetPolynomialExtensionAlgebra C S R0
  let eAff := exactConstantExtensionInfinityAffineNormalizationAlgEquiv
    C S N hExact
  let qA : IsDedekindDomain.HeightOneSpectrum AS :=
    heightOneSpectrumEquivOfAlgEquiv eAff q.1
  let oldToAffine : R0 →+* AS :=
    eAff.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight
        (R := C) (A := S) (B := R0)).toRingHom
  let : Algebra R0 AS := oldToAffine.toAlgebra
  ext x
  change eAff
      (Algebra.TensorProduct.includeRight
        (R := C) (A := S) (B := R0) x) ∈ qA.asIdeal ↔
    Algebra.TensorProduct.includeRight
        (R := C) (A := S) (B := R0) x ∈ q.1.asIdeal
  rw [show qA.asIdeal = q.1.asIdeal.comap eAff.symm by rfl]
  change eAff.symm (eAff
      (Algebra.TensorProduct.includeRight
        (R := C) (A := S) (B := R0) x)) ∈ q.1.asIdeal ↔
    Algebra.TensorProduct.includeRight
        (R := C) (A := S) (B := R0) x ∈ q.1.asIdeal
  rw [eAff.symm_apply_apply]

omit [FiniteDimensional (RatFunc C) N] [Algebra.IsSeparable (RatFunc C) N]
  [FiniteDimensional C S] [IsGalois C S] [Fintype C] [Finite S] in
private theorem
    exactConstantExtensionDownstairsInfinityMappedIdeal_isMaximal
    (q : ExactConstantExtensionPresentedInfinityPlace C S N) :
    let R0 := integralClosure C[X] N
    let R2 := RatFuncInfinityIntegralClosure C N
    letI : Algebra R0 R2 :=
      ratFuncInfinityReciprocalIntegralClosureAlgebra C N
    (Ideal.map (algebraMap R0 R2)
      (exactConstantExtensionInfinityDownstairsIdeal C S N q.1)).IsMaximal := by
  dsimp only
  change (exactConstantExtensionDownstairsInfinityPlace
    C S N q.1 q.2).1.IsMaximal
  infer_instance

/-- The explicit upstairs infinity prime of an exact constant extension
contracts, through the canonical algebra on infinity normalizations, to its
explicit downstairs infinity prime. -/
theorem exactConstantExtensionUpstairsInfinityPlace_under
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (q : ExactConstantExtensionPresentedInfinityPlace C S N) :
    let E := ExactConstantExtension C N S
    letI : Field E := exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) E :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra (RatFunc S) E :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    let R2 := RatFuncInfinityIntegralClosure C N
    let B := RatFuncInfinityIntegralClosure S E
    letI : Algebra R2 B :=
      exactConstantExtensionInfinityNormalizationAlgebra C S N hExact
    (exactConstantExtensionUpstairsInfinityPlace
      C S N hExact q.1 q.2).1.under R2 =
      (exactConstantExtensionDownstairsInfinityPlace C S N q.1 q.2).1 := by
  dsimp only
  let E := ExactConstantExtension C N S
  let R0 := integralClosure C[X] N
  let R2 := RatFuncInfinityIntegralClosure C N
  let : Field E := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) E :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) E := Algebra.toSMul
  let : Module (RatFunc C) E := Algebra.toModule
  let : FiniteDimensional (RatFunc C) E :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc C) E :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra N E := exactConstantExtensionAlgebra C N S
  let : SMul N E := Algebra.toSMul
  let : Module N E := Algebra.toModule
  let : IsScalarTower (RatFunc C) N E :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  let : Algebra (RatFunc S) E :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : SMul (RatFunc S) E := Algebra.toSMul
  let : Module (RatFunc S) E := Algebra.toModule
  let : Algebra S[X] E :=
    ratFuncExtensionReciprocalPolynomialAlgebra S E
  let : SMul S[X] E := Algebra.toSMul
  let : Module S[X] E := Algebra.toModule
  let AS := integralClosure S[X] E
  let : Algebra S[X] (S ⊗[C] R0) :=
    polynomialTensorCancelTargetPolynomialExtensionAlgebra C S R0
  let : SMul S[X] (S ⊗[C] R0) := Algebra.toSMul
  let B := RatFuncInfinityIntegralClosure S E
  let eAff := exactConstantExtensionInfinityAffineNormalizationAlgEquiv
    C S N hExact
  let qA : IsDedekindDomain.HeightOneSpectrum AS :=
    heightOneSpectrumEquivOfAlgEquiv eAff q.1
  let p := exactConstantExtensionInfinityDownstairsIdeal C S N q.1
  let oldToAffine : R0 →+* AS :=
    eAff.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight
        (R := C) (A := S) (B := R0)).toRingHom
  let : Algebra R0 AS := oldToAffine.toAlgebra
  let : SMul R0 AS := Algebra.toSMul
  let : Algebra R0 R2 :=
    ratFuncInfinityReciprocalIntegralClosureAlgebra C N
  let : SMul R0 R2 := Algebra.toSMul
  let : Algebra AS B :=
    ratFuncInfinityReciprocalIntegralClosureAlgebra S E
  let : SMul AS B := Algebra.toSMul
  let : Algebra R2 B :=
    exactConstantExtensionInfinityNormalizationAlgebra C S N hExact
  let : SMul R2 B := Algebra.toSMul
  let : Module R2 B := Algebra.toModule
  let : Algebra R0 B :=
    RingHom.toAlgebra
      ((algebraMap R2 B).comp (algebraMap R0 R2))
  let : SMul R0 B := Algebra.toSMul
  let : IsScalarTower R0 R2 B :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R0 AS B :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change
        (((algebraMap R2 B) ((algebraMap R0 R2) x) : B) : E) =
          (((algebraMap AS B)
            (eAff (Algebra.TensorProduct.includeRight
              (R := C) (A := S) (B := R0) x)) : B) : E)
      exact exactConstantExtensionInfinityAffineLocalizationSquare_coe
        C S N hExact x)
  have hAffine : qA.asIdeal.under R0 = p := by
    exact exactConstantExtensionInfinityAffinePrime_under C S N hExact q
  have hMaxExplicit :=
    exactConstantExtensionDownstairsInfinityMappedIdeal_isMaximal C S N q
  have hUpstairsNe :=
    (exactConstantExtensionUpstairsInfinityPlace
      C S N hExact q.1 q.2).2.1.ne_top
  change (Ideal.map (algebraMap AS B) qA.asIdeal).under R2 =
    Ideal.map (algebraMap R0 R2) p
  rw [Ideal.under_map_eq_map_under
    (A := R0) (B := AS) (C := R2) (D := B) qA.asIdeal
    (by rw [hAffine]; exact hMaxExplicit)
    (by
      change (exactConstantExtensionUpstairsInfinityPlace
        C S N hExact q.1 q.2).1 ≠ ⊤
      exact hUpstairsNe), hAffine]

end

end BGS.HasseWeil
