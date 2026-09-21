/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.RatFuncExactConstantExtension
import LeanPool.MarkoffModP.BGS.HasseWeil.RatFuncInfinityLocalization

/-!
# Normalization at infinity in an exact constant extension

The affine coordinate at infinity is the reciprocal variable `X⁻¹`.  This
file checks that the copy of `S(X)` in the exact constant extension
`S ⊗[C] N` sends that reciprocal variable to the tensor extension of the
reciprocal coordinate on `N`.

Smooth base change and polynomial tensor cancellation then identify the
constant extension of the reciprocal affine normalization with the
reciprocal affine normalization over `S`.  Localizing away from the origin
gives a ring equivalence with the actual infinity integral closure.  Thus no
comparison with the finite-place coordinate is used or assumed.
-/

open scoped Polynomial TensorProduct

namespace BGS.HasseWeil

open BGS.CorvajaZannier

noncomputable section


variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Algebra (RatFunc C) N] [Algebra C S]
  [FiniteDimensional C S] [IsGalois C S]

local instance infinityDecidableEqBase : DecidableEq C := Classical.decEq C
local instance infinityDecidableEqRatFuncBase : DecidableEq (RatFunc C) :=
  Classical.decEq (RatFunc C)
local instance infinityDecidableEqConstants : DecidableEq S := Classical.decEq S
local instance infinityDecidableEqRatFuncConstants : DecidableEq (RatFunc S) :=
  Classical.decEq (RatFunc S)

local instance infinityConstantAlgebra : Algebra C N :=
  RingHom.toAlgebra ((algebraMap (RatFunc C) N).comp
    (algebraMap C (RatFunc C)))

local instance infinityReciprocalPolynomialAlgebra : Algebra C[X] N :=
  ratFuncExtensionReciprocalPolynomialAlgebra C N

local instance infinityReciprocalPolynomialTower :
    IsScalarTower C C[X] N := by
  exact IsScalarTower.of_algebraMap_eq' (by
    ext c
    change algebraMap (RatFunc C) N (algebraMap C (RatFunc C) c) =
      algebraMap (RatFunc C) N
        (((reciprocalPolynomialRingHom C (Polynomial.C c) :
          RatFuncInfinityIntegers C) : RatFunc C))
    rw [reciprocalPolynomialRingHom_coe]
    simp)

local instance infinityReciprocalNormalizationConstantAlgebra :
    Algebra C (integralClosure C[X] N) :=
  RingHom.toAlgebra
    ((algebraMap C[X] (integralClosure C[X] N)).comp
      (algebraMap C C[X]))

local instance infinityReciprocalNormalizationPolynomialTower :
    IsScalarTower C C[X] (integralClosure C[X] N) :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance infinityCoefficientPolynomialAlgebra : Algebra C[X] S[X] :=
  Polynomial.algebra C S

local instance infinitySpanXPrime :
    (Ideal.span ({Polynomial.X} : Set S[X])).IsPrime :=
  (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X

variable (hExact : algebraicClosure C N =
  (⊥ : IntermediateField C N))

/-- The reciprocal coordinate in the exact constant extension is the tensor
extension of the reciprocal coordinate on `N`. -/
theorem ratFuncToExactConstantExtension_reciprocal_X :
    ratFuncToExactConstantExtension C S N hExact (1 / RatFunc.X) =
      polynomialTensorCancelEvaluationPoint C S N := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  rw [one_div]
  have hrecip : polynomialTensorCancelEvaluationPoint C S N =
      (Algebra.TensorProduct.includeRight :
        N →ₐ[C] ExactConstantExtension C N S)
        (algebraMap (RatFunc C) N (RatFunc.X⁻¹)) := by
    unfold polynomialTensorCancelEvaluationPoint
    congr 1
    change algebraMap (RatFunc C) N
        (((reciprocalPolynomialRingHom C Polynomial.X :
          RatFuncInfinityIntegers C) : RatFunc C)) =
      algebraMap (RatFunc C) N (RatFunc.X⁻¹)
    rw [reciprocalPolynomialRingHom_coe]
    simp
  rw [hrecip]
  rw [map_inv₀, map_inv₀, map_inv₀,
    ratFuncToExactConstantExtension_X]
  rfl

/-- The tensor-product polynomial action in the reciprocal coordinate is
exactly the reciprocal polynomial action induced from `S(X)`. -/
theorem exactConstantExtensionReciprocalPolynomialAlgebra_eq :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    polynomialTensorCancelTargetPolynomialExtensionAlgebra C S N =
      ratFuncExtensionReciprocalPolynomialAlgebra S
        (ExactConstantExtension C N S) := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
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

section FiniteConstants

variable [Fintype C] [Finite S]

/-- Smooth base change in the reciprocal coordinate, before identifying the
target polynomial action with the one induced from `S(X)`. -/
noncomputable def finiteFieldReciprocalNormalizationAlgEquiv :
    letI : Algebra S[X]
        (S ⊗[C] integralClosure C[X] N) :=
      polynomialTensorCancelTargetPolynomialExtensionAlgebra C S
        (integralClosure C[X] N)
    letI : Algebra S[X] (ExactConstantExtension C N S) :=
      polynomialTensorCancelTargetPolynomialExtensionAlgebra C S N
    S ⊗[C] integralClosure C[X] N ≃ₐ[S[X]]
      integralClosure S[X] (ExactConstantExtension C N S) := by
  letI : Algebra S[X]
      (S ⊗[C] integralClosure C[X] N) :=
    polynomialTensorCancelTargetPolynomialExtensionAlgebra C S
      (integralClosure C[X] N)
  letI : Algebra S[X] (ExactConstantExtension C N S) :=
    polynomialTensorCancelTargetPolynomialExtensionAlgebra C S N
  exact (polynomialTensorCancelOverCoefficientPolynomial C S
        (integralClosure C[X] N)).symm |>.trans
      (finiteFieldPolynomialIntegralClosureBaseChangeAlgEquiv C S N) |>.trans
      (polynomialTensorCancelOverCoefficientPolynomial C S N).mapIntegralClosure

/-- The constant extension of the reciprocal affine normalization is the
actual reciprocal affine normalization of the exact constant extension. -/
noncomputable def exactConstantExtensionInfinityAffineNormalizationAlgEquiv :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : Algebra S[X]
        (S ⊗[C] integralClosure C[X] N) :=
      polynomialTensorCancelTargetPolynomialExtensionAlgebra C S
        (integralClosure C[X] N)
    letI : Algebra S[X] (ExactConstantExtension C N S) :=
      ratFuncExtensionReciprocalPolynomialAlgebra S
        (ExactConstantExtension C N S)
    S ⊗[C] integralClosure C[X] N ≃ₐ[S[X]]
      integralClosure S[X] (ExactConstantExtension C N S) := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  letI : Algebra S[X]
      (S ⊗[C] integralClosure C[X] N) :=
    polynomialTensorCancelTargetPolynomialExtensionAlgebra C S
      (integralClosure C[X] N)
  letI : Algebra S[X] (ExactConstantExtension C N S) :=
    ratFuncExtensionReciprocalPolynomialAlgebra S
      (ExactConstantExtension C N S)
  have h := exactConstantExtensionReciprocalPolynomialAlgebra_eq
    C S N hExact
  rw [← h]
  exact finiteFieldReciprocalNormalizationAlgEquiv C S N

/-- The reciprocal affine normalization equivalence carries the natural
localization set away from `X = 0` to the corresponding target set. -/
theorem exactConstantExtensionInfinityAffineNormalization_map_primeCompl :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : Algebra S[X]
        (S ⊗[C] integralClosure C[X] N) :=
      polynomialTensorCancelTargetPolynomialExtensionAlgebra C S
        (integralClosure C[X] N)
    letI : Algebra S[X] (ExactConstantExtension C N S) :=
      ratFuncExtensionReciprocalPolynomialAlgebra S
        (ExactConstantExtension C N S)
    let e := exactConstantExtensionInfinityAffineNormalizationAlgEquiv
      C S N hExact
    Submonoid.map e
        (Algebra.algebraMapSubmonoid
          (S ⊗[C] integralClosure C[X] N)
          (Ideal.span ({Polynomial.X} : Set S[X])).primeCompl) =
      Algebra.algebraMapSubmonoid
        (integralClosure S[X] (ExactConstantExtension C N S))
        (Ideal.span ({Polynomial.X} : Set S[X])).primeCompl := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  letI : Algebra S[X]
      (S ⊗[C] integralClosure C[X] N) :=
    polynomialTensorCancelTargetPolynomialExtensionAlgebra C S
      (integralClosure C[X] N)
  letI : Algebra S[X] (ExactConstantExtension C N S) :=
    ratFuncExtensionReciprocalPolynomialAlgebra S
      (ExactConstantExtension C N S)
  let e := exactConstantExtensionInfinityAffineNormalizationAlgEquiv
    C S N hExact
  dsimp only
  unfold Algebra.algebraMapSubmonoid
  ext x
  constructor
  · rintro ⟨y, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, (e.commutes p).symm⟩
  · rintro ⟨p, hp, rfl⟩
    refine ⟨algebraMap S[X]
      (S ⊗[C] integralClosure C[X] N) p, ⟨p, hp, rfl⟩, ?_⟩
    exact e.commutes p

/-- Localizing the constant extension of the reciprocal normalization gives
the actual integral closure of the infinity valuation ring in the exact
constant extension.  As a ring equivalence, this directly transports prime
ideals, local rings, and residue rings. -/
noncomputable def exactConstantExtensionInfinityNormalizationLocalizationRingEquiv :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : Algebra S[X]
        (S ⊗[C] integralClosure C[X] N) :=
      polynomialTensorCancelTargetPolynomialExtensionAlgebra C S
        (integralClosure C[X] N)
    Localization
        (Algebra.algebraMapSubmonoid
          (S ⊗[C] integralClosure C[X] N)
          (Ideal.span ({Polynomial.X} : Set S[X])).primeCompl) ≃+*
      RatFuncInfinityIntegralClosure S
        (ExactConstantExtension C N S) := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  letI : Algebra S[X]
      (S ⊗[C] integralClosure C[X] N) :=
    polynomialTensorCancelTargetPolynomialExtensionAlgebra C S
      (integralClosure C[X] N)
  letI : Algebra S[X] (ExactConstantExtension C N S) :=
    ratFuncExtensionReciprocalPolynomialAlgebra S
      (ExactConstantExtension C N S)
  let R := S ⊗[C] integralClosure C[X] N
  let M := Algebra.algebraMapSubmonoid R
    (Ideal.span ({Polynomial.X} : Set S[X])).primeCompl
  let Tm := Algebra.algebraMapSubmonoid
    (integralClosure S[X] (ExactConstantExtension C N S))
    (Ideal.span ({Polynomial.X} : Set S[X])).primeCompl
  let L := Localization M
  letI : Algebra
      (integralClosure S[X] (ExactConstantExtension C N S))
      (RatFuncInfinityIntegralClosure S
        (ExactConstantExtension C N S)) :=
    ratFuncInfinityReciprocalIntegralClosureAlgebra S
      (ExactConstantExtension C N S)
  letI : IsLocalization Tm
      (RatFuncInfinityIntegralClosure S
        (ExactConstantExtension C N S)) :=
    ratFuncInfinityIntegralClosure_isLocalization_reciprocal S
      (ExactConstantExtension C N S)
  let e := exactConstantExtensionInfinityAffineNormalizationAlgEquiv
    C S N hExact
  have hmap : Submonoid.map e M = Tm :=
    exactConstantExtensionInfinityAffineNormalization_map_primeCompl
      C S N hExact
  exact IsLocalization.ringEquivOfRingEquiv L
    (RatFuncInfinityIntegralClosure S
      (ExactConstantExtension C N S)) e.toRingEquiv hmap

end FiniteConstants

end

end BGS.HasseWeil
