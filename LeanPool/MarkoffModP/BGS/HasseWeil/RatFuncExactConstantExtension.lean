/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionAutomorphism
import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteFieldConstantExtensionNormalization
import LeanPool.MarkoffModP.BGS.HasseWeil.FinitePlaceNormalizationTransport
import LeanPool.MarkoffModP.BGS.HasseWeil.PolynomialTensorCancel
import LeanPool.MarkoffModP.BGS.HasseWeil.RatFuncConstantExtension
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Flat.Stability

/-!
# The rational-function field in an exact constant extension

Let `C` be the exact constant field of a function field `N / C(X)`, and let
`S / C` be a finite Galois extension.  The tensor product `S ⊗[C] N` is then
a field.  This file constructs its canonical `S(X)`-algebra structure and
proves that it is compatible with both copies of `C(X)`.

For finite Galois `N / C(X)`, the tensor product is finite and separable over
`S(X)`.  The final equivalence identifies the polynomial normalization after
constant extension with the normalization used by the project's finite-place
model.
-/

open scoped Polynomial TensorProduct nonZeroDivisors

namespace BGS.HasseWeil

open BGS.CorvajaZannier

noncomputable section


variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Algebra (RatFunc C) N] [Algebra C S]
  [FiniteDimensional C S] [IsGalois C S]

local instance constantAlgebra : Algebra C N :=
  RingHom.toAlgebra ((algebraMap (RatFunc C) N).comp
    (algebraMap C (RatFunc C)))

-- Save these instances before installing the competing `C[X]`-algebra on `N`.
@[reducible] private noncomputable def canonicalRatFuncPolynomialAlgebra :
    Algebra C[X] (RatFunc C) := inferInstance

private theorem canonicalRatFuncFractionRing :
    letI := canonicalRatFuncPolynomialAlgebra C
    IsFractionRing C[X] (RatFunc C) := by
  let := canonicalRatFuncPolynomialAlgebra C
  infer_instance

local instance polynomialAlgebra : Algebra C[X] N :=
  RingHom.toAlgebra ((algebraMap (RatFunc C) N).comp
    (algebraMap C[X] (RatFunc C)))

local instance ratFuncCoefficientPolynomialAlgebra : Algebra C[X] S[X] :=
  Polynomial.algebra C S

local instance coefficientPolynomialModule : Module C[X] S[X] :=
  Algebra.toModule

local instance coefficientPolynomialFlat : Module.Flat C[X] S[X] := by
  let : Module.Flat C[X] (TensorProduct C C[X] S) := inferInstance
  exact Module.Flat.of_linearEquiv
    (Algebra.IsPushout.equiv C C[X] S S[X]).symm.toLinearEquiv

local instance constantPolynomialTower : IsScalarTower C C[X] N :=
  IsScalarTower.of_algebraMap_eq' (by
    ext c
    change algebraMap (RatFunc C) N (algebraMap C (RatFunc C) c) =
      algebraMap (RatFunc C) N
        (algebraMap C[X] (RatFunc C) (Polynomial.C c))
    congr 1)

private theorem polynomialAlgebraMap_injective :
    Function.Injective (algebraMap C[X] N) := by
  change Function.Injective
    ((algebraMap (RatFunc C) N).comp (algebraMap C[X] (RatFunc C)))
  exact (algebraMap (RatFunc C) N).injective.comp
    (RatFunc.algebraMap_injective C)

local instance targetPolynomialAlgebra :
    Algebra S[X] (ExactConstantExtension C N S) :=
  polynomialTensorCancelTargetPolynomialExtensionAlgebra C S N

omit [FiniteDimensional C S] in
private theorem targetPolynomialAlgebraMap_injective :
    Function.Injective
      (algebraMap S[X] (ExactConstantExtension C N S)) := by
  intro p q hpq
  let e := polynomialTensorCancelOverCoefficientPolynomial C S N
  have hleft :
      (Algebra.TensorProduct.includeLeft :
        S[X] →ₐ[S[X]] TensorProduct C[X] S[X] N) p =
      (Algebra.TensorProduct.includeLeft :
        S[X] →ₐ[S[X]] TensorProduct C[X] S[X] N) q := by
    apply e.injective
    calc
      e (Algebra.TensorProduct.includeLeft p) =
          algebraMap S[X] (ExactConstantExtension C N S) p := e.commutes p
      _ = algebraMap S[X] (ExactConstantExtension C N S) q := hpq
      _ = e (Algebra.TensorProduct.includeLeft q) := (e.commutes q).symm
  exact Algebra.TensorProduct.includeLeft_injective
    (polynomialAlgebraMap_injective C N) hleft

omit [FiniteDimensional C S] [IsGalois C S] in
private theorem targetEvaluation_coefficientPolynomial (p : C[X]) :
    Polynomial.aeval (polynomialTensorCancelEvaluationPoint C S N)
        (algebraMap C[X] S[X] p) =
      (1 : S) ⊗ₜ[C] (algebraMap C[X] N p) := by
  let e := polynomialTensorCancelOverCoefficientPolynomial C S N
  have hsource :
      (algebraMap C[X] S[X] p) ⊗ₜ[C[X]] (1 : N) =
        (1 : S[X]) ⊗ₜ[C[X]] (algebraMap C[X] N p) := by
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul p
  calc
    Polynomial.aeval (polynomialTensorCancelEvaluationPoint C S N)
        (algebraMap C[X] S[X] p) =
        e ((algebraMap C[X] S[X] p) ⊗ₜ[C[X]] (1 : N)) := by
      exact (e.commutes (algebraMap C[X] S[X] p)).symm
    _ = e ((1 : S[X]) ⊗ₜ[C[X]] (algebraMap C[X] N p)) :=
      congrArg e hsource
    _ = (1 : S) ⊗ₜ[C] (algebraMap C[X] N p) := by
      rw [polynomialTensorCancelOverCoefficientPolynomial_apply,
        polynomialTensorCancel_tmul]
      simp

section Exact

variable (hExact : algebraicClosure C N =
  (⊥ : IntermediateField C N))

/-- The canonical copy of `S(X)` inside the exact constant extension,
obtained by extending the evaluated `S[X]`-algebra map. -/
noncomputable def ratFuncToExactConstantExtension :
    RatFunc S →ₐ[S] ExactConstantExtension C N S := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let hpoly := targetPolynomialAlgebraMap_injective C S N
  exact RatFunc.liftAlgHom
    (Polynomial.aeval
      (polynomialTensorCancelEvaluationPoint C S N))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hpoly)

theorem ratFuncToExactConstantExtension_injective :
    Function.Injective
      (ratFuncToExactConstantExtension C S N hExact) := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let hpoly := targetPolynomialAlgebraMap_injective C S N
  exact RatFunc.liftAlgHom_injective
    (Polynomial.aeval
      (polynomialTensorCancelEvaluationPoint C S N)) hpoly

theorem ratFuncToExactConstantExtension_algebraMap (p : S[X]) :
    ratFuncToExactConstantExtension C S N hExact
        (algebraMap S[X] (RatFunc S) p) =
      Polynomial.aeval
        (polynomialTensorCancelEvaluationPoint C S N) p := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  change RatFunc.liftAlgHom _ _ (algebraMap S[X] (RatFunc S) p) = _
  exact RatFunc.liftRingHom_algebraMap _ _ p

theorem ratFuncToExactConstantExtension_X :
    ratFuncToExactConstantExtension C S N hExact RatFunc.X =
      polynomialTensorCancelEvaluationPoint C S N := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  calc
    ratFuncToExactConstantExtension C S N hExact RatFunc.X =
        ratFuncToExactConstantExtension C S N hExact
          (algebraMap S[X] (RatFunc S) Polynomial.X) := by
      apply congrArg (ratFuncToExactConstantExtension C S N hExact)
      exact (RatFunc.algebraMap_X (K := S)).symm
    _ = Polynomial.aeval
        (polynomialTensorCancelEvaluationPoint C S N) Polynomial.X :=
      ratFuncToExactConstantExtension_algebraMap C S N hExact Polynomial.X
    _ = polynomialTensorCancelEvaluationPoint C S N := by
      exact Polynomial.aeval_X _

/-- The algebra structure induced by the canonical copy of `S(X)`. -/
@[reducible] noncomputable def ratFuncExactConstantExtensionAlgebra :
    Algebra (RatFunc S) (ExactConstantExtension C N S) :=
  (ratFuncToExactConstantExtension C S N hExact).toAlgebra

/-- The copy of `C(X)` obtained through coefficient extension to `S(X)`
agrees with the copy coming from the right tensor factor `N`. -/
theorem rationalBase_algebraMap_eq :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (RatFunc S) :=
      ratFuncCoefficientAlgebra C S
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    algebraMap (RatFunc C) (ExactConstantExtension C N S) =
      (algebraMap (RatFunc S) (ExactConstantExtension C N S)).comp
        (algebraMap (RatFunc C) (RatFunc S)) := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra C[X] (RatFunc C) := canonicalRatFuncPolynomialAlgebra C
  let : IsFractionRing C[X] (RatFunc C) := canonicalRatFuncFractionRing C
  let : Algebra (RatFunc C) (RatFunc S) :=
    ratFuncCoefficientAlgebra C S
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  apply IsFractionRing.ringHom_ext (A := C[X])
  intro p
  change
    (1 : S) ⊗ₜ[C]
        algebraMap (RatFunc C) N (algebraMap C[X] (RatFunc C) p) =
      ratFuncToExactConstantExtension C S N hExact
        (ratFuncCoefficientAlgHom C S
          (algebraMap C[X] (RatFunc C) p))
  rw [ratFuncCoefficientAlgHom_algebraMap]
  change
    (1 : S) ⊗ₜ[C]
        algebraMap (RatFunc C) N (algebraMap C[X] (RatFunc C) p) =
      ratFuncToExactConstantExtension C S N hExact
        (RatFunc.mk (algebraMap C[X] S[X] p) 1)
  rw [RatFunc.mk_eq_localization_mk _ one_ne_zero]
  change _ = RatFunc.liftAlgHom _ _
    (RatFunc.ofFractionRing
      (Localization.mk (algebraMap C[X] S[X] p) (1 : S[X]⁰)))
  rw [RatFunc.liftAlgHom_apply_ofFractionRing_mk]
  have hone :
      Polynomial.aeval (polynomialTensorCancelEvaluationPoint C S N)
          ((1 : S[X]⁰) : S[X]) = 1 := by
    exact map_one _
  rw [hone, div_one]
  change (1 : S) ⊗ₜ[C] (algebraMap C[X] N p) = _
  exact (targetEvaluation_coefficientPolynomial C S N p).symm

/-- The rational-function coefficient extension and the exact constant
extension form a scalar tower. -/
theorem rationalBase_scalarTower :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (RatFunc S) :=
      ratFuncCoefficientAlgebra C S
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : SMul (RatFunc C) (RatFunc S) := Algebra.toSMul
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) := Algebra.toSMul
    letI : SMul (RatFunc S) (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module (RatFunc S) (ExactConstantExtension C N S) :=
      Algebra.toModule
    IsScalarTower (RatFunc C) (RatFunc S)
      (ExactConstantExtension C N S) := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) (RatFunc S) :=
    ratFuncCoefficientAlgebra C S
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : SMul (RatFunc C) (RatFunc S) := Algebra.toSMul
  let : SMul (RatFunc C) (ExactConstantExtension C N S) := Algebra.toSMul
  let : SMul (RatFunc S) (ExactConstantExtension C N S) := Algebra.toSMul
  let : Module (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : Module (RatFunc S) (ExactConstantExtension C N S) :=
    Algebra.toModule
  exact IsScalarTower.of_algebraMap_eq'
    (rationalBase_algebraMap_eq C S N hExact)

section FiniteTop

variable [FiniteDimensional (RatFunc C) N]

/-- If `N / C(X)` is finite, then the exact constant extension is finite over
the enlarged rational function field `S(X)`. -/
theorem finiteDimensional_over_extendedRatFunc :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (RatFunc S) :=
      ratFuncCoefficientAlgebra C S
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : SMul (RatFunc C) (RatFunc S) := Algebra.toSMul
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) := Algebra.toSMul
    letI : SMul (RatFunc S) (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module (RatFunc S) (ExactConstantExtension C N S) :=
      Algebra.toModule
    FiniteDimensional (RatFunc S) (ExactConstantExtension C N S) := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) (RatFunc S) :=
    ratFuncCoefficientAlgebra C S
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : SMul (RatFunc C) (RatFunc S) := Algebra.toSMul
  let : SMul (RatFunc C) (ExactConstantExtension C N S) := Algebra.toSMul
  let : SMul (RatFunc S) (ExactConstantExtension C N S) := Algebra.toSMul
  let : Module (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : Module (RatFunc S) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : IsScalarTower (RatFunc C) (RatFunc S)
      (ExactConstantExtension C N S) :=
    rationalBase_scalarTower C S N hExact
  let : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionAlgebra C N S
  let : SMul N (ExactConstantExtension C N S) := Algebra.toSMul
  let : Module N (ExactConstantExtension C N S) := Algebra.toModule
  let : IsScalarTower (RatFunc C) N (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  let e := exactConstantExtensionLinearEquiv C N S
  let : Module.Finite N (N ⊗[C] S) :=
    Module.Finite.base_change C N S
  let : Module.Finite N (ExactConstantExtension C N S) :=
    Module.Finite.equiv e
  let : Module.Finite (RatFunc C) (ExactConstantExtension C N S) :=
    Module.Finite.trans N (ExactConstantExtension C N S)
  exact Module.Finite.of_restrictScalars_finite
    (RatFunc C) (RatFunc S) (ExactConstantExtension C N S)

section SeparableTop

variable [Algebra.IsSeparable (RatFunc C) N]

include hExact

/-- For a finite separable `N / C(X)`, the exact constant extension remains
separable over the original rational function field `C(X)`. -/
theorem isSeparable_exactConstantExtension_over_baseRatFunc :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    Algebra.IsSeparable (RatFunc C) (ExactConstantExtension C N S) := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : IsScalarTower C (RatFunc C) N :=
    IsScalarTower.of_algebraMap_eq' rfl
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
  exact Algebra.IsSeparable.trans
    (RatFunc C) N (ExactConstantExtension C N S)

/-- For a finite separable `N / C(X)`, the exact constant extension is separable
over the enlarged rational function field `S(X)`. -/
theorem isSeparable_over_extendedRatFunc :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (RatFunc S) :=
      ratFuncCoefficientAlgebra C S
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : SMul (RatFunc C) (RatFunc S) := Algebra.toSMul
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) := Algebra.toSMul
    letI : SMul (RatFunc S) (ExactConstantExtension C N S) := Algebra.toSMul
    Algebra.IsSeparable (RatFunc S) (ExactConstantExtension C N S) := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : IsScalarTower C (RatFunc C) N :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra (RatFunc C) (RatFunc S) :=
    ratFuncCoefficientAlgebra C S
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : SMul (RatFunc C) (RatFunc S) := Algebra.toSMul
  let : SMul (RatFunc C) (ExactConstantExtension C N S) := Algebra.toSMul
  let : SMul (RatFunc S) (ExactConstantExtension C N S) := Algebra.toSMul
  let : IsScalarTower (RatFunc C) (RatFunc S)
      (ExactConstantExtension C N S) :=
    rationalBase_scalarTower C S N hExact
  let : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionAlgebra C N S
  let : SMul N (ExactConstantExtension C N S) := Algebra.toSMul
  let : Module N (ExactConstantExtension C N S) := Algebra.toModule
  let : IsScalarTower (RatFunc C) N
      (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  let : IsGalois N (ExactConstantExtension C N S) :=
    exactConstantExtension_isGalois C N N S hExact
  let : Algebra.IsSeparable (RatFunc C) (ExactConstantExtension C N S) :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  exact Algebra.isSeparable_tower_top_of_isSeparable
    (RatFunc C) (RatFunc S) (ExactConstantExtension C N S)

end SeparableTop

end FiniteTop

/-- The constant field, its rational function field, and the exact constant
extension form a scalar tower. -/
theorem scalarTower_constant_ratFunc_exactConstantExtension :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : SMul (RatFunc S) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    IsScalarTower S (RatFunc S) (ExactConstantExtension C N S) := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : SMul (RatFunc S) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  apply IsScalarTower.of_algebraMap_eq'
  ext s
  exact (ratFuncToExactConstantExtension C S N hExact).commutes s |>.symm

section Normalization

variable [Fintype C] [Finite S]

/-- The polynomial normalization obtained after extending the constants is
the normalization used by the rational-function finite-place model. -/
noncomputable def exactConstantExtensionNormalizationAlgEquiv :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : Algebra S[X] (S ⊗[C] integralClosure C[X] N) :=
      constantExtensionNormalizationTensorPolynomialAlgebra C S N
    S ⊗[C] integralClosure C[X] N ≃ₐ[S[X]]
      RatFuncFiniteIntegralClosure S (ExactConstantExtension C N S) := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  letI : Algebra S[X] (S ⊗[C] integralClosure C[X] N) :=
    constantExtensionNormalizationTensorPolynomialAlgebra C S N
  exact normalizationAlgEquivRatFuncFiniteOfAlgebraMap
    S (ExactConstantExtension C N S)
    (S ⊗[C] integralClosure C[X] N)
    (constantExtensionTensorPolynomialAlgebra C S N)
    (finiteFieldConstantExtensionIntegralClosurePolynomialAlgEquiv C S N)
    (ratFuncToExactConstantExtension_algebraMap C S N hExact)

end Normalization

end Exact

end

end BGS.HasseWeil
