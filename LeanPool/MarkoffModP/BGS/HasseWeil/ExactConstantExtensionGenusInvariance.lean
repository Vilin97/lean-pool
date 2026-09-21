/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionGenusDegree
import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionTotalDifferentDegree

/-!
# Genus invariance under exact constant extension

Equality of the presented total-different multiplicities preserves the total
different degree.  Riemann--Hurwitz and preservation of the rational-function
extension degree then identify the two chart genera.
-/

open scoped Polynomial

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier


variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Fintype C] [Finite S]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance (priority := 10000)
    exactConstantGenusInvarianceConstantsDecidableEq
    (K : Type*) [Field K] : DecidableEq K :=
  infinityBridgeDecidableEqConstants K

local instance (priority := 10001)
    exactConstantGenusInvarianceRatFuncDecidableEq
    (K : Type*) [Field K] : DecidableEq (RatFunc K) :=
  infinityBridgeDecidableEqRatFuncConstants K

local instance exactConstantGenusInvarianceBaseConstantAlgebra : Algebra C N :=
  bridgeBaseConstantAlgebra C N

local instance exactConstantGenusInvarianceBaseConstantTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance (priority := 10)
    exactConstantGenusInvarianceBasePolynomialAlgebra : Algebra C[X] N :=
  RingHom.toAlgebra ((algebraMap (RatFunc C) N).comp
    (algebraMap C[X] (RatFunc C)))

local instance exactConstantGenusInvarianceBasePolynomialTower :
    IsScalarTower C[X] (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance exactConstantGenusInvarianceBaseConstantPolynomialTower :
    IsScalarTower C C[X] N :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Exact finite extension of constants preserves chart genus once the
pointwise total-different multiplicity compatibility is known. -/
theorem exactConstantExtension_chart_genus_eq_of_presentedMultiplicity
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N)) :
    let E := ExactConstantExtension C N S
    letI : Field E := exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) E :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) E := Algebra.toSMul
    letI : Module (RatFunc C) E := Algebra.toModule
    letI : FiniteDimensional (RatFunc C) E :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc
        C S N hExact
    letI : Algebra.IsSeparable (RatFunc C) E :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : Algebra (RatFunc S) E :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : SMul (RatFunc S) E := Algebra.toSMul
    letI : Module (RatFunc S) E := Algebra.toModule
    letI : FiniteDimensional (RatFunc S) E :=
      finiteDimensional_over_extendedRatFunc C S N hExact
    letI : Algebra.IsSeparable (RatFunc S) E :=
      isSeparable_over_extendedRatFunc C S N hExact
    let extendedConstantAlgebra : Algebra S E :=
      RingHom.toAlgebra ((algebraMap (RatFunc S) E).comp
        (algebraMap S (RatFunc S)))
    let tensorConstantAlgebra : Algebra S E :=
      Algebra.TensorProduct.leftAlgebra
    let hconstantMap : ∀ s : S,
        (@algebraMap S E _ _ extendedConstantAlgebra) s =
          (@algebraMap S E _ _ tensorConstantAlgebra) s := by
      intro s
      exact (ratFuncToExactConstantExtension C S N hExact).commutes s
    let htensorPolynomialMap : ∀ s : S,
        (@algebraMap S E _ _ tensorConstantAlgebra) s =
          (@algebraMap S[X] E _ _
            (constantExtensionTensorPolynomialAlgebra C S N))
              (algebraMap S S[X] s) := by
      intro s
      change (s ⊗ₜ[C] (1 : N)) =
        Polynomial.aeval
          (polynomialTensorCancelEvaluationPoint C S N)
          (Polynomial.C s)
      simp
    letI : Algebra S E := extendedConstantAlgebra
    letI : SMul S E := Algebra.toSMul
    letI : Algebra S[X] E :=
      constantExtensionTensorPolynomialAlgebra C S N
    letI : SMul S[X] E := Algebra.toSMul
    letI : IsScalarTower S[X] (RatFunc S) E :=
      IsScalarTower.of_algebraMap_eq' (by
        apply DFunLike.ext _ _
        intro p
        change algebraMap S[X] E p =
          ratFuncToExactConstantExtension C S N hExact
            (algebraMap S[X] (RatFunc S) p)
        exact
          (ratFuncToExactConstantExtension_algebraMap C S N hExact p).symm)
    letI : IsScalarTower S S[X] E :=
      IsScalarTower.of_algebraMap_eq' (by
        apply DFunLike.ext _ _
        intro s
        exact (hconstantMap s).trans (htensorPolynomialMap s))
    letI : FunctionField.IsFullConstantField C N :=
      (FunctionField.isFullConstantField_iff_algebraicClosure_eq_bot C N).2
        hExact
    letI : FunctionField.IsFullConstantField S E :=
      (FunctionField.isFullConstantField_iff_algebraicClosure_eq_bot S E).2
        (exactConstantExtension_extended_algebraicClosure_eq_bot
          C S N hExact)
    (∀ q : ExactConstantExtensionPresentedPlace C S N,
      finiteExtensionTotalDifferentEffectiveDivisor S E
          (exactConstantExtensionPresentedUpstairsPlaceEquiv
            C S N hExact q) =
        finiteExtensionTotalDifferentEffectiveDivisor C N
          (exactConstantExtensionPresentedDownstairsPlace
            C S N hExact q)) →
      FunctionField.Chart.genus S E = FunctionField.Chart.genus C N := by
  dsimp only
  let E := ExactConstantExtension C N S
  letI : Field E := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) (RatFunc S) :=
    ratFuncCoefficientAlgebra C S
  letI : Algebra (RatFunc C) E :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) E := Algebra.toSMul
  letI : Module (RatFunc C) E := Algebra.toModule
  letI : FiniteDimensional (RatFunc C) E :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc
      C S N hExact
  letI : Algebra.IsSeparable (RatFunc C) E :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  letI : Algebra (RatFunc S) E :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  letI : SMul (RatFunc S) E := Algebra.toSMul
  letI : Module (RatFunc S) E := Algebra.toModule
  letI : FiniteDimensional (RatFunc S) E :=
    finiteDimensional_over_extendedRatFunc C S N hExact
  letI : Algebra.IsSeparable (RatFunc S) E :=
    isSeparable_over_extendedRatFunc C S N hExact
  let extendedConstantAlgebra : Algebra S E :=
    RingHom.toAlgebra ((algebraMap (RatFunc S) E).comp
      (algebraMap S (RatFunc S)))
  let tensorConstantAlgebra : Algebra S E :=
    Algebra.TensorProduct.leftAlgebra
  have hconstantMap (s : S) :
      (@algebraMap S E _ _ extendedConstantAlgebra) s =
        (@algebraMap S E _ _ tensorConstantAlgebra) s := by
    exact (ratFuncToExactConstantExtension C S N hExact).commutes s
  have htensorPolynomialMap (s : S) :
      (@algebraMap S E _ _ tensorConstantAlgebra) s =
        (@algebraMap S[X] E _ _
          (constantExtensionTensorPolynomialAlgebra C S N))
            (algebraMap S S[X] s) := by
    change (s ⊗ₜ[C] (1 : N)) =
      Polynomial.aeval
        (polynomialTensorCancelEvaluationPoint C S N)
        (Polynomial.C s)
    simp
  letI : Algebra S E := extendedConstantAlgebra
  letI : SMul S E := Algebra.toSMul
  letI : Algebra S[X] E :=
    constantExtensionTensorPolynomialAlgebra C S N
  letI : SMul S[X] E := Algebra.toSMul
  letI : IsScalarTower S[X] (RatFunc S) E :=
    IsScalarTower.of_algebraMap_eq' (by
      apply DFunLike.ext _ _
      intro p
      change algebraMap S[X] E p =
        ratFuncToExactConstantExtension C S N hExact
          (algebraMap S[X] (RatFunc S) p)
      exact
        (ratFuncToExactConstantExtension_algebraMap C S N hExact p).symm)
  letI : IsScalarTower S S[X] E :=
    IsScalarTower.of_algebraMap_eq' (by
      apply DFunLike.ext _ _
      intro s
      exact (hconstantMap s).trans (htensorPolynomialMap s))
  intro hPresentedMultiplicity
  letI : FunctionField.IsFullConstantField C N :=
    (FunctionField.isFullConstantField_iff_algebraicClosure_eq_bot C N).2
      hExact
  have hExtendedExact : algebraicClosure S E =
      (⊥ : IntermediateField S E) :=
    exactConstantExtension_extended_algebraicClosure_eq_bot C S N hExact
  letI : FunctionField.IsFullConstantField S E :=
    (FunctionField.isFullConstantField_iff_algebraicClosure_eq_bot S E).2
      hExtendedExact
  have hTotalNat :=
    exactConstantExtension_totalDifferentDegree_eq_of_presentedMultiplicity
      C S N hExact hPresentedMultiplicity
  have hTotalInt :
      (finiteExtensionFiniteDifferentDegree S E
          (finiteExtensionFiniteDifferentIdeal_ne_bot S E) : ℤ) +
          (infinityDifferentDegree S E : ℤ) =
        (finiteExtensionFiniteDifferentDegree C N
          (finiteExtensionFiniteDifferentIdeal_ne_bot C N) : ℤ) +
          (infinityDifferentDegree C N : ℤ) := by
    exact_mod_cast hTotalNat
  have hUp :=
    finiteExtension_totalDifferentDegree_eq_two_finrank_add_two_genus_sub_two_of_compatibleChart
      S E
  have hDown :=
    finiteExtension_totalDifferentDegree_eq_two_finrank_add_two_genus_sub_two_of_compatibleChart
      C N
  have hRank : Module.finrank (RatFunc S) E =
      Module.finrank (RatFunc C) N :=
    exactConstantExtension_finrank_over_extendedRatFunc_eq C S N hExact
  dsimp only [E] at hTotalInt hUp hDown hRank ⊢
  omega

end

end BGS.HasseWeil
