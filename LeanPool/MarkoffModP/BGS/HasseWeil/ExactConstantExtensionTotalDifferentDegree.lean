/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantExtensionClosedPlaceSplittingFormula
import LeanPool.MarkoffModP.BGS.HasseWeil.FinsuppWeightedFiber
import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionTotalDifferentEffectiveDivisor

/-!
# Total different degree under exact constant extension

This file separates the global weighted-degree cancellation from the local
normalization compatibility needed for invariance of the different under an
exact extension of finite constants.

The theorem below assumes only pointwise equality of the total-different
multiplicity on a presented upstairs place and its contracted downstairs
place.  The exhaustive presented-place equivalence, the division-by-gcd
degree formula, and the matching gcd fiber cardinality then prove equality of
the total finite-plus-infinity different degrees.  The remaining pointwise
hypothesis is intended to be discharged branchwise by the finite and
reciprocal-infinity different-map theorems.
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
    exactConstantTotalDifferentConstantsDecidableEq
    (K : Type*) [Field K] : DecidableEq K :=
  infinityBridgeDecidableEqConstants K

local instance (priority := 10001)
    exactConstantTotalDifferentRatFuncDecidableEq
    (K : Type*) [Field K] : DecidableEq (RatFunc K) :=
  infinityBridgeDecidableEqRatFuncConstants K

local instance exactConstantTotalDifferentBaseConstantAlgebra : Algebra C N :=
  bridgeBaseConstantAlgebra C N

local instance exactConstantTotalDifferentBaseConstantTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance (priority := 10)
    exactConstantTotalDifferentBasePolynomialAlgebra : Algebra C[X] N :=
  RingHom.toAlgebra ((algebraMap (RatFunc C) N).comp
    (algebraMap C[X] (RatFunc C)))

local instance exactConstantTotalDifferentBasePolynomialTower :
    IsScalarTower C[X] (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- If the total-different multiplicity is preserved at every presented
place, then an exact extension of finite constants preserves the total
finite-plus-infinity different degree. -/
theorem exactConstantExtension_totalDifferentDegree_eq_of_presentedMultiplicity
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
    letI : Algebra S[X] E :=
      constantExtensionTensorPolynomialAlgebra C S N
    letI : SMul S[X] E := Algebra.toSMul
    letI : Module S[X] E := Algebra.toModule
    letI : IsScalarTower S[X] (RatFunc S) E :=
      IsScalarTower.of_algebraMap_eq' (by
        apply DFunLike.ext _ _
        intro p
        change algebraMap S[X] E p =
          ratFuncToExactConstantExtension C S N hExact
            (algebraMap S[X] (RatFunc S) p)
        exact
          (ratFuncToExactConstantExtension_algebraMap C S N hExact p).symm)
    letI : FiniteDimensional (RatFunc S) E :=
      finiteDimensional_over_extendedRatFunc C S N hExact
    letI : Algebra.IsSeparable (RatFunc S) E :=
      isSeparable_over_extendedRatFunc C S N hExact
    (∀ q : ExactConstantExtensionPresentedPlace C S N,
      finiteExtensionTotalDifferentEffectiveDivisor S E
          (exactConstantExtensionPresentedUpstairsPlaceEquiv
            C S N hExact q) =
        finiteExtensionTotalDifferentEffectiveDivisor C N
          (exactConstantExtensionPresentedDownstairsPlace
            C S N hExact q)) →
      finiteExtensionFiniteDifferentDegree S E
          (finiteExtensionFiniteDifferentIdeal_ne_bot S E) +
          infinityDifferentDegree S E =
        finiteExtensionFiniteDifferentDegree C N
            (finiteExtensionFiniteDifferentIdeal_ne_bot C N) +
          infinityDifferentDegree C N := by
  dsimp only
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
  letI : Algebra S[X] E :=
    constantExtensionTensorPolynomialAlgebra C S N
  letI : SMul S[X] E := Algebra.toSMul
  letI : Module S[X] E := Algebra.toModule
  letI : IsScalarTower S[X] (RatFunc S) E :=
    IsScalarTower.of_algebraMap_eq' (by
      apply DFunLike.ext _ _
      intro p
      change algebraMap S[X] E p =
        ratFuncToExactConstantExtension C S N hExact
          (algebraMap S[X] (RatFunc S) p)
      exact
        (ratFuncToExactConstantExtension_algebraMap C S N hExact p).symm)
  letI : FiniteDimensional (RatFunc S) E :=
    finiteDimensional_over_extendedRatFunc C S N hExact
  letI : Algebra.IsSeparable (RatFunc S) E :=
    isSeparable_over_extendedRatFunc C S N hExact
  intro hPresentedMultiplicity
  let Base := FiniteExtensionPlace C N
  let Up := ExactConstantExtensionPresentedPlace C S N
  let Actual := FiniteExtensionPlace S E
  let down : Up → Base :=
    exactConstantExtensionPresentedDownstairsPlace C S N hExact
  let e : Up ≃ Actual :=
    exactConstantExtensionPresentedUpstairsPlaceEquiv C S N hExact
  let Dbase : Base →₀ ℕ :=
    finiteExtensionTotalDifferentEffectiveDivisor C N
  let Dactual : Actual →₀ ℕ :=
    finiteExtensionTotalDifferentEffectiveDivisor S E
  let Dup : Up →₀ ℕ := (Finsupp.domCongr e).symm Dactual
  have hDup (q : Up) : Dup q = Dactual (e q) := by
    simp [Dup, Finsupp.domCongr_apply]
  have hWeighted :
      Dup.sum (fun q m =>
          m * finiteExtensionPlaceDegree S E (e q)) =
        Dbase.sum (fun P m =>
          m * finiteExtensionPlaceDegree C N P) := by
    apply Finsupp.sum_mul_degree_eq_of_div_gcd_fibers
      down (finiteExtensionPlaceDegree C N)
        (fun q => finiteExtensionPlaceDegree S E (e q))
        Dbase Dup (Module.finrank C S)
    · intro q
      rw [hDup]
      exact hPresentedMultiplicity q
    · intro q
      dsimp [e, down]
      rw [exactConstantExtensionPresentedUpstairsPlaceEquiv_apply]
      exact exactConstantExtensionPresentedPlace_degree_eq_div_gcd
        C S N hExact q
    · intro P
      exact
        exactConstantExtensionPresentedPlaceFiber_natCard_eq_gcd_of_downstairs
          C S N hExact P
  have hReindex :
      Dactual.sum (fun Q m =>
          m * finiteExtensionPlaceDegree S E Q) =
        Dup.sum (fun q m =>
          m * finiteExtensionPlaceDegree S E (e q)) := by
    dsimp [Dup]
    rw [Finsupp.domCongr_symm]
    change Dactual.sum _ =
      (Finsupp.equivMapDomain e.symm Dactual).sum _
    rw [Finsupp.sum_equivMapDomain]
    simp only [Equiv.apply_symm_apply]
  calc
    finiteExtensionFiniteDifferentDegree S E
          (finiteExtensionFiniteDifferentIdeal_ne_bot S E) +
          infinityDifferentDegree S E =
        finiteExtensionEffectiveDivisorDegree S E Dactual :=
      (finiteExtensionTotalDifferentEffectiveDivisor_degree S E).symm
    _ = Dactual.sum (fun Q m =>
          m * finiteExtensionPlaceDegree S E Q) := rfl
    _ = Dup.sum (fun q m =>
          m * finiteExtensionPlaceDegree S E (e q)) := hReindex
    _ = Dbase.sum (fun P m =>
          m * finiteExtensionPlaceDegree C N P) := hWeighted
    _ = finiteExtensionEffectiveDivisorDegree C N Dbase := rfl
    _ = finiteExtensionFiniteDifferentDegree C N
          (finiteExtensionFiniteDifferentIdeal_ne_bot C N) +
          infinityDifferentDegree C N :=
      finiteExtensionTotalDifferentEffectiveDivisor_degree C N

end

end BGS.HasseWeil
