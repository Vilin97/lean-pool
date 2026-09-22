/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionHasseBoundFromEvenConstantExtensions
import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneAffineHasseWeilFromZeta
import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneConstantField
import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneCurveGenusBoundAutomatic

/-!
# Affine plane Hasse bounds from the even-extension error

For a separating absolutely irreducible plane curve, exact constants and the
bidegree genus bound are already formalized.  This file composes those facts
with the automatic zeta package and the two-sided affine/normalization
comparison.  The sole remaining premise is therefore the even constant-field
extension error used by the spectral argument.
-/

namespace BGS.HasseWeil

open Filter Asymptotics
open BGS.CorvajaZannier

noncomputable section

/-- For a separating absolutely irreducible plane curve, the even-extension
error estimate implies the affine Hasse--Weil bound with coefficient `8`.

The exact constant-field theorem, divisor index one, standard zeta
rationality, trace formula, numerator-degree budget, and intrinsic genus bound
are all discharged in the proof. -/
theorem abs_affinePlaneCurveZeros_card_sub_card_le_eight_mul_bidegree_of_evenError
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {f : MvPolynomial (Fin 2) K} {firstDegree secondDegree : ℕ}
    (hfirst : 0 < firstDegree)
    (hsecond : 0 < secondDegree)
    (hdegree : BGS.External.HasBidegreeAtMost
      f firstDegree secondDegree)
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    let hf : Irreducible f :=
      irreducible_of_irreducible_map_algebraicClosure habsolute
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    let L := PlaneCurveFunctionField f
    let ratAlg : Algebra (RatFunc K) L :=
      planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (RatFunc K) L := ratAlg
    letI : SMul (RatFunc K) L := ratAlg.toSMul
    letI : Module (RatFunc K) L := ratAlg.toModule
    letI : FiniteDimensional (RatFunc K) L :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) L :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : DecidableEq (RatFunc K) := Classical.decEq _
    ((fun n : ℕ ↦
        (finiteExtensionClosedPlaceExtensionCount K L (2 * n) : ℂ) -
          (Nat.card K : ℂ) ^ (2 * n) - 1) =O[atTop]
      fun n : ℕ ↦ (Nat.card K : ℝ) ^ n) →
    |((BGS.External.affinePlaneCurveZeros K f).card : ℝ) -
        (Fintype.card K : ℝ)| ≤
      8 * Real.sqrt (Fintype.card K : ℝ) *
        (firstDegree : ℝ) * (secondDegree : ℝ) := by
  classical
  let hf : Irreducible f :=
    irreducible_of_irreducible_map_algebraicClosure habsolute
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let canonicalAlg : Algebra K L := inferInstance
  let ratAlg : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : Algebra (RatFunc K) L := ratAlg
  let : SMul (RatFunc K) L := ratAlg.toSMul
  let : Module (RatFunc K) L := ratAlg.toModule
  let : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : DecidableEq (RatFunc K) := Classical.decEq _
  let inducedAlg : Algebra K L := bridgeBaseConstantAlgebra K L
  have hinducedAlg : inducedAlg = canonicalAlg := by
    apply Algebra.algebra_ext
    intro c
    change (@ratFuncSpecialization K L _ _ canonicalAlg
      (planeCurveFunction f 0) hx) (RatFunc.C c) =
        @algebraMap K L _ _ canonicalAlg c
    have h := DFunLike.congr_fun
      (@ratFuncSpecialization_comp_polynomial_algebraMap
        K L _ _ canonicalAlg (planeCurveFunction f 0) hx)
      (Polynomial.C c)
    simpa using h
  let : Algebra K L := inducedAlg
  dsimp only
  intro herror
  let budget := (firstDegree - 1) * (secondDegree - 1)
  have hExactCanonical :
      @algebraicClosure K L _ _ canonicalAlg =
        (⊥ : @IntermediateField K L _ _ canonicalAlg) := by
    simpa only [L] using
      planeCurveFunctionField_algebraicClosure_eq_bot
        f habsolute hpartialSecond
  have hExact : algebraicClosure K L =
      (⊥ : IntermediateField K L) := by
    change @algebraicClosure K L _ _ inducedAlg =
      (⊥ : @IntermediateField K L _ _ inducedAlg)
    rw [hinducedAlg]
    exact hExactCanonical
  have hgenusActualCanonical :
      @FunctionField.genus K L _ _ canonicalAlg ≤
      planeCurveBidegreeGenusBudget f := by
    simpa only [L] using
      planeCurve_genus_le_bidegreeGenusBudget
        habsolute hpartialFirst hpartialSecond
  have hfirstDegree : MvPolynomial.degreeOf 0 f ≤ firstDegree :=
    degreeOf_first_le_of_hasBidegreeAtMost hdegree
  have hsecondDegree : MvPolynomial.degreeOf 1 f ≤ secondDegree :=
    degreeOf_second_le_of_hasBidegreeAtMost hdegree
  have hbudget : planeCurveBidegreeGenusBudget f ≤ budget := by
    dsimp only [planeCurveBidegreeGenusBudget, budget]
    exact Nat.mul_le_mul
      (Nat.sub_le_sub_right hfirstDegree 1)
      (Nat.sub_le_sub_right hsecondDegree 1)
  have hgenusCanonical :
      @FunctionField.genus K L _ _ canonicalAlg ≤ budget :=
    hgenusActualCanonical.trans hbudget
  have hgenus : FunctionField.genus K L ≤ budget := by
    change @FunctionField.genus K L _ _ inducedAlg ≤ budget
    rw [hinducedAlg]
    exact hgenusCanonical
  have hhasse :=
    finiteExtensionClosedPlaceHasseBound_of_exactConstants_and_evenError
      K L budget hExact hgenus herror
  rw [finiteExtensionClosedPlaceExtensionCount_one_eq_rationalPlaceCount K L]
    at hhasse
  have hnormalization :
      |(separatingPlaneCurveRationalPlaceCount f hf hpartialSecond : ℝ) -
          (Fintype.card K : ℝ) - 1| ≤
        (2 * (budget : ℝ) + 1) * Real.sqrt (Fintype.card K : ℝ) := by
    change
      |(@finiteExtensionRationalPlaceCount K _ _ L _ ratAlg
          (Classical.decEq (RatFunc K)) : ℝ) -
          (Fintype.card K : ℝ) - 1| ≤
        (2 * (budget : ℝ) + 1) * Real.sqrt (Fintype.card K : ℝ)
    simpa only [Fintype.card_eq_nat_card] using hhasse
  rw [affinePlaneCurveZeros_card_eq_affinePlaneCurvePoint_card]
  exact
    abs_affinePlaneCurvePoint_card_sub_card_le_eight_mul_bidegree_of_rationalPlaceHasse
      hdegree hf hpartialFirst hpartialSecond hfirst hsecond
      (show 2 * budget + 1 ≤
          2 * ((firstDegree - 1) * (secondDegree - 1)) + 1 by rfl)
      (by simpa using hnormalization)

/-- For a separating absolutely irreducible plane curve, a two-sided
constant-extension estimate along one fixed positive divisible-even
subsequence implies the affine Hasse--Weil bound with coefficient `8`.

This is the plane-curve endpoint used by the selected Lorenzini route.  No
estimate at extension degrees outside the subsequence `2 * δ * n` is needed. -/
theorem
    abs_affinePlaneCurveZeros_card_sub_card_le_eight_mul_bidegree_of_divisibleEvenError
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {f : MvPolynomial (Fin 2) K} {firstDegree secondDegree δ : ℕ}
    (hfirst : 0 < firstDegree)
    (hsecond : 0 < secondDegree)
    (hdegree : BGS.External.HasBidegreeAtMost
      f firstDegree secondDegree)
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hδ : 0 < δ) :
    let hf : Irreducible f :=
      irreducible_of_irreducible_map_algebraicClosure habsolute
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    let L := PlaneCurveFunctionField f
    let ratAlg : Algebra (RatFunc K) L :=
      planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (RatFunc K) L := ratAlg
    letI : SMul (RatFunc K) L := ratAlg.toSMul
    letI : Module (RatFunc K) L := ratAlg.toModule
    letI : FiniteDimensional (RatFunc K) L :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) L :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : DecidableEq (RatFunc K) := Classical.decEq _
    ((fun n : ℕ ↦
        (finiteExtensionClosedPlaceExtensionCount K L (2 * δ * n) : ℂ) -
          (Nat.card K : ℂ) ^ (2 * δ * n) - 1) =O[atTop]
      fun n : ℕ ↦ ((Nat.card K : ℝ) ^ δ) ^ n) →
    |((BGS.External.affinePlaneCurveZeros K f).card : ℝ) -
        (Fintype.card K : ℝ)| ≤
      8 * Real.sqrt (Fintype.card K : ℝ) *
        (firstDegree : ℝ) * (secondDegree : ℝ) := by
  classical
  let hf : Irreducible f :=
    irreducible_of_irreducible_map_algebraicClosure habsolute
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let canonicalAlg : Algebra K L := inferInstance
  let ratAlg : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : Algebra (RatFunc K) L := ratAlg
  let : SMul (RatFunc K) L := ratAlg.toSMul
  let : Module (RatFunc K) L := ratAlg.toModule
  let : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : DecidableEq (RatFunc K) := Classical.decEq _
  let inducedAlg : Algebra K L := bridgeBaseConstantAlgebra K L
  have hinducedAlg : inducedAlg = canonicalAlg := by
    apply Algebra.algebra_ext
    intro c
    change (@ratFuncSpecialization K L _ _ canonicalAlg
      (planeCurveFunction f 0) hx) (RatFunc.C c) =
        @algebraMap K L _ _ canonicalAlg c
    have h := DFunLike.congr_fun
      (@ratFuncSpecialization_comp_polynomial_algebraMap
        K L _ _ canonicalAlg (planeCurveFunction f 0) hx)
      (Polynomial.C c)
    simpa using h
  let : Algebra K L := inducedAlg
  dsimp only
  intro herror
  let budget := (firstDegree - 1) * (secondDegree - 1)
  have hExactCanonical :
      @algebraicClosure K L _ _ canonicalAlg =
        (⊥ : @IntermediateField K L _ _ canonicalAlg) := by
    simpa only [L] using
      planeCurveFunctionField_algebraicClosure_eq_bot
        f habsolute hpartialSecond
  have hExact : algebraicClosure K L =
      (⊥ : IntermediateField K L) := by
    change @algebraicClosure K L _ _ inducedAlg =
      (⊥ : @IntermediateField K L _ _ inducedAlg)
    rw [hinducedAlg]
    exact hExactCanonical
  have hgenusActualCanonical :
      @FunctionField.genus K L _ _ canonicalAlg ≤
      planeCurveBidegreeGenusBudget f := by
    simpa only [L] using
      planeCurve_genus_le_bidegreeGenusBudget
        habsolute hpartialFirst hpartialSecond
  have hfirstDegree : MvPolynomial.degreeOf 0 f ≤ firstDegree :=
    degreeOf_first_le_of_hasBidegreeAtMost hdegree
  have hsecondDegree : MvPolynomial.degreeOf 1 f ≤ secondDegree :=
    degreeOf_second_le_of_hasBidegreeAtMost hdegree
  have hbudget : planeCurveBidegreeGenusBudget f ≤ budget := by
    dsimp only [planeCurveBidegreeGenusBudget, budget]
    exact Nat.mul_le_mul
      (Nat.sub_le_sub_right hfirstDegree 1)
      (Nat.sub_le_sub_right hsecondDegree 1)
  have hgenusCanonical :
      @FunctionField.genus K L _ _ canonicalAlg ≤ budget :=
    hgenusActualCanonical.trans hbudget
  have hgenus : FunctionField.genus K L ≤ budget := by
    change @FunctionField.genus K L _ _ inducedAlg ≤ budget
    rw [hinducedAlg]
    exact hgenusCanonical
  have hhasse :=
    finiteExtensionClosedPlaceHasseBound_of_exactConstants_and_divisibleEvenError
      K L budget δ hExact hgenus hδ herror
  rw [finiteExtensionClosedPlaceExtensionCount_one_eq_rationalPlaceCount K L]
    at hhasse
  have hnormalization :
      |(separatingPlaneCurveRationalPlaceCount f hf hpartialSecond : ℝ) -
          (Fintype.card K : ℝ) - 1| ≤
        (2 * (budget : ℝ) + 1) * Real.sqrt (Fintype.card K : ℝ) := by
    change
      |(@finiteExtensionRationalPlaceCount K _ _ L _ ratAlg
          (Classical.decEq (RatFunc K)) : ℝ) -
          (Fintype.card K : ℝ) - 1| ≤
        (2 * (budget : ℝ) + 1) * Real.sqrt (Fintype.card K : ℝ)
    simpa only [Fintype.card_eq_nat_card] using hhasse
  rw [affinePlaneCurveZeros_card_eq_affinePlaneCurvePoint_card]
  exact
    abs_affinePlaneCurvePoint_card_sub_card_le_eight_mul_bidegree_of_rationalPlaceHasse
      hdegree hf hpartialFirst hpartialSecond hfirst hsecond
      (show 2 * budget + 1 ≤
          2 * ((firstDegree - 1) * (secondDegree - 1)) + 1 by rfl)
      (by simpa using hnormalization)

end

end BGS.HasseWeil
