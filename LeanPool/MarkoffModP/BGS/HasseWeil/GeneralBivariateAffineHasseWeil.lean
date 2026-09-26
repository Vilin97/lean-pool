/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionHasseWeil
public import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneAffineHasseWeilFromZeta
public import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneConstantField
public import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneCurveGenusBoundAutomatic
public import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneFrobeniusReduction

/-!
# The general affine bivariate Hasse--Weil theorem

The closed Hasse--Weil theorem for finite separable extensions of `K(X)` is
applied to the function field of a separating absolutely irreducible plane
curve.  Exact constants and the bidegree genus budget identify its intrinsic
Hasse bound, while the existing normalization-to-affine comparison gives the
coefficient `8`.  Frobenius deflation then removes both separating-coordinate
hypotheses without changing the affine point count or increasing the supplied
bidegree bounds.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier

noncomputable section

/-- The coefficient-`8` affine Hasse--Weil estimate for a separating
absolutely irreducible plane equation. -/
theorem
    abs_affinePlaneCurveZeros_card_sub_card_le_eight_mul_bidegree_of_separating
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
    |((BGS.External.affinePlaneCurveZeros K f).card : ℝ) -
        (Fintype.card K : ℝ)| ≤
      8 * Real.sqrt (Fintype.card K : ℝ) *
        (firstDegree : ℝ) * (secondDegree : ℝ) := by
  classical
  let hf : Irreducible f :=
    irreducible_of_irreducible_map_algebraicClosure habsolute
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let canonicalAlg : Algebra K L := inferInstance
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
  letI : Algebra K L := inducedAlg
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
  have hhasse := finiteExtensionClosedPlaceHasseWeil K L hExact
  rw [finiteExtensionClosedPlaceExtensionCount_one_eq_rationalPlaceCount K L]
    at hhasse
  have hnormalization :
      |(separatingPlaneCurveRationalPlaceCount f hf hpartialSecond : ℝ) -
          (Fintype.card K : ℝ) - 1| ≤
        (2 * (budget : ℝ) + 1) *
          Real.sqrt (Fintype.card K : ℝ) := by
    change
      |(@finiteExtensionRationalPlaceCount K _ _ L _ ratAlg
          (Classical.decEq (RatFunc K)) : ℝ) -
          (Fintype.card K : ℝ) - 1| ≤
        (2 * (budget : ℝ) + 1) * Real.sqrt (Fintype.card K : ℝ)
    have hhasse' :
        |(@finiteExtensionRationalPlaceCount K _ _ L _ ratAlg
            (Classical.decEq (RatFunc K)) : ℝ) -
            (Fintype.card K : ℝ) - 1| ≤
          (2 * FunctionField.genus K L + 1 : ℝ) *
            Real.sqrt (Fintype.card K : ℝ) := by
      simpa only [Fintype.card_eq_nat_card] using hhasse
    apply hhasse'.trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul_left 2 hgenus) 1
  rw [affinePlaneCurveZeros_card_eq_affinePlaneCurvePoint_card]
  exact
    abs_affinePlaneCurvePoint_card_sub_card_le_eight_mul_bidegree_of_rationalPlaceHasse
      hdegree hf hpartialFirst hpartialSecond hfirst hsecond
      (show 2 * budget + 1 ≤
          2 * ((firstDegree - 1) * (secondDegree - 1)) + 1 by rfl)
      (by simpa using hnormalization)

/-- The coefficient-`8` affine Hasse--Weil estimate for every absolutely
irreducible bivariate equation of positive supplied bidegree. -/
theorem abs_affinePlaneCurveZeros_card_sub_card_le_eight_mul_bidegree
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (f : MvPolynomial (Fin 2) K) (firstDegree secondDegree : ℕ)
    (hfirst : 0 < firstDegree)
    (hsecond : 0 < secondDegree)
    (hdegree : BGS.External.HasBidegreeAtMost
      f firstDegree secondDegree)
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f)) :
    |((BGS.External.affinePlaneCurveZeros K f).card : ℝ) -
        (Fintype.card K : ℝ)| ≤
      8 * Real.sqrt (Fintype.card K : ℝ) *
        (firstDegree : ℝ) * (secondDegree : ℝ) := by
  exact abs_affinePlaneCurveZeros_card_sub_card_le_of_separating_case
    K f firstDegree secondDegree hdegree habsolute
      (fun g hgdegree hgabsolute hgpartialFirst hgpartialSecond =>
        abs_affinePlaneCurveZeros_card_sub_card_le_eight_mul_bidegree_of_separating
          hfirst hsecond hgdegree hgabsolute hgpartialFirst hgpartialSecond)

/-- The in-repository inhabitant of the general affine bivariate
Hasse--Weil interface. -/
theorem bivariateAffineHasseWeilBound_eight :
    BGS.External.BivariateAffineHasseWeilBound 8 := by
  intro K _ _ _ f firstDegree secondDegree hfirst hsecond hdegree habsolute
  exact abs_affinePlaneCurveZeros_card_sub_card_le_eight_mul_bidegree
    K f firstDegree secondDegree hfirst hsecond hdegree habsolute

/-- The in-repository inhabitant of the general affine bivariate
Hasse--Weil interface. -/
theorem generalBivariateAffineHasseWeilTheorem :
    BGS.External.GeneralBivariateAffineHasseWeilTheorem := by
  exact ⟨8, by norm_num, bivariateAffineHasseWeilBound_eight⟩

end

end BGS.HasseWeil
