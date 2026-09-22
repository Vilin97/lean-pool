/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionCanonicalDifferentCotraceCanonicality
import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionCanonicalDifferentGenusBound
import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneConstantField

/-!
# Plane-curve genus bound from the cotrace divisor

For an absolutely irreducible plane curve with the second coordinate
separating, the cotrace construction and the explicit bidegree estimate reduce
the intrinsic genus bound to the Riemann--Hurwitz degree identity for the
canonical-different divisor.  The identity remains a visible premise here.
-/

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier
open scoped Polynomial

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]

/-- The one-separating-coordinate plane-curve genus bound, conditional only
on the displayed Riemann--Hurwitz degree identity for the cotrace divisor.

Absolute irreducibility supplies the exact constant field, while
`planeCurve_canonicalDifferentDivisor_degree_le_two_genusBudget_sub_two`
supplies the required degree upper bound. -/
theorem planeCurve_genus_le_bidegreeGenusBudget_of_cotrace_degree_eq
    {f : MvPolynomial (Fin 2) K}
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hcardK : MvPolynomial.degreeOf 1 f < Fintype.card K) :
    let hf : Irreducible f :=
      irreducible_of_irreducible_map_algebraicClosure habsolute
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    let L := PlaneCurveFunctionField f
    let canonicalAlg : Algebra K L := inferInstance
    let ratAlg : Algebra (RatFunc K) L :=
      planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (RatFunc K) L := ratAlg
    let polynomialAlg : Algebra K[X] L :=
      RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
        (algebraMap K[X] (RatFunc K)))
    letI : Algebra K[X] L := polynomialAlg
    letI : SMul K[X] L := polynomialAlg.toSMul
    letI : Module K[X] L := polynomialAlg.toModule
    letI : IsScalarTower K[X] (RatFunc K) L :=
      IsScalarTower.of_algebraMap_eq' rfl
    let inducedAlg : Algebra K L :=
      RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
        (algebraMap K (RatFunc K)))
    letI : Algebra K L := inducedAlg
    letI : SMul K L := inducedAlg.toSMul
    letI : Module K L := inducedAlg.toModule
    letI : IsScalarTower K (RatFunc K) L :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower K K[X] L :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (RatFunc K) L :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc
        hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) L :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    finiteExtensionDivisorDegree K L
        (finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L)) =
      2 * (FunctionField.genus K L : ℤ) - 2 →
    @FunctionField.genus K L _ _ canonicalAlg ≤
      planeCurveBidegreeGenusBudget f := by
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
  let polynomialAlg : Algebra K[X] L :=
    RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
      (algebraMap K[X] (RatFunc K)))
  let : Algebra K[X] L := polynomialAlg
  let : SMul K[X] L := polynomialAlg.toSMul
  let : Module K[X] L := polynomialAlg.toModule
  let : IsScalarTower K[X] (RatFunc K) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let inducedAlg : Algebra K L :=
    RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
      (algebraMap K (RatFunc K)))
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
  let : SMul K L := inducedAlg.toSMul
  let : Module K L := inducedAlg.toModule
  let : IsScalarTower K (RatFunc K) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K K[X] L :=
    IsScalarTower.of_algebraMap_eq' rfl
  dsimp only
  intro hdegreeEq
  have hconstantsCanonical :
      @algebraicClosure K L _ _ canonicalAlg = ⊥ := by
    simpa only [L] using
      planeCurveFunctionField_algebraicClosure_eq_bot
        f habsolute hpartialSecond
  have hconstants : algebraicClosure K L = ⊥ := by
    change @algebraicClosure K L _ _ inducedAlg = ⊥
    rw [hinducedAlg]
    exact hconstantsCanonical
  let : FunctionField.IsFullConstantField K L :=
    (FunctionField.isFullConstantField_iff_algebraicClosure_eq_bot K L).2
      hconstants
  have hdegreeEqChart :
      finiteExtensionDivisorDegree K L
          (finiteExtensionCanonicalDifferentDivisor K L
            (finiteExtensionFiniteDifferentIdeal_ne_bot K L)) =
        2 * (FunctionField.Chart.genus K L : ℤ) - 2 := by
    rw [← FunctionField.genus_eq_genusChart K L]
    exact hdegreeEq
  have hdegreeLe :
      finiteExtensionDivisorDegree K L
          (finiteExtensionCanonicalDifferentDivisor K L
            (finiteExtensionFiniteDifferentIdeal_ne_bot K L)) ≤
        2 * (planeCurveBidegreeGenusBudget f : ℤ) - 2 := by
    simpa only [L] using
      planeCurve_canonicalDifferentDivisor_degree_le_two_genusBudget_sub_two
        hf hpartialSecond hcardK
  have hgenus : FunctionField.genus K L ≤
      planeCurveBidegreeGenusBudget f :=
    finiteExtension_genus_le_budget_of_cotrace_and_degree_eq
      K L (planeCurveBidegreeGenusBudget f) hdegreeEqChart hdegreeLe
  change @FunctionField.genus K L _ _ canonicalAlg ≤
    planeCurveBidegreeGenusBudget f
  change @FunctionField.genus K L _ _ inducedAlg ≤
    planeCurveBidegreeGenusBudget f at hgenus
  rw [hinducedAlg] at hgenus
  exact hgenus

end

end BGS.HasseWeil
