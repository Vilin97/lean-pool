/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveCanonicalDegreeBound
public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionRiemannRoch
public import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneOnePointRiemannLower

/-!
# Canonical-different genus bridge

The explicit different divisor used by the Corvaja--Zannier development has
the correct degree bound under only one separating coordinate.  This module
isolates the exact remaining bridge to the intrinsic Riemann--Roch genus:
after transporting that divisor to the Riemann--Roch chart, it must be shown
to be canonical.

No canonicality premise is hidden in a definition.  The generic theorem
below takes `FunctionField.Chart.IsCanonical` explicitly, while the plane
theorem proves the complete degree estimate available below that boundary.
-/

@[expose] public section

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier
open scoped Polynomial

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance canonicalGenusConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance canonicalGenusConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance (priority := 10) canonicalGenusPolynomialAlgebra :
    Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance canonicalGenusPolynomialTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance canonicalGenusConstantPolynomialTower :
    IsScalarTower K K[X] L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Identifying the explicit different divisor with a canonical divisor
turns any upper bound for its degree into a genus bound. -/
theorem finiteExtension_genus_le_budget_of_canonicalDifferent_isCanonical
    [FunctionField.IsFullConstantField K L]
    (budget : ℕ)
    (hcanonical : FunctionField.Chart.IsCanonical K L
      (finiteExtensionDivisorEquivChart K L
        (finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L))))
    (hdegree : finiteExtensionDivisorDegree K L
        (finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L)) ≤
      2 * (budget : ℤ) - 2) :
    FunctionField.genus K L ≤ budget := by
  let D := finiteExtensionCanonicalDifferentDivisor K L
    (finiteExtensionFiniteDifferentIdeal_ne_bot K L)
  have hcanonicalDegree : finiteExtensionDivisorDegree K L D =
      2 * (FunctionField.Chart.genus K L : ℤ) - 2 := by
    rw [finiteExtensionDivisorDegree_eq_chart]
    exact FunctionField.Chart.deg_canonical K L hcanonical
  have hchart : FunctionField.Chart.genus K L ≤ budget := by
    have hdegree' : finiteExtensionDivisorDegree K L D ≤
        2 * (budget : ℤ) - 2 := by
      simpa only [D] using hdegree
    have hcast : (FunctionField.Chart.genus K L : ℤ) ≤ budget := by
      omega
    exact_mod_cast hcast
  rw [FunctionField.genus_eq_genusChart K L]
  exact hchart

end

noncomputable section

open BGS.CorvajaZannier

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]

/-- The one-separating-coordinate canonical-degree estimate already has
exactly the degree shape needed for the bidegree genus budget. -/
theorem planeCurve_canonicalDifferentDivisor_degree_le_two_genusBudget_sub_two
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hcardK : MvPolynomial.degreeOf 1 f < Fintype.card K) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    finiteExtensionDivisorDegree K (PlaneCurveFunctionField f)
        (finiteExtensionCanonicalDifferentDivisor K
          (PlaneCurveFunctionField f)
          (finiteExtensionFiniteDifferentIdeal_ne_bot K
            (PlaneCurveFunctionField f))) ≤
      2 * (planeCurveBidegreeGenusBudget f : ℤ) - 2 := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  have hcanonical :=
    planeCurve_canonicalDifferentDivisor_degree_le
      hf hpartialSecond hcardK
  have hb : 0 < MvPolynomial.degreeOf 1 f :=
    degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond
  change finiteExtensionDivisorDegree K (PlaneCurveFunctionField f)
        (finiteExtensionCanonicalDifferentDivisor K
          (PlaneCurveFunctionField f)
          (finiteExtensionFiniteDifferentIdeal_ne_bot K
            (PlaneCurveFunctionField f))) ≤
      2 * (((MvPolynomial.degreeOf 0 f - 1) *
        (MvPolynomial.degreeOf 1 f - 1) : ℕ) : ℤ) - 2
  by_cases ha : MvPolynomial.degreeOf 0 f = 0
  · rw [ha] at hcanonical ⊢
    simp only [Nat.zero_sub, zero_mul, Nat.cast_zero, zero_mul]
    omega
  · have ha' : 1 ≤ MvPolynomial.degreeOf 0 f :=
      Nat.one_le_iff_ne_zero.mpr ha
    have hb' : 1 ≤ MvPolynomial.degreeOf 1 f := by omega
    rw [Nat.cast_mul, Nat.cast_sub ha', Nat.cast_sub hb']
    push_cast
    nlinarith [hcanonical]

end


end BGS.HasseWeil
