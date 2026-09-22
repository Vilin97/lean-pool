/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveCanonicalDegreeBound
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveBoundarySupport
import Mathlib.Tactic

/-!
# The log-canonical degree budget for a plane curve

This module combines the canonical-different estimate with the weighted
zero/pole boundary estimate.  It is the exact geometric input `chi = 2ab`
used by the exhaustive-place form of Corvaja--Zannier Proposition 2.
-/

open scoped Polynomial BigOperators

namespace BGS.CorvajaZannier

noncomputable section

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]

/-- The canonical divisor together with the actual weighted zero/pole
boundary of positive coordinate powers has degree at most twice the product
of the two coordinate degrees. -/
theorem planeCurve_canonicalDifferent_add_propositionTwoExceptional_weightedDegree_le
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hcardK : MvPolynomial.degreeOf 1 f < Fintype.card K)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    finiteExtensionDivisorDegree K (PlaneCurveFunctionField f)
          (finiteExtensionCanonicalDifferentDivisor K
            (PlaneCurveFunctionField f)
            (finiteExtensionFiniteDifferentIdeal_ne_bot K
              (PlaneCurveFunctionField f))) +
        (∑ w ∈ propositionTwoExceptionalPlaces K
            (PlaneCurveFunctionField f)
            ((planeCurveFunction f 0) ^ m) ((planeCurveFunction f 1) ^ n),
          finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) w : ℤ) ≤
      (2 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f : ℕ) := by
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
  have hcanonical := planeCurve_canonicalDifferentDivisor_degree_le
    hf hpartialSecond hcardK
  have hboundary :=
    planeCurve_propositionTwoExceptionalPlaces_weightedDegree_le
      hf hpartialFirst hpartialSecond m n hm hn
  have hboundaryInt :
      (∑ w ∈ propositionTwoExceptionalPlaces K
          (PlaneCurveFunctionField f)
          ((planeCurveFunction f 0) ^ m) ((planeCurveFunction f 1) ^ n),
        finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) w : ℤ) ≤
        2 * ((MvPolynomial.degreeOf 0 f : ℤ) +
          MvPolynomial.degreeOf 1 f) := by
    exact_mod_cast hboundary
  norm_num at hcanonical hboundaryInt ⊢
  omega

end

end BGS.CorvajaZannier
