/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveSharedOriginBoundary
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveAuxiliaryIndependence
import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.CorvajaZannierFromGeneral
import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.Boundary
import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.WeightedBidegree
import Mathlib.Tactic

/-!
# Euler budget seven for the weighted trace curve

The reduced weighted trace closure has bidegree `(2,2)` and, when the second
weight is nonzero, contains the affine origin.  Both coordinate functions
vanish at the finite place selected above that origin.  Combining this shared
place with the generic canonical-divisor estimate lowers the sound
log-canonical degree budget from `8` to `7`.

This is deliberately weaker than the paper's unsupported value `3`, but it
uses only the normalization-place machinery proved in the repository.
-/

open scoped Polynomial BigOperators

namespace BGS.Markoff

open BGS.CorvajaZannier

noncomputable section

variable {K : Type*} [Field K]

/-- The first actual coordinate degree of the weighted trace closure. -/
theorem weightedTraceTorusClosurePolynomial_degreeOf_first
    (alpha beta : K) (hbeta : beta ≠ 0) :
    MvPolynomial.degreeOf 0
      (weightedTraceTorusClosurePolynomial alpha beta) = 2 := by
  rw [← planeCurveToBivariate_natDegree_eq_degreeOf_zero]
  change (finTwoToIteratedPolynomial (K := K)
    (weightedTraceTorusClosurePolynomial alpha beta)).natDegree = 2
  rw [finTwoToIteratedPolynomial_weightedTraceTorusClosurePolynomial
    alpha beta hbeta]
  exact weightedTraceIteratedPolynomial_right_natDegree alpha beta

/-- The second actual coordinate degree of the weighted trace closure. -/
theorem weightedTraceTorusClosurePolynomial_degreeOf_second
    (alpha beta : K) (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) :
    MvPolynomial.degreeOf 1
      (weightedTraceTorusClosurePolynomial alpha beta) = 2 := by
  rw [← bivariateEquiv_symm_natDegree_eq_degreeOf_one]
  rw [← transposeBivariate_planeCurveToBivariate]
  rw [transposeBivariate_eq_bivariateSwap]
  change (Polynomial.Bivariate.swap
    (finTwoToIteratedPolynomial (K := K)
      (weightedTraceTorusClosurePolynomial alpha beta))).natDegree = 2
  rw [finTwoToIteratedPolynomial_weightedTraceTorusClosurePolynomial
    alpha beta hbeta]
  exact weightedTraceIteratedPolynomial_left_natDegree alpha beta halpha

/-- The common affine origin of the two coordinate divisors. -/
def weightedTraceTorusClosureOrigin
    (alpha beta : K) (hbeta : beta ≠ 0) :
    AffinePlaneCurvePoint
      (weightedTraceTorusClosurePolynomial alpha beta) :=
  ⟨(0, 0), by
    rw [weightedTraceTorusClosurePolynomial, if_neg hbeta]
    exact splitTraceCoverPolynomial_origin_zero
      alpha beta 1 1 (by norm_num) (by norm_num)⟩

section Finite

variable [Fintype K] [DecidableEq K]

/-- The sound log-canonical degree budget for the weighted trace curve is at
most seven.  The sole field-size premise is the one needed by the canonical
different estimate. -/
theorem weightedTraceTorusClosure_canonicalExceptionalDegree_le_seven
    (alpha beta : K) (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hnondegenerate : alpha * beta ≠ 1)
    (hcardK : 2 < Fintype.card K)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    let f := weightedTraceTorusClosurePolynomial alpha beta
    let hf : Irreducible f :=
      weightedTraceTorusClosurePolynomial_irreducible
        alpha beta halpha hbeta hnondegenerate
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero
        (weightedTraceTorusClosurePolynomial_pderiv_second_ne_zero
          alpha beta hbeta))
    letI : DecidableEq (RatFunc K) := Classical.decEq _
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf (weightedTraceTorusClosurePolynomial_pderiv_second_ne_zero
        alpha beta hbeta)
    letI := separable_planeCurveFunctionField_over_ratFunc
      hf (weightedTraceTorusClosurePolynomial_pderiv_second_ne_zero
        alpha beta hbeta)
    finiteExtensionDivisorDegree K (PlaneCurveFunctionField f)
          (finiteExtensionCanonicalDifferentDivisor K
            (PlaneCurveFunctionField f)
            (finiteExtensionFiniteDifferentIdeal_ne_bot K
              (PlaneCurveFunctionField f))) +
        (∑ w ∈ propositionTwoExceptionalPlaces K
            (PlaneCurveFunctionField f)
            ((planeCurveFunction f 0) ^ m) ((planeCurveFunction f 1) ^ n),
          finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) w : ℤ) ≤
      7 := by
  let f := weightedTraceTorusClosurePolynomial alpha beta
  let hf : Irreducible f :=
    weightedTraceTorusClosurePolynomial_irreducible
      alpha beta halpha hbeta hnondegenerate
  let hpartialFirst :
      MvPolynomial.pderiv 0 f ≠ 0 :=
    weightedTraceTorusClosurePolynomial_pderiv_first_ne_zero
      alpha beta hbeta
  let hpartialSecond :
      MvPolynomial.pderiv 1 f ≠ 0 :=
    weightedTraceTorusClosurePolynomial_pderiv_second_ne_zero
      alpha beta hbeta
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  letI : DecidableEq (RatFunc K) := Classical.decEq _
  letI : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  have hdegreeFirst :
      MvPolynomial.degreeOf 0 f = 2 :=
    weightedTraceTorusClosurePolynomial_degreeOf_first alpha beta hbeta
  have hdegreeSecond :
      MvPolynomial.degreeOf 1 f = 2 :=
    weightedTraceTorusClosurePolynomial_degreeOf_second
      alpha beta halpha hbeta
  have hcardCurve :
      MvPolynomial.degreeOf 1 f < Fintype.card K := by
    rw [hdegreeSecond]
    exact hcardK
  have hEulerPlusOne :=
    planeCurve_canonicalDifferent_add_propositionTwoExceptional_add_one_le
      hf hpartialFirst hpartialSecond hcardCurve
      (weightedTraceTorusClosureOrigin alpha beta hbeta)
      rfl rfl m n hm hn
  rw [hdegreeFirst, hdegreeSecond] at hEulerPlusOne
  dsimp only [f] at hEulerPlusOne
  norm_num at hEulerPlusOne ⊢
  omega

end Finite

end

end BGS.Markoff
