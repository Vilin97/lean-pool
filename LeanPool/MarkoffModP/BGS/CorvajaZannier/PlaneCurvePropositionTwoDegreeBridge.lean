/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveExhaustiveGcdEndpoint
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveCanonicalDegreeBound
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PropositionTwoDegreeMonotonicity
import Mathlib.Tactic

/-!
# From actual plane-curve degrees to the public Proposition 2 certificate

The canonical divisor argument naturally computes with the actual coordinate
degrees `degreeOf 0 f` and `degreeOf 1 f`.  The public theorem instead accepts
arbitrary declared bidegree bounds.  This file performs that last change of
degree data without asserting the false monotonicity of Proposition 2's degree
alternative.
-/

namespace BGS.CorvajaZannier

noncomputable section

/-- The actual lower powered-coordinate degree is bounded by the lower degree
built from any declared bidegree bounds. -/
theorem planeCurveTorsionLowerDegree_actual_le_public
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (firstDegree secondDegree firstOrder secondOrder : ℕ)
    (hbidegree : BGS.External.HasBidegreeAtMost
      f firstDegree secondDegree) :
    planeCurveTorsionLowerDegree
        (MvPolynomial.degreeOf 0 f) (MvPolynomial.degreeOf 1 f)
        firstOrder secondOrder ≤
      planeCurveTorsionLowerDegree
        firstDegree secondDegree firstOrder secondOrder := by
  unfold planeCurveTorsionLowerDegree
  exact min_le_min
    (Nat.mul_le_mul_left secondOrder
      (degreeOf_first_le_of_hasBidegreeAtMost hbidegree))
    (Nat.mul_le_mul_left firstOrder
      (degreeOf_second_le_of_hasBidegreeAtMost hbidegree))

/-- The actual upper powered-coordinate degree is bounded by the upper degree
built from any declared bidegree bounds. -/
theorem planeCurveTorsionUpperDegree_actual_le_public
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (firstDegree secondDegree firstOrder secondOrder : ℕ)
    (hbidegree : BGS.External.HasBidegreeAtMost
      f firstDegree secondDegree) :
    planeCurveTorsionUpperDegree
        (MvPolynomial.degreeOf 0 f) (MvPolynomial.degreeOf 1 f)
        firstOrder secondOrder ≤
      planeCurveTorsionUpperDegree
        firstDegree secondDegree firstOrder secondOrder := by
  unfold planeCurveTorsionUpperDegree
  exact max_le_max
    (Nat.mul_le_mul_left secondOrder
      (degreeOf_first_le_of_hasBidegreeAtMost hbidegree))
    (Nat.mul_le_mul_left firstOrder
      (degreeOf_second_le_of_hasBidegreeAtMost hbidegree))

/-- The actual bidegree Euler budget is bounded by the public one. -/
theorem planeCurve_actualEulerBudget_le_public
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (firstDegree secondDegree : ℕ)
    (hbidegree : BGS.External.HasBidegreeAtMost
      f firstDegree secondDegree) :
    2 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f ≤
      2 * firstDegree * secondDegree := by
  exact Nat.mul_le_mul
    (Nat.mul_le_mul_left 2
      (degreeOf_first_le_of_hasBidegreeAtMost hbidegree))
    (degreeOf_second_le_of_hasBidegreeAtMost hbidegree)

/-- Proposition 2 at the actual coordinate degrees supplies the public
certificate at arbitrary declared bidegree bounds.

The actual Proposition 2 input is allowed to bound the exhaustive gcd degree.
The certificate itself uses the torsion-point cardinality.  It is below that
gcd degree, has the required trivial bound at the actual degrees, and can
therefore be transported to the larger public degrees by
`propositionTwoNumericalAlternatives_mono_degreeBounds`. -/
theorem planeCurvePropositionTwoCertificate_of_actualDegree_exhaustiveGcd
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {f : MvPolynomial (Fin 2) K}
    (p firstDegree secondDegree firstOrder secondOrder : ℕ)
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hbidegree : BGS.External.HasBidegreeAtMost
      f firstDegree secondDegree)
    (hcurve : BGS.External.IsCorvajaZannierPlaneCurve f)
    (hfirstDegree : 0 < firstDegree)
    (hsecondDegree : 0 < secondDegree)
    (hfirstOrder : 0 < firstOrder) (hsecondOrder : 0 < secondOrder)
    (hfirstNonzero : planeCurveFunction f 0 ^ firstOrder - 1 ≠ 0)
    (hsecondNonzero : planeCurveFunction f 1 ^ secondOrder - 1 ≠ 0)
    (hpropositionTwoActual : PropositionTwoNumericalAlternatives
      (planeCurveTorsionLowerDegree
        (MvPolynomial.degreeOf 0 f) (MvPolynomial.degreeOf 1 f)
        firstOrder secondOrder)
      (planeCurveTorsionUpperDegree
        (MvPolynomial.degreeOf 0 f) (MvPolynomial.degreeOf 1 f)
        firstOrder secondOrder)
      p (2 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f)
      (planeCurveExhaustiveTorsionGcdWeightedDegree
        hf hpartialSecond firstOrder secondOrder : ℝ)) :
    PlaneCurvePropositionTwoCertificate
      p K f firstDegree secondDegree firstOrder secondOrder := by
  let actualLower : ℕ := planeCurveTorsionLowerDegree
    (MvPolynomial.degreeOf 0 f) (MvPolynomial.degreeOf 1 f)
    firstOrder secondOrder
  let actualUpper : ℕ := planeCurveTorsionUpperDegree
    (MvPolynomial.degreeOf 0 f) (MvPolynomial.degreeOf 1 f)
    firstOrder secondOrder
  let publicLower : ℕ := planeCurveTorsionLowerDegree
    firstDegree secondDegree firstOrder secondOrder
  let publicUpper : ℕ := planeCurveTorsionUpperDegree
    firstDegree secondDegree firstOrder secondOrder
  let actualChi : ℕ :=
    2 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f
  let publicChi : ℕ := 2 * firstDegree * secondDegree
  let card : ℕ :=
    (BGS.External.torusCurveTorsionIntersection
      K f firstOrder secondOrder).card
  let gcdDegree : ℕ := planeCurveExhaustiveTorsionGcdWeightedDegree
    hf hpartialSecond firstOrder secondOrder
  have hfirstActual : 0 < MvPolynomial.degreeOf 0 f :=
    degreeOf_first_pos_of_pderiv_ne_zero hcurve.2.2.1
  have hsecondActual : 0 < MvPolynomial.degreeOf 1 f :=
    degreeOf_second_pos_of_pderiv_ne_zero hcurve.2.2.2
  have hactualLowerPos : 0 < actualLower := by
    dsimp only [actualLower, planeCurveTorsionLowerDegree]
    exact lt_min (Nat.mul_pos hsecondOrder hfirstActual)
      (Nat.mul_pos hfirstOrder hsecondActual)
  have hactualUpperPos : 0 < actualUpper := by
    dsimp only [actualUpper, planeCurveTorsionUpperDegree]
    exact lt_of_lt_of_le
      (Nat.mul_pos hsecondOrder hfirstActual) (le_max_left _ _)
  have hactualLowerPublic : actualLower ≤ publicLower := by
    exact planeCurveTorsionLowerDegree_actual_le_public
      firstDegree secondDegree firstOrder secondOrder hbidegree
  have hactualUpperPublic : actualUpper ≤ publicUpper := by
    exact planeCurveTorsionUpperDegree_actual_le_public
      firstDegree secondDegree firstOrder secondOrder hbidegree
  have hactualChiPublic : actualChi ≤ publicChi := by
    exact planeCurve_actualEulerBudget_le_public
      firstDegree secondDegree hbidegree
  have hpublicChiPos : 0 < publicChi := by
    dsimp only [publicChi]
    positivity
  have hcardActualTrivial : card ≤ actualLower := by
    dsimp only [card, actualLower, planeCurveTorsionLowerDegree]
    simpa only [min_comm] using
      torusCurveTorsionIntersection_card_le_min_bidegree_order
        f (MvPolynomial.degreeOf 0 f) (MvPolynomial.degreeOf 1 f)
          firstOrder secondOrder (hasBidegreeAtMost_degreeOf f) hcurve
          hfirstOrder hsecondOrder
  have hcardGcd : card ≤ gcdDegree := by
    dsimp only [card, gcdDegree]
    rw [torusCurveTorsionIntersection_card_eq_torsionPoint_card]
    exact torsionPoint_card_le_planeCurveExhaustiveTorsionGcdWeightedDegree
      hf hpartialSecond firstOrder secondOrder
        hfirstNonzero hsecondNonzero
  have hpropositionTwoCardActual : PropositionTwoNumericalAlternatives
      actualLower actualUpper p actualChi (card : ℝ) := by
    apply propositionTwoNumericalAlternatives_mono
      (G := (card : ℝ)) (H := (gcdDegree : ℝ))
    · exact_mod_cast hcardGcd
    · simpa only [actualLower, actualUpper, actualChi, gcdDegree] using
        hpropositionTwoActual
  have hpropositionTwoCardPublic : PropositionTwoNumericalAlternatives
      publicLower publicUpper p publicChi (card : ℝ) := by
    exact propositionTwoNumericalAlternatives_mono_degreeBounds
      actualLower actualUpper publicLower publicUpper p actualChi publicChi
      (card : ℝ) hactualLowerPos hactualUpperPos
      hactualLowerPublic hactualUpperPublic hactualChiPublic hpublicChiPos
      (by exact_mod_cast hcardActualTrivial) hpropositionTwoCardActual
  refine ⟨(card : ℝ), le_rfl, ?_, ?_⟩
  · exact_mod_cast hcardActualTrivial.trans hactualLowerPublic
  · simpa only [publicLower, publicUpper, publicChi] using
      hpropositionTwoCardPublic

/-- Pointwise Proposition 2 at the actual source-coordinate heights assembles
the exact universal certificate proposition expected by the public endpoint.

This theorem is intentionally a composition boundary, not a replacement for
the geometric proof: its hypothesis still asks for the actual-height
Proposition 2 estimate for the exhaustive gcd divisor. -/
theorem generalPlaneCurvePropositionTwoCertificatesAboveElementaryRange_of_actualDegree
    (hactual : ∀ (p : ℕ) [Fact p.Prime]
      (K : Type) [Field K] [Fintype K] [DecidableEq K] [CharP K p]
      (f : MvPolynomial (Fin 2) K)
      (firstDegree secondDegree firstOrder secondOrder : ℕ)
      (_hfirstDegree : 0 < firstDegree)
      (_hsecondDegree : 0 < secondDegree)
      (_hbidegree : BGS.External.HasBidegreeAtMost f firstDegree secondDegree)
      (hcurve : BGS.External.IsCorvajaZannierPlaneCurve f)
      (_hfirstOrder : 0 < firstOrder)
      (_hsecondOrder : 0 < secondOrder)
      (_hfirstPrimeToChar : ¬ p ∣ firstOrder)
      (_hsecondPrimeToChar : ¬ p ∣ secondOrder)
      (_hlarge : 12 * firstDegree * secondDegree < p),
      let hf : Irreducible f :=
        irreducible_of_irreducible_map_algebraicClosure
          hcurve.1
      PropositionTwoNumericalAlternatives
        (planeCurveTorsionLowerDegree
          (MvPolynomial.degreeOf 0 f) (MvPolynomial.degreeOf 1 f)
          firstOrder secondOrder)
        (planeCurveTorsionUpperDegree
          (MvPolynomial.degreeOf 0 f) (MvPolynomial.degreeOf 1 f)
          firstOrder secondOrder)
        p (2 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f)
        (planeCurveExhaustiveTorsionGcdWeightedDegree
          hf hcurve.2.2.2
          firstOrder secondOrder : ℝ)) :
    GeneralPlaneCurvePropositionTwoCertificatesAboveElementaryRange := by
  unfold GeneralPlaneCurvePropositionTwoCertificatesAboveElementaryRange
  intro p _ K _ _ _ _ f firstDegree secondDegree firstOrder secondOrder
    hfirstDegree hsecondDegree hbidegree hcurve hfirstOrder hsecondOrder
    hfirstPrimeToChar hsecondPrimeToChar hlarge
  let hf : Irreducible f :=
    irreducible_of_irreducible_map_algebraicClosure hcurve.1
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  have hnonzero :
      planeCurveFunction f 0 ^ firstOrder - 1 ≠ 0 ∧
        planeCurveFunction f 1 ^ secondOrder - 1 ≠ 0 :=
    poweredTorsionFunctions_ne_zero_of_isCorvajaZannierPlaneCurve
      hcurve firstOrder secondOrder hfirstOrder hsecondOrder
  apply planeCurvePropositionTwoCertificate_of_actualDegree_exhaustiveGcd
    p firstDegree secondDegree firstOrder secondOrder hf hcurve.2.2.2
      hbidegree hcurve hfirstDegree hsecondDegree hfirstOrder hsecondOrder
      hnonzero.1 hnonzero.2
  simpa only [hf] using hactual p (K := K) f
    firstDegree secondDegree firstOrder secondOrder
    hfirstDegree hsecondDegree hbidegree hcurve hfirstOrder hsecondOrder
    hfirstPrimeToChar hsecondPrimeToChar hlarge

end

end BGS.CorvajaZannier
