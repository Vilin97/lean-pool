/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.EndpointComposition
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.TorsionExhaustiveGcdDivisorBound

/-!
# Exhaustive gcd divisor at the plane-curve endpoint

This module converts the exhaustive, degree-weighted gcd divisor into the
certificate expected by the public Corvaja--Zannier endpoint.  The sharp
bidegree fiber count supplies the certificate's elementary upper bound, while
the injection of rational torsion points into the exhaustive divisor lets us
transfer Proposition 2 downward to the actual torsion-point cardinality.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

/-- The exhaustive weighted gcd divisor supplies a Proposition 2 certificate.

The certificate uses the actual torsion-point cardinality as its gcd quantity.
The bidegree estimate gives its trivial bound, and monotonicity transfers the
Proposition 2 alternatives from the larger exhaustive weighted gcd degree. -/
theorem planeCurvePropositionTwoCertificate_of_exhaustiveGcdWeightedDegree_and_bidegree
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {f : MvPolynomial (Fin 2) K}
    (p firstDegree secondDegree firstOrder secondOrder : ℕ)
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hbidegree : BGS.External.HasBidegreeAtMost
      f firstDegree secondDegree)
    (hcurve : BGS.External.IsCorvajaZannierPlaneCurve f)
    (hfirstOrder : 0 < firstOrder) (hsecondOrder : 0 < secondOrder)
    (hfirstNonzero : planeCurveFunction f 0 ^ firstOrder - 1 ≠ 0)
    (hsecondNonzero : planeCurveFunction f 1 ^ secondOrder - 1 ≠ 0)
    (hpropositionTwo : PropositionTwoNumericalAlternatives
      (planeCurveTorsionLowerDegree
        firstDegree secondDegree firstOrder secondOrder)
      (planeCurveTorsionUpperDegree
        firstDegree secondDegree firstOrder secondOrder)
      p (2 * firstDegree * secondDegree)
      (planeCurveExhaustiveTorsionGcdWeightedDegree
        hf hpartialSecond firstOrder secondOrder : ℝ)) :
    PlaneCurvePropositionTwoCertificate
      p K f firstDegree secondDegree firstOrder secondOrder := by
  let card : ℕ :=
    (BGS.External.torusCurveTorsionIntersection
      K f firstOrder secondOrder).card
  let gcdDegree : ℕ :=
    planeCurveExhaustiveTorsionGcdWeightedDegree
      hf hpartialSecond firstOrder secondOrder
  have hcardTrivial : card ≤ planeCurveTorsionLowerDegree
      firstDegree secondDegree firstOrder secondOrder := by
    dsimp only [card, planeCurveTorsionLowerDegree]
    simpa only [min_comm] using
      torusCurveTorsionIntersection_card_le_min_bidegree_order
        f firstDegree secondDegree firstOrder secondOrder
        hbidegree hcurve hfirstOrder hsecondOrder
  have hcardGcd : card ≤ gcdDegree := by
    dsimp only [card, gcdDegree]
    rw [torusCurveTorsionIntersection_card_eq_torsionPoint_card]
    exact torsionPoint_card_le_planeCurveExhaustiveTorsionGcdWeightedDegree
      hf hpartialSecond firstOrder secondOrder
        hfirstNonzero hsecondNonzero
  refine ⟨(card : ℝ), le_rfl, ?_, ?_⟩
  · exact_mod_cast hcardTrivial
  · apply propositionTwoNumericalAlternatives_mono
      (G := (card : ℝ)) (H := (gcdDegree : ℝ))
    · exact_mod_cast hcardGcd
    · simpa only [gcdDegree] using hpropositionTwo

end


end BGS.CorvajaZannier
