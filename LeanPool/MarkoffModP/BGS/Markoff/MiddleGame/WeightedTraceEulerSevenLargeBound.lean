/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.WeightedTraceEulerSevenPropositionTwo
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveExhaustiveGcdEndpoint
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.NumericalCorollary
public import Mathlib.Tactic

/-!
# The Euler-seven weighted trace bound above the elementary range

This module converts the exact χ≤7 Proposition Two result into its numerical
torsion-intersection estimate when `48 < p`.
-/

@[expose] public section

namespace BGS.Markoff

open BGS.CorvajaZannier

noncomputable section


theorem weightedTraceTorsionIntersection_card_cast_le_eulerSeven_of_largeChar
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {p : ℕ} [Fact p.Prime] [CharP K p]
    (alpha beta : K)
    (hadmissible : WeightedTraceCurveIsCorvajaZannierAdmissible alpha beta)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmPrime : ¬ p ∣ m) (hnPrime : ¬ p ∣ n)
    (hlarge : 48 < p) :
    ((BGS.External.torusCurveTorsionIntersection K
        (weightedTraceTorusClosurePolynomial alpha beta) m n).card : ℝ) ≤
      corvajaZannierCorollaryTwoNumericalBound p m n 2 2 7 := by
  let f := weightedTraceTorusClosurePolynomial alpha beta
  let hf : Irreducible f :=
    irreducible_of_irreducible_map_algebraicClosure
      hadmissible.2.2.2.1
  let hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0 :=
    weightedTraceTorusClosurePolynomial_pderiv_first_ne_zero
      alpha beta hadmissible.2.1
  let hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0 :=
    weightedTraceTorusClosurePolynomial_pderiv_second_ne_zero
      alpha beta hadmissible.2.1
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let card : ℕ :=
    (BGS.External.torusCurveTorsionIntersection K f m n).card
  let gcdDegree : ℕ :=
    planeCurveExhaustiveTorsionGcdWeightedDegree
      hf hpartialSecond m n
  have hdegreeFirst :
      MvPolynomial.degreeOf 0 f = 2 :=
    weightedTraceTorusClosurePolynomial_degreeOf_first
      alpha beta hadmissible.2.1
  have hdegreeSecond :
      MvPolynomial.degreeOf 1 f = 2 :=
    weightedTraceTorusClosurePolynomial_degreeOf_second
      alpha beta hadmissible.1 hadmissible.2.1
  have hlargeActual :
      12 * MvPolynomial.degreeOf 0 f *
          MvPolynomial.degreeOf 1 f < p := by
    rw [hdegreeFirst, hdegreeSecond]
    norm_num at hlarge ⊢
    exact hlarge
  have hcardK : 2 < Fintype.card K := by
    have hdegreeCard :=
      planeCurve_degreeOf_second_lt_card_of_twelve_mul_degrees_lt_char
        hpartialFirst hpartialSecond hlargeActual
    rw [hdegreeSecond] at hdegreeCard
    exact hdegreeCard
  have hpropositionGcd :=
    weightedTracePropositionTwo_eulerSeven
      (p := p) alpha beta hadmissible m n hm hn
        hmPrime hnPrime hcardK
  have hcurve :=
    weightedTraceCurve_isGeneralCorvajaZannierPlaneCurve
      alpha beta hadmissible
  have hbidegree :=
    weightedTraceTorusClosurePolynomial_hasBidegreeAtMost
      alpha beta hadmissible.2.1
  have hnonzero :=
    poweredTorsionFunctions_ne_zero_of_isCorvajaZannierPlaneCurve
      hcurve m n hm hn
  have hcardGcd : card ≤ gcdDegree := by
    dsimp only [card, gcdDegree]
    rw [torusCurveTorsionIntersection_card_eq_torsionPoint_card]
    exact torsionPoint_card_le_planeCurveExhaustiveTorsionGcdWeightedDegree
      hf hpartialSecond m n hnonzero.1 hnonzero.2
  have hcardTrivial :
      card ≤ planeCurveTorsionLowerDegree 2 2 m n := by
    dsimp only [card, planeCurveTorsionLowerDegree]
    simpa only [min_comm] using
      torusCurveTorsionIntersection_card_le_min_bidegree_order
        f 2 2 m n hbidegree hcurve hm hn
  have hpropositionCard : PropositionTwoNumericalAlternatives
      (planeCurveTorsionLowerDegree 2 2 m n)
      (planeCurveTorsionUpperDegree 2 2 m n)
      p 7 (card : ℝ) := by
    apply propositionTwoNumericalAlternatives_mono
      (G := (card : ℝ)) (H := (gcdDegree : ℝ))
    · exact_mod_cast hcardGcd
    · simpa only [f, hf, gcdDegree, hdegreeFirst, hdegreeSecond] using
        hpropositionGcd
  let a := planeCurveTorsionLowerDegree 2 2 m n
  let b := planeCurveTorsionUpperDegree 2 2 m n
  have ha : 0 < a := by
    dsimp only [a, planeCurveTorsionLowerDegree]
    exact lt_min (Nat.mul_pos hn (by norm_num))
      (Nat.mul_pos hm (by norm_num))
  have hab : a ≤ b := by
    dsimp only [a, b, planeCurveTorsionLowerDegree,
      planeCurveTorsionUpperDegree]
    exact min_le_max
  have hbound :=
    theoremTwo_maxBound_of_propositionTwo
      a b 7 p (card : ℝ) ha hab (by norm_num)
      (Fact.out : p.Prime).pos (Nat.cast_nonneg card)
      (by exact_mod_cast hcardTrivial) (by
        simpa only [a, b] using hpropositionCard)
  have habProduct : a * b = m * n * 2 * 2 := by
    simpa only [a, b] using
      planeCurveTorsionLowerDegree_mul_upperDegree 2 2 m n
  have habProductReal :
      (a : ℝ) * (b : ℝ) = ((m * n * 2 * 2 : ℕ) : ℝ) := by
    exact_mod_cast habProduct
  rw [habProductReal] at hbound
  simpa only [card, f, corvajaZannierCorollaryTwoNumericalBound,
    Nat.cast_ofNat, mul_assoc] using hbound

end

end BGS.Markoff
