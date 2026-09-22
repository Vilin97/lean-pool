/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.External.GeneralCurveTheorems
import LeanPool.MarkoffModP.BGS.Markoff.Endgame.WeilFromGeneralHasse
import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.WeightedTraceBound
import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.WeightedIrreducibility
import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.WeightedNotSubtorus
import LeanPool.MarkoffModP.BGS.CorvajaZannier.GeneralCorvajaZannier

/-!
# Applying general Corvaja--Zannier to the weighted trace curve
-/

namespace BGS.Markoff

noncomputable section

variable {K : Type*} [Field K]

theorem weightedTraceTorusClosurePolynomial_pderiv_first_ne_zero
    (alpha beta : K) (hbeta : beta ≠ 0) :
    MvPolynomial.pderiv 0
      (weightedTraceTorusClosurePolynomial alpha beta) ≠ 0 := by
  rw [weightedTraceTorusClosurePolynomial, ite_eq_right hbeta]
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval ![(0 : K), (0 : K)]) hzero
  simp [splitTraceCoverPolynomial] at heval
  exact hbeta heval

theorem weightedTraceTorusClosurePolynomial_pderiv_second_ne_zero
    (alpha beta : K) (hbeta : beta ≠ 0) :
    MvPolynomial.pderiv 1
      (weightedTraceTorusClosurePolynomial alpha beta) ≠ 0 := by
  rw [weightedTraceTorusClosurePolynomial, ite_eq_right hbeta]
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval ![(0 : K), (0 : K)]) hzero
  simp [splitTraceCoverPolynomial] at heval

theorem weightedTraceCurveNotSubtorusTranslate_general
    (alpha beta : K) (hbeta : beta ≠ 0)
    (hnot : WeightedTraceCurveNotSubtorusTranslate alpha beta) :
    BGS.External.TorusCurveNotSubtorusTranslate
      (weightedTraceTorusClosurePolynomial alpha beta) := by
  intro a b hab c
  obtain ⟨x, y, hcurve, hcharacter⟩ := hnot a b hab c
  refine ⟨x, y, ?_, hcharacter⟩
  rw [map_weightedTraceTorusClosurePolynomial_of_beta_ne_zero
    (algebraMap K (AlgebraicClosure K)) alpha beta hbeta]
  exact (eval_weightedTraceTorusClosurePolynomial_eq_zero_iff
    (algebraMap K (AlgebraicClosure K) alpha)
    (algebraMap K (AlgebraicClosure K) beta) x y).2 hcurve

theorem weightedTraceTorusClosurePolynomial_hasBidegreeAtMost
    (alpha beta : K) (hbeta : beta ≠ 0) :
    BGS.External.HasBidegreeAtMost
      (weightedTraceTorusClosurePolynomial alpha beta) 2 2 := by
  rw [weightedTraceTorusClosurePolynomial, ite_eq_right hbeta]
  simpa using splitTraceCoverPolynomial_hasBidegreeAtMost alpha beta 1 1

theorem weightedTraceCurve_isGeneralCorvajaZannierPlaneCurve
    (alpha beta : K) (hadmissible :
      WeightedTraceCurveIsCorvajaZannierAdmissible alpha beta) :
    BGS.External.IsCorvajaZannierPlaneCurve
      (weightedTraceTorusClosurePolynomial alpha beta) := by
  refine ⟨hadmissible.2.2.2.1,
    weightedTraceCurveNotSubtorusTranslate_general
      alpha beta hadmissible.2.1 hadmissible.2.2.2.2,
    weightedTraceTorusClosurePolynomial_pderiv_first_ne_zero
      alpha beta hadmissible.2.1,
    weightedTraceTorusClosurePolynomial_pderiv_second_ne_zero
      alpha beta hadmissible.2.1⟩

section Finite

variable [Fintype K] [DecidableEq K]

theorem generalTorusTorsionIntersection_weightedTrace_eq
    (alpha beta : K) (leftOrder rightOrder : ℕ) :
    BGS.External.torusCurveTorsionIntersection K
      (weightedTraceTorusClosurePolynomial alpha beta) rightOrder leftOrder =
      weightedTraceCurveTorsionIntersection alpha beta leftOrder rightOrder := by
  ext z
  rw [BGS.External.mem_torusCurveTorsionIntersection_iff,
    mem_weightedTraceCurveTorsionIntersection_iff,
    eval_weightedTraceTorusClosurePolynomial_eq_zero_iff]
  tauto

end Finite

/-- The weighted-trace estimate is a proved application of the one general
Corvaja--Zannier plane-curve theorem. -/
theorem corvajaZannierWeightedTraceBound_of_generalTheorem
    (hGeneral : BGS.External.GeneralCorvajaZannierPlaneCurveTheorem)
    (p : ℕ) [Fact p.Prime]
    (K : Type) [Field K] [Fintype K] [DecidableEq K] [CharP K p] :
    WeightedTraceTorsionIntersectionBound p K := by
  intro alpha beta leftOrder rightOrder hadmissible
    hleftPositive hrightPositive hleftPrime hrightPrime
  have hsource := hGeneral p K
    (weightedTraceTorusClosurePolynomial alpha beta)
    2 2 rightOrder leftOrder (by norm_num) (by norm_num)
    (weightedTraceTorusClosurePolynomial_hasBidegreeAtMost
      alpha beta hadmissible.2.1)
    (weightedTraceCurve_isGeneralCorvajaZannierPlaneCurve
      alpha beta hadmissible)
    hrightPositive hleftPositive hrightPrime hleftPrime
  rw [generalTorusTorsionIntersection_weightedTrace_eq] at hsource
  rw [show BGS.External.planeTorusEulerCharacteristicBound 2 2 = 8 by
    norm_num [BGS.External.planeTorusEulerCharacteristicBound]] at hsource
  exact hsource.trans <| by
    simpa [corvajaZannierTraceUpperBound,
      mul_comm, mul_left_comm, mul_assoc] using
      (corvajaZannierCorollaryTwoNumericalBound_bidegree_two_euler_eight_le
        p rightOrder leftOrder)

/-- The weighted-trace Corvaja--Zannier estimate, obtained by instantiating
the unconditional general plane-curve theorem proved in this repository. -/
theorem corvajaZannierWeightedTraceBound
    (p : ℕ) [Fact p.Prime]
    (K : Type) [Field K] [Fintype K] [DecidableEq K] [CharP K p] :
    WeightedTraceTorsionIntersectionBound p K :=
  corvajaZannierWeightedTraceBound_of_generalTheorem
    BGS.CorvajaZannier.generalCorvajaZannierPlaneCurveTheorem p K

end

end BGS.Markoff
