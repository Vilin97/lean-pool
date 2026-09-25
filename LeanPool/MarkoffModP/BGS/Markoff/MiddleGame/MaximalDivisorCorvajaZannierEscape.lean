/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.Diagonalization
public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.MaximalDivisorOrderEscape
public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.TraceCurveWeights
public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.WeightedTraceBound

/-!
# Feeding the weighted trace bound into maximal-divisor escape

The general Corvaja--Zannier theorem already provides a uniform estimate for
all finite multiplicative subgroups.  This adapter applies it only to the
divisibility-maximal right subgroups required by the improved middle game.
-/

@[expose] public section

namespace BGS.Markoff

/-- Diagonalize a nonzero nonparabolic fiber and apply the maximal-order
escape theorem. -/
theorem exists_iterate_with_larger_secondRotationOrder_of_nonzero_nonparabolic_maximalOrders
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (x : NormalizedPoint (ZMod p)) (hx : IsNormalizedMarkoff x)
    (hnonzero : x.u1 ≠ 0) (hnonparabolic : x.u1 ^ 2 ≠ 4)
    (hbelowEndgame :
      (rotationOrder x.u1 : ℝ) < (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hcube :
      (corvajaZannierCorollaryTwoSafeCoefficient *
        (middleGameMaximalOrders p (rotationOrder x.u1)).card) ^ 3 <
          rotationOrder x.u1)
    (hlinear :
      corvajaZannierCorollaryTwoSafeCoefficient *
        (middleGameMaximalOrders p (rotationOrder x.u1)).card *
          rotationOrder x.u1 < p)
    (hCZ :
      ∀ (w s : (quadraticFiniteField p)ˣ),
        (w : quadraticFiniteField p) ^ 2 ≠ 1 →
        algebraMapNormalizedPoint p x = splitFiberPoint w s →
        (s : quadraticFiniteField p) *
            (splitFiberProduct w * ((s⁻¹ : (quadraticFiniteField p)ˣ) :
              quadraticFiniteField p)) ≠ 1 →
        ∀ d ∈ middleGameMaximalOrders p (rotationOrder x.u1),
          ((weightedTraceEquationSolutions
            (s : quadraticFiniteField p)
            (splitFiberProduct w * ((s⁻¹ : (quadraticFiniteField p)ˣ) :
              quadraticFiniteField p))
            (Subgroup.zpowers w) (middleGameRightSubgroup p d)).card : ℝ) ≤
            corvajaZannierTraceUpperBound p (rotationOrder x.u1)
              (Nat.card (middleGameRightSubgroup p d))) :
    ∃ n : ℕ,
      rotationOrder x.u1 <
        rotationOrder ((normalizedRotate1^[n]) x).u2 := by
  obtain ⟨w, s, hw, hpoint⟩ :=
    exists_diagonalizedFiberPoint_of_nonzero_nonparabolic
      p hpTwo x hx hnonzero hnonparabolic
  exact
    exists_iterate_with_larger_secondRotationOrder_of_diagonalizedFiber_maximalOrders
      p hpTwo delta hdelta x w s hw hpoint hbelowEndgame hcube hlinear
        (hCZ w s hw hpoint)

/-- The in-repository weighted torsion-intersection theorem supplies every
maximal-order estimate needed by the improved escape step. -/
theorem exists_iterate_with_larger_secondRotationOrder_of_weightedTraceBound_maximalOrders
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (x : NormalizedPoint (ZMod p)) (hx : IsNormalizedMarkoff x)
    (hnonzero : x.u1 ≠ 0) (hnonparabolic : x.u1 ^ 2 ≠ 4)
    (hbelowEndgame :
      (rotationOrder x.u1 : ℝ) < (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hcube :
      (corvajaZannierCorollaryTwoSafeCoefficient *
        (middleGameMaximalOrders p (rotationOrder x.u1)).card) ^ 3 <
          rotationOrder x.u1)
    (hlinear :
      corvajaZannierCorollaryTwoSafeCoefficient *
        (middleGameMaximalOrders p (rotationOrder x.u1)).card *
          rotationOrder x.u1 < p)
    (hBound :
      WeightedTraceTorsionIntersectionBound p (quadraticFiniteField p)) :
    ∃ n : ℕ,
      rotationOrder x.u1 <
        rotationOrder ((normalizedRotate1^[n]) x).u2 := by
  apply
    exists_iterate_with_larger_secondRotationOrder_of_nonzero_nonparabolic_maximalOrders
      p hpTwo delta hdelta x hx hnonzero hnonparabolic hbelowEndgame
        hcube hlinear
  intro w s hw hpoint _hnondegenerate d _hd
  let alpha : quadraticFiniteField p := s
  let beta : quadraticFiniteField p :=
    splitFiberProduct w *
      ((s⁻¹ : (quadraticFiniteField p)ˣ) : quadraticFiniteField p)
  let Hleft : Subgroup (quadraticFiniteField p)ˣ := Subgroup.zpowers w
  let Hright : Subgroup (quadraticFiniteField p)ˣ :=
    middleGameRightSubgroup p d
  have hadmissible :
      WeightedTraceCurveIsCorvajaZannierAdmissible alpha beta := by
    simpa [alpha, beta] using
      diagonalizedFiber_weightedTraceCurve_isCorvajaZannierAdmissible
        p hpTwo x hnonzero w s hw hpoint
  have hbound :=
    weightedTraceEquationSolutions_card_cast_le_of_weightedTraceBound
      p (quadraticFiniteField p) hBound alpha beta Hleft Hright hadmissible
  have htrace :
      algebraMap (ZMod p) (quadraticFiniteField p) x.u1 =
        splitTorusTrace w :=
    congrArg NormalizedPoint.u1 hpoint
  have horder : orderOf w = rotationOrder x.u1 := by
    rw [← rotationOrder_eq_orderOf_extensionEigenvalue x.u1 w hw htrace]
  have hleftCard : Nat.card Hleft = rotationOrder x.u1 := by
    rw [Nat.card_zpowers, horder]
  simpa [alpha, beta, Hleft, Hright, hleftCard] using hbound

end BGS.Markoff
