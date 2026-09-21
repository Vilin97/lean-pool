/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.Diagonalization
import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.WeightedTraceBound
import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.TraceCurveWeights

/-!
# Feeding the geometric Corvaja--Zannier estimate into a Markoff move

This module connects the weighted torsion-intersection bound to the already completed middle-game
order-escape chain.  The actual weighted trace curve's admissibility is proved from its Markoff
coefficients.

Given those premises, Lean returns a natural iterate of the Markoff rotation with strictly larger
neighboring rotation order.  No independent weighted-finset estimate remains between the cited
curve theorem and the dynamical conclusion.
-/

namespace BGS.Markoff

/-- The uniform weighted-trace bound, after Lean verifies every concrete diagonalized Markoff
trace curve, produces an actual middle-game order-increasing iterate. -/
theorem exists_iterate_with_larger_secondRotationOrder_of_weightedTraceBound
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)] (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (x : NormalizedPoint (ZMod p)) (hx : IsNormalizedMarkoff x)
    (hnonzero : x.u1 ≠ 0) (hnonparabolic : x.u1 ^ 2 ≠ 4)
    (hbelowEndgame :
      (rotationOrder x.u1 : ℝ) < (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hcube :
      (corvajaZannierCorollaryTwoSafeCoefficient *
          ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 <
        rotationOrder x.u1)
    (hlinear :
      corvajaZannierCorollaryTwoSafeCoefficient *
          ((p - 1).divisors.card + (p + 1).divisors.card) *
        rotationOrder x.u1 < p)
    (hBound : WeightedTraceTorsionIntersectionBound p (quadraticFiniteField p)) :
    ∃ n : ℕ,
      rotationOrder x.u1 < rotationOrder ((normalizedRotate1^[n]) x).u2 := by
  apply exists_iterate_with_larger_secondRotationOrder_of_nonzero_nonparabolic
    p hpTwo delta hdelta x hx hnonzero hnonparabolic hbelowEndgame hcube hlinear
  intro w s hw hpoint _hnondegenerate d hd
  let alpha : quadraticFiniteField p := s
  let beta : quadraticFiniteField p :=
    splitFiberProduct w * ((s⁻¹ : (quadraticFiniteField p)ˣ) : quadraticFiniteField p)
  let H₁ : Subgroup (quadraticFiniteField p)ˣ := Subgroup.zpowers w
  let H₂ : Subgroup (quadraticFiniteField p)ˣ := middleGameRightSubgroup p d
  have hadmissible : WeightedTraceCurveIsCorvajaZannierAdmissible alpha beta := by
    simpa [alpha, beta] using
      diagonalizedFiber_weightedTraceCurve_isCorvajaZannierAdmissible
        p hpTwo x hnonzero w s hw hpoint
  have hbound :=
    weightedTraceEquationSolutions_card_cast_le_of_weightedTraceBound
      p (quadraticFiniteField p) hBound alpha beta H₁ H₂ hadmissible
  have htrace :
      algebraMap (ZMod p) (quadraticFiniteField p) x.u1 = splitTorusTrace w :=
    congrArg NormalizedPoint.u1 hpoint
  have horder : orderOf w = rotationOrder x.u1 := by
    rw [← rotationOrder_eq_orderOf_extensionEigenvalue x.u1 w hw htrace]
  have hleftCard : Nat.card H₁ = rotationOrder x.u1 := by
    rw [Nat.card_zpowers, horder]
  simpa [alpha, beta, H₁, H₂, hleftCard] using hbound

end BGS.Markoff
