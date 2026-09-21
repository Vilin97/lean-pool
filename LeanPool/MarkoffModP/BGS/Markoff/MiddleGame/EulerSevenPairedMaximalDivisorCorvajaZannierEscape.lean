/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.Diagonalization
import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.EulerSevenPairedMaximalDivisorOrderEscape
import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.TraceCurveWeights

/-!
# Unconditional Euler-seven paired maximal-divisor middle-game escape

The exact support-index and Euler-characteristic calculation improves the
paired cube condition from `(6 * K)^3 < d` to `189 * K^3 < d`.
-/

namespace BGS.Markoff

/-- Diagonalize a nonzero nonparabolic fiber and apply the exact
Euler-seven paired maximal-order escape theorem. -/
theorem
    exists_iterate_with_larger_secondRotationOrder_of_nonzero_nonparabolic_eulerSevenPairedMaximalOrders
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (x : NormalizedPoint (ZMod p)) (hx : IsNormalizedMarkoff x)
    (hnonzero : x.u1 ≠ 0) (hnonparabolic : x.u1 ^ 2 ≠ 4)
    (hbelowEndgame :
      (rotationOrder x.u1 : ℝ) <
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hcube :
      189 *
        (middleGameMaximalOrders p (rotationOrder x.u1)).card ^ 3 <
          rotationOrder x.u1)
    (hlinear :
      24 * (middleGameMaximalOrders p (rotationOrder x.u1)).card *
          rotationOrder x.u1 < p) :
    ∃ n : ℕ,
      rotationOrder x.u1 <
        rotationOrder ((normalizedRotate1^[n]) x).u2 := by
  obtain ⟨w, s, hw, hpoint⟩ :=
    exists_diagonalizedFiberPoint_of_nonzero_nonparabolic
      p hpTwo x hx hnonzero hnonparabolic
  have hadmissible :
      WeightedTraceCurveIsCorvajaZannierAdmissible
        (s : quadraticFiniteField p)
        (splitFiberProduct w *
          ((s⁻¹ : (quadraticFiniteField p)ˣ) : quadraticFiniteField p)) :=
    diagonalizedFiber_weightedTraceCurve_isCorvajaZannierAdmissible
      p hpTwo x hnonzero w s hw hpoint
  exact
    exists_iterate_with_larger_secondRotationOrder_of_diagonalizedFiber_eulerSevenPairedMaximalOrders
      p hpTwo delta hdelta x w s hw hpoint hadmissible
        hbelowEndgame hcube hlinear

end BGS.Markoff
