/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.EulerSevenPairedMaximalDivisorMiddleGame
public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.MiddleGameThenEndgame
public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.PairedMaximalDivisorCorvajaZannierEscape

/-!
# Paired maximal-divisor middle-game assembly

This module lifts the paired maximal-order escape from a chosen coordinate to
the maximum of the three coordinate rotation orders.
-/

@[expose] public section

namespace BGS.Markoff

open BGS.NumberTheory

noncomputable section

/-- One paired middle-game step strictly increases the maximum coordinate
order under the coefficient-sensitive maximal-divisor inequalities. -/
theorem
    exists_sameNormalizedComponent_maximalOrder_increase_of_pairedMaximalDivisorBounds
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpTwo : p ≠ 2)
    {delta : ℝ} (hdelta : delta ≤ (1 : ℝ) / 2)
    (x : NormalizedMarkoffSurface (ZMod p))
    (hbelow : (maximalCoordinateRotationOrder x.1 : ℝ) <
      (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hcube :
      (6 *
        (middleGameMaximalOrders p
          (maximalCoordinateRotationOrder x.1)).card) ^ 3 <
        maximalCoordinateRotationOrder x.1)
    (hlinear :
      24 *
        (middleGameMaximalOrders p
          (maximalCoordinateRotationOrder x.1)).card *
        maximalCoordinateRotationOrder x.1 < p) :
    ∃ y : NormalizedMarkoffSurface (ZMod p),
      SameNormalizedComponent x y ∧
        maximalCoordinateRotationOrder x.1 <
          maximalCoordinateRotationOrder y.1 := by
  apply exists_sameNormalizedComponent_maximalOrder_increase_of_eulerSevenPairedMaximalDivisorBounds
    p hpTwo hdelta x hbelow _ hlinear
  exact lt_of_le_of_lt (eulerSeven_bound_le_six_cube _) hcube

end

end BGS.Markoff
