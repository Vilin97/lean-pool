/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.EulerSevenPairedMaximalDivisorOrderEscape
public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.MaximalDivisorOrderEscape
public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.PairedMaximalDivisorCorvajaZannierStep

/-!
# Paired nonparabolic order escape using maximal divisors

This is the geometric diagonalized-fiber step for the paired maximal-order
union.  A hypothetical bounded target coordinate is first shown to be
nonparabolic.  Its trace is then represented by a non-two-torsion element of
a maximal candidate subgroup, exactly the kind of witness excluded by the
paired finite escape theorem.
-/

@[expose] public section

namespace BGS.Markoff

/-- Complete order escape from a diagonalized fiber under the paired
coefficient conditions `(6*K)^3 < currentOrder` and
`24*K*currentOrder < p`. -/
theorem
    exists_iterate_with_larger_secondRotationOrder_of_diagonalizedFiber_pairedMaximalOrders
    (p : ℕ) [Fact p.Prime]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (x : NormalizedPoint (ZMod p))
    (w s : (quadraticFiniteField p)ˣ)
    (hw : (w : quadraticFiniteField p) ^ 2 ≠ 1)
    (hpoint : algebraMapNormalizedPoint p x = splitFiberPoint w s)
    (hadmissible :
      WeightedTraceCurveIsCorvajaZannierAdmissible
        (s : quadraticFiniteField p)
        (splitFiberProduct w *
          ((s⁻¹ : (quadraticFiniteField p)ˣ) : quadraticFiniteField p)))
    (hbelowEndgame :
      (rotationOrder x.u1 : ℝ) <
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hcube :
      (6 *
        (middleGameMaximalOrders p (rotationOrder x.u1)).card) ^ 3 <
          rotationOrder x.u1)
    (hlinear :
      24 * (middleGameMaximalOrders p (rotationOrder x.u1)).card *
          rotationOrder x.u1 < p) :
    ∃ n : ℕ,
      rotationOrder x.u1 <
        rotationOrder ((normalizedRotate1^[n]) x).u2 := by
  apply exists_iterate_larger_secondRotationOrder_of_diagonalizedFiber_eulerSevenPairedMaximalOrders
    p hpTwo delta hdelta x w s hw hpoint hadmissible hbelowEndgame _ hlinear
  exact lt_of_le_of_lt (eulerSeven_bound_le_six_cube _) hcube

end BGS.Markoff
