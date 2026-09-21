/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.NumberTheory.JointMaximalDivisorCertificate

/-!
# Arithmetic core of the joint maximal-divisor algorithm

The paper's independent `2C` estimate is replaced by a certified square
envelope `M^2 ≤ S`. This removes square roots and division from both the
connectivity test and the rank-refinement bound.
-/

namespace BGS.NumberTheory

/-- A paper-style first-interval witness forces failure of the joint square
test. -/
theorem jointSquareEnvelope_failure_of_firstInterval
    {p n M S : ℕ}
    (hn : n + 2 ≤ 4 * p)
    (hfirst : 128 * p < (3 * M) ^ 8)
    (hSquare : M ^ 2 ≤ S) :
    32 * (n + 2) < 3 ^ 8 * S ^ 4 := by
  calc
    32 * (n + 2) ≤ 32 * (4 * p) := Nat.mul_le_mul_left 32 hn
    _ = 128 * p := by ring
    _ < (3 * M) ^ 8 := hfirst
    _ = 3 ^ 8 * (M ^ 2) ^ 4 := by ring
    _ ≤ 3 ^ 8 * S ^ 4 := by
      gcongr

/-- The joint envelope shrinks the divisor range in the rank-refinement
step from the paper's `162 C^3` to the root-free bound `81 C S / 2`. -/
theorem jointRankRefinement_of_firstInterval
    {d M C S : ℕ}
    (hfirst : 4 * d < 81 * M ^ 3)
    (hLinear : M ≤ 2 * C)
    (hSquare : M ^ 2 ≤ S) :
    2 * d < 81 * C * S := by
  have hCube : M ^ 3 ≤ 2 * C * S := by
    calc
      M ^ 3 = M * M ^ 2 := by ring
      _ ≤ (2 * C) * S := Nat.mul_le_mul hLinear hSquare
      _ = 2 * C * S := rfl
  have hscaled : 4 * d < 81 * (2 * C * S) :=
    hfirst.trans_le (Nat.mul_le_mul_left 81 hCube)
  by_contra hnot
  have hreverse : 81 * C * S ≤ 2 * d := Nat.le_of_not_gt hnot
  have hdouble : 81 * (2 * C * S) ≤ 4 * d := by
    calc
      81 * (2 * C * S) = 2 * (81 * C * S) := by ring
      _ ≤ 2 * (2 * d) := Nat.mul_le_mul_left 2 hreverse
      _ = 4 * d := by ring
  exact (Nat.not_le_of_lt hscaled) hdouble

/-- If the joint square test succeeds, no first-interval witness can
exist. -/
theorem no_firstInterval_of_jointSquareEnvelope
    {p n M S : ℕ}
    (hn : n + 2 ≤ 4 * p)
    (hSquare : M ^ 2 ≤ S)
    (hpasses : 3 ^ 8 * S ^ 4 ≤ 32 * (n + 2)) :
    ¬ 128 * p < (3 * M) ^ 8 := by
  intro hfirst
  exact (not_lt_of_ge hpasses)
    (jointSquareEnvelope_failure_of_firstInterval hn hfirst hSquare)

end BGS.NumberTheory
