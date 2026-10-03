/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.NumberTheory.JointMaximalDivisorCriterion

/-!
# Arithmetic criterion for the nonparabolic complement route

The complement count supplies `8 * p ≤ (d * M) ^ 2`.  The exact
Euler-characteristic coefficient anticipated by the strengthened
Corvaja--Zannier step gives `d ≤ 189 * M ^ 3`.  Eliminating `d` yields the
integer obstruction `8 * p ≤ 189 ^ 2 * M ^ 8`.

A root-free square envelope `M ^ 2 ≤ S` then gives
`8 * p ≤ 35721 * S ^ 4`.
-/

@[expose] public section

namespace BGS.NumberTheory

/-- Eliminate the maximal order `d` from the nonparabolic complement count
using the exact coefficient `189`. -/
theorem eight_mul_le_189_sq_mul_eighth_of_le_square_of_le_189_mul_cube
    {p d M : ℕ}
    (hcount : 8 * p ≤ (d * M) ^ 2)
    (hdegree : d ≤ 189 * M ^ 3) :
    8 * p ≤ 189 ^ 2 * M ^ 8 := by
  calc
    8 * p ≤ (d * M) ^ 2 := hcount
    _ ≤ ((189 * M ^ 3) * M) ^ 2 := by
      gcongr
    _ = 189 ^ 2 * M ^ 8 := by ring

/-- Replace `M` by any certified square envelope `S`; `189^2 = 35721`. -/
theorem eight_mul_le_35721_mul_fourth_of_le_189_sq_mul_eighth
    {p M S : ℕ}
    (hbad : 8 * p ≤ 189 ^ 2 * M ^ 8)
    (hSquare : M ^ 2 ≤ S) :
    8 * p ≤ 35721 * S ^ 4 := by
  calc
    8 * p ≤ 189 ^ 2 * M ^ 8 := hbad
    _ = 35721 * (M ^ 2) ^ 4 := by ring
    _ ≤ 35721 * S ^ 4 := by
      gcongr

/-- Combined root-free obstruction for the nonparabolic complement route. -/
theorem eight_mul_le_35721_mul_fourth_of_count_degree_squareEnvelope
    {p d M S : ℕ}
    (hcount : 8 * p ≤ (d * M) ^ 2)
    (hdegree : d ≤ 189 * M ^ 3)
    (hSquare : M ^ 2 ≤ S) :
    8 * p ≤ 35721 * S ^ 4 :=
  eight_mul_le_35721_mul_fourth_of_le_189_sq_mul_eighth
    (eight_mul_le_189_sq_mul_eighth_of_le_square_of_le_189_mul_cube
      hcount hdegree)
    hSquare

end BGS.NumberTheory
