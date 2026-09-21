/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.RawRationalBitBounds
import LeanPool.BeyondBethe.BeyondBethe.DyadicRounding
import Mathlib.Tactic

/-! # Binary Rational Floor -/

namespace BeyondBethe

/-!
# Rational floor through verified binary division

The numerical implementation repeatedly rounds rational state entries to a
dyadic grid.  This file removes `Int.floor` from the machine-facing path: the
quotient and remainder are obtained by `binaryLongDiv`, whose recurrence and
fixed-width bounds are proved in `BinaryLongDivision.lean`.
-/

/-- Euclidean floor of a canonical rational.  For a negative numerator,
`-a/d` rounds to `-(a/d)` when the remainder vanishes and to
`-(a/d+1)` otherwise. -/
def binaryRatFloor (q : ℚ) : ℤ :=
  let qr := binaryLongDiv q.num.natAbs q.den
  if 0 ≤ q.num then
    (qr.1 : ℤ)
  else if qr.2 = 0 then
    -(qr.1 : ℤ)
  else
    -((qr.1 + 1 : ℕ) : ℤ)

theorem binaryRatFloor_eq_floor (q : ℚ) :
    binaryRatFloor q = Int.floor q := by
  rw [Rat.floor_def', binaryRatFloor, binaryLongDiv_eq_div_mod]
  simp only [Prod.fst, Prod.snd]
  cases hnum : q.num with
  | ofNat n =>
      simp [hnum, Int.ediv]
  | negSucc n =>
      have hden : 0 < q.den := q.den_pos
      by_cases hrem : (n + 1) % q.den = 0
      · simp [hnum, hrem, Int.ediv, Int.bdiv, Int.bmod]
        have hdvdNat : q.den ∣ n + 1 := Nat.dvd_of_mod_eq_zero hrem
        have hdvdInt : (q.den : ℤ) ∣ ((n + 1 : ℕ) : ℤ) := by
          exact_mod_cast hdvdNat
        have hrepr : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by omega
        rw [hrepr, Int.neg_ediv_of_dvd hdvdInt]
        norm_num
      · simp [hnum, hrem, Int.ediv, Int.bdiv, Int.bmod]
        have hndvdNat : ¬q.den ∣ n + 1 := by
          rwa [Nat.dvd_iff_mod_eq_zero]
        have hndvdInt : ¬(q.den : ℤ) ∣ ((n + 1 : ℕ) : ℤ) := by
          exact_mod_cast hndvdNat
        have hrepr : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by omega
        rw [hrepr, Int.neg_ediv, if_neg hndvdInt,
          Int.sign_eq_one_of_pos (by exact_mod_cast hden)]
        norm_num [Nat.add_comm]
        ring

/-- Ceiling obtained from the same verified floor routine. -/
def binaryRatCeil (q : ℚ) : ℤ := -binaryRatFloor (-q)

theorem binaryRatCeil_eq_ceil (q : ℚ) :
    binaryRatCeil q = Int.ceil q := by
  rw [binaryRatCeil, binaryRatFloor_eq_floor]
  simpa only [neg_neg] using
    congrArg Neg.neg (Int.floor_neg (a := q))

/-- Machine-facing dyadic floor, using verified integer division in the only
non-field operation. -/
def binaryDyadicFloor (p : ℕ) (q : ℚ) : ℚ :=
  (binaryRatFloor (q * (2 : ℚ) ^ p) : ℚ) / (2 : ℚ) ^ p

theorem binaryDyadicFloor_eq_dyadicFloor (p : ℕ) (q : ℚ) :
    binaryDyadicFloor p q = dyadicFloor p q := by
  rw [binaryDyadicFloor, dyadicFloor, binaryRatFloor_eq_floor]

end BeyondBethe
