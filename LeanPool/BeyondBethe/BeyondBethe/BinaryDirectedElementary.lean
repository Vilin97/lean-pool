/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.BinaryRationalFloor
public import LeanPool.BeyondBethe.BeyondBethe.BinaryRationalComparison
public import LeanPool.BeyondBethe.BeyondBethe.DirectedElementary
public import Mathlib.Tactic

/-! # Binary Directed Elementary -/

@[expose] public section

namespace BeyondBethe

/-!
# Directed elementary functions through verified binary arithmetic

The analytic definitions in `DirectedElementary.lean` are convenient field
expressions.  The definitions below give extensionally equal, machine-facing
programs whose rational operations are the explicit long-division, bounded
Euclid, and normalization routines from the binary arithmetic layer.
-/

/-- Partial sum of the odd logarithm series, evaluated by a fixed natural
loop. -/
def binaryRationalLogSeriesSum (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | N + 1 =>
      binaryRatAdd (binaryRationalLogSeriesSum x N)
        (binaryRatDiv (binaryRatPow x (2 * N + 1)) (2 * N + 1))

theorem binaryRationalLogSeriesSum_eq (x : ℚ) : ∀ N : ℕ,
    binaryRationalLogSeriesSum x N =
      ∑ k ∈ Finset.range N, x ^ (2 * k + 1) / (2 * k + 1) := by
  intro N
  induction N with
  | zero => simp [binaryRationalLogSeriesSum]
  | succ N ih =>
      rw [binaryRationalLogSeriesSum, binaryRatAdd_eq_add,
        binaryRatDiv_eq_div, binaryRatPow_eq_pow, ih,
        Finset.sum_range_succ]

/-- Twice the first `N` odd terms of the rational logarithm series, evaluated with binary
arithmetic. -/
def binaryRationalLogSeries (x : ℚ) (N : ℕ) : ℚ :=
  binaryRatMul 2 (binaryRationalLogSeriesSum x N)

theorem binaryRationalLogSeries_eq (x : ℚ) (N : ℕ) :
    binaryRationalLogSeries x N = rationalLogSeries x N := by
  rw [binaryRationalLogSeries, rationalLogSeries,
    binaryRatMul_eq_mul, binaryRationalLogSeriesSum_eq]

/-- The rational remainder expression `2 * x^(2*N+1) / (1-x^2)` for the logarithm series. -/
def binaryRationalLogSeriesError (x : ℚ) (N : ℕ) : ℚ :=
  binaryRatMul 2
    (binaryRatDiv (binaryRatPow x (2 * N + 1))
      (binaryRatSub 1 (binaryRatPow x 2)))

theorem binaryRationalLogSeriesError_eq (x : ℚ) (N : ℕ) :
    binaryRationalLogSeriesError x N = rationalLogSeriesError x N := by
  simp [binaryRationalLogSeriesError, rationalLogSeriesError,
    binaryRatMul_eq_mul, binaryRatDiv_eq_div, binaryRatSub_eq_sub,
    binaryRatPow_eq_pow]

/-- The logarithm-series substitution `(y-1)/(y+1)`, computed with binary rational arithmetic. -/
def binaryRationalLogUnitParameter (y : ℚ) : ℚ :=
  binaryRatDiv (binaryRatSub y 1) (binaryRatAdd y 1)

theorem binaryRationalLogUnitParameter_eq (y : ℚ) :
    binaryRationalLogUnitParameter y = rationalLogUnitParameter y := by
  simp [binaryRationalLogUnitParameter, rationalLogUnitParameter,
    binaryRatDiv_eq_div, binaryRatSub_eq_sub, binaryRatAdd_eq_add]

/-- The lower unit-logarithm approximation obtained by evaluating the truncated odd-power
series. -/
def binaryDirectedLogUnitLower (y : ℚ) (N : ℕ) : ℚ :=
  binaryRationalLogSeries (binaryRationalLogUnitParameter y) N

theorem binaryDirectedLogUnitLower_eq (y : ℚ) (N : ℕ) :
    binaryDirectedLogUnitLower y N = directedLogUnitLower y N := by
  simp [binaryDirectedLogUnitLower, directedLogUnitLower,
    binaryRationalLogSeries_eq, binaryRationalLogUnitParameter_eq]

/-- The upper unit-logarithm approximation obtained by adding the series remainder expression. -/
def binaryDirectedLogUnitUpper (y : ℚ) (N : ℕ) : ℚ :=
  binaryRatAdd
    (binaryRationalLogSeries (binaryRationalLogUnitParameter y) N)
    (binaryRationalLogSeriesError (binaryRationalLogUnitParameter y) N)

theorem binaryDirectedLogUnitUpper_eq (y : ℚ) (N : ℕ) :
    binaryDirectedLogUnitUpper y N = directedLogUnitUpper y N := by
  simp [binaryDirectedLogUnitUpper, directedLogUnitUpper,
    binaryRatAdd_eq_add, binaryRationalLogSeries_eq,
    binaryRationalLogSeriesError_eq, binaryRationalLogUnitParameter_eq]

/-- Base-two logarithm read from the length of the canonical binary word. -/
def binaryNatLog2 (n : ℕ) : ℕ := n.size - 1

theorem binaryNatLog2_eq_log_two (n : ℕ) :
    binaryNatLog2 n = Nat.log 2 n := by
  by_cases hn : n = 0
  · subst n
    simp [binaryNatLog2]
  · have hsize := Nat.size_eq_log_two_add_one hn
    rw [binaryNatLog2, hsize]
    omega

/-- The power-of-two scale determined by the binary logarithms of the absolute numerator and
denominator. -/
def binaryRationalBinaryScale (q : ℚ) : ℚ :=
  binaryRatDiv
    (binaryRatPow 2 (binaryNatLog2 q.num.natAbs))
    (binaryRatPow 2 (binaryNatLog2 q.den))

theorem binaryRationalBinaryScale_eq (q : ℚ) :
    binaryRationalBinaryScale q = rationalBinaryScale q := by
  simp [binaryRationalBinaryScale, rationalBinaryScale,
    binaryRatDiv_eq_div, binaryRatPow_eq_pow,
    binaryNatLog2_eq_log_two]

/-- Signed range-reduction exponent computed from binary word lengths. -/
def binaryRationalBinaryExponent (q : ℚ) : ℤ :=
  (binaryNatLog2 q.num.natAbs : ℤ) - (binaryNatLog2 q.den : ℤ)

theorem binaryRationalBinaryExponent_eq (q : ℚ) :
    binaryRationalBinaryExponent q = rationalBinaryExponent q := by
  simp [binaryRationalBinaryExponent, rationalBinaryExponent,
    binaryNatLog2_eq_log_two]

/-- The rational input divided by its power-of-two scale. -/
def binaryRationalBinaryResidual (q : ℚ) : ℚ :=
  binaryRatDiv q (binaryRationalBinaryScale q)

theorem binaryRationalBinaryResidual_eq (q : ℚ) :
    binaryRationalBinaryResidual q = rationalBinaryResidual q := by
  simp [binaryRationalBinaryResidual, rationalBinaryResidual,
    binaryRatDiv_eq_div, binaryRationalBinaryScale_eq]

/-- The binary residual used for logarithm approximation, inverted when it is below one. -/
def binaryRationalLogUnit (q : ℚ) : ℚ :=
  if binaryRatLt (binaryRationalBinaryResidual q) 1 then
    binaryRatInv (binaryRationalBinaryResidual q)
  else
    binaryRationalBinaryResidual q

theorem binaryRationalLogUnit_eq (q : ℚ) :
    binaryRationalLogUnit q = rationalLogUnit q := by
  simp [binaryRationalLogUnit, rationalLogUnit,
    binaryRationalBinaryResidual_eq, binaryRatInv_eq_inv,
    binaryRatLt_eq_true_iff]

/-- The lower endpoint for multiplication of an interval by an integer, accounting for its sign. -/
def binaryDirectedIntMulLower (k : ℤ) (lo hi : ℚ) : ℚ :=
  if 0 ≤ k then binaryRatMul k lo else binaryRatMul k hi

theorem binaryDirectedIntMulLower_eq (k : ℤ) (lo hi : ℚ) :
    binaryDirectedIntMulLower k lo hi = directedIntMulLower k lo hi := by
  simp [binaryDirectedIntMulLower, directedIntMulLower,
    binaryRatMul_eq_mul]

/-- The upper endpoint for multiplication of an interval by an integer, accounting for its sign. -/
def binaryDirectedIntMulUpper (k : ℤ) (lo hi : ℚ) : ℚ :=
  if 0 ≤ k then binaryRatMul k hi else binaryRatMul k lo

theorem binaryDirectedIntMulUpper_eq (k : ℤ) (lo hi : ℚ) :
    binaryDirectedIntMulUpper k lo hi = directedIntMulUpper k lo hi := by
  simp [binaryDirectedIntMulUpper, directedIntMulUpper,
    binaryRatMul_eq_mul]

/-- Complete directed lower logarithm implemented only with binary rational
primitives and fixed natural loops. -/
def binaryDirectedLogLower (q : ℚ) (N : ℕ) : ℚ :=
  let kPart := binaryDirectedIntMulLower (binaryRationalBinaryExponent q)
    (binaryDirectedLogUnitLower 2 N) (binaryDirectedLogUnitUpper 2 N)
  let y := binaryRationalLogUnit q
  binaryRatAdd kPart
    (if binaryRatLt (binaryRationalBinaryResidual q) 1 then
      binaryRatNeg (binaryDirectedLogUnitUpper y N)
    else
      binaryDirectedLogUnitLower y N)

theorem binaryDirectedLogLower_eq (q : ℚ) (N : ℕ) :
    binaryDirectedLogLower q N = directedLogLower q N := by
  simp [binaryDirectedLogLower, directedLogLower,
    binaryDirectedIntMulLower_eq, binaryDirectedLogUnitLower_eq,
    binaryDirectedLogUnitUpper_eq, binaryRationalLogUnit_eq,
    binaryRationalBinaryResidual_eq, binaryRatNeg_eq_neg,
    binaryRatAdd_eq_add, binaryRationalBinaryExponent_eq,
    binaryRatLt_eq_true_iff]

/-- The upper logarithm approximation combining the binary exponent contribution with the
residual contribution. -/
def binaryDirectedLogUpper (q : ℚ) (N : ℕ) : ℚ :=
  let kPart := binaryDirectedIntMulUpper (binaryRationalBinaryExponent q)
    (binaryDirectedLogUnitLower 2 N) (binaryDirectedLogUnitUpper 2 N)
  let y := binaryRationalLogUnit q
  binaryRatAdd kPart
    (if binaryRatLt (binaryRationalBinaryResidual q) 1 then
      binaryRatNeg (binaryDirectedLogUnitLower y N)
    else
      binaryDirectedLogUnitUpper y N)

theorem binaryDirectedLogUpper_eq (q : ℚ) (N : ℕ) :
    binaryDirectedLogUpper q N = directedLogUpper q N := by
  simp [binaryDirectedLogUpper, directedLogUpper,
    binaryDirectedIntMulUpper_eq, binaryDirectedLogUnitLower_eq,
    binaryDirectedLogUnitUpper_eq, binaryRationalLogUnit_eq,
    binaryRationalBinaryResidual_eq, binaryRatNeg_eq_neg,
    binaryRatAdd_eq_add, binaryRationalBinaryExponent_eq,
    binaryRatLt_eq_true_iff]

/-- Natural ceiling used by the exponential schedule, now routed through the
verified rational-floor implementation. -/
def binaryRationalCeilNat (t : ℚ) : ℕ :=
  Int.toNat (binaryRatCeil t)

theorem binaryRationalCeilNat_eq (t : ℚ) :
    binaryRationalCeilNat t = rationalCeilNat t := by
  rw [binaryRationalCeilNat, rationalCeilNat, binaryRatCeil_eq_ceil]

/-- The odd step count `2 * ceil(t + t^2/loss) + 1` used in the exponential approximation. -/
def binaryRationalExpApproxSteps (t loss : ℚ) : ℕ :=
  2 * binaryRationalCeilNat
    (binaryRatAdd t (binaryRatDiv (binaryRatPow t 2) loss)) + 1

theorem binaryRationalExpApproxSteps_eq (t loss : ℚ) :
    binaryRationalExpApproxSteps t loss =
      rationalExpApproxSteps t loss := by
  simp [binaryRationalExpApproxSteps, rationalExpApproxSteps,
    binaryRationalCeilNat_eq, binaryRatAdd_eq_add,
    binaryRatDiv_eq_div, binaryRatPow_eq_pow]

/-- The binomial expression `(1-t/M)^M` used to approximate `exp(-t)` from below. -/
def binaryRationalNegativeExpLower (t loss : ℚ) : ℚ :=
  let M := binaryRationalExpApproxSteps t loss
  binaryRatPow
    (binaryRatSub 1 (binaryRatDiv t M)) M

theorem binaryRationalNegativeExpLower_eq (t loss : ℚ) :
    binaryRationalNegativeExpLower t loss =
      rationalNegativeExpLower t loss := by
  simp [binaryRationalNegativeExpLower, rationalNegativeExpLower,
    binaryRationalExpApproxSteps_eq, binaryRatPow_eq_pow,
    binaryRatSub_eq_sub, binaryRatDiv_eq_div]

/-- The binomial expression `(1+t/M)^M` used to approximate `exp(t)` from below. -/
def binaryRationalPositiveExpLower (t loss : ℚ) : ℚ :=
  let M := binaryRationalExpApproxSteps t loss
  binaryRatPow
    (binaryRatAdd 1 (binaryRatDiv t M)) M

theorem binaryRationalPositiveExpLower_eq (t loss : ℚ) :
    binaryRationalPositiveExpLower t loss =
      rationalPositiveExpLower t loss := by
  simp [binaryRationalPositiveExpLower, rationalPositiveExpLower,
    binaryRationalExpApproxSteps_eq, binaryRatPow_eq_pow,
    binaryRatAdd_eq_add, binaryRatDiv_eq_div]

/-- Select the positive- or negative-exponent binomial approximation according to the sign of
the input. -/
def binaryRationalExpLower (s loss : ℚ) : ℚ :=
  if binaryRatNonnegative s then binaryRationalPositiveExpLower s loss
  else binaryRationalNegativeExpLower (binaryRatNeg s) loss

theorem binaryRationalExpLower_eq (s loss : ℚ) :
    binaryRationalExpLower s loss = rationalExpLower s loss := by
  simp [binaryRationalExpLower, rationalExpLower,
    binaryRationalPositiveExpLower_eq, binaryRationalNegativeExpLower_eq,
    binaryRatNeg_eq_neg, binaryRatNonnegative_eq_true_iff]

end BeyondBethe
