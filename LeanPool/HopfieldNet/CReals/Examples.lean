/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.CRealLog
import LeanPool.HopfieldNet.CReals.CRealSigmoid
import LeanPool.HopfieldNet.CReals.CRealPre2.InvTranscendental

open Computable CReal

/-!
# Computable Real Number Examples

This file demonstrates the use of the `CReal` implementation by computing
approximations of various constants and function values.

Since `CReal` is a quotient type, we cannot directly `#eval` a `CReal`.
Instead, we define a helper function `show` that computes a rational
approximation to a given precision, and a `toString` function to display it.
-/

/--
Get a rational approximation of a `CReal` to precision `n`.
This means the result is within `1/2^n` of the true value.
This function uses `Quotient.out`, which is non-constructive, but it is fine
for demonstration purposes with `#eval`.
-/
noncomputable def show' (x : CReal) (n : ℕ) : ℚ :=
  (Quotient.out x).approx (n + 1)

/--
A simple function to convert a rational number to a decimal string representation
with a given precision.
-/
def ratToString (q : ℚ) (prec : ℕ) : String :=
  let sign := if q < 0 then "-" else ""
  let q' := |q|
  let intPart := q'.floor.toNat
  let fracPart := q' - intPart
  let rec go (k : ℕ) (r : ℚ) (s : String) : String :=
    if k = 0 then s
    else
      let r' := 10 * r
      let digit := Nat.floor r'
      go (k-1) (r' - digit) (s ++ toString digit)
  sign ++ toString intPart ++ "." ++ go prec fracPart ""

noncomputable def CReal.toString (x : CReal) (prec : ℕ) : String :=
  -- To get `prec` decimal digits, we need an error < 10⁻ᵖʳᵉᶜ / 2.
  -- We use an approximation with error < 1/2ⁿ.
  -- We need 2ⁿ > 2 * 10ᵖʳᵉᶜ, so n > log₂(2 * 10ᵖʳᵉᶜ) = 1 + prec * log₂(10).
  -- log₂(10) ≈ 3.32, so n > 1 + 3.32 * prec. `n = 4 * prec` is a safe choice.
  let n := 4 * prec
  let q := show' x n
  ratToString q prec

/-! ## Basic Arithmetic -/

def one : CReal := 1
def two : CReal := 2
def three : CReal := 3
def half : CReal := (1 : CReal) * CReal.Pre.inv 2 (by norm_num) -- Using inv directly

-- Note: `#eval` on `CReal` will not work directly. We use `toString`.
-- These are marked noncomputable, so we use #check instead to verify they typecheck.
#check CReal.toString (one + two) 10 -- Expected: 3.0000000000
#check CReal.toString three 10

#eval CReal.toString (two * three) 10 -- Expected: 6.0000000000

/-! ## Transcendental Functions -/

-- `log(1+x)` is defined for `|x| ≤ 1/2`
def log_one_and_a_half : CReal := log1pRatSmall (1/2) (by norm_num)

-- log(1.5) ≈ 0.405465
#eval CReal.toString log_one_and_a_half 5 -- Expected: 0.40546

-- `sigmoid(x)` is defined for `|x| ≤ 1/2`
-- sigmoid(0) = 1 / (1 + exp(0)) = 1/2
def sigmoid_zero : CReal := sigmoidRatSmall 0 (by norm_num)
#eval CReal.toString sigmoid_zero 10 -- Expected: 0.5000000000

-- sigmoid(0.5) = 1 / (1 + exp(-0.5)) ≈ 1 / (1 + 0.6065) ≈ 0.62245
def sigmoid_half : CReal := sigmoidRatSmall (1/2) (by norm_num)
#eval CReal.toString sigmoid_half 5 -- Expected: 0.62245

/-! ## Sanity checks for the small-exp pre-real on rationals -/

#eval (CReal.Pre.small_exp (1/4 : ℚ) (by norm_num)).approx 5
#eval (CReal.Pre.small_exp (-1/3 : ℚ) (by norm_num)).approx 5

/-! ## Comparisons -/

-- We can't `#eval` a `Prop`, but we can prove it.
theorem one_lt_two' : (1 : CReal) < 2 := by
  have : (0 : CReal) < 1 := _root_.zero_lt_one
  have : (1 : CReal) < 1 + 1 := by
    rw [← add_lt_add_iff_left (1 : CReal)]
    simp [this]
  convert this

-- This is a sanity check that the order is working as expected.
#guard one_lt_two
