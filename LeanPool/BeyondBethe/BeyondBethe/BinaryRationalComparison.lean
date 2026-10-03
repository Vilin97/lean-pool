/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.RawRationalBitBounds
public import Mathlib.Tactic

/-! # Binary Rational Comparison -/

@[expose] public section

namespace BeyondBethe

/-!
# Rational comparison through signed cross multiplication

The machine-facing numerical path must not hide an order oracle on canonical
rationals.  The tests below compare signed cross products of the stored
numerators and positive denominators.  Their correctness is a direct
consequence of positivity of the denominators.
-/

/-- Strict rational comparison by signed cross multiplication. -/
def binaryRatLt (q r : ℚ) : Bool :=
  decide (q.num * (r.den : ℤ) < r.num * (q.den : ℤ))

theorem binaryRatLt_eq_true_iff (q r : ℚ) :
    binaryRatLt q r = true ↔ q < r := by
  simp only [binaryRatLt, decide_eq_true_eq]
  constructor
  · intro h
    have hcross : (q.num : ℚ) * (r.den : ℚ) <
        (r.num : ℚ) * (q.den : ℚ) := by
      exact_mod_cast h
    have hdiv : (q.num : ℚ) / (q.den : ℚ) <
        (r.num : ℚ) / (r.den : ℚ) :=
      (div_lt_div_iff₀ (by positivity) (by positivity)).2 hcross
    simpa only [q.num_div_den, r.num_div_den] using hdiv
  · intro h
    have hdiv : (q.num : ℚ) / (q.den : ℚ) <
        (r.num : ℚ) / (r.den : ℚ) := by
      simpa only [q.num_div_den, r.num_div_den] using h
    have hcross :=
      (div_lt_div_iff₀ (by positivity : (0 : ℚ) < q.den)
        (by positivity : (0 : ℚ) < r.den)).1 hdiv
    exact_mod_cast hcross

/-- Non-strict rational comparison by signed cross multiplication. -/
def binaryRatLe (q r : ℚ) : Bool :=
  decide (q.num * (r.den : ℤ) ≤ r.num * (q.den : ℤ))

theorem binaryRatLe_eq_true_iff (q r : ℚ) :
    binaryRatLe q r = true ↔ q ≤ r := by
  simp only [binaryRatLe, decide_eq_true_eq]
  constructor
  · intro h
    have hcross : (q.num : ℚ) * (r.den : ℚ) ≤
        (r.num : ℚ) * (q.den : ℚ) := by
      exact_mod_cast h
    have hdiv : (q.num : ℚ) / (q.den : ℚ) ≤
        (r.num : ℚ) / (r.den : ℚ) :=
      (div_le_div_iff₀ (by positivity) (by positivity)).2 hcross
    simpa only [q.num_div_den, r.num_div_den] using hdiv
  · intro h
    have hdiv : (q.num : ℚ) / (q.den : ℚ) ≤
        (r.num : ℚ) / (r.den : ℚ) := by
      simpa only [q.num_div_den, r.num_div_den] using h
    have hcross :=
      (div_le_div_iff₀ (by positivity : (0 : ℚ) < q.den)
        (by positivity : (0 : ℚ) < r.den)).1 hdiv
    exact_mod_cast hcross

/-- Equality of canonical rationals by equality of their stored fields. -/
def binaryRatEq (q r : ℚ) : Bool :=
  decide (q.num = r.num ∧ q.den = r.den)

theorem binaryRatEq_eq_true_iff (q r : ℚ) :
    binaryRatEq q r = true ↔ q = r := by
  simp only [binaryRatEq, decide_eq_true_eq]
  constructor
  · rintro ⟨hnum, hden⟩
    exact Rat.ext hnum hden
  · rintro rfl
    exact ⟨rfl, rfl⟩

/-- Sign test read directly from the stored numerator. -/
def binaryRatNonnegative (q : ℚ) : Bool := decide (0 ≤ q.num)

theorem binaryRatNonnegative_eq_true_iff (q : ℚ) :
    binaryRatNonnegative q = true ↔ 0 ≤ q := by
  simp [binaryRatNonnegative, Rat.num_nonneg]

end BeyondBethe
