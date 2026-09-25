/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.FactorialBound

/-!
# The square root of the factorial beats every geometric progression

The asymptotic input to Deligne §1.20: for any real
constants `C` and `c` there is an `n` with
`C * c ^ n < Real.sqrt n.factorial`.

The route is elementary.  The integral bound
`three_pow_mul_factorial_ge` (`n ^ n ≤ 3 ^ n * n !`, from
`RS/Common/FactorialBound.lean`) gives `(n / 3) ^ n ≤ n !` over ℝ,
so at an even index `n = 2 * m` the square root of the factorial is
at least `(2 * m / 3) ^ m`.  Replacing `C` and `c` by
`max |C| 1` and `max |c| 1` reduces every sign case to constants at
least `1`, and it then suffices to pick `m` beyond both `3 * b ^ 2`
(so the base `2 * m / 3` dominates `2 * b ^ 2`) and a natural number
exceeding the constant (so the spare factor `2 ^ m` swallows it).
-/

@[expose] public section

namespace RS

/-- Real form of `three_pow_mul_factorial_ge`:
`(n / 3) ^ n ≤ n !` over ℝ. -/
theorem div_three_pow_le_factorial (n : ℕ) :
    ((n : ℝ) / 3) ^ n ≤ (n.factorial : ℝ) := by
  have h : ((n : ℝ)) ^ n ≤ 3 ^ n * (n.factorial : ℝ) := by
    exact_mod_cast three_pow_mul_factorial_ge n
  rw [div_pow, div_le_iff₀ (by positivity : (0 : ℝ) < 3 ^ n)]
  calc ((n : ℝ)) ^ n ≤ 3 ^ n * (n.factorial : ℝ) := h
    _ = (n.factorial : ℝ) * 3 ^ n := mul_comm _ _

/-- At an even index the square root of the factorial dominates
`(2 * m / 3) ^ m`. -/
theorem pow_le_sqrt_factorial_two_mul (m : ℕ) :
    (((2 * m : ℕ) : ℝ) / 3) ^ m ≤ Real.sqrt ((2 * m).factorial) := by
  set x : ℝ := ((2 * m : ℕ) : ℝ) / 3 with hx_def
  have hx0 : 0 ≤ x := by positivity
  have hsq : x ^ (2 * m) = (x ^ m) ^ 2 := pow_mul' x 2 m
  have h1 : x ^ (2 * m) ≤ ((2 * m).factorial : ℝ) :=
    div_three_pow_le_factorial (2 * m)
  calc x ^ m
      = Real.sqrt ((x ^ m) ^ 2) := (Real.sqrt_sq (pow_nonneg hx0 m)).symm
    _ = Real.sqrt (x ^ (2 * m)) := by rw [hsq]
    _ ≤ Real.sqrt ((2 * m).factorial) := Real.sqrt_le_sqrt h1

/-- **The square root of the factorial beats every geometric
progression**: for any real constants `C` and `c` there is an `n`
with `C * c ^ n < Real.sqrt n.factorial`.  This is the asymptotic
input to Deligne §1.20. -/
theorem exists_lt_sqrt_factorial (C c : ℝ) :
    ∃ n : ℕ, C * c ^ n < Real.sqrt (n.factorial) := by
  set A : ℝ := max |C| 1 with hA_def
  set b : ℝ := max |c| 1 with hb_def
  have hA1 : (1 : ℝ) ≤ A := le_max_right _ _
  have hb1 : (1 : ℝ) ≤ b := le_max_right _ _
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le one_pos hb1
  obtain ⟨k₁, hk₁⟩ := exists_nat_gt A
  obtain ⟨k₂, hk₂⟩ := exists_nat_ge (3 * b ^ 2)
  set m : ℕ := max k₁ k₂ with hm_def
  refine ⟨2 * m, ?_⟩
  -- The given progression is dominated by one with constants ≥ 1.
  have habs : C * c ^ (2 * m) ≤ A * (b ^ 2) ^ m := by
    have h1 : C * c ^ (2 * m) ≤ |C| * |c| ^ (2 * m) := by
      calc C * c ^ (2 * m) ≤ |C * c ^ (2 * m)| := le_abs_self _
        _ = |C| * |c| ^ (2 * m) := by rw [abs_mul, abs_pow]
    have h2 : |c| ^ (2 * m) ≤ b ^ (2 * m) :=
      pow_le_pow_left₀ (abs_nonneg c) (le_max_left _ _) _
    have h3 : |C| * |c| ^ (2 * m) ≤ A * b ^ (2 * m) :=
      mul_le_mul (le_max_left _ _) h2 (pow_nonneg (abs_nonneg c) _)
        (le_trans zero_le_one hA1)
    calc C * c ^ (2 * m) ≤ A * b ^ (2 * m) := h1.trans h3
      _ = A * (b ^ 2) ^ m := by rw [← pow_mul]
  -- The spare factor `2 ^ m` swallows the constant `A`.
  have hA_lt : A < (2 : ℝ) ^ m := by
    have hk₁m : (k₁ : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast Nat.le_max_left k₁ k₂
    have hm2 : (m : ℝ) < (2 : ℝ) ^ m := by
      exact_mod_cast @Nat.lt_two_pow_self m
    linarith
  have hbpos : (0 : ℝ) < (b ^ 2) ^ m := pow_pos (pow_pos hb0 2) m
  -- Base comparison: `2 * b ^ 2 ≤ 2 * m / 3`.
  have h6 : 2 * b ^ 2 ≤ ((2 * m : ℕ) : ℝ) / 3 := by
    have hk₂m : (k₂ : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast Nat.le_max_right k₁ k₂
    have h3b : 3 * b ^ 2 ≤ (m : ℝ) := hk₂.trans hk₂m
    push_cast
    linarith
  calc C * c ^ (2 * m)
      ≤ A * (b ^ 2) ^ m := habs
    _ < (2 : ℝ) ^ m * (b ^ 2) ^ m := mul_lt_mul_of_pos_right hA_lt hbpos
    _ = ((2 : ℝ) * b ^ 2) ^ m := (mul_pow 2 (b ^ 2) m).symm
    _ ≤ (((2 * m : ℕ) : ℝ) / 3) ^ m :=
        pow_le_pow_left₀ (by positivity) h6 m
    _ ≤ Real.sqrt ((2 * m).factorial) := pow_le_sqrt_factorial_two_mul m

end RS
