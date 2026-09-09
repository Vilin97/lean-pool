/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-! Products of intermediate entries of a nonnegative log-convex
sequence are bounded by the corresponding endpoint product.  The
proof also covers zero entries and uses no logarithm or division. -/

namespace EulerNonnegativeLogConvex

variable (x : ℕ → ℝ) (hx : ∀ n, 0 ≤ x n)
  (hc : ∀ n, (x (n + 1)) ^ 2 ≤ x n * x (n + 2))

include hx hc

theorem cross (a d : ℕ) : x (a+1)*x (a+d) ≤ x a*x (a+d+1) := by
  induction d with
  | zero => simp only [Nat.add_zero]; exact le_of_eq (mul_comm _ _)
  | succ d ih =>
    by_cases hz : x (a+d)=0
    · have hz' : x (a+d+1)=0 := by
        have h := hc (a+d)
        rw [hz,zero_mul] at h
        nlinarith [hx (a+d+1)]
      simpa only [Nat.add_succ,hz',mul_zero] using
        mul_nonneg (hx a) (hx (a+d+2))
    · have hp : 0 < x (a+d) := lt_of_le_of_ne (hx (a+d)) (Ne.symm hz)
      apply (mul_le_mul_iff_right₀ hp).mp
      calc
        x (a+d)*(x (a+1)*x (a+d.succ)) =
            (x (a+1)*x (a+d))*x (a+d+1) := by simp only [Nat.add_succ]; ring
        _ ≤ (x a*x (a+d+1))*x (a+d+1) :=
          mul_le_mul_of_nonneg_right ih (hx _)
        _ = x a*(x (a+d+1))^2 := by ring
        _ ≤ x a*(x (a+d)*x (a+d+2)) := mul_le_mul_of_nonneg_left (hc _) (hx a)
        _ = x (a+d)*(x a*x (a+d.succ+1)) := by simp only [Nat.add_succ]; ring

theorem pair (a k d : ℕ) :
    x (a+k)*x (a+k+d) ≤ x a*x (a+2*k+d) := by
  induction k generalizing d with
  | zero => simp
  | succ k ih =>
    have h := cross x hx hc (a+k) (d+1)
    have hh := ih (d+2)
    convert h.trans hh using 1 <;> congr 2 <;> omega

theorem between (s a b : ℕ) (hsa : s ≤ a) (hab : a ≤ b) :
    x a*x b ≤ x s*x (a+b-s) := by
  have h := pair x hx hc s (a-s) (b-a)
  convert h using 1 <;> congr 2 <;> omega

end EulerNonnegativeLogConvex
