/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Algebraic identities for ascending Pochhammer symbols

These multiplicative identities avoid division by parameter-dependent factors, so they remain
valid at zeros of the Pochhammer symbols.
-/

open Polynomial

public noncomputable section

/-- A division-free shift identity for ascending Pochhammer symbols. -/
theorem ascPochhammer_eval_shift {R : Type*} [CommSemiring R] (p : R) (n : ℕ) :
    p * (ascPochhammer R n).eval (p + 1) =
      (p + n) * (ascPochhammer R n).eval p := by
  have h := congrArg (Polynomial.eval p) (ascPochhammer_succ_left R n)
  simpa [ascPochhammer_succ_eval, mul_comm] using h.symm

/-- Evaluation of the product formula for ascending Pochhammer symbols. -/
theorem ascPochhammer_add_eval {R : Type*} [CommSemiring R] (p : R) (n m : ℕ) :
    (ascPochhammer R (n + m)).eval p =
      (ascPochhammer R n).eval p * (ascPochhammer R m).eval (p + n) := by
  simpa using (congrArg (Polynomial.eval p) (ascPochhammer_mul R n m)).symm

/-- Duplication of ascending Pochhammer symbols, in division-free multiplicative form. -/
theorem ascPochhammer_eval_double {R : Type*} [Field R] [CharZero R] (p : R) (n : ℕ) :
    (ascPochhammer R (2 * n)).eval (2 * p) =
      4 ^ n * (ascPochhammer R n).eval p * (ascPochhammer R n).eval (p + 1 / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      ascPochhammer_succ_eval, ascPochhammer_succ_eval, ih,
      ascPochhammer_succ_eval, ascPochhammer_succ_eval, pow_succ]
    push_cast
    ring

/-- Splitting an ascending Pochhammer symbol and reflecting the remaining factors.

The multiplicative form remains valid when one of the Pochhammer factors vanishes, unlike the
corresponding quotient identity. -/
theorem ascPochhammer_eval_split_reflect {R : Type*} [CommRing R] (c : R) {m n : ℕ} (hmn : m ≤ n) :
    (ascPochhammer R n).eval c =
      (-1 : R) ^ (n - m) * (ascPochhammer R m).eval c *
        (ascPochhammer R (n - m)).eval (1 - c - n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  simp only [Nat.add_sub_cancel_left]
  have hmul := congrArg (Polynomial.eval c) (ascPochhammer_mul R m d)
  simp only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_natCast] at hmul
  rw [← hmul]
  have href := ascPochhammer_eval_neg_eq_descPochhammer R (c + m + d - 1) d
  rw [descPochhammer_eval_eq_ascPochhammer] at href
  have harg : -(c + (m : R) + d - 1) = 1 - c - (m + d : ℕ) := by
    rw [Nat.cast_add]
    ring
  have harg' : c + (m : R) + d - 1 - d + 1 = c + m := by ring
  rw [harg, harg'] at href
  rw [href]
  ring_nf
  simp

/-- Reflection of ascending Pochhammer symbols, including their zeros. -/
theorem ascPochhammer_eval_reflect {R : Type*} [CommRing R] (p : R) (n : ℕ) :
    (ascPochhammer R n).eval (1 - p - n) =
      (-1 : R) ^ n * (ascPochhammer R n).eval p := by
  have H := ascPochhammer_eval_split_reflect p (m := 0) (n := n) (Nat.zero_le n)
  simp only [Nat.sub_zero, ascPochhammer_zero, Polynomial.eval_one, mul_one] at H
  rw [H, ← mul_assoc, ← mul_pow]
  simp

end
