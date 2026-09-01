/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Strong divisibility of sequences from a translation congruence

A sequence `a` in a GCD domain with `a 0 = 0` satisfying the *translation congruence*
`a m ∣ a (m + j) - a j` for all `m, j` is a strong divisibility sequence:
`gcd (a m) (a n) = normalize (a (gcd m n))`. Over `ℤ` this reads
`Int.gcd (a m) (a n) = |a (gcd m n)|`. This is the arithmetic engine behind the
Fibonacci-style `Int.gcd_fib`, isolated from the specific recurrence.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

variable {R : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]

private theorem gcd_seq_add {a : ℕ → R} (hdvd : ∀ m j, a m ∣ a (m + j) - a j) (m n : ℕ) :
    gcd (a m) (a (n + m)) = gcd (a m) (a n) := by
  obtain ⟨t, ht⟩ := hdvd m n
  have h1 : a (n + m) = a n + a m * t := by rw [add_comm n m]; linear_combination ht
  rw [h1]
  refine dvd_antisymm_of_normalize_eq (normalize_gcd ..) (normalize_gcd ..)
    (dvd_gcd (gcd_dvd_left ..) ?_) (dvd_gcd (gcd_dvd_left ..) ?_)
  · simpa using dvd_sub (gcd_dvd_right (a m) (a n + a m * t))
      ((gcd_dvd_left (a m) (a n + a m * t)).mul_right t)
  · exact dvd_add (gcd_dvd_right ..) ((gcd_dvd_left ..).mul_right t)

private theorem gcd_seq_add_mul {a : ℕ → R} (hdvd : ∀ m j, a m ∣ a (m + j) - a j) (m n : ℕ) :
    ∀ k, gcd (a m) (a (n + k * m)) = gcd (a m) (a n)
  | 0 => by simp
  | k + 1 => by
    rw [← gcd_seq_add_mul hdvd m n k, add_mul, ← add_assoc, one_mul, gcd_seq_add hdvd]

/-- If `a 0 = 0` and `a m ∣ a (m + j) - a j` for all `m, j` (the *translation congruence*), then
`a` is a strong divisibility sequence: `gcd (a m) (a n) = normalize (a (gcd m n))`. -/
theorem gcd_eq_normalize_of_dvd_sub {a : ℕ → R} (h0 : a 0 = 0)
    (hdvd : ∀ m j, a m ∣ a (m + j) - a j) (m n : ℕ) :
    gcd (a m) (a n) = normalize (a (m.gcd n)) := by
  induction m, n using Nat.gcd.induction with
  | H0 n => simp [h0]
  | H1 m n _ ih =>
    rw [Nat.gcd_rec, ← ih]
    conv_lhs => rw [← Nat.mod_add_div' n m]
    rw [gcd_seq_add_mul hdvd m (n % m) (n / m), gcd_comm]

/-- The `Associated` form of `gcd_eq_normalize_of_dvd_sub`. -/
theorem associated_gcd_of_dvd_sub {a : ℕ → R} (h0 : a 0 = 0)
    (hdvd : ∀ m j, a m ∣ a (m + j) - a j) (m n : ℕ) :
    Associated (gcd (a m) (a n)) (a (m.gcd n)) :=
  gcd_eq_normalize_of_dvd_sub h0 hdvd m n ▸ normalize_associated _

/-- If `a 0 = 0` and `a m ∣ a (m + j) - a j` for all `m, j` (the *translation congruence*), then
`a` is a strong divisibility sequence: `Int.gcd (a m) (a n) = |a (gcd m n)|`. -/
theorem Int.gcd_eq_natAbs_of_dvd_sub {a : ℕ → ℤ} (h0 : a 0 = 0)
    (hdvd : ∀ m j, a m ∣ a (m + j) - a j) (m n : ℕ) :
    Int.gcd (a m) (a n) = (a (m.gcd n)).natAbs := by
  have h := Int.associated_iff_natAbs.mp (associated_gcd_of_dvd_sub h0 hdvd m n)
  rw [← h, ← Int.coe_gcd, Int.natAbs_natCast]
