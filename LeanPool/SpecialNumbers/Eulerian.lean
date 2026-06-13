/-
Copyright (c) 2026 Walter Moreira, Joe Stubbs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Walter Moreira, Joe Stubbs
-/
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.NeZero
import Mathlib.Data.Nat.Choose.Sum

/-!
# Eulerian Numbers

This module defines the Eulerian numbers by their standard triangular recurrence
(Section 6.2 of [Concrete Mathematics][knuth1989concrete]), proves their boundary
values, and proves Worpitzky's identity (6.37): for all natural numbers `x` and `n`,
`x ^ n = ∑ k ∈ Finset.range (n + 1), eulerian n k * (x + k).choose n`.

The combinatorial interpretation of $\left\langle{n\atop k}\right\rangle$ — counting
the permutations of $\{1,2,\ldots,n\}$ with $k$ ascents — is not formalized here.

## References

* [Concrete Mathematics][knuth1989concrete]
-/

namespace SpecialNumbers

/--
Eulerian number, defined by the recurrence
`eulerian (n + 1) k = (k + 1) * eulerian n k + (n + 1 - k) * eulerian n (k - 1)`
with boundary values `eulerian n 0 = 1` and `eulerian 0 k = 0` for `k > 0`.
-/
def eulerian (n k : ℕ) : ℕ :=
  match n, k with
    | _, 0 => 1
    | 0, _ => 0
    | n + 1, k => (k + 1) * eulerian n k + (n + 1 - k) * eulerian n (k - 1)

theorem eulerian_0_0 : eulerian 0 0 = 1 := by rfl

theorem eulerian_of_n_zero (n : ℕ) : eulerian n 0 = 1 := by simp [eulerian]

theorem eulerian_of_zero : eulerian 0 0 = 1 := eulerian_of_n_zero 0

theorem eulerian_of_zero_k (k : ℕ) (h : k > 0) : eulerian 0 k = 0 := by
  by_cases c : k = 0
  · omega
  · simp [eulerian]

theorem eulerian_of_n_succ_n (n k : ℕ) (h : n > 0) (hp : k ≥ n) : eulerian n k = 0 := by
  induction n generalizing k with
    | zero => contradiction
    | succ n ih =>
        rw [eulerian]
        · by_cases c : n = 0
          · rw [c]
            simp only [zero_add, Nat.add_eq_zero_iff, mul_eq_zero, one_ne_zero, and_false,
              false_or]
            constructor
            · exact eulerian_of_zero_k k (by omega)
            · by_cases d : 1 - k = 0
              · exact Or.inl d
              · exact Or.inr <| eulerian_of_zero_k (k - 1) (by omega)
          · simp [ih k (by omega) (by omega), ih (k - 1) (by omega) (by omega)]
        · omega

theorem eulerian_of_succ_n_n (n : ℕ) : eulerian (n + 1) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [eulerian]
      · rw [eulerian_of_n_succ_n (n + 1) (n + 1) (by omega) (by omega),
          show n + 1 - 1 = n by omega, ih]
        omega
      · omega

theorem eulerian_eq_zero_of_lt {n k : ℕ} (h : n < k) : eulerian n k = 0 := by
  cases n with
  | zero => exact eulerian_of_zero_k k h
  | succ n => exact eulerian_of_n_succ_n (n + 1) k (by omega) (by omega)

theorem eulerian_succ_succ (n k : ℕ) :
    eulerian (n + 1) (k + 1) = (k + 1 + 1) * eulerian n (k + 1) + (n - k) * eulerian n k := by
  rw [eulerian]
  · rw [Nat.succ_sub_succ, Nat.add_sub_cancel]
  · omega

/--
The binomial-coefficient recurrence behind the inductive step of Worpitzky's identity:
multiplying `(x + k).choose n` by `x` re-expands it in the basis of binomial coefficients
of order `n + 1`. Valid over `ℕ` for `k ≤ n`.
-/
theorem worpitzky_step (x n k : ℕ) (hk : k ≤ n) :
    x * (x + k).choose n =
      (k + 1) * (x + k).choose (n + 1) + (n - k) * (x + k + 1).choose (n + 1) := by
  rcases Nat.lt_or_ge (x + k) n with hxk | hxk
  · rw [Nat.choose_eq_zero_of_lt hxk, Nat.choose_eq_zero_of_lt (by omega),
      Nat.choose_eq_zero_of_lt (by omega), mul_zero, mul_zero, mul_zero, add_zero]
  · symm
    calc (k + 1) * (x + k).choose (n + 1) + (n - k) * (x + k + 1).choose (n + 1)
        = (k + 1 + (n - k)) * (x + k).choose (n + 1) + (n - k) * (x + k).choose n := by
          rw [Nat.choose_succ_succ']
          ring
      _ = (x + k).choose (n + 1) * (n + 1) + (n - k) * (x + k).choose n := by
          rw [show k + 1 + (n - k) = n + 1 by omega]
          ring
      _ = (x + k - n + (n - k)) * (x + k).choose n := by
          rw [Nat.choose_succ_right_eq]
          ring
      _ = x * (x + k).choose n := by
          rw [show x + k - n + (n - k) = x by omega]

/--
Re-grouping step for Worpitzky's identity: the order-`n + 1` Eulerian expansion arises
from the order-`n` one via the triangular recurrence.
-/
theorem sum_eulerian_succ_mul_choose (n x : ℕ) :
    ∑ k ∈ Finset.range (n + 1 + 1), eulerian (n + 1) k * (x + k).choose (n + 1)
      = (∑ k ∈ Finset.range (n + 1), (k + 1) * eulerian n k * (x + k).choose (n + 1))
        + ∑ k ∈ Finset.range (n + 1), (n - k) * eulerian n k * (x + k + 1).choose (n + 1) := by
  have expand : ∀ j ∈ Finset.range (n + 1),
      eulerian (n + 1) (j + 1) * (x + (j + 1)).choose (n + 1)
        = (j + 1 + 1) * eulerian n (j + 1) * (x + (j + 1)).choose (n + 1)
          + (n - j) * eulerian n j * (x + j + 1).choose (n + 1) := by
    intro j _
    rw [eulerian_succ_succ, show x + (j + 1) = x + j + 1 from rfl]
    ring
  rw [Finset.sum_range_succ' (fun k => eulerian (n + 1) k * (x + k).choose (n + 1)) (n + 1),
    Finset.sum_range_succ' (fun k => (k + 1) * eulerian n k * (x + k).choose (n + 1)) n,
    Finset.sum_congr rfl expand, Finset.sum_add_distrib,
    Finset.sum_range_succ
      (fun j => (j + 1 + 1) * eulerian n (j + 1) * (x + (j + 1)).choose (n + 1)) n,
    eulerian_eq_zero_of_lt (show n < n + 1 by omega), eulerian_of_n_zero, eulerian_of_n_zero]
  ring

/--
**Worpitzky's identity** (Concrete Mathematics, identity (6.37)): the power `x ^ n`
expands in the binomial-coefficient basis with Eulerian-number coefficients,
`x ^ n = ∑ k ∈ Finset.range (n + 1), eulerian n k * (x + k).choose n`.
-/
theorem worpitzky (n x : ℕ) :
    x ^ n = ∑ k ∈ Finset.range (n + 1), eulerian n k * (x + k).choose n := by
  induction n with
  | zero => simp [eulerian_0_0]
  | succ n ih =>
    have expand : ∀ k ∈ Finset.range (n + 1),
        eulerian n k * (x + k).choose n * x
          = (k + 1) * eulerian n k * (x + k).choose (n + 1)
            + (n - k) * eulerian n k * (x + k + 1).choose (n + 1) := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      calc eulerian n k * (x + k).choose n * x
          = eulerian n k * (x * (x + k).choose n) := by ring
        _ = eulerian n k * ((k + 1) * (x + k).choose (n + 1)
              + (n - k) * (x + k + 1).choose (n + 1)) := by rw [worpitzky_step x n k hkn]
        _ = (k + 1) * eulerian n k * (x + k).choose (n + 1)
              + (n - k) * eulerian n k * (x + k + 1).choose (n + 1) := by ring
    calc x ^ (n + 1)
        = (∑ k ∈ Finset.range (n + 1), eulerian n k * (x + k).choose n) * x := by
          rw [pow_succ, ih]
      _ = ∑ k ∈ Finset.range (n + 1), eulerian n k * (x + k).choose n * x :=
          Finset.sum_mul ..
      _ = ∑ k ∈ Finset.range (n + 1),
            ((k + 1) * eulerian n k * (x + k).choose (n + 1)
              + (n - k) * eulerian n k * (x + k + 1).choose (n + 1)) :=
          Finset.sum_congr rfl expand
      _ = (∑ k ∈ Finset.range (n + 1), (k + 1) * eulerian n k * (x + k).choose (n + 1))
            + ∑ k ∈ Finset.range (n + 1), (n - k) * eulerian n k * (x + k + 1).choose (n + 1) :=
          Finset.sum_add_distrib
      _ = ∑ k ∈ Finset.range (n + 1 + 1), eulerian (n + 1) k * (x + k).choose (n + 1) :=
          (sum_eulerian_succ_mul_choose n x).symm

end SpecialNumbers
