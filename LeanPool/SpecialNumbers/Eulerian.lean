/-
Copyright (c) 2026 Walter Moreira, Joe Stubbs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Walter Moreira, Joe Stubbs
-/
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.NeZero

/-!
# Eulerian Numbers

This module defines the Eulerian numbers by their standard triangular recurrence
(Section 6.2 of [Concrete Mathematics][knuth1989concrete]) and proves their
boundary values.

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

theorem eulerian_of_n_zero (n : ℕ) : eulerian n 0 = 1 := by
  simp [eulerian]

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

end SpecialNumbers
