/-
Copyright (c) 2026 Walter Moreira, Joe Stubbs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Walter Moreira, Joe Stubbs
-/
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Eulerian Numbers

This module formalizes the definition of Eulerian numbers (Section 6.2 from
[Concrete Mathematics][knuth1989concrete]).

The Eulerian number $\left\langle{n\atop k}\right\rangle$ counts the number of permutations
of $\{1,2,\ldots,n\}$ with $k$ ascents.

## References

* [Concrete Mathematics][knuth1989concrete]
-/

open Ring Polynomial

namespace SpecialNumbers

/--
Eulerian number: counts the permutations of `{1, …, n}` with exactly `k` ascents.
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

lemma smul_mul_eq [NonAssocRing S] (r s : S) (a : ℕ) : (a • r) * s = r * (a • s) := by
  rw [mul_smul_comm]
  exact smul_mul_assoc a r s

variable [NonAssocRing R] [Pow R ℕ] [BinomialRing R] [NatPowAssoc R]

attribute [local instance] BinomialRing.toIsAddTorsionFree in
lemma succ_mul_choose_eq (r : R) (n : ℕ) :
    (n + 1) • choose (r + 1) (n + 1) = (r + 1) * choose r n := by
  suffices h : (n + 1).factorial • choose (r + 1) (n + 1) = n.factorial • (r + 1) * choose r n by
    rw [Nat.factorial] at h
    nth_rw 1 [Nat.mul_comm] at h
    rw [mul_smul] at h
    rw [smul_mul_assoc] at h
    exact nsmul_right_injective (by positivity) h
  rw [← descPochhammer_eq_factorial_smul_choose]
  simp only [descPochhammer]
  rw [smeval_mul, smeval_X, smeval_comp, smul_mul_eq]
  simp [descPochhammer_eq_factorial_smul_choose]

end SpecialNumbers
