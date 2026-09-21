/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
import LeanPool.PentagonalNumberTheoremAnalytic.QSeries.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite q-binomial theorem

This file proves the finite q-binomial theorem:
$$\prod_{k=0}^{n-1}(1 + z q^k) = \sum_{k=0}^{n} q^{\binom{k}{2}} \binom{n}{k}_q z^k.$$

## Main results

* `QSeries.prod_one_add_mul_pow_eq_sum_qBinom` — the finite q-binomial theorem.
-/

open Finset Filter
open scoped Topology

namespace QSeries

variable {R : Type*}


/-- **Finite q-binomial theorem.**
$$\prod_{k=0}^{n-1}(1 + z q^k) = \sum_{k=0}^{n} q^{\binom{k}{2}} \binom{n}{k}_q z^k.$$ -/
theorem prod_one_add_mul_pow_eq_sum_qBinom [CommRing R] (q z : R) (n : ℕ) :
    ∏ k ∈ Finset.range n, (1 + z * q ^ k)
      = ∑ k ∈ Finset.range (n + 1), q ^ k.choose 2 * qBinom n k q * z ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      rw [Finset.sum_range_succ'
            (fun k => q ^ k.choose 2 * qBinom (n + 1) k q * z ^ k) (n + 1)]
      simp only [Nat.choose_zero_succ, pow_zero, qBinom_succ_zero, mul_one]
      have stepB :
          (∑ k ∈ Finset.range (n + 1),
              q ^ (k + 1).choose 2 * qBinom (n + 1) (k + 1) q * z ^ (k + 1))
            = (∑ k ∈ Finset.range (n + 1),
                  q ^ (k + 1).choose 2 * qBinom n (k + 1) q * z ^ (k + 1))
              + ∑ k ∈ Finset.range (n + 1),
                  q ^ (k + 1).choose 2 * q ^ (n - k) * qBinom n k q
                    * z ^ (k + 1) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [qBinom_succ_succ]
        ring
      rw [stepB]
      have stepC :
          (∑ k ∈ Finset.range (n + 1),
              q ^ (k + 1).choose 2 * q ^ (n - k) * qBinom n k q * z ^ (k + 1))
            = z * q ^ n *
                ∑ k ∈ Finset.range (n + 1),
                    q ^ k.choose 2 * qBinom n k q * z ^ k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        have hkle : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [Nat.choose_two_succ k, pow_add q (k.choose 2) k,
            mul_assoc (q ^ k.choose 2) (q ^ k) (q ^ (n - k)),
            ← pow_add q k (n - k),
            show k + (n - k) = n from by omega,
            pow_succ z k]
        ring
      rw [stepC]
      have stepD :
          (∑ k ∈ Finset.range (n + 1), q ^ k.choose 2 * qBinom n k q * z ^ k)
            = (∑ k ∈ Finset.range (n + 1),
                  q ^ (k + 1).choose 2 * qBinom n (k + 1) q * z ^ (k + 1)) + 1 := by
        have h := Finset.sum_range_succ'
          (fun k => q ^ k.choose 2 * qBinom n k q * z ^ k) (n + 1)
        simp only [Nat.choose_zero_succ, pow_zero, qBinom_zero_right, mul_one] at h
        rw [Finset.sum_range_succ
              (f := fun k => q ^ k.choose 2 * qBinom n k q * z ^ k) (n := n + 1),
            qBinom_eq_zero_of_lt q (Nat.lt_succ_self n)] at h
        simp only [mul_zero, zero_mul, add_zero] at h
        exact h
      linear_combination stepD

end QSeries
