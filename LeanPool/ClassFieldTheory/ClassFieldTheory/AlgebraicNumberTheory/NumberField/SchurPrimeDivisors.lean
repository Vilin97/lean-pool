/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Order.Filter.TendstoCofinite
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Ring
/-!
# New prime divisors of integer-polynomial values

A nonconstant integer polynomial has a nonzero value A. On any progression
through that argument with step A times the product P of forbidden primes,
its values have shape A * (1 + P*b). Finite fibres allow a value different
from 0, A and -A. A prime divisor of the second factor is therefore new.
This is the elementary Schur argument and does not invoke prime density.
-/

open scoped BigOperators

namespace AlgebraicNumberTheory.PrimeSelection

/-- A nonconstant integer polynomial has a nonzero value with a prime factor
outside any prescribed finite set of natural numbers. -/
theorem exists_prime_not_mem_dvd_eval
    (f : Polynomial ℤ) (hf : f.natDegree ≠ 0) (S : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ S ∧
      ∃ n : ℤ, f.eval n ≠ 0 ∧ (q : ℤ) ∣ f.eval n := by
  classical
  let : Filter.TendstoCofinite f.eval :=
    f.tendstoCofinite_of_natDegree_ne_zero hf
  obtain ⟨a, ha⟩ : ∃ a : ℤ, f.eval a ≠ 0 := by
    by_contra! h
    exact hf (by rw [Polynomial.zero_of_eval_zero f h]; rfl)
  let A := f.eval a
  let P : ℕ := ∏ q ∈ S.filter Nat.Prime, q
  have hP : P ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    exact (Finset.mem_filter.mp hq).2.ne_zero
  have hAP : A * (P : ℤ) ≠ 0 := mul_ne_zero ha (Int.natCast_ne_zero.mpr hP)
  have hInjective : Function.Injective (fun t : ℤ => a + A * (P : ℤ) * t) := by
    intro s t h
    exact (mul_left_cancel₀ hAP) (add_left_cancel h)
  have hBad : (f.eval ⁻¹' ({0, A, -A} : Set ℤ)).Finite :=
    Filter.TendstoCofinite.finite_preimage f.eval (by simp)
  obtain ⟨x, ⟨t, rfl⟩, hx⟩ :=
    (Set.infinite_range_of_injective hInjective).exists_notMem_finite hBad
  have hx0 : f.eval (a + A * (P : ℤ) * t) ≠ 0 := by
    intro h
    exact hx (by simp only [Set.mem_preimage, h, Set.mem_insert_iff, Set.mem_singleton_iff,
      true_or])
  have hxA : f.eval (a + A * (P : ℤ) * t) ≠ A := by
    intro h
    exact hx (by simp only [Set.mem_preimage, h, Set.mem_insert_iff, Set.mem_singleton_iff,
      true_or, or_true])
  have hxNegA : f.eval (a + A * (P : ℤ) * t) ≠ -A := by
    intro h
    exact hx (by simp only [Set.mem_preimage, h, Set.mem_insert_iff, Set.mem_singleton_iff,
      or_true])
  have hdifference : A * (P : ℤ) ∣ f.eval (a + A * (P : ℤ) * t) - A := by
    apply dvd_trans (show A * (P : ℤ) ∣ (a + A * (P : ℤ) * t) - a from
      ⟨t, by ring⟩)
    exact Polynomial.sub_dvd_eval_sub _ a f
  obtain ⟨b, hb⟩ := hdifference
  let y : ℤ := 1 + (P : ℤ) * b
  have hy : f.eval (a + A * (P : ℤ) * t) = A * y := by
    calc
      f.eval (a + A * (P : ℤ) * t) =
          A + (f.eval (a + A * (P : ℤ) * t) - A) := by ring
      _ = A + A * (P : ℤ) * b := congrArg (A + ·) hb
      _ = A * y := by dsimp only [y]; ring
  have hyAbs : y.natAbs ≠ 1 := by
    intro h
    rcases Int.natAbs_eq_natAbs_iff.mp
      (show y.natAbs = (1 : ℤ).natAbs from h) with hyOne | hyNegOne
    · apply hxA
      rw [hy, hyOne, mul_one]
    · apply hxNegA
      rw [hy, hyNegOne, mul_neg_one]
  obtain ⟨q, hq, hqy⟩ := Nat.exists_prime_and_dvd hyAbs
  have hqyInt : (q : ℤ) ∣ y := Int.natCast_dvd.mpr hqy
  have hqS : q ∉ S := by
    intro hqS
    have hqP : q ∣ P := Finset.dvd_prod_of_mem (fun r : ℕ => r)
      (Finset.mem_filter.mpr ⟨hqS, hq⟩)
    have hqPb : (q : ℤ) ∣ (P : ℤ) * b :=
      dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hqP) b
    have hqOne : (q : ℤ) ∣ 1 := by
      simpa only [y, add_sub_cancel_right] using dvd_sub hqyInt hqPb
    exact hq.not_dvd_one (Int.natCast_dvd_natCast.mp hqOne)
  refine ⟨q, hq, hqS, a + A * (P : ℤ) * t, hx0, ?_⟩
  rw [hy]
  exact dvd_mul_of_dvd_right hqyInt A

/-- The prime divisors of nonzero values of a nonconstant integer polynomial
form an infinite set. -/
theorem infinite_primes_dvd_nonzero_eval
    (f : Polynomial ℤ) (hf : f.natDegree ≠ 0) :
    Set.Infinite {q : ℕ | q.Prime ∧ ∃ n : ℤ, f.eval n ≠ 0 ∧ (q : ℤ) ∣ f.eval n} := by
  intro hFinite
  obtain ⟨q, hq, hqS, n, hn, hqn⟩ :=
    exists_prime_not_mem_dvd_eval f hf hFinite.toFinset
  exact hqS (hFinite.mem_toFinset.mpr ⟨hq, n, hn, hqn⟩)

end AlgebraicNumberTheory.PrimeSelection
