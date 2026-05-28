/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Ring.Regular
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative
import LeanPool.LeanPolyABC.Lib.Radical
import LeanPool.LeanPolyABC.Lib.Wronskian

/-
On `a.divRadical = a / radical a`. The purpose of this file is to prove our "main lemma" that
`a.divRadical` divides `a'` for any nonzero polynomial `a`.
The proof is based on induction (`UniqueFactorizationMonoid.induction_on_coprime`).
-/
noncomputable section

open scoped Polynomial

open Polynomial UniqueFactorizationMonoid

namespace LeanPolyABC

namespace Polynomial

variable {k : Type _} [Field k] [DecidableEq k]

/--
For a given polynomial `a`, `a.divRadical` is `a` divided by its radical `radical a`.
This is the key to our implementation. -/
def divRadical (a : k[X]) : k[X] :=
  a / radical a

theorem hMul_radical_divRadical (a : k[X]) : radical a * divRadical a = a := by
  rw [divRadical]
  rw [← EuclideanDomain.mul_div_assoc _ (radical_dvd_self a)]
  exact mul_div_cancel_left₀ a (radical_ne_zero a)

theorem divRadical_ne_zero {a : k[X]} (ha : a ≠ 0) : divRadical a ≠ 0 := by
  rw [← hMul_radical_divRadical a] at ha
  exact right_ne_zero_of_mul ha

theorem divRadical_isUnit {u : k[X]} (hu : IsUnit u) : IsUnit (divRadical u) := by
  rwa [divRadical, radical_unit_eq_one hu, EuclideanDomain.div_one]

theorem eq_divRadical {a x : k[X]} (h : radical a * x = a) : x = divRadical a := by
  apply EuclideanDomain.eq_div_of_mul_eq_left (radical_ne_zero a)
  rwa [mul_comm]

theorem divRadical_hMul {a b : k[X]} (hc : IsCoprime a b) :
    divRadical (a * b) = divRadical a * divRadical b := by
  by_cases ha : a = 0
  · rw [ha, MulZeroClass.zero_mul, divRadical, EuclideanDomain.zero_div, MulZeroClass.zero_mul]
  by_cases hb : b = 0
  · rw [hb, MulZeroClass.mul_zero, divRadical, EuclideanDomain.zero_div, MulZeroClass.mul_zero]
  symm; apply eq_divRadical
  rw [radical_hMul hc]
  rw [mul_mul_mul_comm, hMul_radical_divRadical, hMul_radical_divRadical]

theorem divRadical_dvd_self (a : k[X]) : divRadical a ∣ a := by
  rw [divRadical]
  apply EuclideanDomain.div_dvd_of_dvd
  exact radical_dvd_self a

/- Main lemma: a / rad(a) ∣ a'.
Proof uses `induction_on_coprime` of `UniqueFactorizationMonoid`.
-/

theorem divRadical_dvd_derivative (a : k[X]) : divRadical a ∣ derivative a := by
  induction a using induction_on_coprime with
  | h0 =>
    rw [derivative_zero]
    apply dvd_zero
  | @h1 a ha =>
    exact (divRadical_isUnit ha).dvd
  | @hpr p i hp =>
    cases i with
    | zero =>
      rw [pow_zero, derivative_one]
      apply dvd_zero
    | succ i =>
      rw [← mul_dvd_mul_iff_left (radical_ne_zero (p ^ i.succ)), hMul_radical_divRadical,
        radical_prime_pow hp i.succ_pos, derivative_pow_succ, ← mul_assoc]
      apply dvd_mul_of_dvd_left
      rw [mul_comm, mul_assoc]
      apply dvd_mul_of_dvd_right
      rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero i hp.ne_zero), dvd_normalize_iff]
  | @hcp x y hpxy hx hy =>
    -- If it holds for coprime pair a and b, then it also holds for a * b.
    have hc : IsCoprime x y :=
      EuclideanDomain.isCoprime_of_dvd
        (fun ⟨hx, hy⟩ => not_isUnit_zero (hpxy (zero_dvd_iff.mpr hx) (zero_dvd_iff.mpr hy)))
        fun p hp _ hpx hpy => hp (hpxy hpx hpy)
    rw [divRadical_hMul hc, derivative_mul]
    exact dvd_add (mul_dvd_mul hx (divRadical_dvd_self y))
      (mul_dvd_mul (divRadical_dvd_self x) hy)

theorem divRadical_dvd_wronskian_left (a b : k[X]) : divRadical a ∣ wronskian a b := by
  rw [wronskian]
  apply dvd_sub
  · apply dvd_mul_of_dvd_left
    exact divRadical_dvd_self a
  · apply dvd_mul_of_dvd_left
    exact divRadical_dvd_derivative a

theorem divRadical_dvd_wronskian_right (a b : k[X]) : divRadical b ∣ wronskian a b := by
  rw [wronskian_anticomm, dvd_neg]
  exact divRadical_dvd_wronskian_left b a

end Polynomial

end LeanPolyABC
