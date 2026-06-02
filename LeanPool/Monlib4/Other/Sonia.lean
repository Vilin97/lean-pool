/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Lift
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.Abel
import Init.Data.Nat.Lemmas

/-!

# Useless and interesting fact(s) on naturals and integers

*Sonia* recently asked me:
  "Is there a way to prove that a number is divisible by 9, by looking at the sum of its digits?"
So here is the generalised version of the question.

## Main results

In both of the following results, `b` is a natural number greater than `1`.

* `nat_repr_mod_eq_sum_repr_mod`: this says that the remainder of dividing a number
  in base `b + 1` by `b` is equal to the remainder of dividing the sum of its digits by `b`
* `nat_dvd_repr_iff_nat_dvd_sum_repr`: this says that a number in base `b + 1` is divisible by `b`
  if and only if the sum of its digits is divisible by `b`

-/


open scoped BigOperators

/-- `(∑ i, x i) % a = (∑ i, (x i % a)) % a` -/
theorem Int.sum_mod {n : ℕ} (x : Fin n → ℤ) (a : ℤ) : (∑ i, x i) % a = (∑ i, x i % a) % a :=
  by
  induction n generalizing a with
  | zero => rfl
  | succ d hd =>
    let x' : Fin d → ℤ := fun i => x i.succ
    have hx' : ∀ i, x' i = x i.succ := fun i => rfl
    simp_rw [Fin.sum_univ_succ]
    rw [Int.add_emod]
    simp_rw [← hx', Int.emod_add_cancel_left]
    rw [hd]
    simp_rw [Int.emod_emod]

-- `n.succ % n = 1` if `1 < n`
theorem Fin.succ_mod_self {n : ℕ} (hn : 1 < n) : n.succ % n = 1 :=
  by
  rw [Nat.succ_eq_add_one, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
  exact Nat.mod_eq_of_lt hn

/-- `a.succ ^ n % a = 1` when `1 < a` -/
theorem Fin.succ_pow_mod_self {n a : ℕ} (ha : 1 < a) : a.succ ^ n % a = 1 :=
  by
  induction n generalizing a ha with
  | zero =>
    rw [pow_zero]
    exact Nat.mod_eq_of_lt ha
  | succ d hd =>
    rw [Nat.pow_mod]
    simp_rw [Nat.pow_mod (Nat.succ _)] at hd
    specialize hd ha
    rw [Fin.succ_mod_self ha, one_pow] at hd ⊢
    exact hd

-- `(a * b.succ ^ n) % b = a % b`
theorem Int.hMul_nat_succ_pow_mod_nat (a : ℤ) {b n : ℕ} (hb : 1 < b) :
    a * ((b : ℕ).succ ^ n : ℕ) % (b : ℕ) = a % b := by
  rw [Int.mul_emod, Int.ofNat_mod_ofNat, Fin.succ_pow_mod_self hb, Int.ofNat_one, mul_one,
    Int.emod_emod]

/-- `(∑ i, (x i * a.succ ^ i)) % a = (∑ i, x i) % a`
-/
theorem nat_repr_mod_eq_sum_repr_mod {a n : ℕ} (x : Fin n → ℤ) (ha : 1 < a) :
    (∑ i, x i * (a.succ : ℕ) ^ (i : ℕ)) % a = (∑ i, x i) % a :=
  by
  induction n with
  | zero => rfl
  | succ d hd =>
    simp_rw [Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ,
      Int.emod_add_cancel_left]
    let x' : Fin d → ℤ := fun i => x i.succ
    have hx' : ∀ i, x' i = x i.succ := fun i => rfl
    simp_rw [← Nat.succ_eq_add_one, ← hx']
    simp only [hx']
    rw [Int.sum_mod]
    simp_rw [← hx']
    rw [← Int.emod_emod, Int.emod_emod]
    have : ∀ (c : ℤ) (d : ℕ), c * (a.succ : ℕ) ^ d % a = c % a := fun c d =>
      calc
        c * (a.succ : ℕ) ^ d % a = c * ((a.succ : ℕ) ^ d : ℕ) % (a : ℕ) := by
          simp_rw [Int.natCast_pow]
        _ = c % a := Int.hMul_nat_succ_pow_mod_nat _ ha
    simp_rw [this, ← Int.sum_mod]

/-- `a ∣ (∑ i, (x i * a.succ ^ i)) ↔ a ∣ (∑ i, x i)`
  in other words, a number in base `a.succ` is divisible by `a`, if and only if
  the sum of its digits is divisible by `a`
-/
theorem nat_dvd_repr_iff_nat_dvd_sum_repr {a n : ℕ} (x : Fin n → ℤ) (ha : 1 < a) :
    (a : ℤ) ∣ ∑ i, x i * (a.succ : ℕ) ^ (i : ℕ) ↔ (a : ℤ) ∣ ∑ i, x i := by
  simp_rw [Int.dvd_iff_emod_eq_zero, nat_repr_mod_eq_sum_repr_mod _ ha]

/-- most natural example:
 `9 ∣ ∑ i, (x i * 10 ^ i) ↔ 9 ∣ ∑ i, x i`
 in other words, a number (in base `10`) is divisible by `9`, if and only if
 the sum of its digits is divisible by `9`
-/
example {n : ℕ} (x : Fin n → ℤ) : 9 ∣ ∑ i, x i * 10 ^ (i : ℕ) ↔ 9 ∣ ∑ i, x i :=
  nat_dvd_repr_iff_nat_dvd_sum_repr x (Nat.one_lt_succ_succ _)

/-- so when the base is `8`, then a number in base `8` is divisible by `7`,
 if and only if the sum of its digits is divisible by `7` -/
example {n : ℕ} (x : Fin n → ℤ) : 7 ∣ ∑ i, x i * 8 ^ (i : ℕ) ↔ 7 ∣ ∑ i, x i :=
  nat_dvd_repr_iff_nat_dvd_sum_repr _ (Nat.one_lt_succ_succ _)
