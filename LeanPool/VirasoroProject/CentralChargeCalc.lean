/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.Henselian

/-!
# Central charge calculations for Sugawara constructions

This file contains the crucial auxiliary calculations leading to the values of the central charge
in various Sugawara constructions. The calculations make use of "discrete integration" on `ℤ`.

## Main definitions

* `zPrimitive`: A "discrete integral function" to a given function `f : ℤ → R`. The defining
  properties of `F = zPrimitive f` are `F(0) = 0` and `F(n+1) - F(n) = f(n)`.
* `zMonomialF`: The `d`th discrete monomial function is defined by `d`-fold discrete integration
  starting from the function `1`. (The continuum analogue is the monomial `1/d! • x^d`.)

## Main statements

* `zMonomialF_eq` The `d`th discrete monomial function is given by
  `n ↦ 1/d! • ∏ j (0 ≤ j < d), (n - j)`
* `bosonic_sugawara_cc_calc`: For any `n ∈ ℤ`, we have
   `zPrimitive (fun l ↦ (l : R) * (n - l)) n = (n^3 - n) / 6`.
* `bosonic_sugawara_cc_calc_nonneg`: For any `n ∈ ℕ`, we have
   `∑ l (0 ≤ l < n), (l : ℚ) * (n - l) = (n^3 - n) / 6`.

## TODO

* TODO: Add variants of the calculation for fermionic Sugawara constructions etc.

## Tags

central charge, Sugawara construction

-/

namespace VirasoroProject



section central_charge_calculation

open Finset

/-- A discrete integral of a function on `ℤ`. -/
def zPrimitive {R : Type*} [AddCommGroup R] (f : ℤ → R) (n : ℤ) : R :=
  if 0 ≤ n then ∑ j ∈ range (Int.toNat n), f j else -(∑ j ∈ range (Int.natAbs n), f (-j-1))

@[simp] lemma zPrimitive_zero {R : Type*} [AddCommGroup R] (f : ℤ → R) :
    zPrimitive f 0 = 0 :=
  rfl

@[simp] lemma zPrimitive_apply_of_nonneg {R : Type*} [AddCommGroup R] (f : ℤ → R)
    {n : ℤ} (hn : 0 ≤ n) :
    zPrimitive f n = ∑ j ∈ range (Int.toNat n), f j := by
  simp [zPrimitive, hn]

@[simp] lemma zPrimitive_apply_of_nonpos {R : Type*} [AddCommGroup R] (f : ℤ → R)
    {n : ℤ} (hn : n ≤ 0) :
    zPrimitive f n = -(∑ j ∈ range (Int.natAbs n), f (-j-1)) := by
  by_cases hn' : n = 0
  · simp [hn']
  · grind [zPrimitive]

@[simp] lemma zPrimitive_succ {R : Type*} [AddCommGroup R] (f : ℤ → R) (n : ℤ) :
    zPrimitive f (n + 1) = zPrimitive f n + f n := by
  by_cases hn : 0 ≤ n
  · simp [zPrimitive, hn, Int.le_add_one hn, Int.toNat_add hn zero_le_one, sum_range_succ]
  · simp only [not_le] at hn
    have n_natAbs : n.natAbs = (n+1).natAbs + 1 := by grind
    simp only [zPrimitive_apply_of_nonpos _ hn, zPrimitive_apply_of_nonpos _ hn.le, n_natAbs,
               sum_range_succ, Int.natCast_natAbs, neg_add_rev]
    simp only [add_comm (-(f _)), add_assoc, left_eq_add]
    simp [show -|n + 1| - 1 = n by rw [abs_of_nonpos hn, neg_neg]; ring]

lemma eq_zPrimitive_of_eq_zero_of_forall_eq_add {R : Type*} [AddCommGroup R] {f F : ℤ → R}
    (h0 : F 0 = 0) (h1 : ∀ n, F (n + 1) = F n + f n) :
    F = zPrimitive f := by
  have obsP : ∀ (n : ℕ), F n = zPrimitive f n := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih => aesop
  have obsM : ∀ (n : ℕ), F (-n) = zPrimitive f (-n) := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      have keyF := h1 (-(n + 1))
      have keyP := zPrimitive_succ f (-(n + 1))
      grind
  ext m
  by_cases hm : 0 ≤ m
  · rw [(Int.toNat_of_nonneg hm).symm]
    exact obsP m.toNat
  · have hm' : m < 0 := Int.lt_of_not_ge hm
    rw [show m = -m.natAbs from Int.eq_neg_comm.mp (by simpa [hm'] using hm'.le)]
    exact obsM m.natAbs

lemma zPrimitive_add {R : Type*} [AddCommGroup R] (f g : ℤ → R) :
    zPrimitive (f + g) = zPrimitive f + zPrimitive g  := by
  apply (eq_zPrimitive_of_eq_zero_of_forall_eq_add ..).symm
  · simp
  · intro n
    simp only [Pi.add_apply, zPrimitive_succ]
    ac_rfl

lemma zPrimitive_smul {R S : Type*} [AddCommGroup R] [DistribSMul S R]
    (c : S) (f : ℤ → R) :
    zPrimitive (c • f) = c • (zPrimitive f) := by
  apply (eq_zPrimitive_of_eq_zero_of_forall_eq_add ..).symm <;> simp

lemma zPrimitive_sub {R : Type*} [AddCommGroup R] (f g : ℤ → R) :
    zPrimitive (f - g) = zPrimitive f - zPrimitive g  := by
  apply (eq_zPrimitive_of_eq_zero_of_forall_eq_add ..).symm
  · simp
  · intro n
    simp only [Pi.sub_apply, zPrimitive_succ, sub_eq_add_neg, neg_add_rev, ← add_assoc]
    ac_rfl

lemma zPrimitive_mul_left {R : Type*} [Ring R] (c : R) (f : ℤ → R) :
    zPrimitive (fun n ↦ c * f n) = fun n ↦ c * zPrimitive f n := by
  apply (eq_zPrimitive_of_eq_zero_of_forall_eq_add ..).symm
  · simp
  · intro n
    simp [mul_add]

lemma zPrimitive_mul_right {R : Type*} [Ring R] (c : R) (f : ℤ → R) :
    zPrimitive (fun n ↦ f n * c) = fun n ↦ zPrimitive f n * c := by
  apply (eq_zPrimitive_of_eq_zero_of_forall_eq_add ..).symm
  · simp
  · intro n
    simp [add_mul]

/-- A discrete monomial function of degree `d`, obtained recursively by starting from the
unit function `1` and taking the discrete primitive `d` times.
(Note: The resulting normalization is such that this monomial approximately `x ↦ 1/d! * x^d`.) -/
def zMonomialF (R : Type*) [AddCommGroup R] [One R] (d : ℕ) : ℤ → R := match d with
  | 0 => fun _ ↦ 1
  | d + 1 => zPrimitive (zMonomialF R d)

lemma zMonomialF_eq (R : Type*) [Field R] [CharZero R] (d : ℕ) :
    (zMonomialF R d) = (fun (n : ℤ) ↦ ((∏ j ∈ range d, (n - j : R)) / (Nat.factorial d : R))) := by
  induction d with
  | zero =>
    funext n
    simp [zMonomialF]
  | succ d ihd =>
    rw [zMonomialF, Eq.comm]
    apply eq_zPrimitive_of_eq_zero_of_forall_eq_add
    · simpa using Or.inl <| prod_eq_zero_iff.mpr ⟨0, by simp, by simp⟩
    · intro n
      have aux₀ : (d.factorial : R) ≠ 0 := by simp [Nat.factorial_ne_zero _]
      have aux₁: ((d+1).factorial : R) ≠ 0 := by simp [Nat.factorial_ne_zero _]
      have aux' : ((d+1) : R) ≠ 0 := by norm_cast
      calc  (∏ j ∈ range (d + 1), ((↑(n + 1) : R) - j)) / (d + 1).factorial
        _ = (∏ x ∈ range (d + 1), (n + 1 - x)) / (d + 1).factorial                      := by simp
        _ = (∏ j ∈ range (d + 1), (n - j)) / ((d + 1) * d.factorial)
            + (∏ j ∈ range d, (n - j : R)) / d.factorial                                := ?_
        _ = (∏ j ∈ range (d + 1), (↑n - ↑j)) / ↑(d + 1).factorial + zMonomialF R d n    := ?_
      · simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        simp only [prod_range_succ (fun a ↦ (n : R) - a), Int.cast_prod, Int.cast_sub, Int.cast_add,
                   Int.cast_one, Int.cast_natCast]
        field_simp
        simp [sub_add, prod_range_succ']
      · simp [ihd, mul_comm _ (d.factorial : R), Nat.factorial_succ, mul_comm]

lemma zMonomialF_zero_eq (R : Type*) [Field R] (n : ℤ) :
    zMonomialF R 0 n = 1 := by
  simp [zMonomialF]

lemma zMonomialF_one_eq (R : Type*) [Field R] [CharZero R] (n : ℤ) :
    zMonomialF R 1 n = n := by
  simp [zMonomialF_eq]

lemma zMonomialF_two_eq (R : Type*) [Field R] [CharZero R] (n : ℤ) :
    zMonomialF R 2 n = n * (n - 1) / 2 := by
  simp [zMonomialF_eq, prod_range_succ]

lemma zMonomialF_three_eq (R : Type*) [Field R] [CharZero R] (n : ℤ) :
    zMonomialF R 3 n = n * (n - 1) * (n - 2) / 6 := by
  simp [zMonomialF_eq, prod_range_succ, show Nat.factorial 3 = 6 from rfl]

lemma zMonomialF_four_eq (R : Type*) [Field R] [CharZero R] (n : ℤ) :
    zMonomialF R 4 n = n * (n - 1) * (n - 2) * (n - 3) / 24 := by
  simp [zMonomialF_eq, prod_range_succ, show Nat.factorial 4 = 24 from rfl]

lemma zMonomialF_five_eq (R : Type*) [Field R] [CharZero R] (n : ℤ) :
    zMonomialF R 5 n = n * (n - 1) * (n - 2) * (n - 3) * (n - 4) / 120 := by
  simp [zMonomialF_eq, prod_range_succ, show Nat.factorial 5 = 120 from rfl]

lemma zMonomialF_apply_eq_zero_of_of_nonneg_lt (R : Type*) [Field R] [CharZero R]
    (d : ℕ) {n : ℕ} (n_lt : n < d) :
    zMonomialF R d n = 0 := by
  simpa only [zMonomialF_eq R d, Int.cast_natCast, div_eq_zero_iff, Nat.cast_eq_zero]
    using Or.inl <| prod_eq_zero_iff.mpr ⟨n, ⟨mem_range.mpr n_lt, by simp⟩⟩

lemma bosonic_sugawara_cc_calc (R : Type*) [Field R] [CharZero R] (n : ℤ) :
    zPrimitive (fun l ↦ (l : R) * (n - l)) n = (n^3 - n) / 6 := by
  have obs : (n^3 - n) / 6 = (n - 1 : R) * zMonomialF R 2 n - 2 * zMonomialF R 3 n := by
    rw [zMonomialF_two_eq, zMonomialF_three_eq]
    field_simp
    ring
  have key : (zPrimitive fun l ↦ (n - 1 : R) * l) - (zPrimitive fun l ↦ 2 * zMonomialF R 2 l)
              = zPrimitive ((fun (l : ℤ) ↦ (l : R) * (n - l))) := by
    rw [← zPrimitive_sub]
    apply congr_arg zPrimitive
    ext l
    simp [zMonomialF_two_eq]
    ring
  simp_rw [obs, ← key, zPrimitive_mul_left]
  dsimp
  congr
  ext m
  rw [zMonomialF_one_eq]

lemma bosonic_sugawara_cc_calc_nonneg (n : ℕ) :
    ∑ l ∈ range n, (l : ℚ) * (n - l) = (n^3 - n) / 6 := by
  have key := bosonic_sugawara_cc_calc ℚ n
  simp only [Int.cast_natCast, Nat.cast_nonneg, zPrimitive_apply_of_nonneg, Int.toNat_natCast]
    at key
  rw [← key]

end central_charge_calculation

end VirasoroProject -- namespace
