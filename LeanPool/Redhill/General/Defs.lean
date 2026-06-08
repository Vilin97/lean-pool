/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/

import Mathlib.FieldTheory.Finite.Basic
import LeanPool.Redhill.Common.VWPair

/-!
# Definitions for the general case

In this section `h` is the variable such that `tup n F h ∈ factorFreeTuples F (n + 6)`
for sufficiently large `h`.

The lower bound `s` for `primeChain` in `U` was originally `200 * Y F ^ 6`.
-/


namespace GeneralCase

open Nat Fin Finset

variable (n : ℕ) (F : Finset ℕ) (h : ℕ)

/-- An optimised version of the paper's `y`. -/
def Y : ℕ := 33330 * (F.erase 0).prod id

/-- `x` in the paper, but using the optimised `y`. -/
def X : ℕ := (Y F + 1) ^ h !

lemma Y_lower_bound {F} : 33330 ≤ Y F := by
  rw [← mul_one 33330]
  exact _root_.mul_le_mul_right (one_le_prod (by grind)) _

lemma Y_pos {F} : 0 < Y F := by grind [Y_lower_bound]

lemma Y_lt_X {F h} : Y F < X F h :=
  (lt_add_one _).trans_le (le_self_pow (factorial_ne_zero h) _)

/-- The sum of `tup` over all indices save `n` and `n + 1`, i.e. the input `u` to `VWPair`. -/
def U : ℕ := (100 * Y F - 2) * Y F ^ 5 + ∑ i ∈ range n, primeChain (100 * Y F ^ 6) i

lemma U_lower_bound {n F} : (100 * 33330 - 2) * 33330 ^ 5 ≤ U n F := by
  apply (Nat.le_add_right ..).trans'
  gcongr <;> exact Y_lower_bound

lemma U_pos {n F} : 0 < U n F := by grind [U_lower_bound]

/-- The `VWPair` generated from the inputs `u = m = U n F`. -/
def VW : VWPair (U n F) (U n F) := .of ..

/-- The sequence of `(n + 6)`-tuples whose tail is in `factorFreeTuples`
and has quality tending to `5 / 4`. -/
def tup (i : Fin (n + 6)) : ℤ :=
  i.addCases (primeChain (100 * Y F ^ 6) ·.1) fun
    | 0 => (VW n F).v
    | 1 => -(VW n F).w
    | 2 => (X F h ^ 2 + 10 * Y F ^ 3) ^ 2
    | 3 => (10 * Y F - 1) * X F h ^ 4
    | 4 => (X F h - Y F) ^ 5
    | 5 => -(X F h + Y F) ^ 5

variable {n F h}

-- Not `@[simp]`: with `Fin.castAdd_to_castSucc` from another pool project in the global
-- simp set, the left-hand side `i.castAdd 6` is rewritten to a `Fin.castSucc` chain, so this
-- lemma's left-hand side is no longer in simp normal form. All call sites invoke it explicitly.
lemma tup_castAdd {i : Fin n} :
    tup n F h (i.castAdd 6) = primeChain (100 * Y F ^ 6) i.1 := by
  simp [tup]

@[simp] lemma tup_natAdd_zero : tup n F h (natAdd n 0) = (VW n F).v := by
  simp [tup]

@[simp] lemma tup_natAdd_one : tup n F h (natAdd n 1) = -(VW n F).w := by
  simp [tup]

@[simp] lemma tup_natAdd_two : tup n F h (natAdd n 2) = (X F h ^ 2 + 10 * Y F ^ 3) ^ 2 := by
  simp [tup]

@[simp] lemma tup_natAdd_three : tup n F h (natAdd n 3) = (10 * Y F - 1) * X F h ^ 4 := by
  simp [tup]

@[simp] lemma tup_natAdd_four : tup n F h (natAdd n 4) = (X F h - Y F) ^ 5 := by
  simp [tup]

@[simp] lemma tup_natAdd_five : tup n F h (natAdd n 5) = -(X F h + Y F) ^ 5 := by
  simp [tup]

lemma sum_tup : ∑ i, tup n F h i = 0 := by
  simp only [tup, sum_univ_add, addCases_left, addCases_right, sum_univ_six, add_assoc]
  set x := X F h
  set y := Y F
  rw [show (x ^ 2 + 10 * y ^ 3) ^ 2 + ((10 * y - 1 : ℤ) * x ^ 4 + ((x - y) ^ 5 + -(x + y) ^ 5)) =
    (100 * y - 2) * y ^ 5 by ring, ← add_assoc _ _ (_ * _), (VW n F).eq_add, cast_add, neg_add,
    add_add_neg_cancel'_right, sum_univ_eq_sum_range fun i ↦ (primeChain _ i : ℤ), ← cast_sum]
  grind [U]

section Factors

variable {f : ℕ} (mf : f ∈ F)

lemma dvd_Y_of_mem_F (mf : f ∈ F.erase 0) : f ∣ Y F :=
  (dvd_prod_of_mem _ mf).mul_left _

include mf

lemma X_modEq_one_of_mem_F (lf : 3 ≤ f) : X F h ≡ 1 [MOD f] := by
  unfold X
  nth_rw 2 [← one_pow (h !)]
  apply ModEq.pow
  rw [add_modEq_right_iff]
  exact dvd_Y_of_mem_F (by grind)

lemma le_Y_of_mem_F : f ≤ Y F :=
  calc
    _ ≤ (F.erase 0).prod id := by
      obtain rfl | f0 := eq_or_ne f 0
      · simp
      · exact single_le_prod' (f := id) (by grind) (by simp_all)
    _ ≤ _ := by grind [Y]

lemma lt_primeChain_of_mem_F : f < primeChain (100 * Y F ^ 6) n :=
  calc
    _ ≤ 1 * Y F := by simp [le_Y_of_mem_F mf]
    _ ≤ 100 * Y F ^ 6 := mul_le_mul' (by decide) (le_self_pow (by decide) _)
    _ < _ := primeChain_gt

lemma le_U_of_mem_F : f ≤ U n F :=
  calc
    _ ≤ 1 * Y F := by simp [le_Y_of_mem_F mf]
    _ ≤ (100 * Y F - 2) * Y F ^ 5 := mul_le_mul' (by grind [Y_pos]) (le_self_pow (by decide) _)
    _ ≤ _ := by grind [U]

theorem not_dvd_tup (lf : 3 ≤ f) (i) : ¬↑f ∣ tup n F h i := by
  cases i using Fin.addCases with
  | left i =>
    rw [tup_castAdd, Int.natCast_dvd_natCast]
    exact (prime_def_lt'.mp prime_primeChain).2 _ (by lia) (lt_primeChain_of_mem_F mf)
  | right i =>
    have df : f ∣ Y F := dvd_Y_of_mem_F (by grind)
    have ndp4 : ¬f ∣ X F h ^ 4 := by
      have : X F h ^ 4 % f = 1 := mod_eq_of_modEq ((X_modEq_one_of_mem_F mf lf).pow 4) (by lia)
      rw [dvd_iff_mod_eq_zero, this]
      decide
    fin_cases i <;> simp only [reduceFinMk]
    · rw [tup_natAdd_zero, Int.natCast_dvd_natCast]
      exact ((VW n F).not_dvd _ (mem_Icc.mpr ⟨lf, le_U_of_mem_F mf⟩)).1
    · rw [tup_natAdd_one, dvd_neg, Int.natCast_dvd_natCast]
      exact ((VW n F).not_dvd _ (mem_Icc.mpr ⟨lf, le_U_of_mem_F mf⟩)).2
    · rw [tup_natAdd_two]
      norm_cast
      rwa [show (X F h ^ 2 + 10 * Y F ^ 3) ^ 2 =
        X F h ^ 4 + (20 * X F h ^ 2 * Y F ^ 2 + 100 * Y F ^ 5) * Y F by ring,
        Nat.dvd_add_left (df.mul_left _)]
    · rw [tup_natAdd_three, sub_one_mul, ← mul_rotate, dvd_sub_right (mod_cast df.mul_left _)]
      exact_mod_cast ndp4
    · rw [tup_natAdd_four]
      have key := X_modEq_one_of_mem_F (h := h) mf lf
      rw [← Int.natCast_modEq_iff] at key
      replace key := (Int.add_modEq_left_iff (b := -Y F)).mpr
        (by rwa [dvd_neg, Int.natCast_dvd_natCast]) |>.trans key
      replace key := key.pow 5
      rw [← sub_eq_add_neg, cast_one, one_pow] at key
      rw [← Int.modEq_zero_iff_dvd]
      by_contra hc
      replace hc : 0 % (f : ℤ) = 1 % f := hc.symm.trans key
      iterate 2 rw [Int.emod_eq_of_lt (by lia) (by lia)] at hc
      simp at hc
    · rw [tup_natAdd_five, dvd_neg]
      norm_cast
      have key := X_modEq_one_of_mem_F (h := h) mf lf
      replace key := ((add_modEq_left_iff.mpr df).trans key).pow 5
      rw [dvd_iff_mod_eq_zero, mod_eq_of_modEq key (by lia)]
      decide

end Factors

end GeneralCase
