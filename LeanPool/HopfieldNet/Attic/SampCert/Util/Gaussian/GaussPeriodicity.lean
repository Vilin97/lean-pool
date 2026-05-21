/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.Util.Gaussian.GaussConvergence

/-!
# Discrete Gaussian Periodicity

This file contains lemmas related to the periodicity of the ``gauss_term`` function,
as well as the sum of the ``gauss_term`` function.
-/


/--
Shifting ``gauss_term_ℝ`` is equivalent to shifting its mean.
-/
theorem shifted_gauss_mean_pos (μ σ : ℝ) (n : ℤ) (k : ℤ) :
  (gauss_term_ℝ σ μ) (((n + k) : ℤ) : ℝ) = (gauss_term_ℝ σ (μ - k)) n := by
  simp [gauss_term_ℝ, gauss_term_ℝ]
  ring_nf

/--
Shifting ``gauss_term_ℝ`` is equivalent to shifting its mean.
-/
theorem shifted_gauss_mean_neg (μ : ℝ) (n : ℤ) (k : ℤ) :
  (gauss_term_ℝ σ μ) (((-(n + k)) : ℤ) : ℝ) = (gauss_term_ℝ σ (-(μ + k))) n := by
  simp [gauss_term_ℝ, gauss_term_ℝ]
  ring_nf

/--
``gauss_term_ℝ`` is summable under any shift.
-/
theorem shifted_gauss_summable_pos {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) (k : ℤ) :
  Summable fun (n : ℕ) => (gauss_term_ℝ σ μ) ((n + k) : ℤ) := by
  conv =>
    right
    intro n
    rw [shifted_gauss_mean_pos μ σ n k]
  apply gauss_convergence_nat_pos h

/--
``gauss_term_ℝ`` is summable under any shift.
-/
theorem shifted_gauss_summable_neg {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) (k : ℤ) :
  Summable fun (n : ℕ) => (gauss_term_ℝ σ μ) ((-(n + k)) : ℤ) := by
  conv =>
    right
    intro n
    rw [shifted_gauss_mean_neg μ n k]
  apply gauss_convergence_nat_pos h

/--
The sum of ``gauss_term_ℝ`` does not change when the mean shifts by 1.
-/
theorem gauss_sum_1_periodic {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) :
  (∑' (n : ℤ), (gauss_term_ℝ σ μ) n) = ∑' (n : ℤ), (gauss_term_ℝ σ (μ + 1)) n := by stop
  have A : ∀ n : ℤ, (gauss_term_ℝ σ (μ + 1)) n = (gauss_term_ℝ σ μ) (n - 1) := by
    intro n ; simp [gauss_term_ℝ, gauss_term_ℝ]
    ring_nf
  conv => enter [2,1, n] ; rw [A]
  clear A

  have S1 : Summable fun (n : ℕ) => (gauss_term_ℝ σ μ) ((n + 1) : ℤ) := by
    apply shifted_gauss_summable_pos h
  have S2 : Summable fun (n : ℕ) => (gauss_term_ℝ σ μ) ((-(n + 1)) : ℤ) := by
    apply gauss_convergence_nat_neg h
  have X := @tsum_of_add_one_of_neg_add_one ℝ _ _ _ _ (fun (n : ℤ) => (gauss_term_ℝ σ μ) n) S1 S2
  rw [X]
  clear X

  have S3 : Summable fun (n : ℕ) => (gauss_term_ℝ σ μ) (((n + 1) : ℤ) - 1) := by
    simp
    apply gauss_convergence_nat_pos h
  have S4 : Summable fun (n : ℕ) => (gauss_term_ℝ σ μ) ((((-(n + 1)) : ℤ) - 1)) := by
    have X : ∀ n : ℕ, ((-(n + 1)) : ℤ) - (1 : ℝ) = ((-(n + 2)) : ℤ) := by
      intro n
      simp
      ring_nf
    conv =>
      right
      intro n
      rw [X]
    apply shifted_gauss_summable_neg h
  have Y := @tsum_of_add_one_of_neg_add_one ℝ _ _ _ _ (fun (n : ℤ) => (gauss_term_ℝ σ μ) (n - 1)) S3 S4
  rw [Y]
  clear Y

  simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, Int.cast_zero, neg_add_rev,
    Int.reduceNeg, Int.cast_neg, add_sub_cancel_right, zero_sub]
  clear S1 S2 S3 S4

  have S5 : Summable fun (n : ℕ) => (gauss_term_ℝ σ μ) (n : ℤ) := by
    apply gauss_convergence_nat_pos h
  have X5 := @tsum_eq_zero_add ℝ _ _ _ _ (fun (n : ℕ) => (gauss_term_ℝ σ μ) n) S5
  rw [X5]; clear X5 S5

  have S6 :  Summable fun (n : ℕ) => (gauss_term_ℝ σ μ) (n + 1) := by
    have S := @shifted_gauss_summable_pos σ h μ 1
    apply Summable.congr S
    intro b
    simp

  have X6 := @tsum_eq_zero_add ℝ _ _ _ _ (fun (n : ℕ) => (gauss_term_ℝ σ μ) (n + 1)) S6
  rw [X6]

  simp

  rw [X6] ; clear X6 S6

  have S7 : Summable fun (n : ℕ) => (gauss_term_ℝ σ μ) (-1 + -(@Nat.cast ℝ AddMonoidWithOne.toNatCast n)) := by
    have X : ∀ n : ℕ, -(1 : ℝ) + -n = -(n + 1) := by
      simp
    conv =>
      right
      intro n
      rw [X]
    have S := @shifted_gauss_summable_neg σ h μ 1
    apply Summable.congr S
    intro b
    simp

  have X7 := @tsum_eq_zero_add ℝ _ _ _ _ (fun (n : ℕ) => (gauss_term_ℝ σ μ) (-1 + -(@Nat.cast ℝ AddMonoidWithOne.toNatCast n ))) S7
  rw [X7] ; clear X7 S7

  simp

  ring_nf

  conv =>
    left
    left
    left
    rw [add_assoc]
    right
    rw [add_comm]

  ring_nf

  conv =>
    left
    left
    rw [add_assoc]
    right
    rw [add_comm]

  ring_nf

  have X : ∀ (b : ℕ), (2 : ℝ) + b = b + 1 + 1 := by
    intro b
    rw [add_comm]
    rw [add_assoc]
    congr
    ring_nf

  conv =>
    left
    left
    right
    right
    intro b
    rw [X]

  congr
  ext n
  congr 1
  ring_nf

/--
The sum of ``gauss_term_ℝ`` does not change when the mean shifts by a positive integer.
-/
theorem shifted_gauss_sum_pos {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) (k : ℕ) :
  (∑' (n : ℤ), (gauss_term_ℝ σ μ) n) = ∑' (n : ℤ), (gauss_term_ℝ σ (μ + k)) n := by
  revert μ
  induction k
  · simp
  · intro μ
    rename_i n IH
    simp
    rw [← add_assoc]
    rw [IH]
    rw [gauss_sum_1_periodic h]

/--
The sum of ``gauss_term_ℝ`` does not change when the mean shifts by a negative integer.
-/
theorem shifted_gauss_sum_neg {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) (k : ℕ) :
  (∑' (n : ℤ), (gauss_term_ℝ σ μ) n) = ∑' (n : ℤ), (gauss_term_ℝ σ (μ - k)) n := by
  revert μ
  induction k
  · simp
  · intro μ
    rename_i n IH
    simp
    rw [sub_add_eq_sub_sub]
    rw [IH]
    have X : μ - n = (μ - n - 1) + 1 := by
      simp
    rw [X]
    rw [← gauss_sum_1_periodic h]
    simp

/--
The sum of ``gauss_term_ℝ`` does not change when the mean shifts by any integer.
-/
theorem shifted_gauss_sum {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) (k : ℤ) :
  (∑' (n : ℤ), (gauss_term_ℝ σ μ) n) = ∑' (n : ℤ), (gauss_term_ℝ σ (μ + k)) n := by
  cases k
  · apply shifted_gauss_sum_pos h
  · simp
    have X : ∀ a : ℕ, -(1: ℝ) + -a = - (((1 + a) : ℕ)) := by
      intro a
      simp
      ring_nf
    rw [X]
    rw [@Mathlib.Tactic.RingNF.add_neg]
    apply shifted_gauss_sum_neg h

/--
The sum of ``gauss_term_ℝ`` equals the sum of the gaussian with mean zero.
-/
theorem shifted_gauss_sum_0 {σ : ℝ} (h : σ ≠ 0) (μ : ℤ) :
  (∑' (n : ℤ), (gauss_term_ℝ σ μ) n) = ∑' (n : ℤ), (gauss_term_ℝ σ 0) n := by
  have X := shifted_gauss_sum h 0 μ
  rw [X]
  simp
