/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.Util.Gaussian.DiscreteGaussian

/-!
# Discrete Gaussian Convergence

This file contains lemmas about the summability of the gaussian function.
-/

open Classical Nat Real

/--
The Gaussian function is summable over the nonnegative integers.
-/
@[simp]
theorem gauss_convergence_nat_pos {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) :
  Summable fun (n : ℕ) => (gauss_term_ℝ σ μ) n := by
  have A := @summable_int_iff_summable_nat_and_neg_add_zero ℝ _ _ _ _ (fun (n : ℤ) => (gauss_term_ℝ σ μ) n)
  replace A := A.1 (summable_gauss_term' h μ)
  cases A
  simpa only

/--
The Gaussian function is summable over the negative integers.
-/
@[simp]
theorem gauss_convergence_nat_neg {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) :
  Summable fun (n : ℕ) => (gauss_term_ℝ σ μ) ((-(n + 1)) : ℤ) := by
  have A := @summable_int_iff_summable_nat_and_neg_add_zero ℝ _ _ _ _ (fun (n : ℤ) => (gauss_term_ℝ σ μ) n)
  replace A := A.1 (summable_gauss_term' h μ)
  cases A
  simpa only
