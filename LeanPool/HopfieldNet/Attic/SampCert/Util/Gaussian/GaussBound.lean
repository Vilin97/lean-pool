/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.Util.Gaussian.DiscreteGaussian

/-!
# Gauss Bound

This file contains a proof that the sum of Gaussian terms with any mean (over the integers)
is bounded above by the sum of mean-zero Gaussian terms.

The argument transforms the series into a Fourier series, and eliminates the Fourier basis functions by
bounding them above by their absolute value. This has the effect of shifting the mean to zero; since
the sum of Fourier coefficients equals the sum of mean-zero Gaussian terms. The Poisson summation formula
justifies the transformation between series of ``gauss_term_ℝ ...`` and ``𝓕 (gauss_term_ℂ ...)``.
-/
#exit
noncomputable section

open Classical Nat BigOperators Real
open FourierTransform GaussianFourier Filter Asymptotics Complex
open ContinuousMap Function

attribute [local instance] Real.fact_zero_lt_one

/-
This is copied from MathLib; it was made private in the release of 4.10 with the suggestion that it would be
auto-generated in 4.11. It wasn't clear if it would become public again at that point.

See: https://github.com/leanprover-community/mathlib4/pull/15340
-/
theorem local_ext_iff {z w : ℂ} : z = w ↔ z.re = w.re ∧ z.im = w.im :=
  ⟨fun H => by simp [H], fun h => Complex.ext h.1 h.2⟩

/--
The sum of any gaussian function over ℤ is bounded above by the sum of the mean-zero gaussian function over ℤ.
-/
theorem sum_gauss_term_bound {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) :
  (∑' (n : ℤ), ((gauss_term_ℝ σ μ) n)) ≤ ∑' (n : ℤ), ((gauss_term_ℝ σ 0) n) := by
  have A : (∑' (n : ℤ), (gauss_term_ℝ σ μ) n) = (∑' (n : ℤ), (gauss_term_ℝ σ 0) ((- μ) + n)) := by
    apply tsum_congr
    intro b
    simp [gauss_term_ℝ]
    congr
    rw [neg_add_eq_sub]

  have B : (∑' (n : ℤ), (gauss_term_ℝ σ 0) (-μ + ↑n)) = |∑' (n : ℤ), (gauss_term_ℝ σ 0) (-μ + ↑n)| := by
    rw [_root_.abs_of_nonneg]
    apply tsum_nonneg
    intro i
    simp [gauss_term_ℝ, exp_nonneg]

  have C : |∑' (n : ℤ), (gauss_term_ℝ σ 0) (-μ + ↑n)| = Complex.abs (∑' (n : ℤ), (gauss_term_ℝ σ 0) (-μ + ↑n)) := by
    rw [← abs_ofReal]
    congr
    rw [ofReal_tsum]

  have D : Complex.abs (∑' (n : ℤ), (gauss_term_ℝ σ 0) (-μ + ↑n)) = Complex.abs (∑' (n : ℤ), (gauss_term_ℝ σ 0) (-μ + ↑n)) := by
    congr

  have E : Complex.abs (∑' (n : ℤ), (gauss_term_ℝ σ 0) (-μ + ↑n)) = Complex.abs (∑' (n : ℤ), 𝓕 (gauss_term_ℂ σ 0) n * (fourier n) (-μ : UnitAddCircle)) := by
    have X := poisson_gauss_term h (-μ)
    congr 1

  have F : (∑' (i : ℤ), Complex.abs (𝓕 (gauss_term_ℂ σ 0) i) * Complex.abs ((@fourier 1 i) (-μ))) = ∑' (i : ℤ), Complex.abs (𝓕 (gauss_term_ℂ σ 0) i) := by
    have X : ∀ i, ∀ x : AddCircle 1, ‖fourier i x‖ = 1 := fun i => fun x => abs_coe_circle _
    conv =>
      left
      right
      intro i
      right
      rw [← Complex.norm_eq_abs]
      rw [X i]
    simp

  have G : (∑' (i : ℤ), Complex.abs (𝓕 (gauss_term_ℂ σ 0) i)) = ∑' (i : ℤ), 𝓕 (gauss_term_ℂ σ 0) i := by
    rw [ofReal_tsum]
    congr
    ext a
    rw [fourier_gauss_term_correspondance h]
    unfold fourier_gauss_term
    simp [sq]
    congr 1
    · rw [Complex.abs_exp]
      simp [sq]
    · have A : 0 ≤ (2⁻¹ * ((↑σ)⁻¹ * (↑σ)⁻¹ * (↑π)⁻¹)) ^ (2 : ℝ)⁻¹ := by
        apply rpow_nonneg
        rw [mul_nonneg_iff]
        left
        simp [pi_pos]
        rw [← pow_two]
        rw [inv_pow]
        rw [inv_nonneg]
        exact sq_nonneg σ
      have H := Complex.abs_of_nonneg A
      have X : ofReal' ((2⁻¹ * ((↑σ)⁻¹ * (↑σ)⁻¹ * (↑π)⁻¹)) ^ (2 : ℝ)⁻¹) = (2⁻¹ * ((σ : ℂ)⁻¹ * (σ : ℂ)⁻¹ * (π : ℂ)⁻¹)) ^ (2 : ℂ)⁻¹ := by
        rw [← ofReal_ofNat]
        rw [← Complex.ofReal_inv]
        rw [← Complex.ofReal_inv]
        rw [← Complex.ofReal_inv]
        rw [← Complex.ofReal_mul]
        rw [← Complex.ofReal_mul]
        rw [← Complex.ofReal_mul]
        rw [local_ext_iff]
        constructor
        · rw [rpow_def]
          simp
        · simp
          rw [cpow_inv_two_im_eq_sqrt]
          · simp
            ring_nf
            simp
            rw [← Real.sqrt_zero]
            congr 1
            have P1 : |π| = π := by
              rw [_root_.abs_of_nonneg]
              rw [le_iff_lt_or_eq]
              left
              apply pi_pos
            rw [P1]
            rw [← mul_add]
            simp
            right
            ring_nf
          · simp
      rw [← X]
      rw [H]

  have H : (∑' (n : ℤ), 𝓕 (gauss_term_ℂ σ 0) n) = ∑' (n : ℤ), (gauss_term_ℂ σ 0) n := by
    have X := poisson_gauss_term h 0
    revert X
    conv =>
      left
      right
      right
      intro n
      right
      rw [QuotientAddGroup.mk_zero]
      rw [fourier_eval_zero n]
    intro X
    simp at X
    simp [X]

  have I : (∑' (n : ℤ), (gauss_term_ℂ σ 0) n) = ∑' (n : ℤ), (gauss_term_ℝ σ 0) n := by
    rw [ofReal_tsum]
    congr

  have J : Complex.abs (∑' (i : ℤ), 𝓕 (gauss_term_ℂ σ 0) i * (@fourier 1 i) (-μ)) ≤ ∑' (i : ℤ), Complex.abs (𝓕 (gauss_term_ℂ σ 0) i) * Complex.abs ((@fourier 1 i) (-μ)) := by
    rw [← Complex.norm_eq_abs]
    have S := summable_fourier_gauss_term' h μ
    rw [← summable_norm_iff] at S
    have Y := @norm_tsum_le_tsum_norm _ _ _ (fun (n : ℤ) => 𝓕 (gauss_term_ℂ σ 0) n * (@fourier 1 n) (-μ)) S
    simp only [smul_neg,  ofReal_one, div_one, Complex.norm_eq_abs, norm_mul] at Y
    apply Y

  rw [A, B, C, D, E]
  rw [F] at J
  apply le_trans J
  refine real_le_real.mp ?_
  rw [G, H, I]
  simp only [real_le_real, le_refl]
