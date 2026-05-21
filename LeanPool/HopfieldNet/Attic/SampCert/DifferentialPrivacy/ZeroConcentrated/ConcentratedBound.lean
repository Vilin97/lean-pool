/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.Util.Gaussian.DiscreteGaussian
import LeanPool.HopfieldNet.SampCert.Util.Gaussian.GaussBound
import LeanPool.HopfieldNet.SampCert.Util.Gaussian.GaussConvergence
import LeanPool.HopfieldNet.SampCert.Util.Gaussian.GaussPeriodicity
import LeanPool.HopfieldNet.SampCert.Util.Shift
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.RenyiDivergence
import LeanPool.HopfieldNet.SampCert.Samplers.GaussianGen.Basic

/-!
# Concentrated Bound

This file derives a cDP bound on the discrete Gaussian, and for the discrete Gaussian
sampler.
-/

open Real Nat

lemma sg_sum_pos' {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) (α : ℝ)  :
  0 < ((gauss_term_ℝ σ μ) x / ∑' (x : ℤ), (gauss_term_ℝ σ μ) x)^α := by
  apply rpow_pos_of_pos
  rw [div_pos_iff]
  left
  constructor
  · apply exp_pos
  · apply sum_gauss_term_pos h

lemma SG_Renyi_simplify {σ : ℝ} (h : σ ≠ 0) (μ ν : ℤ) (α : ℝ) :
  (fun (x : ℤ) => (gauss_term_ℝ σ μ) x / ∑' (x : ℤ), (gauss_term_ℝ σ μ) x) x ^ α *
      (fun (x : ℤ) => (gauss_term_ℝ σ ν) x / ∑' (x : ℤ), (gauss_term_ℝ σ ν) x) x ^ (1 - α)
    = (gauss_term_ℝ σ μ) x ^ α * (gauss_term_ℝ σ ν) x ^ (1 - α) / ∑' (x : ℤ), (gauss_term_ℝ σ ν) x := by
  have B : ∀ μ : ℤ, ∀ x : ℝ, 0 ≤ (gauss_term_ℝ σ μ) x := by
    intro μ x
    unfold gauss_term_ℝ
    apply exp_nonneg
  have C : ∀ μ : ℤ, 0 ≤ (∑' (x : ℤ), (gauss_term_ℝ σ μ) x)⁻¹ := by
    intro μ
    rw [inv_nonneg]
    apply le_of_lt
    apply sum_gauss_term_pos h
  have D : 0 < (∑' (x : ℤ), (gauss_term_ℝ σ 0) x)⁻¹ := by
    rw [inv_pos]
    conv =>
      right
      rw [← Int.cast_zero]
    apply sum_gauss_term_pos h
  simp
  conv =>
    left
    ring_nf
    rw [mul_rpow (B μ x) (C μ)]
    rw [mul_rpow (B ν x) (C ν)]
  rw [shifted_gauss_sum_0 h]
  rw [shifted_gauss_sum_0 h]
  conv =>
    left
    rw [mul_assoc]
    right
    rw [← mul_assoc]
    left
    rw [mul_comm]
  have X : ∀ x y : ℝ, x - y = x + (-y) := fun x y => rfl
  conv =>
    left
    rw [mul_assoc]
    right
    right
    rw [X]
    rw [rpow_add D]
    rw [mul_comm]
    rw [mul_assoc]
    simp
    right
    rw [← rpow_add D]
    simp
  simp
  conv =>
    left
    rw [← mul_assoc]
  rfl

/--
Real-valued Renyi Divergence.
-/
noncomputable def RenyiDivergence' (p q : T → ℝ) (α : ℝ) : ℝ :=
  (1 / (α - 1)) * Real.log (∑' x : T, (p x)^α  * (q x)^(1 - α))

/--
Upper bound on the Renyi Divergence between gaussians for any paramater `α > 1`.
-/
theorem Renyi_divergence_bound {σ : ℝ} (h : σ ≠ 0) (μ : ℤ) (α : ℝ) (h' : 1 < α) :
  RenyiDivergence' (fun (x : ℤ) => (gauss_term_ℝ σ μ) x / ∑' x : ℤ, (gauss_term_ℝ σ μ) x)
                  (fun (x : ℤ) => (gauss_term_ℝ σ (0 : ℤ)) x / ∑' x : ℤ, (gauss_term_ℝ σ (0 : ℤ)) x)
                  α ≤ α * (μ^2 / (2 * σ^2)) := by
  unfold RenyiDivergence'
  have A : 0 < 1 / (α - 1) := by
    simp [h']
  rw [← le_div_iff' A]
  refine Real.exp_le_exp.mp ?_
  have B : ∀ μ : ℤ, ∀ x : ℝ, 0 ≤ (gauss_term_ℝ σ μ) x := by
    intro μ x
    unfold gauss_term_ℝ
    apply exp_nonneg
  have B' : ∀ x : ℝ, 0 ≤ (gauss_term_ℝ σ 0) x := by
    unfold gauss_term_ℝ
    intro x
    apply exp_nonneg
  have C : ∀ μ : ℤ, 0 ≤ (∑' (x : ℤ), (gauss_term_ℝ σ μ) x)⁻¹ := by
    intro μ
    rw [inv_nonneg]
    apply le_of_lt
    apply sum_gauss_term_pos h
  have C' : 0 ≤ (∑' (x : ℤ), (gauss_term_ℝ σ 0) x)⁻¹ := by
    rw [inv_nonneg]
    apply le_of_lt
    conv =>
      right
      rw [← Int.cast_zero]
    apply sum_gauss_term_pos h
  have D : 0 < (∑' (x : ℤ), (gauss_term_ℝ σ 0) x)⁻¹ := by
    rw [inv_pos]
    conv =>
      right
      rw [← Int.cast_zero]
    apply sum_gauss_term_pos h
  rw [exp_log]
  · conv =>
      left
      ring_nf
      right
      intro x
      rw [mul_rpow (B μ x) (C μ)]
      rw [mul_rpow (B' x) C']
    -- First, I work on the denominator
    rw [shifted_gauss_sum_0 h]
    conv =>
      left
      right
      intro x
      rw [mul_assoc]
      right
      rw [← mul_assoc]
      left
      rw [mul_comm]
    have X : ∀ x y : ℝ, x - y = x + (-y) := fun x y => rfl
    conv =>
      left
      right
      intro x
      rw [mul_assoc]
      right
      right
      rw [X]
      rw [rpow_add D]
      rw [mul_comm]
      rw [mul_assoc]
      simp
      right
      rw [← rpow_add D]
      simp
    simp
    conv =>
      left
      right
      intro x
      rw [← mul_assoc]
    rw [tsum_mul_right]
    rw [← division_def]
    -- Now, I work on the numerator
    conv =>
      left
      left
      unfold gauss_term_ℝ
      right
      intro x
      rw [← Real.exp_mul]
      rw [← Real.exp_mul]
      rw [← exp_add]
      rw [← mul_div_right_comm]
      rw [← mul_div_right_comm]
      rw [div_add_div_same]
      rw [mul_sub_left_distrib]
      right
      left
      simp
      ring_nf
    have E : ∀ x : ℤ, x * μ * α * 2 + (-x ^ 2 - μ ^ 2 * α) = - (x - α * μ)^2 + α * (α -1) * μ^2 := by
      intro x
      ring_nf
    conv =>
      left
      left
      right
      intro x
      rw [E]
      rw [_root_.add_div]
      rw [exp_add]
    rw [tsum_mul_right]
    rw [mul_comm]
    rw [mul_div_assoc]
    have F := sum_gauss_term_bound h (α * μ)
    unfold gauss_term_ℝ
    unfold gauss_term_ℝ at F
    --clear A B B' C C' D X E
    have X : 0 < ∑' (x : ℤ), rexp (-(↑x - 0) ^ 2 / (2 * σ^2)) := by
      conv =>
        right
        rw [← Int.cast_zero]
      apply sum_gauss_term_pos h
    have G := @div_le_one ℝ _ (∑' (x : ℤ), rexp (-(↑x - α * ↑μ) ^ 2 / (2 * σ^2))) (∑' (x : ℤ), rexp (-(↑x - 0) ^ 2 / (2 * σ^2)))
    replace G := (G X).2 F
    clear X F
    conv =>
      right
      rw [← mul_rotate]
      right
      left
      rw [mul_comm]
    conv =>
      right
      rw [← mul_div_assoc]
    apply mul_le_of_le_one_right _ G
    apply exp_nonneg
  · apply tsum_pos _ _ 0 _
    · simp -- some of this proof is similar to the one just above and needs to be hoisted
      conv =>
        right
        intro x
        rw [division_def]
        rw [division_def]
        rw [mul_rpow (B μ x) (C μ)]
        rw [mul_rpow (B' x) C']
      conv =>
        right
        intro x
        rw [mul_assoc]
        right
        rw [← mul_assoc]
        left
        rw [mul_comm]
      conv =>
        right
        intro x
        ring_nf
      apply Summable.mul_right
      apply Summable.mul_right
      unfold gauss_term_ℝ
      conv =>
        right
        intro x
        rw [← Real.exp_mul]
        rw [← Real.exp_mul]
        rw [← exp_add]
        rw [← mul_div_right_comm]
        rw [← mul_div_right_comm]
        rw [div_add_div_same]
        rw [mul_sub_left_distrib]
        rw [sub_zero]
        rw [mul_one]
        right
        left
        ring_nf
      have X : ∀ x : ℤ, x * ↑μ * α * 2 + (-x ^ 2 - μ ^ 2 * α) = -(x - α * μ)^2 + α * (α -1) * μ^2 := by
        intro x
        ring_nf
      conv =>
        right
        intro x
        rw [X]
        rw [← div_add_div_same]
        rw [exp_add]
      apply Summable.mul_right
      apply summable_gauss_term' h
    · intro i
      apply le_of_lt
      rw [mul_pos_iff]
      left
      constructor
      · apply sg_sum_pos' h
      · apply sg_sum_pos' h
    · rw [mul_pos_iff]
      left
      constructor
      · apply sg_sum_pos' h
      · apply sg_sum_pos' h

lemma  sg_mul_simplify (ss : ℝ) (x μ ν : ℤ) :
  rexp (-(x - μ) ^ 2 / (2 * ss)) ^ α * rexp (-(x - ν) ^ 2 / (2 * ss)) ^ (1 - α)
  = rexp (-((x - μ) ^ 2 * α + (x - ν) ^ 2 * (1 - α)) / (2 * ss)) := by
  rw [← Real.exp_mul]
  rw [← Real.exp_mul]
  rw [← exp_add]
  rw [← mul_div_right_comm]
  rw [← mul_div_right_comm]
  rw [div_add_div_same]
  rw [← neg_mul_eq_neg_mul]
  rw [← neg_mul_eq_neg_mul]
  rw [← neg_add]

lemma SG_Renyi_shift {σ : ℝ} (h : σ ≠ 0) (α : ℝ) (μ ν τ : ℤ) :
  RenyiDivergence' (fun (x : ℤ) => (gauss_term_ℝ σ μ) x / ∑' x : ℤ, (gauss_term_ℝ σ μ) x) (fun (x : ℤ) => (gauss_term_ℝ σ ν) x / ∑' x : ℤ, (gauss_term_ℝ σ ν) x) α
    = RenyiDivergence' (fun (x : ℤ) => (gauss_term_ℝ σ ((μ + τ) : ℤ)) x / ∑' x : ℤ, (gauss_term_ℝ σ ((μ + τ) : ℤ)) x) (fun (x : ℤ) => (gauss_term_ℝ σ ((ν + τ) : ℤ)) x / ∑' x : ℤ, (gauss_term_ℝ σ ((ν + τ) : ℤ)) x) α := by
  unfold RenyiDivergence'
  congr 2
  conv =>
    left
    right
    intro x
    rw [SG_Renyi_simplify h]
    rw [division_def]
  conv =>
    right
    right
    intro x
    rw [SG_Renyi_simplify h]
    rw [division_def]
  rw [tsum_mul_right]
  rw [tsum_mul_right]
  rw [shifted_gauss_sum_0 h]
  rw [shifted_gauss_sum_0 h]
  congr 1

  -- re-indexing

  have A : ∀ μ : ℤ, ∀ x : ℤ, (gauss_term_ℝ σ ((μ + τ) : ℤ)) x =  (gauss_term_ℝ σ μ) (x - τ) := by
    intro x μ
    simp [gauss_term_ℝ]
    ring_nf
  conv =>
    right
    right
    intro x
    rw [A]
    rw [A]
  clear A

  -- Now for the crux of the proof

  unfold gauss_term_ℝ
  conv =>
    left
    right
    intro x
    rw [sg_mul_simplify]
  conv =>
    right
    right
    intro x
    rw [sub_sub]
    rw [sub_sub]
    rw [← Int.cast_add]
    rw [← Int.cast_add]
    rw [sg_mul_simplify]

  rw [← tsum_shift _ (-τ)]
  · apply tsum_congr
    intro b
    congr 6
    · simp
      ring_nf
    · simp
      ring_nf
  · intro β
    conv =>
      right
      intro x
      rw [Int.cast_add]
      rw [add_sub_assoc]
      rw [add_sub_assoc]
    have X : ∀ x : ℤ, ↑x * ↑β * 2 - ↑x * ↑μ * α * 2 + (↑x * α * ↑ν * 2 - ↑x * ↑ν * 2) + (↑x ^ 2 - ↑β * ↑μ * α * 2) +
                (↑β * α * ↑ν * 2 - ↑β * ↑ν * 2) +
              ↑β ^ 2 +
            (↑μ ^ 2 * α - α * ↑ν ^ 2) +
          ↑ν ^ 2 =
          (↑x ^ 2 - 2 * x * (-↑β + ↑μ * α - α * ↑ν + ↑ν)) + (- ↑β * ↑μ * α * 2 + ↑β * α * ↑ν * 2 - ↑β * ↑ν * 2 + ↑β ^ 2 + ↑μ ^ 2 * α - α * ↑ν ^ 2 + ↑ν ^ 2) := by
      intro x
      ring_nf
    conv =>
      right
      intro x
      right
      left
      right
      ring_nf
      rw [X]
    clear X
    have X : (- ↑β * ↑μ * α * 2 + ↑β * α * ↑ν * 2 - ↑β * ↑ν * 2 + ↑β ^ 2 + ↑μ ^ 2 * α - α * ↑ν ^ 2 + ↑ν ^ 2)
      = (-↑β + ↑μ * α - α * ↑ν + ↑ν)^2 + (- ↑μ * α * ↑ν * 2 + ↑μ * α ^ 2 * ↑ν * 2 -
          ↑μ ^ 2 * α ^ 2 + α * ↑ν ^ 2 - α ^ 2 * ↑ν ^ 2 + α * ↑μ ^ 2) := by
      ring_nf
    conv =>
      right
      intro x
      rw [X]
      rw [← add_assoc]
    clear X
    have X : ∀ x : ℤ, (x - (-↑β + ↑μ * α - α * ↑ν + ↑ν))^2 = ↑x ^ 2 - 2 * ↑x * (-↑β + ↑μ * α - α * ↑ν + ↑ν) + (-↑β + ↑μ * α - α * ↑ν + ↑ν) ^ 2 := by
      intro x
      ring_nf
    conv =>
      right
      intro x
      rw [← X]
      rw [neg_add]
      rw [← div_add_div_same]
      rw [exp_add]
    clear X
    apply Summable.mul_right
    apply summable_gauss_term' h

/--
Upper bound on the Renyi Divergence between discrete gaussians for any paramater `α > 1`.
-/
theorem Renyi_divergence_bound_pre {σ α : ℝ} (h : σ ≠ 0) (h' : 1 < α) (μ ν : ℤ)   :
  RenyiDivergence' (fun (x : ℤ) => discrete_gaussian σ μ x)
                  (fun (x : ℤ) => discrete_gaussian σ ν x)
                  α ≤ α * (((μ - ν) : ℤ)^2 / (2 * σ^2)) := by
  unfold discrete_gaussian
  rw [SG_Renyi_shift h α μ ν (-ν)]
  rw [add_right_neg]
  apply  Renyi_divergence_bound h (μ + -ν) α h'

/--
Summand of Renyi divergence between discrete Gaussians is nonnegative.
-/
theorem Renyi_sum_SG_nonneg {σ α : ℝ} (h : σ ≠ 0) (μ ν n : ℤ) :
  0 ≤ discrete_gaussian σ μ n ^ α * discrete_gaussian σ ν n ^ (1 - α) := by
  have A := discrete_gaussian_nonneg h μ n
  have B := discrete_gaussian_nonneg h ν n
  rw [mul_nonneg_iff]
  left
  constructor
  · apply Real.rpow_nonneg A
  · apply Real.rpow_nonneg B

/--
Sum in Renyi divergence between discrete Gaussians is well-defined.
-/
theorem Renyi_Gauss_summable {σ : ℝ} (h : σ ≠ 0) (μ ν : ℤ) (α : ℝ) :
  Summable fun (x : ℤ) => discrete_gaussian σ μ x ^ α * discrete_gaussian σ ν x ^ (1 - α) := by
  simp [discrete_gaussian]
  have B : ∀ μ : ℤ, ∀ x : ℝ, 0 ≤ (gauss_term_ℝ σ μ) x := by
    intro μ x
    unfold gauss_term_ℝ
    apply exp_nonneg
  have C : ∀ μ : ℤ, 0 ≤ (∑' (x : ℤ), (gauss_term_ℝ σ μ) x)⁻¹ := by
    intro μ
    rw [inv_nonneg]
    apply le_of_lt
    apply sum_gauss_term_pos h
  conv =>
    right
    intro x
    rw [division_def]
    rw [division_def]
    rw [mul_rpow (B μ x) (C μ)]
    rw [mul_rpow (B ν x) (C ν)]
  conv =>
    right
    intro x
    rw [mul_assoc]
    right
    rw [← mul_assoc]
    left
    rw [mul_comm]
  conv =>
    right
    intro x
    ring_nf
  apply Summable.mul_right
  apply Summable.mul_right
  unfold gauss_term_ℝ
  conv =>
    right
    intro x
    rw [← Real.exp_mul]
    rw [← Real.exp_mul]
    rw [← exp_add]
    rw [← mul_div_right_comm]
    rw [← mul_div_right_comm]
    rw [div_add_div_same]
    rw [mul_sub_left_distrib]
    rw [mul_one]
    right
    left
    ring_nf

  have X : ∀ x : ℤ,
    ↑x * ↑μ * α * 2 - ↑x * α * ↑ν * 2 + ↑x * ↑ν * 2 + (-↑x ^ 2 - ↑μ ^ 2 * α) + (α * ↑ν ^ 2 - ↑ν ^ 2)
           = - ((↑x ^ 2 - 2 * x * (↑μ * α - α * ↑ν + ↑ν)) + (↑μ ^ 2 * α - α * ↑ν ^ 2 + ↑ν ^ 2)) := by
        intro x
        ring_nf
  conv =>
    right
    intro x
    rw [X]
  clear X

  have X : (↑μ ^ 2 * α - α * ↑ν ^ 2 + ↑ν ^ 2)
    = (↑μ * α - α * ↑ν + ↑ν)^2 + (- ↑μ * α * ↑ν * 2 + ↑μ * α ^ 2 * ↑ν * 2 -
        ↑μ ^ 2 * α ^ 2 + α * ↑ν ^ 2 - α ^ 2 * ↑ν ^ 2 + α * ↑μ ^ 2) := by
    ring_nf
  conv =>
    right
    intro x
    rw [X]
    rw [← add_assoc]
  clear X

  have X : ∀ x : ℤ, (x - (↑μ * α - α * ↑ν + ↑ν))^2 = ↑x ^ 2 - 2 * ↑x * (↑μ * α - α * ↑ν + ↑ν) + (↑μ * α - α * ↑ν + ↑ν) ^ 2 := by
    intro x
    ring_nf
  conv =>
    right
    intro x
    rw [← X]
    rw [neg_add]
    rw [← div_add_div_same]
    rw [exp_add]
  clear X
  apply Summable.mul_right
  apply summable_gauss_term' h


/--
Upper bound on Renyi divergence between discrete Gaussians.
-/
theorem Renyi_Gauss_divergence_bound' {σ α : ℝ} (h : σ ≠ 0) (h' : 1 < α) (μ ν : ℤ)   :
  RenyiDivergence (discrete_gaussian_pmf h μ)
                  (discrete_gaussian_pmf h ν)
                  α ≤ (ENNReal.ofReal α) * (ENNReal.ofReal ((((μ - ν) : ℤ)^2 : ℝ) / (2 * σ^2))) := by
  have A : RenyiDivergence (discrete_gaussian_pmf h μ) (discrete_gaussian_pmf h ν) α =
           ENNReal.ofReal (RenyiDivergence' (fun (x : ℤ) => discrete_gaussian σ μ x) (fun (x : ℤ) => discrete_gaussian σ ν x) α) := by
    unfold RenyiDivergence
    unfold RenyiDivergence_def
    unfold RenyiDivergence'
    simp
    unfold discrete_gaussian_pmf

    have Hdg_pos (x : ℤ) (w : ℝ) : OfNat.ofNat 0 < discrete_gaussian σ w x.cast := by
      exact discrete_gaussian_pos h w x
    have Hdg_pow_pos (x : ℤ) w : OfNat.ofNat 0 ≤ discrete_gaussian σ w x.cast ^ α := by
      apply rpow_nonneg
      exact discrete_gaussian_nonneg h w x

    conv =>
      lhs
      arg 1
      arg 2
      arg 1
      arg 1
      intro x
      simp [DFunLike.coe]
      rw [ENNReal.ofReal_rpow_of_pos (Hdg_pos x μ.cast)]
      rw [ENNReal.ofReal_rpow_of_pos (Hdg_pos x ν.cast)]
      rw [<- ENNReal.ofReal_mul (Hdg_pow_pos x μ.cast)]
    rw [<- ENNReal.ofEReal_ofReal_toENNReal]
    simp
    congr
    cases (Classical.em (0 = ∑' (x : ℤ), discrete_gaussian σ μ.cast x.cast ^ α * discrete_gaussian σ ν.cast x.cast ^ (1 - α)))
    · rename_i Hzero
      rw [<- Hzero]
      simp
      rw [<- ENNReal.ofReal_tsum_of_nonneg]
      · rw [<- Hzero]
        exfalso
        symm at Hzero
        have Hzero' : (ENNReal.ofReal (∑' (x : ℤ), discrete_gaussian σ ↑μ ↑x ^ α * discrete_gaussian σ ↑ν ↑x ^ (1 - α)) = 0) := by
          simp [Hzero]
        rw [ENNReal.ofReal_tsum_of_nonneg ?G1 ?G2] at Hzero'
        case G1 => exact fun n => Renyi_sum_SG_nonneg h μ ν n
        case G2 => exact Renyi_Gauss_summable h μ ν α
        apply ENNReal.tsum_eq_zero.mp at Hzero'
        have Hzero'' := Hzero' (0 : ℤ)
        simp at Hzero''
        have C : (0 < discrete_gaussian σ (↑μ) 0 ^ α * discrete_gaussian σ (↑ν) 0 ^ (1 - α)) := by
          apply Real.mul_pos
          · apply Real.rpow_pos_of_pos
            have A := discrete_gaussian_pos h μ (0 : ℤ)
            simp at A
            apply A
          · apply Real.rpow_pos_of_pos
            have A := discrete_gaussian_pos h ν (0 : ℤ)
            simp at A
            apply A
        linarith
      · exact fun n => Renyi_sum_SG_nonneg h μ ν n
      · exact Renyi_Gauss_summable h μ ν α
    · rename_i Hnz
      rw [<- ENNReal.elog_ENNReal_ofReal_of_pos]
      · rw [ENNReal.ofReal_tsum_of_nonneg ?Hnn]
        · exact Renyi_Gauss_summable h μ ν α
        · intro n
          exact Renyi_sum_SG_nonneg h μ ν n
      apply lt_of_le_of_ne
      · apply tsum_nonneg
        intro i
        exact Renyi_sum_SG_nonneg h μ ν i
      · apply Hnz
  rw [A]
  rw [<- ENNReal.ofReal_mul]
  apply ENNReal.ofReal_le_ofReal
  apply Renyi_divergence_bound_pre h h' μ ν
  linarith

namespace SLang

/--
Upper bound on Renyi divergence between outputs of the ``SLang`` discrete Gaussian sampler.
-/
theorem discrete_GaussianGenSample_ZeroConcentrated {α : ℝ} (h : 1 < α) (num : PNat) (den : PNat) (μ ν : ℤ) :
  RenyiDivergence ((DiscreteGaussianGenPMF num den μ)) (DiscreteGaussianGenPMF num den ν) α ≤
  (ENNReal.ofReal α) * (ENNReal.ofReal (((μ - ν) : ℤ)^2 : ℝ) / (((2 : ENNReal) * ((num : ENNReal) / (den : ENNReal))^2 : ENNReal))) := by
  have A : (num : ℝ) / (den : ℝ) ≠ 0 := by
    simp only [ne_eq, div_eq_zero_iff, cast_eq_zero, PNat.ne_zero, or_self, not_false_eq_true]
    cases num
    cases den
    simp
    apply And.intro <;> linarith
  have Hpmf (w : ℤ) : (discrete_gaussian_pmf A w = DiscreteGaussianGenPMF num den w) := by
    simp [discrete_gaussian_pmf]
    simp [DiscreteGaussianGenPMF]
    congr
    apply funext
    intro z
    rw [DiscreteGaussianGenSample_apply]
    congr
  conv =>
    left
    congr
    . rw [<- Hpmf]
    . rw [<- Hpmf]
    . skip
  clear Hpmf
  apply le_trans
  · apply (Renyi_Gauss_divergence_bound')
    apply h
  · apply Eq.le
    congr
    simp [NNReal.ofPNat]
    cases num
    cases den
    simp
    rename_i a Ha b Hb
    rw [division_def]
    rw [ENNReal.ofReal_mul ?G1]
    case G1 => exact sq_nonneg (μ.cast - ν.cast)
    rw [division_def]
    congr
    rw [ENNReal.ofReal_inv_of_pos ?G1]
    case G1 =>
      apply Real.mul_pos
      · simp
      apply Real.mul_pos
      · apply sq_pos_of_pos
        apply NNReal.coe_pos.mpr
        exact cast_pos.mpr Ha
      · apply inv_pos_of_pos
        apply sq_pos_of_pos
        apply NNReal.coe_pos.mpr
        exact cast_pos.mpr Hb
    congr
    rw [ENNReal.ofReal_mul ?G1]
    case G1 => simp
    simp
    congr
    rw [division_def]
    rw [← NNReal.coe_pow]
    repeat rw [mul_pow]
    rw [ENNReal.ofReal_mul ?G1]
    case G1 => exact NNReal.zero_le_coe
    congr
    · simp
      rw [← ENNReal.coe_pow]
      rw [← NNReal.coe_pow]
      rw [ENNReal.ofReal_coe_nnreal]
    · rw [← ENNReal.inv_pow]
      rw [← ENNReal.coe_pow]
      rw [← NNReal.coe_pow]
      rw [<- ENNReal.ofReal_coe_nnreal]
      rw [ENNReal.ofReal_inv_of_pos]
      apply NNReal.coe_pos.mpr
      apply pow_two_pos_of_ne_zero
      intro
      simp_all

end SLang
