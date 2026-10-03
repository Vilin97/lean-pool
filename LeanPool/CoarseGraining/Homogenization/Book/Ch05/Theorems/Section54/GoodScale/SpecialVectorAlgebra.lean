/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.Common

/-! # Special Vector Algebra -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace GoodScale

noncomputable section

/-!
# Special-vector scalar algebra for the good-scale lemma

This file contains only the real-variable algebra behind the manuscript choices
`p_e = \widehat\sigma_m^{-1/2} e` and `q_e = \widehat\sigma_m^{1/2} e`.
The law-facing good-scale theorem will use these identities after the
manuscript-facing scalar hypotheses are available.
-/

/-- With `σ = sqrt (b * c)` and `θ = b * c⁻¹`, the product `σ * c⁻¹`
is `sqrt θ`. -/
theorem sigma_mul_inv_star_eq_sqrt_theta {b c sigma theta : ℝ}
    (hb : 0 < b) (hc : 0 < c)
    (hsigma : sigma = Real.sqrt (b * c)) (htheta : theta = b * c⁻¹) :
    sigma * c⁻¹ = Real.sqrt theta := by
  have hsigma_pos : 0 < sigma := by
    rw [hsigma]
    exact Real.sqrt_pos_of_pos (mul_pos hb hc)
  have htheta_nonneg : 0 ≤ theta := by
    rw [htheta]
    exact mul_nonneg hb.le (inv_pos.mpr hc).le
  have hleft_nonneg : 0 ≤ sigma * c⁻¹ :=
    mul_nonneg hsigma_pos.le (inv_pos.mpr hc).le
  have hsq : (sigma * c⁻¹) * (sigma * c⁻¹) =
      Real.sqrt theta * Real.sqrt theta := by
    calc
      (sigma * c⁻¹) * (sigma * c⁻¹) =
          (Real.sqrt (b * c) * Real.sqrt (b * c)) * (c⁻¹ * c⁻¹) := by
        rw [hsigma]
        ring
      _ = (b * c) * (c⁻¹ * c⁻¹) := by
        rw [Real.mul_self_sqrt (mul_pos hb hc).le]
      _ = b * c⁻¹ := by
        have hc_ne : c ≠ 0 := ne_of_gt hc
        field_simp [hc_ne]
      _ = theta := by
        rw [htheta]
      _ = Real.sqrt theta * Real.sqrt theta :=
        (Real.mul_self_sqrt htheta_nonneg).symm
  exact (mul_self_inj_of_nonneg hleft_nonneg (Real.sqrt_nonneg theta)).1 hsq

/-- With `σ = sqrt (b * c)` and `θ = b * c⁻¹`, the product `b * σ⁻¹`
is `sqrt θ`. -/
theorem barSigma_mul_inv_sigma_eq_sqrt_theta {b c sigma theta : ℝ}
    (hb : 0 < b) (hc : 0 < c)
    (hsigma : sigma = Real.sqrt (b * c)) (htheta : theta = b * c⁻¹) :
    b * sigma⁻¹ = Real.sqrt theta := by
  have hsigma_pos : 0 < sigma := by
    rw [hsigma]
    exact Real.sqrt_pos_of_pos (mul_pos hb hc)
  have htheta_nonneg : 0 ≤ theta := by
    rw [htheta]
    exact mul_nonneg hb.le (inv_pos.mpr hc).le
  have hleft_nonneg : 0 ≤ b * sigma⁻¹ :=
    mul_nonneg hb.le (inv_pos.mpr hsigma_pos).le
  have hsq : (b * sigma⁻¹) * (b * sigma⁻¹) =
      Real.sqrt theta * Real.sqrt theta := by
    calc
      (b * sigma⁻¹) * (b * sigma⁻¹) =
          (b * b) * (Real.sqrt (b * c))⁻¹ * (Real.sqrt (b * c))⁻¹ := by
        rw [hsigma]
        ring
      _ = b * c⁻¹ := by
        have hprod_pos : 0 < b * c := mul_pos hb hc
        have hprod_ne : b * c ≠ 0 := ne_of_gt hprod_pos
        have hsqrt_ne : Real.sqrt (b * c) ≠ 0 :=
          ne_of_gt (Real.sqrt_pos_of_pos hprod_pos)
        field_simp [hsqrt_ne, hprod_ne]
        rw [Real.sq_sqrt hprod_pos.le]
      _ = theta := by
        rw [htheta]
      _ = Real.sqrt theta * Real.sqrt theta :=
        (Real.mul_self_sqrt htheta_nonneg).symm
  exact (mul_self_inj_of_nonneg hleft_nonneg (Real.sqrt_nonneg theta)).1 hsq

/-- The product of the negative and positive half-powers of a positive scalar. -/
theorem rpow_neg_half_mul_rpow_half_eq_one {sigma : ℝ} (hsigma_pos : 0 < sigma) :
    sigma ^ (-(1 / 2 : ℝ)) * sigma ^ (1 / 2 : ℝ) = 1 := by
  calc
    sigma ^ (-(1 / 2 : ℝ)) * sigma ^ (1 / 2 : ℝ) =
        sigma ^ ((-(1 / 2 : ℝ)) + (1 / 2 : ℝ)) := by
      rw [Real.rpow_add hsigma_pos (-(1 / 2 : ℝ)) (1 / 2 : ℝ)]
    _ = 1 := by norm_num [Real.rpow_zero]

/-- The square of the positive half-power of a positive scalar. -/
theorem rpow_half_sq_eq_self {sigma : ℝ} (hsigma_pos : 0 < sigma) :
    (sigma ^ (1 / 2 : ℝ)) ^ 2 = sigma := by
  calc
    (sigma ^ (1 / 2 : ℝ)) ^ 2 =
        (sigma ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
      exact (Real.rpow_natCast (sigma ^ (1 / 2 : ℝ)) 2).symm
    _ = sigma ^ ((1 / 2 : ℝ) * (2 : ℝ)) :=
      (Real.rpow_mul hsigma_pos.le (1 / 2 : ℝ) (2 : ℝ)).symm
    _ = sigma := by norm_num [Real.rpow_one]

/-- The square of the negative half-power of a positive scalar. -/
theorem rpow_neg_half_sq_eq_inv {sigma : ℝ} (hsigma_pos : 0 < sigma) :
    (sigma ^ (-(1 / 2 : ℝ))) ^ 2 = sigma⁻¹ := by
  calc
    (sigma ^ (-(1 / 2 : ℝ))) ^ 2 =
        (sigma ^ (-(1 / 2 : ℝ))) ^ (2 : ℝ) := by
      exact (Real.rpow_natCast (sigma ^ (-(1 / 2 : ℝ))) 2).symm
    _ = sigma ^ ((-(1 / 2 : ℝ)) * (2 : ℝ)) :=
      (Real.rpow_mul hsigma_pos.le (-(1 / 2 : ℝ)) (2 : ℝ)).symm
    _ = sigma ^ (-1 : ℝ) := by norm_num
    _ = (sigma ^ (1 : ℝ))⁻¹ := Real.rpow_neg hsigma_pos.le 1
    _ = sigma⁻¹ := by rw [Real.rpow_one]

/-- Coefficient identity for the scaled centered special vector `p_e`. -/
theorem rpow_half_mul_specialP_centering_coeff_eq {b c sigma theta : ℝ}
    (hb : 0 < b) (hc : 0 < c)
    (hsigma : sigma = Real.sqrt (b * c)) (htheta : theta = b * c⁻¹) :
    sigma ^ (1 / 2 : ℝ) *
        (c⁻¹ * sigma ^ (1 / 2 : ℝ) - sigma ^ (-(1 / 2 : ℝ))) =
      Real.sqrt theta - 1 := by
  have hsigma_pos : 0 < sigma := by
    rw [hsigma]
    exact Real.sqrt_pos_of_pos (mul_pos hb hc)
  have hdiv := sigma_mul_inv_star_eq_sqrt_theta hb hc hsigma htheta
  have hhalf_sq : (sigma ^ (1 / 2 : ℝ)) * (sigma ^ (1 / 2 : ℝ)) = sigma := by
    calc
      (sigma ^ (1 / 2 : ℝ)) * (sigma ^ (1 / 2 : ℝ)) =
          (sigma ^ (1 / 2 : ℝ)) ^ 2 := by ring
      _ = (sigma ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        exact (Real.rpow_natCast (sigma ^ (1 / 2 : ℝ)) 2).symm
      _ = sigma ^ ((1 / 2 : ℝ) * (2 : ℝ)) :=
        (Real.rpow_mul hsigma_pos.le (1 / 2 : ℝ) (2 : ℝ)).symm
      _ = sigma := by norm_num [Real.rpow_one]
  have hhalf_neg : sigma ^ (1 / 2 : ℝ) * sigma ^ (-(1 / 2 : ℝ)) = 1 := by
    calc
      sigma ^ (1 / 2 : ℝ) * sigma ^ (-(1 / 2 : ℝ)) =
          sigma ^ ((1 / 2 : ℝ) + (-(1 / 2 : ℝ))) := by
        rw [Real.rpow_add hsigma_pos (1 / 2 : ℝ) (-(1 / 2 : ℝ))]
      _ = 1 := by norm_num [Real.rpow_zero]
  calc
    sigma ^ (1 / 2 : ℝ) *
        (c⁻¹ * sigma ^ (1 / 2 : ℝ) - sigma ^ (-(1 / 2 : ℝ))) =
        c⁻¹ * (sigma ^ (1 / 2 : ℝ) * sigma ^ (1 / 2 : ℝ)) -
          sigma ^ (1 / 2 : ℝ) * sigma ^ (-(1 / 2 : ℝ)) := by ring
    _ = c⁻¹ * sigma - 1 := by rw [hhalf_sq, hhalf_neg]
    _ = Real.sqrt theta - 1 := by
      rw [← hdiv]
      ring

/-- Coefficient identity for the scaled centered special vector `q_e`. -/
theorem rpow_neg_half_mul_specialQ_centering_coeff_eq {b c sigma theta : ℝ}
    (hb : 0 < b) (hc : 0 < c)
    (hsigma : sigma = Real.sqrt (b * c)) (htheta : theta = b * c⁻¹) :
    sigma ^ (-(1 / 2 : ℝ)) *
        (sigma ^ (1 / 2 : ℝ) - b * sigma ^ (-(1 / 2 : ℝ))) =
      1 - Real.sqrt theta := by
  have hsigma_pos : 0 < sigma := by
    rw [hsigma]
    exact Real.sqrt_pos_of_pos (mul_pos hb hc)
  have hdiv := barSigma_mul_inv_sigma_eq_sqrt_theta hb hc hsigma htheta
  have hhalf_neg : sigma ^ (-(1 / 2 : ℝ)) * sigma ^ (1 / 2 : ℝ) = 1 := by
    calc
      sigma ^ (-(1 / 2 : ℝ)) * sigma ^ (1 / 2 : ℝ) =
          sigma ^ ((-(1 / 2 : ℝ)) + (1 / 2 : ℝ)) := by
        rw [Real.rpow_add hsigma_pos (-(1 / 2 : ℝ)) (1 / 2 : ℝ)]
      _ = 1 := by norm_num [Real.rpow_zero]
  have hneg_sq :
      sigma ^ (-(1 / 2 : ℝ)) * sigma ^ (-(1 / 2 : ℝ)) = sigma⁻¹ := by
    calc
      sigma ^ (-(1 / 2 : ℝ)) * sigma ^ (-(1 / 2 : ℝ)) =
          (sigma ^ (-(1 / 2 : ℝ))) ^ 2 := by ring
      _ = (sigma ^ (-(1 / 2 : ℝ))) ^ (2 : ℝ) := by
        exact (Real.rpow_natCast (sigma ^ (-(1 / 2 : ℝ))) 2).symm
      _ = sigma ^ ((-(1 / 2 : ℝ)) * (2 : ℝ)) :=
        (Real.rpow_mul hsigma_pos.le (-(1 / 2 : ℝ)) (2 : ℝ)).symm
      _ = sigma ^ (-1 : ℝ) := by norm_num
      _ = (sigma ^ (1 : ℝ))⁻¹ := Real.rpow_neg hsigma_pos.le 1
      _ = sigma⁻¹ := by rw [Real.rpow_one]
  calc
    sigma ^ (-(1 / 2 : ℝ)) *
        (sigma ^ (1 / 2 : ℝ) - b * sigma ^ (-(1 / 2 : ℝ))) =
        sigma ^ (-(1 / 2 : ℝ)) * sigma ^ (1 / 2 : ℝ) -
          b * (sigma ^ (-(1 / 2 : ℝ)) * sigma ^ (-(1 / 2 : ℝ))) := by ring
    _ = 1 - b * sigma⁻¹ := by rw [hhalf_neg, hneg_sq]
    _ = 1 - Real.sqrt theta := by
      rw [← hdiv]

/-- Squared scalar coefficient identity for the centered special vector
`p_e`. -/
theorem sigmaHat_mul_specialP_centering_coeff_sq_eq {b c sigma theta : ℝ}
    (hb : 0 < b) (hc : 0 < c)
    (hsigma : sigma = Real.sqrt (b * c)) (htheta : theta = b * c⁻¹) :
    sigma * (c⁻¹ * sigma ^ (1 / 2 : ℝ) - sigma ^ (-(1 / 2 : ℝ))) ^ 2 =
      (Real.sqrt theta - 1) ^ 2 := by
  have hsigma_pos : 0 < sigma := by
    rw [hsigma]
    exact Real.sqrt_pos_of_pos (mul_pos hb hc)
  have hdiv := sigma_mul_inv_star_eq_sqrt_theta hb hc hsigma htheta
  have hhalf : sigma ^ (1 / 2 : ℝ) =
      sigma * sigma ^ (-(1 / 2 : ℝ)) := by
    calc
      sigma ^ (1 / 2 : ℝ) = sigma ^ ((1 : ℝ) + (-(1 / 2 : ℝ))) := by
        norm_num
      _ = sigma ^ (1 : ℝ) * sigma ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_add hsigma_pos 1 (-(1 / 2 : ℝ))
      _ = sigma * sigma ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_one]
  have hneg_sq : (sigma ^ (-(1 / 2 : ℝ))) ^ 2 = sigma⁻¹ := by
    calc
      (sigma ^ (-(1 / 2 : ℝ))) ^ 2 =
          (sigma ^ (-(1 / 2 : ℝ))) ^ (2 : ℝ) := by
        exact (Real.rpow_natCast (sigma ^ (-(1 / 2 : ℝ))) 2).symm
      _ = sigma ^ ((-(1 / 2 : ℝ)) * (2 : ℝ)) :=
        (Real.rpow_mul hsigma_pos.le (-(1 / 2 : ℝ)) (2 : ℝ)).symm
      _ = sigma ^ (-1 : ℝ) := by
        norm_num
      _ = (sigma ^ (1 : ℝ))⁻¹ :=
        Real.rpow_neg hsigma_pos.le 1
      _ = sigma⁻¹ := by
        rw [Real.rpow_one]
  calc
    sigma * (c⁻¹ * sigma ^ (1 / 2 : ℝ) - sigma ^ (-(1 / 2 : ℝ))) ^ 2 =
        sigma * (sigma ^ (-(1 / 2 : ℝ)) * (Real.sqrt theta - 1)) ^ 2 := by
      rw [hhalf]
      rw [← hdiv]
      ring
    _ = (Real.sqrt theta - 1) ^ 2 := by
      rw [mul_pow, hneg_sq]
      field_simp [ne_of_gt hsigma_pos]

/-- Squared scalar coefficient identity for the centered special vector
`q_e`. -/
theorem inv_sigmaHat_mul_specialQ_centering_coeff_sq_eq {b c sigma theta : ℝ}
    (hb : 0 < b) (hc : 0 < c)
    (hsigma : sigma = Real.sqrt (b * c)) (htheta : theta = b * c⁻¹) :
    sigma⁻¹ * (sigma ^ (1 / 2 : ℝ) - b * sigma ^ (-(1 / 2 : ℝ))) ^ 2 =
      (Real.sqrt theta - 1) ^ 2 := by
  have hsigma_pos : 0 < sigma := by
    rw [hsigma]
    exact Real.sqrt_pos_of_pos (mul_pos hb hc)
  have hdiv := barSigma_mul_inv_sigma_eq_sqrt_theta hb hc hsigma htheta
  have hhalf : sigma ^ (1 / 2 : ℝ) =
      sigma * sigma ^ (-(1 / 2 : ℝ)) := by
    calc
      sigma ^ (1 / 2 : ℝ) = sigma ^ ((1 : ℝ) + (-(1 / 2 : ℝ))) := by
        norm_num
      _ = sigma ^ (1 : ℝ) * sigma ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_add hsigma_pos 1 (-(1 / 2 : ℝ))
      _ = sigma * sigma ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_one]
  have hpos_sq : (sigma ^ (1 / 2 : ℝ)) ^ 2 = sigma := by
    calc
      (sigma ^ (1 / 2 : ℝ)) ^ 2 =
          (sigma ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        exact (Real.rpow_natCast (sigma ^ (1 / 2 : ℝ)) 2).symm
      _ = sigma ^ ((1 / 2 : ℝ) * (2 : ℝ)) :=
        (Real.rpow_mul hsigma_pos.le (1 / 2 : ℝ) (2 : ℝ)).symm
      _ = sigma ^ (1 : ℝ) := by
        norm_num
      _ = sigma := by
        rw [Real.rpow_one]
  calc
    sigma⁻¹ * (sigma ^ (1 / 2 : ℝ) - b * sigma ^ (-(1 / 2 : ℝ))) ^ 2 =
        sigma⁻¹ * (sigma ^ (1 / 2 : ℝ) * (1 - Real.sqrt theta)) ^ 2 := by
      rw [hhalf]
      rw [← hdiv]
      field_simp [ne_of_gt hsigma_pos]
    _ = (Real.sqrt theta - 1) ^ 2 := by
      rw [mul_pow, hpos_sq]
      field_simp [ne_of_gt hsigma_pos]
      ring

end

end GoodScale
end Section54
end Ch05
end Book
end Homogenization
