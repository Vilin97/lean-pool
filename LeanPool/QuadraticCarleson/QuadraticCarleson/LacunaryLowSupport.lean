/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryMiddleRange
import LeanPool.QuadraticCarleson.QuadraticCarleson.DyadicAtomScales
import LeanPool.QuadraticCarleson.QuadraticCarleson.CalderonZygmundLevelAtoms
import LeanPool.QuadraticCarleson.QuadraticCarleson.LowKernelCalderonZygmund
import LeanPool.QuadraticCarleson.QuadraticCarleson.LowKernelLevelSummation
import LeanPool.QuadraticCarleson.QuadraticCarleson.SchwartzOperator

/-!
# Support vanishing in the lacunary low branch

This file proves the support observation used to discard atom scales above
the paper's middle range. With the project's concrete cutoff the resulting
constant is stronger than the unspecified source constant: a low kernel at
modulation `2^m` cannot connect an atom interval of length in scale `j` to a
point outside its fivefold dilation when `m + 2j > 2B`.
-/

open Function Set

namespace QuadraticCarleson
namespace LacunaryLowSupport


/-- A point outside the half-open fivefold interval is more than two atom
lengths from every point of the original half-open interval. -/
theorem two_mul_length_lt_distance
    {z R x y : ℝ} (hR : 0 < R)
    (hx : x ∉ centeredInterval z (5 * R))
    (hy : y ∈ centeredInterval z R) :
    2 * R < |x - y| := by
  rw [centeredInterval] at hx hy
  simp only [mem_Ico, not_and_or] at hx
  rcases hx with hx | hx
  · have hxy : x - y < 0 := by linarith [hy.1]
    rw [abs_of_neg hxy]
    linarith [hy.1]
  · have hxy : 0 < x - y := by linarith [hy.2]
    rw [abs_of_pos hxy]
    linarith [hy.2]

/-- The fivefold complement is contained in the complement of the closed
triple interval. Positivity is needed only because the fivefold interval is
represented half-open. -/
theorem not_mem_triple_of_not_mem_fivefold
    {z R x : ℝ} (hR : 0 < R)
    (hx : x ∉ centeredInterval z (5 * R)) :
    x ∉ tripleCenteredInterval z R := by
  intro hx3
  apply hx
  rw [centeredInterval]
  rw [tripleCenteredInterval, mem_Icc] at hx3
  constructor <;> linarith

/-- The cancellation-relevant Lipschitz estimate uses the first member
`|lambda|` of the paper's derivative minimum. -/
theorem paperLowCZKernel_sub_center_norm_le_abs_lam
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ)
    {z R x y : ℝ} (hR : 0 < R)
    (hx : x ∉ centeredInterval z (5 * R))
    (hy : y ∈ centeredInterval z R) :
    ‖paperLowCZKernel lam hlam B x y - paperLowCZKernel lam hlam B x z‖ ≤
      lowKernelDerivativeConstant * |lam| * |y - z| := by
  let F := paperLowOscillatoryKernel lam hlam B
  let a := x - y
  let b := x - z
  have hx3 : x ∉ tripleCenteredInterval z R :=
    not_mem_triple_of_not_mem_fivefold hR hx
  have hdiff : ∀ u ∈ uIcc a b, DifferentiableAt ℝ F u := by
    intro u hu
    have huabs : |x - y| / 4 ≤ |u| := by
      simpa [a, b] using
        quarter_distance_le_abs_of_mem_kernel_segment hR hx3 hy hu
    have hxy : 0 < |x - y| := by
      exact (two_mul_length_lt_distance hR hx hy).trans' (by positivity)
    have hu0 : u ≠ 0 := by
      intro heu
      subst u
      simp only [abs_zero] at huabs
      linarith
    exact (hasDerivAt_paperLowOscillatoryKernel hlam B hu0).differentiableAt
  have hderiv : ∀ u ∈ uIcc a b,
      ‖deriv F u‖ ≤ lowKernelDerivativeConstant * |lam| := by
    intro u hu
    have huabs : |x - y| / 4 ≤ |u| := by
      simpa [a, b] using
        quarter_distance_le_abs_of_mem_kernel_segment hR hx3 hy hu
    have hxy : 0 < |x - y| := by
      exact (two_mul_length_lt_distance hR hx hy).trans' (by positivity)
    have hu0 : u ≠ 0 := by
      intro heu
      subst u
      simp only [abs_zero] at huabs
      linarith
    rw [paperLowOscillatoryKernel_deriv hlam B hu0]
    exact paperLowOscillatoryKernelDerivative_norm_le_abs_lam hlam B hu0
  have hmv := (convex_uIcc a b).norm_image_sub_le_of_norm_deriv_le
    (s := uIcc a b) (x := b) (y := a) hdiff hderiv
    right_mem_uIcc left_mem_uIcc
  change ‖F a - F b‖ ≤ _
  calc
    ‖F a - F b‖ ≤ (lowKernelDerivativeConstant * |lam|) * ‖a - b‖ := hmv
    _ = lowKernelDerivativeConstant * |lam| * |y - z| := by
      simp only [a, b, Real.norm_eq_abs]
      rw [show x - y - (x - z) = -(y - z) by ring, abs_neg]

/-- Mean-zero cancellation therefore gives the paper's pointwise
`O(|lambda| R ||b_I||₁)` estimate outside `5I`. -/
theorem norm_setIntegral_paperLowCZKernel_le_abs_lam
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ)
    (f : ℝ → ℂ) {z R x : ℝ} (hR : 0 < R)
    (hx : x ∉ centeredInterval z (5 * R))
    (hf : MeasureTheory.IntegrableOn f (centeredInterval z R))
    (hKf : MeasureTheory.IntegrableOn
      (fun y ↦ paperLowCZKernel lam hlam B x y * f y)
      (centeredInterval z R))
    (hmean : ∫ y in centeredInterval z R, f y = 0) :
    ‖∫ y in centeredInterval z R, paperLowCZKernel lam hlam B x y * f y‖ ≤
      (lowKernelDerivativeConstant * |lam| * (R / 2)) *
        ∫ y in centeredInterval z R, ‖f y‖ := by
  rw [setIntegral_kernel_eq_sub_center
    (paperLowCZKernel lam hlam B) f x z R hf hKf hmean]
  apply norm_setIntegral_kernel_sub_center_le
    (paperLowCZKernel lam hlam B) f x z R
      (lowKernelDerivativeConstant * |lam| * (R / 2)) hf
  intro y hy
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg (f y))
  exact (paperLowCZKernel_sub_center_norm_le_abs_lam hlam B hR hx hy).trans
    (mul_le_mul_of_nonneg_left
      (abs_sub_center_le_of_mem_centeredInterval hy)
      (mul_nonneg lowKernelDerivativeConstant_nonneg (abs_nonneg lam)))

/-- Specialization to the actual magnitude-level atom and dyadic modulation
used in the very-small range. -/
theorem norm_setIntegral_paperLowCZKernel_levelAtom_le_dyadic
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    {k B : ℕ} (hAk : 0 ≤ A k) (m : ℤ)
    {z R x : ℝ} (hR : 0 < R)
    (hx : x ∉ centeredInterval z (5 * R)) :
    ‖∫ y in centeredInterval z R,
      paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
        CalderonZygmundLevelAtoms.levelAtom A f k z R y‖ ≤
      (lowKernelDerivativeConstant * dyadicModulation m * (R / 2)) *
        ∫ y in centeredInterval z R,
          ‖CalderonZygmundLevelAtoms.levelAtom A f k z R y‖ := by
  have hx3 : x ∉ tripleCenteredInterval z R :=
    not_mem_triple_of_not_mem_fivefold hR hx
  simpa only [abs_of_pos (dyadicModulation_pos m)] using
    norm_setIntegral_paperLowCZKernel_le_abs_lam
      (dyadicModulation_pos m).ne' B
      (CalderonZygmundLevelAtoms.levelAtom A f k z R) hR hx
      (CalderonZygmundLevelAtoms.integrable_levelAtom hf hAk z R).integrableOn
      (LowKernelLevelSummation.integrableOn_paperLowCZKernel_mul_levelAtom
        (dyadicModulation_pos m).ne' B hf hAk hR hx3)
      (LowKernelLevelSummation.setIntegral_levelAtom_eq_zero k z R)

/-- Quantitative consequence of the normalized support annulus. This is the
squared form of `R sqrt |lambda| < 2^(B-1)`. -/
theorem four_mul_abs_mul_length_sq_lt
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ)
    {z R x y : ℝ} (hR : 0 < R)
    (hx : x ∉ centeredInterval z (5 * R))
    (hy : y ∈ centeredInterval z R)
    (ht : x - y ∈ support (paperLowOscillatoryKernel lam hlam B)) :
    4 * |lam| * R ^ 2 < ((2 : ℝ) ^ B) ^ 2 := by
  have hs := (paperLowOscillatoryKernel_support_normalized lam hlam B ht).2
  have hd := two_mul_length_lt_distance hR hx hy
  have hsqrt : 0 < Real.sqrt |lam| := Real.sqrt_pos.2 (abs_pos.mpr hlam)
  have hlower : 2 * R * Real.sqrt |lam| < |x - y| * Real.sqrt |lam| :=
    mul_lt_mul_of_pos_right hd hsqrt
  have hmain : 2 * R * Real.sqrt |lam| < (2 : ℝ) ^ B := hlower.trans hs
  have hnonneg : 0 ≤ 2 * R * Real.sqrt |lam| := by positivity
  have hsquare := (sq_lt_sq₀ hnonneg (by positivity : 0 ≤ (2 : ℝ) ^ B)).2 hmain
  nlinarith [Real.sq_sqrt (abs_nonneg lam)]

/-- The too-large alternative in the paper's frozen-range error is genuinely
zero off the fivefold exceptional interval. -/
theorem paperLowCZKernel_eq_zero_of_tooLarge
    (B c : ℕ) (m j : ℤ)
    (hlarge : (c : ℤ) + 2 * (B : ℤ) < m + 2 * j)
    {z R x y : ℝ} (hR : 0 < R)
    (hscale : (2 : ℝ) ^ j ≤ R)
    (hx : x ∉ centeredInterval z (5 * R))
    (hy : y ∈ centeredInterval z R) :
    paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y = 0 := by
  by_contra hne
  have ht : x - y ∈ support
      (paperLowOscillatoryKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B) := by
    simpa only [paperLowCZKernel, mem_support] using hne
  have hs := four_mul_abs_mul_length_sq_lt
    (dyadicModulation_pos m).ne' B hR hx hy ht
  have hR2 : ((2 : ℝ) ^ j) ^ 2 ≤ R ^ 2 := by
    exact sq_le_sq₀ (zpow_nonneg (by norm_num) j) hR.le |>.2 hscale
  have hmpos : 0 < dyadicModulation m := dyadicModulation_pos m
  have hlower :
      4 * |dyadicModulation m| * ((2 : ℝ) ^ j) ^ 2 ≤
        4 * |dyadicModulation m| * R ^ 2 := by
    gcongr
  have hexp :
      4 * |dyadicModulation m| * ((2 : ℝ) ^ j) ^ 2 =
        (2 : ℝ) ^ (m + 2 * j + 2) := by
    rw [abs_of_pos hmpos, dyadicModulation, pow_two,
      show (4 : ℝ) = (2 : ℝ) ^ (2 : ℤ) by norm_num,
      ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  have hBexp : ((2 : ℝ) ^ B) ^ 2 = (2 : ℝ) ^ (2 * (B : ℤ)) := by
    rw [pow_two, ← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    omega
  have hpow : (2 : ℝ) ^ (2 * (B : ℤ)) < (2 : ℝ) ^ (m + 2 * j + 2) := by
    apply (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).2
    omega
  rw [hBexp] at hs
  rw [hexp] at hlower
  exact (not_lt_of_ge (hpow.le.trans hlower)) hs

/-- Scale-class form used directly for a Calderón--Zygmund atom. -/
theorem paperLowCZKernel_eq_zero_of_mem_scale_tooLarge
    {ι : Type*} {length : ι → ℝ} {I : ι}
    (B c : ℕ) (m j : ℤ)
    (hlarge : (c : ℤ) + 2 * (B : ℤ) < m + 2 * j)
    (hI : I ∈ dyadicAtomScaleClass length j)
    {z x y : ℝ} (hR : 0 < length I)
    (hx : x ∉ centeredInterval z (5 * length I))
    (hy : y ∈ centeredInterval z (length I)) :
    paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y = 0 := by
  exact paperLowCZKernel_eq_zero_of_tooLarge B c m j hlarge hR hI.1 hx hy

/-- Consequently the actual low-kernel action on one magnitude-level atom
vanishes. This is the operator-level support observation in the paper, not
merely a comparison of abstract supports. -/
theorem integral_paperLowCZKernel_mul_levelAtom_eq_zero_of_tooLarge
    {A : ℕ → ℝ} {f : ℝ → ℂ} (k : ℕ)
    (B c : ℕ) (m j : ℤ)
    (hlarge : (c : ℤ) + 2 * (B : ℤ) < m + 2 * j)
    {z R x : ℝ} (hR : 0 < R)
    (hscale : (2 : ℝ) ^ j ≤ R)
    (hx : x ∉ centeredInterval z (5 * R)) :
    (∫ y, paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
      CalderonZygmundLevelAtoms.levelAtom A f k z R y) = 0 := by
  have hzero (y : ℝ) :
      paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
        CalderonZygmundLevelAtoms.levelAtom A f k z R y = 0 := by
    by_cases hy : y ∈ centeredInterval z R
    · rw [paperLowCZKernel_eq_zero_of_tooLarge B c m j hlarge hR hscale hx hy,
        zero_mul]
    · rw [CalderonZygmundLevelAtoms.levelAtom_eq_zero_of_not_mem hy, mul_zero]
  simp [hzero]

end LacunaryLowSupport
end QuadraticCarleson
