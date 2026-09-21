/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.LowKernelDerivative
import LeanPool.QuadraticCarleson.QuadraticCarleson.CalderonZygmundBadPart
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Calderón--Zygmund regularity of the low oscillatory kernel

This file turns the derivative estimate for the paper's low kernel into the
kernel-difference estimate used on a mean-zero Calderón--Zygmund atom.  The
mean-value theorem is applied on the segment joining `x - y` and `x - z`.
When `y` belongs to the interval centered at `z` and `x` is outside its
triple, every point of that segment stays quantitatively away from zero.
-/

open MeasureTheory Set

namespace QuadraticCarleson


/-- The translation kernel associated with the low oscillatory convolution
kernel. -/
noncomputable def paperLowCZKernel
    (lam : ℝ) (hlam : lam ≠ 0) (B : ℕ) (x y : ℝ) : ℂ :=
  paperLowOscillatoryKernel lam hlam B (x - y)

/-- The interval point and its center are at most twice as far apart from an
observation point outside the triple interval. -/
theorem distance_interval_point_le_two_center_distance
    {z R x y : ℝ} (hR : 0 < R)
    (hx : x ∉ tripleCenteredInterval z R)
    (hy : y ∈ centeredInterval z R) :
    |x - y| ≤ 2 * |x - z| := by
  have hyz : |y - z| ≤ R / 2 := abs_sub_center_le_of_mem_centeredInterval hy
  have hxz : 3 * R / 2 < |x - z| :=
    not_mem_tripleCenteredInterval_abs hx
  have htri : |x - y| ≤ |x - z| + |z - y| := by
    calc
      |x - y| = |(x - z) + (z - y)| := by ring_nf
      _ ≤ |x - z| + |z - y| := abs_add_le _ _
  rw [abs_sub_comm z y] at htri
  linarith

/-- Subtracting a point of the segment between `x-y` and `x-z` from `x`
produces a point of the segment between `y` and `z`. -/
theorem sub_mem_uIcc_of_mem_sub_uIcc {x y z u : ℝ}
    (hu : u ∈ uIcc (x - y) (x - z)) :
    x - u ∈ uIcc y z := by
  rw [mem_uIcc] at hu ⊢
  rcases hu with hu | hu
  · right
    constructor <;> linarith
  · left
    constructor <;> linarith

/-- Every point of the mean-value segment remains at least one quarter of
`|x-y|` away from zero. -/
theorem quarter_distance_le_abs_of_mem_kernel_segment
    {z R x y u : ℝ} (hR : 0 < R)
    (hx : x ∉ tripleCenteredInterval z R)
    (hy : y ∈ centeredInterval z R)
    (hu : u ∈ uIcc (x - y) (x - z)) :
    |x - y| / 4 ≤ |u| := by
  have hvseg : x - u ∈ uIcc y z := sub_mem_uIcc_of_mem_sub_uIcc hu
  have hvz : |(x - u) - z| ≤ |y - z| := by
    rw [abs_sub_comm (x - u) z]
    simpa [abs_sub_comm z y] using abs_sub_right_of_mem_uIcc hvseg
  have hvbound : |(x - u) - z| ≤ R / 2 :=
    hvz.trans (abs_sub_center_le_of_mem_centeredInterval hy)
  have hhalf : |x - z| / 2 ≤ |x - (x - u)| :=
    by
      have hxz : 3 * R / 2 < |x - z| := not_mem_tripleCenteredInterval_abs hx
      have htri : |x - z| ≤ |x - (x - u)| + |(x - u) - z| := by
        calc
          |x - z| = |(x - (x - u)) + ((x - u) - z)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      linarith
  have hcompare := distance_interval_point_le_two_center_distance hR hx hy
  have hcancel : x - (x - u) = u := by ring
  rw [hcancel] at hhalf
  linarith

/-- The explicit Calderón--Zygmund regularity constant of the low kernel at
height `B`. -/
noncomputable def lowKernelCZConstant (B : ℕ) : ℝ :=
  16 * lowKernelDerivativeConstant * (2 : ℝ) ^ (2 * B)

theorem lowKernelCZConstant_nonneg (B : ℕ) :
    0 ≤ lowKernelCZConstant B := by
  unfold lowKernelCZConstant
  exact mul_nonneg
    (mul_nonneg (by norm_num) lowKernelDerivativeConstant_nonneg) (by positivity)

/-- The paper's low convolution kernel satisfies the precise Lipschitz
kernel-difference estimate required by the cancellative bad-part lemma. -/
theorem paperLowCZKernel_sub_center_norm_le
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ)
    {z R x y : ℝ} (hR : 0 < R)
    (hx : x ∉ tripleCenteredInterval z R)
    (hy : y ∈ centeredInterval z R) :
    ‖paperLowCZKernel lam hlam B x y -
        paperLowCZKernel lam hlam B x z‖ ≤
      lowKernelCZConstant B * |y - z| / |x - y| ^ 2 := by
  let F := paperLowOscillatoryKernel lam hlam B
  let a := x - y
  let b := x - z
  have hxy : 0 < |x - y| := by
    have hhalf := half_center_distance_le_distance hR.le hx hy
    have hxz := not_mem_tripleCenteredInterval_abs hx
    linarith
  have hdiff : ∀ u ∈ uIcc a b, DifferentiableAt ℝ F u := by
    intro u hu
    have huabs : |x - y| / 4 ≤ |u| := by
      simpa [a, b] using
        quarter_distance_le_abs_of_mem_kernel_segment hR hx hy hu
    have hu0 : u ≠ 0 := by
      intro heu
      subst u
      simp only [abs_zero] at huabs
      linarith
    exact (hasDerivAt_paperLowOscillatoryKernel hlam B hu0).differentiableAt
  have hderiv : ∀ u ∈ uIcc a b,
      ‖deriv F u‖ ≤
        16 * lowKernelDerivativeConstant * (2 : ℝ) ^ (2 * B) /
          |x - y| ^ 2 := by
    intro u hu
    have huabs : |x - y| / 4 ≤ |u| := by
      simpa [a, b] using
        quarter_distance_le_abs_of_mem_kernel_segment hR hx hy hu
    have hu0 : u ≠ 0 := by
      intro heu
      subst u
      simp only [abs_zero] at huabs
      linarith
    have hbase := paperLowOscillatoryKernel_deriv_norm_le_min hlam B hu0
    have hdecay : ‖deriv F u‖ ≤
        lowKernelDerivativeConstant *
          ((2 : ℝ) ^ (2 * B) / |u| ^ 2) := by
      exact hbase.trans (mul_le_mul_of_nonneg_left (min_le_right _ _)
        lowKernelDerivativeConstant_nonneg)
    calc
      ‖deriv F u‖ ≤ lowKernelDerivativeConstant *
          ((2 : ℝ) ^ (2 * B) / |u| ^ 2) := hdecay
      _ ≤ lowKernelDerivativeConstant *
          ((2 : ℝ) ^ (2 * B) / (|x - y| / 4) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ lowKernelDerivativeConstant_nonneg
        gcongr
      _ = 16 * lowKernelDerivativeConstant * (2 : ℝ) ^ (2 * B) /
          |x - y| ^ 2 := by
        field_simp [ne_of_gt hxy]
        ring
  have hmv := (convex_uIcc a b).norm_image_sub_le_of_norm_deriv_le
    (s := uIcc a b) (x := b) (y := a) hdiff hderiv
    right_mem_uIcc left_mem_uIcc
  change ‖F a - F b‖ ≤ _
  calc
    ‖F a - F b‖ ≤
        (16 * lowKernelDerivativeConstant * (2 : ℝ) ^ (2 * B) /
          |x - y| ^ 2) * ‖a - b‖ := hmv
    _ = lowKernelCZConstant B * |y - z| / |x - y| ^ 2 := by
      simp only [a, b, Real.norm_eq_abs, lowKernelCZConstant]
      rw [show x - y - (x - z) = -(y - z) by ring, abs_neg]
      ring

/-- Integrated `L¹` estimate for a mean-zero atom acted on by the paper's
low kernel, outside the triple of its supporting interval. -/
theorem integral_norm_paperLowCZKernel_le
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ)
    (f : ℝ → ℂ) (z R : ℝ)
    (hR : 0 < R)
    (hf : IntegrableOn f (centeredInterval z R))
    (hmean : ∫ y in centeredInterval z R, f y = 0)
    (hKf : ∀ x ∉ tripleCenteredInterval z R,
      IntegrableOn
        (fun y ↦ paperLowCZKernel lam hlam B x y * f y)
        (centeredInterval z R))
    (hmeas : AEStronglyMeasurable
      (fun x ↦ ∫ y in centeredInterval z R,
        paperLowCZKernel lam hlam B x y * f y)
      (volume.restrict (tripleCenteredInterval z R)ᶜ)) :
    ∫ x in (tripleCenteredInterval z R)ᶜ,
        ‖∫ y in centeredInterval z R,
          paperLowCZKernel lam hlam B x y * f y‖ ≤
      (8 * lowKernelCZConstant B / 3) *
        ∫ y in centeredInterval z R, ‖f y‖ := by
  exact integral_norm_setIntegral_kernel_le
    (paperLowCZKernel lam hlam B) f z R (lowKernelCZConstant B)
    hR (lowKernelCZConstant_nonneg B) hf hmean hKf
    (fun x hx y hy ↦ paperLowCZKernel_sub_center_norm_le hlam B hR hx hy)
    hmeas

end QuadraticCarleson
