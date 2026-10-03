/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.LowKernelCalderonZygmund
public import LeanPool.QuadraticCarleson.QuadraticCarleson.LowOscillatoryMajorant

/-!
# Sharp low-kernel estimate for a cancellative bad atom

The derivative estimate alone gives a bound growing like `2^(2B)`. The
paper obtains the sharp `O(B)` estimate by taking the minimum of that
cancellation bound and the `1 / |t|` size bound for the telescoped low
kernel. This file proves the resulting common pointwise majorant uniformly
in the modulation parameter `lam`, then integrates it with
`integral_lowDecayMajorant_two_pow_le`.
-/

@[expose] public section

open MeasureTheory Set

namespace QuadraticCarleson


/-- Absolute constant multiplying the logarithmic low-kernel majorant. -/
noncomputable def lowKernelBadAtomConstant : ℝ :=
  max 2 (32 * lowKernelDerivativeConstant)

theorem lowKernelBadAtomConstant_nonneg :
    0 ≤ lowKernelBadAtomConstant := by
  exact le_trans (by norm_num) (le_max_left 2 (32 * lowKernelDerivativeConstant))

theorem two_le_lowKernelBadAtomConstant :
    2 ≤ lowKernelBadAtomConstant :=
  le_max_left _ _

theorem thirtytwo_mul_deriv_le_lowKernelBadAtomConstant :
    32 * lowKernelDerivativeConstant ≤ lowKernelBadAtomConstant :=
  le_max_right _ _

/-- The uncancelled size estimate for the low kernel on an atom interval.
It is uniform in both `lam` and `B`. -/
theorem norm_setIntegral_paperLowCZKernel_le_size
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ)
    (f : ℝ → ℂ) {z R x : ℝ}
    (hR : 0 < R)
    (hx : x ∉ tripleCenteredInterval z R)
    (hf : IntegrableOn f (centeredInterval z R)) :
    ‖∫ y in centeredInterval z R,
        paperLowCZKernel lam hlam B x y * f y‖ ≤
      (2 / |x - z|) * ∫ y in centeredInterval z R, ‖f y‖ := by
  have hxz : 0 < |x - z| := by
    have := not_mem_tripleCenteredInterval_abs hx
    linarith
  have hmajorant : IntegrableOn
      (fun y ↦ (2 / |x - z|) * ‖f y‖) (centeredInterval z R) :=
    hf.norm.const_mul (2 / |x - z|)
  have hbound : ∀ᵐ y ∂volume.restrict (centeredInterval z R),
      ‖paperLowCZKernel lam hlam B x y * f y‖ ≤
        (2 / |x - z|) * ‖f y‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
    have hdist : |x - z| / 2 ≤ |x - y| :=
      half_center_distance_le_distance hR.le hx hy
    have hxy : 0 < |x - y| := lt_of_lt_of_le (half_pos hxz) hdist
    have hkernel : ‖paperLowCZKernel lam hlam B x y‖ ≤ 2 / |x - z| := by
      calc
        ‖paperLowCZKernel lam hlam B x y‖ ≤ 1 / |x - y| := by
          exact paperLowOscillatoryKernel_norm_le_inv_abs hlam B
            (sub_ne_zero.mpr (by
              intro h
              rw [h] at hxy
              simp at hxy))
        _ ≤ 1 / (|x - z| / 2) :=
          one_div_le_one_div_of_le (half_pos hxz) hdist
        _ = 2 / |x - z| := by field_simp [ne_of_gt hxz]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hkernel (norm_nonneg (f y))
  calc
    ‖∫ y in centeredInterval z R,
        paperLowCZKernel lam hlam B x y * f y‖ ≤
        ∫ y in centeredInterval z R, (2 / |x - z|) * ‖f y‖ :=
      norm_integral_le_of_norm_le hmajorant hbound
    _ = (2 / |x - z|) * ∫ y in centeredInterval z R, ‖f y‖ := by
      rw [integral_const_mul]

/-- Cancellation and the derivative estimate give the inverse-square member
of the sharp minimum. -/
theorem norm_setIntegral_paperLowCZKernel_le_cancellation
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ)
    (f : ℝ → ℂ) {z R x : ℝ}
    (hR : 0 < R)
    (hx : x ∉ tripleCenteredInterval z R)
    (hf : IntegrableOn f (centeredInterval z R))
    (hKf : IntegrableOn
      (fun y ↦ paperLowCZKernel lam hlam B x y * f y)
      (centeredInterval z R))
    (hmean : ∫ y in centeredInterval z R, f y = 0) :
    ‖∫ y in centeredInterval z R,
        paperLowCZKernel lam hlam B x y * f y‖ ≤
      (32 * lowKernelDerivativeConstant * (2 : ℝ) ^ (2 * B) * R /
          |x - z| ^ 2) *
        ∫ y in centeredInterval z R, ‖f y‖ := by
  have h := norm_setIntegral_kernel_le_decay
    (paperLowCZKernel lam hlam B) f x z R (lowKernelCZConstant B)
    hR (lowKernelCZConstant_nonneg B) hx hf hKf hmean
    (fun y hy ↦ paperLowCZKernel_sub_center_norm_le hlam B hR hx hy)
  calc
    ‖∫ y in centeredInterval z R,
        paperLowCZKernel lam hlam B x y * f y‖ ≤
      (2 * lowKernelCZConstant B * R / |x - z| ^ 2) *
        ∫ y in centeredInterval z R, ‖f y‖ := h
    _ = (32 * lowKernelDerivativeConstant * (2 : ℝ) ^ (2 * B) * R /
          |x - z| ^ 2) *
        ∫ y in centeredInterval z R, ‖f y‖ := by
      unfold lowKernelCZConstant
      ring

/-- Sharp pointwise bad-atom estimate. Its right-hand side is independent
of `lam`, so it is also a common pointwise majorant for any modulation
supremum. -/
theorem norm_setIntegral_paperLowCZKernel_le_lowDecayMajorant
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ)
    (f : ℝ → ℂ) {z R x : ℝ}
    (hR : 0 < R)
    (hx : x ∉ tripleCenteredInterval z R)
    (hf : IntegrableOn f (centeredInterval z R))
    (hKf : IntegrableOn
      (fun y ↦ paperLowCZKernel lam hlam B x y * f y)
      (centeredInterval z R))
    (hmean : ∫ y in centeredInterval z R, f y = 0) :
    ‖∫ y in centeredInterval z R,
        paperLowCZKernel lam hlam B x y * f y‖ ≤
      lowKernelBadAtomConstant *
        (∫ y in centeredInterval z R, ‖f y‖) *
        lowDecayMajorant ((2 : ℝ) ^ (2 * B)) R z x := by
  let A : ℝ := ∫ y in centeredInterval z R, ‖f y‖
  have hA : 0 ≤ A := integral_nonneg fun _ ↦ norm_nonneg _
  have hxz : 0 < |x - z| := by
    have := not_mem_tripleCenteredInterval_abs hx
    linarith
  have hsize := norm_setIntegral_paperLowCZKernel_le_size
    hlam B f hR hx hf
  have hcancel := norm_setIntegral_paperLowCZKernel_le_cancellation
    hlam B f hR hx hf hKf hmean
  rw [lowDecayMajorant, mul_min_of_nonneg _ _
    (mul_nonneg lowKernelBadAtomConstant_nonneg hA)]
  apply le_min
  · calc
      ‖∫ y in centeredInterval z R,
          paperLowCZKernel lam hlam B x y * f y‖ ≤
          (2 / |x - z|) * A := hsize
      _ ≤ (lowKernelBadAtomConstant * A) * (1 / |x - z|) := by
        have hrecip : 0 ≤ 1 / |x - z| := one_div_nonneg.mpr hxz.le
        rw [show (2 / |x - z|) * A = (2 * A) * (1 / |x - z|) by ring]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right two_le_lowKernelBadAtomConstant hA)
          hrecip
  · calc
      ‖∫ y in centeredInterval z R,
          paperLowCZKernel lam hlam B x y * f y‖ ≤
          (32 * lowKernelDerivativeConstant * (2 : ℝ) ^ (2 * B) * R /
            |x - z| ^ 2) * A := hcancel
      _ ≤ (lowKernelBadAtomConstant * A) *
          ((2 : ℝ) ^ (2 * B) * R / |x - z| ^ 2) := by
        have hfactor : 0 ≤
            (2 : ℝ) ^ (2 * B) * R / |x - z| ^ 2 := by positivity
        rw [show
          (32 * lowKernelDerivativeConstant * (2 : ℝ) ^ (2 * B) * R /
              |x - z| ^ 2) * A =
            (32 * lowKernelDerivativeConstant * A) *
              ((2 : ℝ) ^ (2 * B) * R / |x - z| ^ 2) by ring]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            thirtytwo_mul_deriv_le_lowKernelBadAtomConstant hA) hfactor

/-- Enlarging the atom scale only enlarges the low-decay majorant. -/
theorem lowDecayMajorant_mono_length
    {D ℓ₁ ℓ₂ z x : ℝ} (hD : 0 ≤ D) (hℓ : ℓ₁ ≤ ℓ₂) :
    lowDecayMajorant D ℓ₁ z x ≤ lowDecayMajorant D ℓ₂ z x := by
  unfold lowDecayMajorant
  apply min_le_min le_rfl
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hℓ hD) (sq_nonneg |x - z|)

/-- The sharp integrated estimate outside the triple interval. The
constant is absolute and the estimate is uniform in `lam`. -/
theorem integral_norm_paperLowCZKernel_le_sharp
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
      (fun x ↦ ‖∫ y in centeredInterval z R,
        paperLowCZKernel lam hlam B x y * f y‖)
      (volume.restrict (tripleCenteredInterval z R)ᶜ)) :
    ∫ x in (tripleCenteredInterval z R)ᶜ,
        ‖∫ y in centeredInterval z R,
          paperLowCZKernel lam hlam B x y * f y‖ ≤
      4 * (B + 1 : ℝ) *
        (lowKernelBadAtomConstant *
          ∫ y in centeredInterval z R, ‖f y‖) := by
  let A : ℝ := ∫ y in centeredInterval z R, ‖f y‖
  have hA : 0 ≤ A := integral_nonneg fun _ ↦ norm_nonneg _
  have hscale : 0 < 3 * R / 2 := by positivity
  have hmajorant : ∀ x ∉ tripleCenteredInterval z R,
      ‖∫ y in centeredInterval z R,
          paperLowCZKernel lam hlam B x y * f y‖ ≤
        (lowKernelBadAtomConstant * A) *
          lowDecayMajorant ((2 : ℝ) ^ (2 * B)) (3 * R / 2) z x := by
    intro x hx
    calc
      ‖∫ y in centeredInterval z R,
          paperLowCZKernel lam hlam B x y * f y‖ ≤
          lowKernelBadAtomConstant * A *
            lowDecayMajorant ((2 : ℝ) ^ (2 * B)) R z x :=
        norm_setIntegral_paperLowCZKernel_le_lowDecayMajorant
          hlam B f hR hx hf (hKf x hx) hmean
      _ ≤ (lowKernelBadAtomConstant * A) *
          lowDecayMajorant ((2 : ℝ) ^ (2 * B)) (3 * R / 2) z x := by
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg lowKernelBadAtomConstant_nonneg hA)
        exact lowDecayMajorant_mono_length (by positivity) (by linarith)
  have h := integral_le_four_mul_succ_of_le_lowDecayMajorant
    (fun x ↦ ‖∫ y in centeredInterval z R,
      paperLowCZKernel lam hlam B x y * f y‖)
    (lowKernelBadAtomConstant * A) (3 * R / 2) z B
    (mul_nonneg lowKernelBadAtomConstant_nonneg hA) hscale
    (by simpa only [tripleCenteredInterval] using hmeas)
    (fun _ _ ↦ norm_nonneg _)
    (by
      intro x hx
      apply hmajorant x
      simpa only [tripleCenteredInterval] using hx)
  simpa only [A, tripleCenteredInterval] using h

end QuadraticCarleson
