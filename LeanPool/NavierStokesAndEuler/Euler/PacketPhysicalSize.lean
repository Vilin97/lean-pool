/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketScaledVelocity
import Mathlib.Algebra.Order.Star.Real

/-!
Actual physical norms and normalized next-frame coupling in the scaled
coordinates of source (28).  These are identities for the constructed
coordinate maps, rather than assumptions on a model system.
-/

@[expose] public section


noncomputable section


namespace EulerPacketMovingFrame

open EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay
  EulerPacketCrossProduct InnerProductSpace ContinuousLinearMap

/-- Velocity denominator, given by `1+ε^2*(r^2+w₃^2)`. -/
def velocityDenominator (ε r w₃ : ℝ) : ℝ := 1+ε^2*(r^2+w₃^2)

theorem velocityDenominator_pos (ε r w₃ : ℝ) : 0 < velocityDenominator ε r w₃ := by
  unfold velocityDenominator
  positivity

/-- Normalized coupling, given by `⟪unit r,M (unit w)⟫_ℝ`. -/
def normalizedCoupling (M : Space →L[ℝ] Space) (r w : Space) : ℝ :=
  ⟪unit r,M (unit w)⟫_ℝ

/-- Normalized tilt, given by `⟪cross (unit r) (unit w),M (unit w)⟫_ℝ/normalizedCoupling M r w`. -/
def normalizedTilt (M : Space →L[ℝ] Space) (r w : Space) : ℝ :=
  ⟪cross (unit r) (unit w),M (unit w)⟫_ℝ/normalizedCoupling M r w

theorem normalizedCoupling_eq (M : Space →L[ℝ] Space) (r w : Space) :
    normalizedCoupling M r w = ⟪r,M w⟫_ℝ/(‖r‖*‖w‖) := by
  simp only [normalizedCoupling, unit, map_smul, real_inner_smul_left,
    real_inner_smul_right, div_eq_mul_inv, mul_inv_rev]
  ring

theorem cross_smul_smul (a b : ℝ) (r w : Space) :
    cross (a • r) (b • w) = (a*b) • cross r w := by
  change crossBilinear (a • r) (b • w) = (a*b) • crossBilinear r w
  simp only [map_smul, smul_apply, smul_smul]
  rw [mul_comm b a]

theorem normalizedTilt_eq (M : Space →L[ℝ] Space) (r w : Space)
    (hr : r ≠ 0) (hw : w ≠ 0) (hflux : ⟪r, M w⟫_ℝ ≠ 0) :
    normalizedTilt M r w = ⟪cross r w,M w⟫_ℝ/(‖w‖*⟪r,M w⟫_ℝ) := by
  rw [normalizedTilt, normalizedCoupling_eq]
  simp only [unit, cross_smul_smul, map_smul, real_inner_smul_left, real_inner_smul_right]
  have hrn := norm_ne_zero_iff.mpr hr
  have hwn := norm_ne_zero_iff.mpr hw
  field_simp

theorem scaledRay_norm_sq (m v r : ℝ → Space) {s₀ t₀ a ε τ : ℝ}
    (hs₀ : s₀ ≠ 0) (hε : ε ≠ 0)
    (hm : m (physicalTime t₀ a ε τ) ≠ 0) (hv : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0) :
    ‖r (physicalTime t₀ a ε τ)‖^2 = s₀^2 *
      rayDenominator ε (scaledRay m v r s₀ t₀ a ε τ 0)
        (scaledRay m v r s₀ t₀ a ε τ 1) (scaledRay m v r s₀ t₀ a ε τ 2) := by
  rw [← movingDenominator_eq m v r _ hm hv hmv]
  exact movingDenominator_scaling m v r hs₀ hε

theorem scaledRay_norm (m v r : ℝ → Space) {s₀ t₀ a ε τ : ℝ}
    (hs₀ : s₀ ≠ 0) (hε : ε ≠ 0)
    (hm : m (physicalTime t₀ a ε τ) ≠ 0) (hv : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0) :
    ‖r (physicalTime t₀ a ε τ)‖ = |s₀| *
      Real.sqrt (rayDenominator ε (scaledRay m v r s₀ t₀ a ε τ 0)
        (scaledRay m v r s₀ t₀ a ε τ 1) (scaledRay m v r s₀ t₀ a ε τ 2)) := by
  calc
    _ = Real.sqrt (‖r (physicalTime t₀ a ε τ)‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = _ := by rw [scaledRay_norm_sq m v r hs₀ hε hm hv hmv,
      Real.sqrt_mul (sq_nonneg s₀), Real.sqrt_sq_eq_abs]

theorem scaledVelocity_norm_sq (m v w : ℝ → Space) {t₀ a ε τ : ℝ}
    (hε : ε ≠ 0) (hm : m (physicalTime t₀ a ε τ) ≠ 0) (hv : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0) :
    ‖w (physicalTime t₀ a ε τ)‖^2 = ε^2*(scaledVelocity m v w t₀ a ε τ 0)^2 +
      (scaledVelocity m v w t₀ a ε τ 1)^2+ε^2*(scaledVelocity m v w t₀ a ε τ 2)^2 := by
  have h := frame_norm_sq (unit (m (physicalTime t₀ a ε τ))) (unit (v (physicalTime t₀ a ε τ)))
    (w (physicalTime t₀ a ε τ)) (unit_inner_self hm) (unit_inner_self hv) (unit_inner_zero hmv)
  change (∑ j : Fin 3, (movingVelocity m v w (physicalTime t₀ a ε τ) j)^2) = _ at h
  simp_rw [← scaledVelocity_restore m v w hε] at h
  norm_num [Fin.sum_univ_three, velocityScale, Fin.ext_iff] at h
  nlinarith only [h]

theorem scaledVelocity_norm_ratio_sq (m v w : ℝ → Space) {t₀ a ε τ : ℝ}
    (hε : ε ≠ 0) (hm : m (physicalTime t₀ a ε τ) ≠ 0) (hv : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hV : scaledVelocity m v w t₀ a ε τ 1 ≠ 0) :
    ‖w (physicalTime t₀ a ε τ)‖^2 = (scaledVelocity m v w t₀ a ε τ 1)^2 *
      velocityDenominator ε (scaledVelocity m v w t₀ a ε τ 0/scaledVelocity m v w t₀ a ε τ 1)
        (scaledVelocity m v w t₀ a ε τ 2/scaledVelocity m v w t₀ a ε τ 1) := by
  rw [scaledVelocity_norm_sq m v w hε hm hv hmv]
  unfold velocityDenominator
  field_simp
  ring

theorem scaledVelocity_norm_ratio (m v w : ℝ → Space) {t₀ a ε τ : ℝ}
    (hε : ε ≠ 0) (hm : m (physicalTime t₀ a ε τ) ≠ 0) (hv : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hV : scaledVelocity m v w t₀ a ε τ 1 ≠ 0) :
    ‖w (physicalTime t₀ a ε τ)‖ = |scaledVelocity m v w t₀ a ε τ 1| *
      Real.sqrt (velocityDenominator ε
        (scaledVelocity m v w t₀ a ε τ 0/scaledVelocity m v w t₀ a ε τ 1)
        (scaledVelocity m v w t₀ a ε τ 2/scaledVelocity m v w t₀ a ε τ 1)) := by
  calc
    _ = Real.sqrt (‖w (physicalTime t₀ a ε τ)‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = _ := by rw [scaledVelocity_norm_ratio_sq m v w hε hm hv hmv hV,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- The exact physical size used in source (36), expressed through actual
ray and velocity coordinates. -/
theorem physical_primary_size (m v r w : ℝ → Space) {s₀ t₀ a ε τ : ℝ}
    (hs₀ : 0 < s₀) (hε : ε ≠ 0)
    (hm : m (physicalTime t₀ a ε τ) ≠ 0) (hv : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hV : 0 < scaledVelocity m v w t₀ a ε τ 1) :
    let R := scaledRay m v r s₀ t₀ a ε τ
    let V := scaledVelocity m v w t₀ a ε τ
    ‖r (physicalTime t₀ a ε τ)‖*‖w (physicalTime t₀ a ε τ)‖ =
      s₀*Real.sqrt (rayDenominator ε (R 0) (R 1) (R 2))*V 1 *
        Real.sqrt (velocityDenominator ε (V 0/V 1) (V 2/V 1)) := by
  rw [scaledRay_norm m v r (ne_of_gt hs₀) hε hm hv hmv,
    scaledVelocity_norm_ratio m v w hε hm hv hmv (ne_of_gt hV), abs_of_pos hs₀, abs_of_pos hV]
  dsimp
  ring

end EulerPacketMovingFrame
