/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketScaledVelocity
import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalNormBounds

/-! Polynomial conversion between physical tangent vectors and the two-state system. -/

@[expose] public section


noncomputable section


namespace EulerPacketMovingFrame

open EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay InnerProductSpace

theorem scaled_pair_le_physical_norm (m v w : ℝ → Space) {t₀ a ε τ : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hm : m (physicalTime t₀ a ε τ) ≠ 0) (hv : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0) :
    |scaledVelocity m v w t₀ a ε τ 0|+|scaledVelocity m v w t₀ a ε τ 1| ≤
      (2/ε)*‖w (physicalTime t₀ a ε τ)‖ := by
  have hU := frame_coordinate_abs_le_norm (unit (m (physicalTime t₀ a ε τ)))
    (unit (v (physicalTime t₀ a ε τ))) (w (physicalTime t₀ a ε τ))
    (unit_inner_self hm) (unit_inner_self hv) (unit_inner_zero hmv) 0
  have hV := frame_coordinate_abs_le_norm (unit (m (physicalTime t₀ a ε τ)))
    (unit (v (physicalTime t₀ a ε τ))) (w (physicalTime t₀ a ε τ))
    (unit_inner_self hm) (unit_inner_self hv) (unit_inner_zero hmv) 1
  change |movingVelocity m v w (physicalTime t₀ a ε τ) 0| ≤ _ at hU
  change |movingVelocity m v w (physicalTime t₀ a ε τ) 1| ≤ _ at hV
  rw [← scaledVelocity_restore m v w (ne_of_gt hε) 0] at hU
  rw [← scaledVelocity_restore m v w (ne_of_gt hε) 1] at hV
  norm_num [velocityScale, Fin.ext_iff, abs_mul, abs_of_pos hε] at hU hV
  have hεV := mul_le_mul_of_nonneg_left hV hε.le
  have hεnorm := mul_le_mul_of_nonneg_right hε1 (norm_nonneg (w (physicalTime t₀ a ε τ)))
  have hh : |scaledVelocity m v w t₀ a ε τ 0|+|scaledVelocity m v w t₀ a ε τ 1| ≤
      (2*‖w (physicalTime t₀ a ε τ)‖)/ε := by
    apply (le_div_iff₀ hε).mpr
    nlinarith only [hU, hεV, hεnorm]
  convert! hh using 1
  ring

theorem physical_velocity_le_scaled_state (m v r w : ℝ → Space)
    {s₀ t₀ a ε τ Θ ρ P₀ Q₀ : ℝ}
    (hs₀ : s₀ ≠ 0) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hm : m (physicalTime t₀ a ε τ) ≠ 0) (hv : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hrw : ⟪r (physicalTime t₀ a ε τ), w (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hΘ : 1 ≤ Θ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 2)
    (hP₀ : |P₀| ≤ Θ ^ 2) (hQ₀ : |Q₀| ≤ 2 * Θ ^ 2)
    (hP : |scaledRay m v r s₀ t₀ a ε τ 0 - P₀| ≤ ρ)
    (hQ : |scaledRay m v r s₀ t₀ a ε τ 1 - Q₀| ≤ ρ)
    (hN : |scaledRay m v r s₀ t₀ a ε τ 2 - 1| ≤ ρ) :
    ‖w (physicalTime t₀ a ε τ)‖ ≤
      7*Θ^2*(|scaledVelocity m v w t₀ a ε τ 0|+|scaledVelocity m v w t₀ a ε τ 1|) := by
  let R := scaledRay m v r s₀ t₀ a ε τ
  let V := scaledVelocity m v w t₀ a ε τ
  have hpair := scaled_pairing_zero m v r w hs₀ (ne_of_gt hε) hm hv hmv hrw
  obtain ⟨hn, _, _, _, hw, _, _⟩ := ray_geometric_bounds (ε := ε) (U := V 0) (V := V 1)
    hΘ hρ0 hρ hP₀ hQ₀ hP hQ hN
  have hNne : R 2 ≠ 0 := by linarith only [hn]
  have hthird := thirdVelocity_of_pairing R V hNne hpair
  rw [← hthird] at hw
  have hΘ2 : 1 ≤ Θ^2 := one_le_pow₀ hΘ
  have hV : norm3 (V 0) (V 1) (V 2) ≤ 7*Θ^2*(|V 0|+|V 1|) := by
    dsimp [norm3]
    have ht := mul_le_mul_of_nonneg_right hΘ2 (add_nonneg (abs_nonneg (V 0)) (abs_nonneg (V 1)))
    nlinarith only [hw, ht]
  exact (scaledVelocity_norm_le_norm3 m v w hε hε1 hm hv hmv).trans hV

end EulerPacketMovingFrame
