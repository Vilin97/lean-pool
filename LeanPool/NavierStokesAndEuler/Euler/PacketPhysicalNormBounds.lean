/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketOrientedCoordinates
public import LeanPool.NavierStokesAndEuler.Euler.PacketScaledVelocity

/-! Actual Euclidean norm estimates for the scaled moving coordinates. -/

@[expose] public section


noncomputable section


namespace EulerPacketMovingFrame

open EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay InnerProductSpace

theorem frame_coordinate_abs_le_norm (p q x : Space)
    (hp : ⟪p, p⟫_ℝ = 1) (hq : ⟪q, q⟫_ℝ = 1) (hpq : ⟪p, q⟫_ℝ = 0) (i : Fin 3) :
    |frameCoordinates p q x i| ≤ ‖x‖ := by
  have h := abs_real_inner_le_norm (frame p q i) x
  simpa only [frameCoordinates, (frame_orthonormal p q hp hq hpq).norm_eq_one i, one_mul] using h

theorem norm_le_frame_norm3 (p q x : Space)
    (hp : ⟪p, p⟫_ℝ = 1) (hq : ⟪q, q⟫_ℝ = 1) (hpq : ⟪p, q⟫_ℝ = 0) :
    ‖x‖ ≤ norm3 (frameCoordinates p q x 0) (frameCoordinates p q x 1) (frameCoordinates p q x 2) :=
        by
  have heq := (frameBasis p q hp hq hpq).sum_repr' x
  calc
    ‖x‖ = ‖∑ i : Fin 3, ⟪frameBasis p q hp hq hpq i,x⟫_ℝ • frameBasis p q hp hq hpq i‖ :=
      congrArg norm heq.symm
    _ ≤ ∑ i : Fin 3, ‖⟪frameBasis p q hp hq hpq i,x⟫_ℝ • frameBasis p q hp hq hpq i‖ :=
      norm_sum_le _ _
    _ = _ := by
      simp only [norm_smul, Real.norm_eq_abs, frameBasis_apply,
        (frame_orthonormal p q hp hq hpq).norm_eq_one, mul_one, Fin.sum_univ_three, norm3,
            frameCoordinates]

theorem scaledRay_norm_le_norm3 (m v r : ℝ → Space) {s₀ t₀ a ε τ : ℝ}
    (hs₀ : 0 < s₀) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hm : m (physicalTime t₀ a ε τ) ≠ 0) (hv : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0) :
    ‖r (physicalTime t₀ a ε τ)‖ ≤ s₀*norm3
      (scaledRay m v r s₀ t₀ a ε τ 0) (scaledRay m v r s₀ t₀ a ε τ 1)
      (scaledRay m v r s₀ t₀ a ε τ 2) := by
  have hh := norm_le_frame_norm3 (unit (m (physicalTime t₀ a ε τ)))
    (unit (v (physicalTime t₀ a ε τ))) (r (physicalTime t₀ a ε τ))
    (unit_inner_self hm) (unit_inner_self hv) (unit_inner_zero hmv)
  change ‖r (physicalTime t₀ a ε τ)‖ ≤ norm3
    (movingRay m v r (physicalTime t₀ a ε τ) 0) (movingRay m v r (physicalTime t₀ a ε τ) 1)
    (movingRay m v r (physicalTime t₀ a ε τ) 2) at hh
  simp_rw [← scaledRay_restore m v r (ne_of_gt hs₀) (ne_of_gt hε)] at hh
  norm_num [rayScale, Fin.ext_iff, norm3, abs_mul, abs_of_pos hs₀, abs_of_pos hε] at hh
  dsimp [norm3]
  have hbound := mul_le_mul_of_nonneg_left hε1
    (show 0 ≤ s₀*|scaledRay m v r s₀ t₀ a ε τ 1| by positivity)
  nlinarith only [hh, hbound]

theorem scaledVelocity_norm_le_norm3 (m v w : ℝ → Space) {t₀ a ε τ : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hm : m (physicalTime t₀ a ε τ) ≠ 0) (hv : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0) :
    ‖w (physicalTime t₀ a ε τ)‖ ≤ norm3
      (scaledVelocity m v w t₀ a ε τ 0) (scaledVelocity m v w t₀ a ε τ 1)
      (scaledVelocity m v w t₀ a ε τ 2) := by
  have hh := norm_le_frame_norm3 (unit (m (physicalTime t₀ a ε τ)))
    (unit (v (physicalTime t₀ a ε τ))) (w (physicalTime t₀ a ε τ))
    (unit_inner_self hm) (unit_inner_self hv) (unit_inner_zero hmv)
  change ‖w (physicalTime t₀ a ε τ)‖ ≤ norm3
    (movingVelocity m v w (physicalTime t₀ a ε τ) 0) (movingVelocity m v w (physicalTime t₀ a ε τ)
        1)
    (movingVelocity m v w (physicalTime t₀ a ε τ) 2) at hh
  simp_rw [← scaledVelocity_restore m v w (ne_of_gt hε)] at hh
  norm_num [velocityScale, Fin.ext_iff, norm3, abs_mul, abs_of_pos hε] at hh
  dsimp [norm3]
  have h0 := mul_le_mul_of_nonneg_right hε1 (abs_nonneg (scaledVelocity m v w t₀ a ε τ 0))
  have h2 := mul_le_mul_of_nonneg_right hε1 (abs_nonneg (scaledVelocity m v w t₀ a ε τ 2))
  nlinarith only [hh, h0, h2]

theorem physical_size_ge_second (m v r w : ℝ → Space) {s₀ t₀ a ε τ : ℝ}
    (hs₀ : 0 < s₀) (hε : ε ≠ 0)
    (hm : m (physicalTime t₀ a ε τ) ≠ 0) (hv : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hN : 1 / 2 ≤ scaledRay m v r s₀ t₀ a ε τ 2)
    (hV : 0 ≤ scaledVelocity m v w t₀ a ε τ 1) :
    s₀*scaledVelocity m v w t₀ a ε τ 1/2 ≤
      ‖r (physicalTime t₀ a ε τ)‖*‖w (physicalTime t₀ a ε τ)‖ := by
  have hn := frame_coordinate_abs_le_norm (unit (m (physicalTime t₀ a ε τ)))
    (unit (v (physicalTime t₀ a ε τ))) (r (physicalTime t₀ a ε τ))
    (unit_inner_self hm) (unit_inner_self hv) (unit_inner_zero hmv) 2
  change |movingRay m v r (physicalTime t₀ a ε τ) 2| ≤ _ at hn
  rw [← scaledRay_restore m v r (ne_of_gt hs₀) hε 2] at hn
  norm_num [rayScale, Fin.ext_iff] at hn
  have hnpos : 0 ≤ scaledRay m v r s₀ t₀ a ε τ 2 := by linarith only [hN]
  rw [abs_of_pos hs₀, abs_of_nonneg hnpos] at hn
  have hr : s₀/2 ≤ ‖r (physicalTime t₀ a ε τ)‖ := by
    nlinarith only [hn, mul_le_mul_of_nonneg_left hN hs₀.le]
  have hw := frame_coordinate_abs_le_norm (unit (m (physicalTime t₀ a ε τ)))
    (unit (v (physicalTime t₀ a ε τ))) (w (physicalTime t₀ a ε τ))
    (unit_inner_self hm) (unit_inner_self hv) (unit_inner_zero hmv) 1
  change |movingVelocity m v w (physicalTime t₀ a ε τ) 1| ≤ _ at hw
  rw [← scaledVelocity_restore m v w hε 1] at hw
  norm_num [velocityScale, Fin.ext_iff] at hw
  rw [abs_of_nonneg hV] at hw
  have hp := mul_le_mul hr hw hV (norm_nonneg _)
  nlinarith only [hp]

theorem physical_size_le_scaled_state (m v r w : ℝ → Space)
    {s₀ t₀ a ε τ Θ ρ P₀ Q₀ : ℝ}
    (hs₀ : 0 < s₀) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hm : m (physicalTime t₀ a ε τ) ≠ 0) (hv : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hrw : ⟪r (physicalTime t₀ a ε τ), w (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hΘ : 1 ≤ Θ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 2)
    (hP₀ : |P₀| ≤ Θ ^ 2) (hQ₀ : |Q₀| ≤ 2 * Θ ^ 2)
    (hP : |scaledRay m v r s₀ t₀ a ε τ 0 - P₀| ≤ ρ)
    (hQ : |scaledRay m v r s₀ t₀ a ε τ 1 - Q₀| ≤ ρ)
    (hN : |scaledRay m v r s₀ t₀ a ε τ 2 - 1| ≤ ρ) :
    ‖r (physicalTime t₀ a ε τ)‖*‖w (physicalTime t₀ a ε τ)‖ ≤
      49*s₀*Θ^4*(|scaledVelocity m v w t₀ a ε τ 0|+|scaledVelocity m v w t₀ a ε τ 1|) := by
  let R := scaledRay m v r s₀ t₀ a ε τ
  let V := scaledVelocity m v w t₀ a ε τ
  have hpair := scaled_pairing_zero m v r w (ne_of_gt hs₀) (ne_of_gt hε) hm hv hmv hrw
  obtain ⟨hn, hp, hq, hnabs, hw, _, _⟩ := ray_geometric_bounds (ε := ε) (U := V 0) (V := V 1)
    hΘ hρ0 hρ hP₀ hQ₀ hP hQ hN
  have hNne : R 2 ≠ 0 := by linarith only [hn]
  have hthird := thirdVelocity_of_pairing R V hNne hpair
  rw [← hthird] at hw
  have hΘ2 : 1 ≤ Θ^2 := one_le_pow₀ hΘ
  have hR : norm3 (R 0) (R 1) (R 2) ≤ 7*Θ^2 := by
    dsimp [norm3]
    linarith only [hp, hq, hnabs, hΘ2]
  have hV : norm3 (V 0) (V 1) (V 2) ≤ 7*Θ^2*(|V 0|+|V 1|) := by
    dsimp [norm3]
    have ht := mul_le_mul_of_nonneg_right hΘ2 (add_nonneg (abs_nonneg (V 0)) (abs_nonneg (V 1)))
    nlinarith only [hw, ht]
  have hrn := scaledRay_norm_le_norm3 m v r hs₀ hε hε1 hm hv hmv
  have hwn := scaledVelocity_norm_le_norm3 m v w hε hε1 hm hv hmv
  have hr' : ‖r (physicalTime t₀ a ε τ)‖ ≤ 7*s₀*Θ^2 := by
    nlinarith only [hrn, mul_le_mul_of_nonneg_left hR hs₀.le]
  have hw' := hwn.trans hV
  have hb := mul_le_mul hr' hw' (norm_nonneg _) (show 0 ≤ 7*s₀*Θ^2 by positivity)
  nlinarith only [hb]

end EulerPacketMovingFrame
