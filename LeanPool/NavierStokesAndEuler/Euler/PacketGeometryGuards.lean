/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryData
public import LeanPool.NavierStokesAndEuler.Euler.PacketShearMotion

@[expose] public section

/-! Consequences of the literal numerical guards for a physical geometry stage. -/

noncomputable section


namespace EulerPacketMovingFrame.PhysicalGeometryData

open Set Real EulerSmoothLimit EulerPacketRay EulerPacketFrameQuantitative

variable {α : Type*} (D : PhysicalGeometryData α)

theorem a_pos : 0 < D.a := by linarith only [D.a_lower]
theorem Theta_pos : 0 < D.Θ := by linarith only [D.Theta_lower]
theorem error_nonneg : 0 ≤ D.error := by unfold error; positivity [D.epsilon_pos, D.Theta_pos,
  D.d_nonneg]

theorem target_from_sigma : 1/D.σ ≤ D.target := by
  have hy : 1 ≤ D.y⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ D.y_pos).mpr
    linarith only [D.y_small]
  exact div_le_div_of_nonneg_right hy D.sigma_pos.le

theorem target_one : 1 ≤ D.target := by
  have hs : 1 ≤ 1/D.σ := (le_div_iff₀ D.sigma_pos).mpr (by linarith only [D.sigma_small])
  exact hs.trans D.target_from_sigma

theorem target_pos : 0 < D.target := lt_of_lt_of_le zero_lt_one D.target_one
theorem horizon_one : 1 ≤ D.H := D.target_one.trans D.target_le_horizon
theorem horizon_pos : 0 < D.H := lt_of_lt_of_le zero_lt_one D.horizon_one
theorem target_le_Theta : D.target ≤ D.Θ := D.target_le_horizon.trans D.horizon_le_Theta

theorem sigma_Theta : 1 ≤ D.σ*D.Θ := by
  have h := (div_le_iff₀ D.sigma_pos).mp (D.target_from_sigma.trans D.target_le_Theta)
  nlinarith only [h]

theorem target_scale : 1 ≤ D.σ^2*D.target^2 := by
  have h : 1 ≤ D.σ*D.target := by
    have hh := (div_le_iff₀ D.sigma_pos).mp D.target_from_sigma
    nlinarith only [hh]
  have hh := mul_le_mul h h (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0 ≤ D.σ*D.target)
  nlinarith only [hh]

theorem time_mem {τ : ℝ} (hτ : τ ∈ Icc 0 D.H) : D.time τ ∈ D.S :=
  D.time_maps ⟨hτ.1, hτ.2.trans D.horizon_le_Theta⟩

theorem target_time_mem : D.targetTime ∈ D.S :=
  D.time_mem ⟨D.target_pos.le, D.target_le_horizon⟩

theorem error_le_half : D.error ≤ 1/2 := by
  have hp := scaled_power_le D.Theta_lower
    ((by norm_num : (1:ℝ) ≤ 1000000000).trans neighborStabilityConstant_ge) D.error_nonneg
    (by decide : 0 ≤ 40)
  have hs := D.small
  change 1000000*neighborStabilityConstant*D.error*D.Θ^40 ≤ 1 at hs
  norm_num only [pow_zero, mul_one] at hp
  nlinarith only [hp, hs]

theorem error_le_one : D.error ≤ 1 := D.error_le_half.trans (by norm_num)

theorem epsilon_le_error : D.ε ≤ D.error := by
  have hg : 1 ≤ (4*D.G)^2 := by nlinarith only [D.G_lower, sq_nonneg (D.G-1)]
  have hc : 1 ≤ D.Θ*(4*D.G)^2 := by
    simpa only [one_mul] using mul_le_mul D.Theta_lower hg
      (by norm_num : (0:ℝ) ≤ 1) D.Theta_pos.le
  have hh := mul_le_mul_of_nonneg_left hc D.epsilon_pos.le
  unfold error
  nlinarith only [hh, D.d_nonneg, D.epsilon_pos]

theorem epsilon_le_one : D.ε ≤ 1 := D.epsilon_le_error.trans D.error_le_one

theorem ray_error_small : 800*D.error*D.Θ^5 ≤ 1/2 := by
  have hp := scaled_power_le D.Theta_lower
    ((by norm_num : (1:ℝ) ≤ 1000000000).trans neighborStabilityConstant_ge) D.error_nonneg
    (by decide : 5 ≤ 40)
  have hs := D.small
  change 1000000*neighborStabilityConstant*D.error*D.Θ^40 ≤ 1 at hs
  nlinarith only [hp, hs]

theorem relative_error_small : neighborStabilityConstant*D.error*D.Θ^29 ≤ 1/2 := by
  have hK : 0 ≤ neighborStabilityConstant := (by norm_num : (0:ℝ) ≤ 1000000000).trans
    neighborStabilityConstant_ge
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ D.Theta_lower (by decide : 29 ≤ 40))
    (mul_nonneg hK D.error_nonneg)
  have hs := D.small
  change 1000000*neighborStabilityConstant*D.error*D.Θ^40 ≤ 1 at hs
  nlinarith only [hp, hs]

theorem scalar_error_small : 4*exp 6*(400000000*D.error*D.Θ^29) ≤ 1 := by
  have hr := D.relative_error_small
  have hK : 0 ≤ neighborStabilityConstant :=
    (by norm_num : (0:ℝ) ≤ 1000000000).trans neighborStabilityConstant_ge
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ D.Theta_lower (by decide : 29 ≤ 40))
    (mul_nonneg hK D.error_nonneg)
  have hs := D.small
  change 1000000*neighborStabilityConstant*D.error*D.Θ^40 ≤ 1 at hs
  unfold neighborStabilityConstant at hp hs hr
  nlinarith only [hp, hs, hr]

theorem propagator_small : 8000000*D.error*D.Θ^21 ≤ 1 := by
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ D.Theta_lower (by decide : 21 ≤ 40))
    D.error_nonneg
  have hk : 0 ≤ neighborStabilityConstant-8 := by linarith only [neighborStabilityConstant_ge]
  have hmul := mul_nonneg hk (mul_nonneg D.error_nonneg (pow_nonneg D.Theta_pos.le 40))
  have hs := D.small
  change 1000000*neighborStabilityConstant*D.error*D.Θ^40 ≤ 1 at hs
  nlinarith only [hp, hmul, hs]

theorem action_error (ξ : α) {τ : ℝ} (hτ : τ ∈ Icc 0 D.H) :
    ∀ i j, |scaledAction (D.M ξ (D.time τ)) D.m D.v D.a D.ε (D.time τ) i j-
      idealVelocityEntry (D.σ^2) i j| ≤ 3*D.error := by
  have h := physical_matrix_errors D.a_lower D.epsilon_pos D.Theta_lower D.G_lower D.d_nonneg
    D.error_le_one D.time_maps D.B_derivative D.old_ray_equation D.old_velocity_equation
    D.old_ray_nonzero D.old_velocity_nonzero D.old_tangent D.B_bound D.B_derivative_bound
    (D.E_bound ξ) (D.parent_decomposition ξ) D.initial_coupling D.initial_tilt D.initial_shear
  exact (h.2 τ ⟨hτ.1, hτ.2.trans D.horizon_le_Theta⟩).2.1

theorem target_shear_lower : D.a/(2*D.ε^2) ≤ D.targetShear := by
  have hh := physical_shear_motion_bound D.a_lower D.epsilon_pos D.Theta_lower D.G_lower D.d_nonneg
    D.error_le_one D.time_maps D.B_derivative D.old_ray_equation D.old_velocity_equation
    D.old_ray_nonzero D.old_velocity_nonzero D.old_tangent D.B_bound D.B_derivative_bound
    (D.E_bound D.center) D.initial_coupling D.initial_tilt D.initial_shear
  have hb := (abs_le.mp (hh.2 D.target ⟨D.target_pos.le, D.target_le_Theta⟩)).1
  have hratio : 1/2 ≤ D.ε^2*D.targetShear/D.a := by
    change -D.error ≤ D.ε^2*D.targetShear/D.a-1 at hb
    linarith only [hb, D.error_le_half]
  have hmul := (le_div_iff₀ D.a_pos).mp hratio
  apply (div_le_iff₀ (show 0 < 2*D.ε^2 by positivity [D.epsilon_pos])).mpr
  nlinarith only [hmul]

theorem target_shear_pos : 0 < D.targetShear :=
  lt_of_lt_of_le (by positivity [D.a_pos, D.epsilon_pos]) D.target_shear_lower

theorem compression_domination :
    30*(‖D.B D.targetTime‖+‖D.E D.center D.targetTime‖)*D.target < D.targetShear*D.ε := by
  have hguard := D.compression_guard
  change 60*(D.G+D.d)*D.target*D.ε < D.a at hguard
  have hlower := mul_le_mul_of_nonneg_right D.target_shear_lower D.epsilon_pos.le
  have heq : (D.a/(2*D.ε^2))*D.ε = D.a/(2*D.ε) := by
    field_simp [ne_of_gt D.epsilon_pos]
  rw [heq] at hlower
  have hsmall : 30*(D.G+D.d)*D.target < D.a/(2*D.ε) :=
    (lt_div_iff₀ (show 0 < 2*D.ε by positivity [D.epsilon_pos])).mpr (by nlinarith only [hguard])
  have hnorm := add_le_add (D.B_bound _ D.target_time_mem) (D.E_bound D.center _ D.target_time_mem)
  have hm := mul_le_mul_of_nonneg_right hnorm (show 0 ≤ 30*D.target by positivity [D.target_pos])
  have hfirst : 30*(‖D.B D.targetTime‖+‖D.E D.center D.targetTime‖)*D.target ≤
      30*(D.G+D.d)*D.target := by nlinarith only [hm]
  exact hfirst.trans_lt (hsmall.trans_le hlower)

end EulerPacketMovingFrame.PhysicalGeometryData
