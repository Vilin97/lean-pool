/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryGuards
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalSign
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalCompression
public import LeanPool.NavierStokesAndEuler.Euler.PacketEarlyPhysical
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalPropagator
public import LeanPool.NavierStokesAndEuler.Euler.PacketPropagationTime

@[expose] public section

/-!
One geometric stage: actual neighboring physical fields, the constructed
common scalar reference, and the source amplitude choice.  All hypotheses
are the literal physical data and explicit scale guards in the data record.
-/

noncomputable section


namespace EulerPacketMovingFrame

open Set Real EulerSmoothLimit EulerPacketRay InnerProductSpace PhysicalGeometryData

structure PhysicalGeometryConclusion {α : Type*} (D : PhysicalGeometryData α)
    (F F₁ Z Z₁ : ℝ → ℝ) : Prop where
  initial_values : F 0 = 1 ∧ F₁ 0 = 0 ∧ Z 0 = 1 ∧ Z₁ 0 = D.lam
  F_derivative : ∀ t, HasDerivAt F (F₁ t) t
  Z_derivative : ∀ t, HasDerivAt Z (Z₁ t) t
  F_flux : ∀ t, HasDerivAt (fun s => (1+(D.σ^2*s^2)^2)*F₁ s)
    (2*(1-D.σ^2*(D.σ^2*t^2))*F t) t
  Z_flux : ∀ t, HasDerivAt (fun s => (1+(D.σ^2*s^2)^2)*Z₁ s)
    (2*(1-D.σ^2*(D.σ^2*t^2))*Z t) t
  ray_control : ∀ ξ τ, τ ∈ Icc 0 D.H →
    norm3 (D.ray ξ τ 0-D.σ^2*τ^2) (D.ray ξ τ 1+2*D.σ^2*τ) (D.ray ξ τ 2-1) ≤
      800*D.error*D.Θ^5 ∧ 1/2 ≤ D.ray ξ τ 2 ∧
      ⟪D.r ξ (D.time τ),D.w ξ (D.time τ)⟫_ℝ = 0
  state_error : ∀ ξ τ, τ ∈ Icc 0 D.H →
    |D.velocity ξ τ 1-Z τ|+|D.velocity ξ τ 0+Z₁ τ| ≤ 400000000*D.error*D.Θ^29*(1+D.lam)*F τ
  relative_error : ∀ ξ τ, τ ∈ Icc 1 D.H →
    0 < D.velocity ξ τ 1 ∧ |D.velocity ξ τ 1/Z τ-1| ≤ neighborStabilityConstant*D.error*D.Θ^29 ∧
      |D.velocity ξ τ 0/D.velocity ξ τ 1+Z₁ τ/Z τ| ≤ 10*(neighborStabilityConstant*D.error*D.Θ^29)
  positive_pressure : ∀ ξ τ, τ ∈ Icc 1 D.H →
    0 < ⟪D.r ξ (D.time τ),(D.M ξ (D.time τ)) (D.w ξ (D.time τ))⟫_ℝ
  target_positive : 0 < D.targetSize
  target_growth : D.s₀*exp (1/(4*D.σ)) ≤ 4*D.Θ*D.targetSize
  horizon_size : ∀ ξ τ, τ ∈ Icc 1 D.H → D.size ξ τ ≤ 64*exp 6*D.targetSize
  early_size : ∀ ξ τ, τ ∈ Icc 0 1 →
    D.size ξ τ/D.targetSize ≤ 8232*exp 9*D.Θ^5*exp (-(1/(4*D.σ)))
  next_frame :
    |D.nextCoupling/D.a-1| ≤
      D.y^4+D.σ^2*D.y^2+8*D.σ*D.y^3+30000000*neighborStabilityConstant*D.error*D.Θ^40 ∧
    |(D.y⁻¹)^2*D.nextTilt-1| ≤ 1500*D.σ+30000000*neighborStabilityConstant*D.error*D.Θ^40
  compression_bound : D.nextCompression ≤ -(D.targetShear*D.ε)/(10*D.target)+3*(D.G+D.d)
  compression_negative : D.nextCompression < 0
  amplitude_nonneg : 0 ≤ D.amplitude
  amplitude_normalization : D.amplitude*D.targetSize = D.δ*D.hchild
  amplitude_exponential : D.amplitude ≤ (4*D.Θ*D.δ*D.hchild/D.s₀)*exp (-(1/(4*D.σ)))
  amplitude_profile : ∀ τ ∈ Icc 0 D.H, D.amplitude*Z τ ≤ 8*exp 6*D.δ*D.hchild/D.s₀
  amplitude_profile_sup : sSup ((fun τ => D.amplitude*Z τ) '' Icc 0 D.H) ≤ 8*exp 6*D.δ*D.hchild/D.s₀
  physical_profile_continuous :
    ContinuousOn (physicalProfile Z D.t₀ D.a D.ε) (Icc D.t₀ (D.time D.H))
  physical_profile_positive : ∀ t ∈ Icc D.t₀ (D.time D.H), 0 < physicalProfile Z D.t₀ D.a D.ε t
  tangent_propagator : ∀ ξ (u : ℝ → Space),
    (∀ t ∈ D.S, HasDerivWithinAt u
      (-(D.M ξ t) (u t)+(2*⟪D.r ξ t,(D.M ξ t) (u t)⟫_ℝ/‖D.r ξ t‖^2) • D.r ξ t) D.S t) →
    ⟪D.r ξ D.t₀,u D.t₀⟫_ℝ = 0 →
    ∀ s t, s ∈ Icc D.t₀ (D.time D.H) → t ∈ Icc D.t₀ (D.time D.H) → s ≤ t →
      ‖u t‖ ≤ (560*D.Θ^10/D.ε)*
        (physicalProfile Z D.t₀ D.a D.ε t/physicalProfile Z D.t₀ D.a D.ε s)*‖u s‖

theorem PhysicalGeometryData.exists_geometry {α : Type*} (D : PhysicalGeometryData α) :
    ∃ F F₁ Z Z₁ : ℝ → ℝ, PhysicalGeometryConclusion D F F₁ Z Z₁ := by
  have hK : 1 ≤ neighborStabilityConstant :=
    (by norm_num : (1:ℝ) ≤ 1000000000).trans neighborStabilityConstant_ge
  obtain ⟨F, F₁, Z, Z₁, hF0, hF₁0, hZ0, hZ₁0, hF, hZ, hfluxF, hfluxZ, hray, herr, hrel, _⟩ :=
    physical_family_amplification_and_size D.center D.sigma_pos D.sigma_small D.horizon_one
      D.horizon_le_Theta
      D.a_lower D.epsilon_pos D.Theta_lower D.G_lower D.d_nonneg D.ray_scale_pos D.slope_nonneg
        D.small
      D.time_maps D.M_continuous D.B_derivative D.old_ray_equation D.old_velocity_equation
      D.ray_equation D.velocity_equation D.old_ray_nonzero D.old_velocity_nonzero D.old_tangent
      D.initial_tangent D.B_bound D.B_derivative_bound D.E_bound D.parent_decomposition
      D.initial_coupling D.initial_tilt D.initial_shear D.initial_ray_error D.initial_velocity_error
  have hZ₁pos : 0 ≤ Z₁ 0 := by rw [hZ₁0]; exact D.slope_nonneg
  have hZpos := EulerPacketGrowth.equation30_global_positive D.sigma_pos D.sigma_small
    (fun t _ => hZ t) (fun t _ => hfluxZ t) hZ0 hZ₁pos
  have hsub : Icc (1:ℝ) D.H ⊆ Icc 0 D.H := fun _ ht => ⟨by linarith only [ht.1], ht.2⟩
  have htarget : D.target ∈ Icc 0 D.H := ⟨D.target_pos.le, D.target_le_horizon⟩
  have htarget1 : D.target ∈ Icc 1 D.H := ⟨D.target_one, D.target_le_horizon⟩
  have hcoords (ξ : α) (τ : ℝ) (hτ : τ ∈ Icc 0 D.H) :
      |D.ray ξ τ 0-D.σ^2*τ^2| ≤ 800*D.error*D.Θ^5 ∧
      |D.ray ξ τ 1-(-2*D.σ^2*τ)| ≤ 800*D.error*D.Θ^5 ∧
      |D.ray ξ τ 2-1| ≤ 800*D.error*D.Θ^5 := by
    have hh : norm3 (D.ray ξ τ 0-D.σ^2*τ^2) (D.ray ξ τ 1+2*D.σ^2*τ) (D.ray ξ τ 2-1) ≤
        800*D.error*D.Θ^5 := (hray ξ τ hτ).1
    rw [show D.ray ξ τ 1-(-2*D.σ^2*τ) = D.ray ξ τ 1+2*D.σ^2*τ by ring]
    dsimp [norm3] at hh
    constructor
    · linarith only [hh, abs_nonneg (D.ray ξ τ 1+2*D.σ^2*τ), abs_nonneg (D.ray ξ τ 2-1)]
    constructor
    · linarith only [hh, abs_nonneg (D.ray ξ τ 0-D.σ^2*τ^2), abs_nonneg (D.ray ξ τ 2-1)]
    · linarith only [hh, abs_nonneg (D.ray ξ τ 0-D.σ^2*τ^2), abs_nonneg (D.ray ξ τ 1+2*D.σ^2*τ)]
  have htcoords := hcoords D.center D.target htarget
  have htstate := hrel D.center D.target htarget1
  have htframes := D.target_time_mem
  have hsizeTarget := physical_ideal_size_comparison_order40 D.m D.v (D.r D.center) (D.w D.center)
    D.ray_scale_pos D.epsilon_pos D.sigma_pos D.sigma_small
    (D.old_ray_nonzero _ htframes) (D.old_velocity_nonzero _ htframes) (D.old_tangent _ htframes)
    (hray D.center D.target htarget).2.2 D.Theta_lower hK D.error_nonneg D.epsilon_le_error D.small
    D.target_one D.target_le_Theta (fun t _ => hZ t) (fun t _ => hfluxZ t) hZ0 hZ₁pos
    htcoords.1 htcoords.2.1 htcoords.2.2 htstate.2.1 htstate.2.2
  have hgrowth := physical_target_exponential_lower D.m D.v (D.r D.center) (D.w D.center)
    D.ray_scale_pos (ne_of_gt D.epsilon_pos) D.sigma_pos D.sigma_small D.target_from_sigma
      D.target_le_Theta
    (D.old_ray_nonzero _ htframes) (D.old_velocity_nonzero _ htframes) (D.old_tangent _ htframes)
    (hray D.center D.target htarget).2.1 (htstate.2.1.trans D.relative_error_small)
    (fun t _ => hZ t) (fun t _ => hfluxZ t) hZ0 hZ₁pos
  have hsize := physical_horizon_size_bound D.center (fun _ => D.m) (fun _ => D.v) D.r D.w
    D.ray_scale_pos D.epsilon_pos D.sigma_pos D.sigma_small D.target_one D.target_le_horizon
      D.horizon_le_Theta
    D.short_extension D.Theta_lower hK D.error_nonneg D.epsilon_le_error D.small
    (fun _ τ hτ => D.old_ray_nonzero _ (D.time_mem (hsub hτ)))
    (fun _ τ hτ => D.old_velocity_nonzero _ (D.time_mem (hsub hτ)))
    (fun _ τ hτ => D.old_tangent _ (D.time_mem (hsub hτ)))
    (fun ξ τ hτ => (hray ξ τ (hsub hτ)).2.2)
    (fun t _ => hZ t) (fun t _ => hfluxZ t) hZ0 hZ₁pos
    (fun ξ τ hτ => (hcoords ξ τ (hsub hτ)).1)
    (fun ξ τ hτ => (hcoords ξ τ (hsub hτ)).2.1)
    (fun ξ τ hτ => (hcoords ξ τ (hsub hτ)).2.2)
    (fun ξ τ hτ => (hrel ξ τ hτ).2.1) (fun ξ τ hτ => (hrel ξ τ hτ).2.2)
  have htoH : Icc (0:ℝ) D.target ⊆ Icc 0 D.H := fun _ ht => ⟨ht.1, ht.2.trans D.target_le_horizon⟩
  have hearly := early_physical_size_suppression D.center D.m D.v D.r D.w
    D.ray_scale_pos D.epsilon_pos D.epsilon_le_one D.sigma_pos D.sigma_small D.Theta_lower
      D.target_le_Theta
    D.target_from_sigma D.slope_nonneg (show 0 ≤ 400000000*D.error*D.Θ^29 by positivity
      [D.error_nonneg, D.Theta_pos])
    D.scalar_error_small (show 0 ≤ 800*D.error*D.Θ^5 by positivity [D.error_nonneg, D.Theta_pos])
      D.ray_error_small
    (fun τ hτ => D.old_ray_nonzero _ (D.time_mem (htoH hτ)))
    (fun τ hτ => D.old_velocity_nonzero _ (D.time_mem (htoH hτ)))
    (fun τ hτ => D.old_tangent _ (D.time_mem (htoH hτ)))
    (fun ξ τ hτ => (hray ξ τ (htoH hτ)).2.2)
    (fun ξ τ hτ => (hcoords ξ τ (htoH hτ)).1)
    (fun ξ τ hτ => (hcoords ξ τ (htoH hτ)).2.1)
    (fun ξ τ hτ => (hcoords ξ τ (htoH hτ)).2.2)
    hF hZ hfluxF hfluxZ hF0 hF₁0 hZ0 hZ₁0 (fun ξ τ hτ => herr ξ τ (htoH hτ))
  have hPeq : D.σ^2*D.target^2 = (D.y⁻¹)^2 := by
    dsimp [target]
    field_simp [ne_of_gt D.sigma_pos]
  have hQeq : 2*D.σ^2*D.target = 2*D.σ*D.y⁻¹ := by
    dsimp [target]
    field_simp [ne_of_gt D.sigma_pos]
  have hframeP : |D.ray D.center D.target 0-(D.y⁻¹)^2| ≤ 800*D.error*D.Θ^5 := by
    simpa only [hPeq] using htcoords.1
  have hframeQ : |D.ray D.center D.target 1+2*D.σ*D.y⁻¹| ≤ 800*D.error*D.Θ^5 := by
    simpa only [neg_mul, sub_neg_eq_add, hQeq] using htcoords.2.1
  have hframe := physical_frame_renewal_order40 (D.M D.center D.targetTime) D.m D.v (D.r D.center)
    (D.w D.center)
    (ne_of_gt D.a_pos) D.ray_scale_pos D.epsilon_pos
    (D.old_ray_nonzero _ htframes) (D.old_velocity_nonzero _ htframes) (D.old_tangent _ htframes)
    (hray D.center D.target htarget).2.2 htstate.1 D.sigma_pos D.sigma_small D.y_pos D.y_small
    D.Theta_lower hK D.error_nonneg D.epsilon_le_error D.target_le_Theta D.small
    (fun t _ => hZ t) (fun t _ => hfluxZ t) hZ0 hZ₁pos hframeP hframeQ htcoords.2.2 htstate.2.2
    (D.action_error D.center htarget)
  have hcompressQ : |D.ray D.center D.target 1+2*D.σ^2*D.target| ≤ 800*D.error*D.Θ^5 := by
    simpa only [neg_mul, sub_neg_eq_add] using htcoords.2.1
  have hcomp := physical_target_compression (D.B D.targetTime) (D.M D.center D.targetTime)
    (D.E D.center D.targetTime) D.targetShear D.m D.v (D.r D.center)
    (ne_of_gt D.ray_scale_pos) D.epsilon_pos
    (D.old_ray_nonzero _ htframes) (D.old_velocity_nonzero _ htframes) (D.old_tangent _ htframes)
    (D.parent_decomposition D.center _ htframes) (sq_pos_of_pos D.sigma_pos)
    (by nlinarith only [D.sigma_pos, D.sigma_small] : D.σ^2 ≤ 1) D.target_pos D.target_le_Theta
    D.Theta_lower hK D.error_nonneg D.epsilon_le_error D.target_shear_pos.le D.small D.target_scale
    htcoords.1 hcompressQ htcoords.2.2
  have hampProfile := primaryAmplitude_profile_bound (D.r D.center) (D.w D.center)
    (targetTime := D.targetTime) D.delta_nonneg D.child_nonneg D.ray_scale_pos D.sigma_pos
      D.sigma_small
    D.target_one D.short_extension (fun t _ => hZ t) (fun t _ => hfluxZ t) hZ0 hZ₁pos hsizeTarget.1
  have hzcont : ContinuousOn Z (Icc 0 D.H) := fun t ht => (hZ t).continuousAt.continuousWithinAt
  refine ⟨F, F₁, Z, Z₁, {
    initial_values := ⟨hF0, hF₁0, hZ0, hZ₁0⟩
    F_derivative := hF
    Z_derivative := hZ
    F_flux := hfluxF
    Z_flux := hfluxZ
    ray_control := hray
    state_error := herr
    relative_error := hrel
    positive_pressure := ?_
    target_positive := hgrowth.1
    target_growth := hgrowth.2
    horizon_size := hsize
    early_size := hearly.2
    next_frame := hframe
    compression_bound := ?_
    compression_negative := hcomp.2 D.compression_domination
    amplitude_nonneg := primaryAmplitude_nonneg _ _ _ _ _ D.delta_nonneg D.child_nonneg
    amplitude_normalization := primaryAmplitude_target_identity _ _ _ _ _ hgrowth.1
    amplitude_exponential := primaryAmplitude_exponential_bound _ _ D.delta_nonneg D.child_nonneg
      D.ray_scale_pos D.Theta_pos hgrowth.2
    amplitude_profile := hampProfile
    amplitude_profile_sup := ?_
    physical_profile_continuous := physicalProfile_continuousOn D.a_pos D.epsilon_pos hzcont
    physical_profile_positive := physicalProfile_positive D.a_pos D.epsilon_pos (fun t ht => hZpos
      t ht.1)
    tangent_propagator := ?_ }⟩
  · intro ξ τ hτ
    have hp := hcoords ξ τ (hsub hτ)
    have hv := hrel ξ τ hτ
    exact (physical_pressure_positive_order40 (D.M ξ (D.time τ)) D.m D.v (D.r ξ) (D.w ξ)
      D.a_pos D.ray_scale_pos D.epsilon_pos
      (D.old_ray_nonzero _ (D.time_mem (hsub hτ))) (D.old_velocity_nonzero _ (D.time_mem (hsub hτ)))
      (D.old_tangent _ (D.time_mem (hsub hτ))) (hray ξ τ (hsub hτ)).2.2 hv.1
      D.sigma_pos D.sigma_small D.Theta_lower hK D.error_nonneg D.sigma_Theta hτ.1
      (hτ.2.trans D.horizon_le_Theta) D.small (fun t _ => hZ t) (fun t _ => hfluxZ t) hZ0 hZ₁pos
      hp.1 hp.2.1 hp.2.2 hv.2.2 (D.action_error ξ (hsub hτ))).2
  · have hn := add_le_add (D.B_bound _ htframes) (D.E_bound D.center _ htframes)
    exact hcomp.1.trans (by nlinarith only [hn])
  · apply csSup_le
    · exact ⟨D.amplitude*Z 0, 0, ⟨le_rfl, D.horizon_pos.le⟩, rfl⟩
    · rintro _ ⟨τ, hτ, rfl⟩
      exact hampProfile τ hτ
  · intro ξ u hu hutangent
    have hp := physical_tangent_propagator D.sigma_pos D.sigma_small D.horizon_pos
      D.horizon_le_Theta
      D.a_lower D.epsilon_pos D.Theta_lower D.G_lower D.d_nonneg (ne_of_gt D.ray_scale_pos)
      D.propagator_small D.time_maps (D.M_continuous ξ) D.B_derivative D.old_ray_equation
        D.old_velocity_equation
      (D.ray_equation ξ) hu D.old_ray_nonzero D.old_velocity_nonzero D.old_tangent hutangent
      D.B_bound D.B_derivative_bound (D.E_bound ξ) (D.parent_decomposition ξ) D.initial_coupling
        D.initial_tilt
      D.initial_shear (D.initial_ray_error ξ) (fun t _ => hZ t) (fun t _ => hfluxZ t) hZ0 hZ₁pos
    exact physical_propagation_of_scaled u Z D.a_pos D.epsilon_pos hp.2.2

end EulerPacketMovingFrame
