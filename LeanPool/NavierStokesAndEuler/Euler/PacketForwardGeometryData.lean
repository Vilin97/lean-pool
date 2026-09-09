/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceGeometryAssembly
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardFactorization

@[expose] public section

/-! The first amplification stage starts at time zero. Its primary is
the actual homogeneous forward solution with a fixed initial coordinate;
no stationary-history solve is used in this stage. -/

noncomputable section

namespace EulerPacketSourceGeometry

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransversePacketProvider EulerPacketMovingFrame EulerPacketNormalizedPrimary
  EulerPacketCrossProduct EulerTransverseFrameCoordinates EulerPacketRay
  EulerPacketForwardFactorization

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {D : Data U}

def ParentFrame.forwardError (P : ParentFrame D 0) (radius : ℝ) : ℝ :=
  P.error+‖D.M.derivative.field‖*radius

structure ForwardGuards (P : ParentFrame D 0) where
  radius : ℝ
  y : ℝ
  δ : ℝ
  hchild : ℝ
  radius_nonneg : 0 ≤ radius
  delta_nonneg : 0 ≤ δ
  child_nonneg : 0 ≤ hchild
  coupling_lower : 1/2 ≤ P.a
  shear_pos : 0 < P.shear
  sigma_pos : 0 < P.sigma
  sigma_small : P.sigma ≤ 1/4
  y_pos : 0 < y
  y_small : y ≤ 1/2
  target_le_horizon : y⁻¹/P.sigma ≤ P.horizon
  horizon_lower : 1 ≤ P.horizon
  short_extension : P.horizon-y⁻¹/P.sigma ≤ 1
  small : 1000000*neighborStabilityConstant*
    (16*(P.epsilon*P.horizon*(4*P.G)^2+P.forwardError radius))*P.horizon^40 ≤ 1
  compression_guard : 60*(P.G+P.forwardError radius)*(y⁻¹/P.sigma)*P.epsilon < P.a
  initial_frame : ∀ x, D.F.field ⟨0,le_rfl,D.T_pos.le⟩ x=ContinuousLinearMap.id ℝ Space
  normal_choice : D.m₀=cross (unit (P.m 0)) (unit (P.v 0))

namespace ForwardGuards

variable {P : ParentFrame D 0} (G : ForwardGuards P)

include G in
theorem a_pos : 0 < P.a := by linarith only [G.coupling_lower]

include G in
theorem epsilon_pos : 0 < P.epsilon :=
  Real.sqrt_pos.mpr (div_pos G.a_pos G.shear_pos)

theorem error_nonneg : 0 ≤ P.forwardError G.radius :=
  add_nonneg P.error_nonneg (mul_nonneg (norm_nonneg _) G.radius_nonneg)

def initialCoordinate : U := D.R.symm
  ⟨unit (P.v 0),Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (by
    rw [G.normal_choice,real_inner_comm]
    exact inner_cross_second _ _)⟩

theorem initialCoordinate_map : (D.R G.initialCoordinate : Space)=unit (P.v 0) := by
  exact congrArg (fun z : referencePlane D.m₀ => (z : Space)) (D.R.apply_symm_apply _)

theorem initialCoordinate_norm : ‖G.initialCoordinate‖=1 := by
  rw [← D.R.norm_map G.initialCoordinate]
  change ‖(D.R G.initialCoordinate : Space)‖=1
  rw [G.initialCoordinate_map]
  exact unit_norm (P.velocity_nonzero 0 ⟨le_rfl,D.T_pos.le⟩)

theorem initialCoordinate_ne_zero : G.initialCoordinate ≠ 0 := by
  intro hz
  have h := G.initialCoordinate_norm
  rw [hz,norm_zero] at h
  norm_num at h

include G in
theorem initial_inverse (x : Space) :
    D.FInv.field ⟨0,le_rfl,D.T_pos.le⟩ x=ContinuousLinearMap.id ℝ Space := by
  apply ContinuousLinearMap.ext
  intro v
  have h := D.inverse_left ⟨0,le_rfl,D.T_pos.le⟩ x v
  simpa only [G.initial_frame,ContinuousLinearMap.id_apply] using h

include G in
theorem initial_normal (x : Space) : sourceRay D x 0=cross (unit (P.m 0)) (unit (P.v 0)) := by
  change (D.FInv.field (D.clamp 0) x).adjoint D.m₀=_
  rw [show D.clamp 0=⟨0,le_rfl,D.T_pos.le⟩ from Data.clamp_coe D ⟨0,le_rfl,D.T_pos.le⟩,
    G.initial_inverse,adjoint_id,ContinuousLinearMap.id_apply,G.normal_choice]

variable [CompleteSpace U]

def sourceVelocity (x : Space) (t : ℝ) : Space :=
  EulerPacketForwardFactorization.uncutVelocity D G.initialCoordinate t x

theorem initial_velocity (x : Space) : G.sourceVelocity x 0=unit (P.v 0) := by
  rw [sourceVelocity,uncutVelocity_initial]
  change D.F.field ⟨0,le_rfl,D.T_pos.le⟩ x (D.R G.initialCoordinate)=_
  rw [G.initial_frame,ContinuousLinearMap.id_apply,G.initialCoordinate_map]

theorem sourceVelocity_equation (x : Space) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (G.sourceVelocity x)
      (-(sourceMatrix D x t) (G.sourceVelocity x t)+
        (2*⟪sourceRay D x t,(sourceMatrix D x t) (G.sourceVelocity x t)⟫_ℝ/
          ‖sourceRay D x t‖^2) • sourceRay D x t) (Icc (0 : ℝ) D.T) t := by
  have h := uncutVelocity_equation D G.initialCoordinate ⟨t,ht⟩ x
  rw [EulerPacketPrimaryFactorization.physicalGenerator_apply] at h
  have hc : D.clamp t=⟨t,ht⟩ := Data.clamp_coe D ⟨t,ht⟩
  unfold sourceVelocity sourceMatrix sourceRay
  rw [hc]
  exact h

omit [CompleteSpace U] in
theorem sourceRay_equation (x : Space) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (sourceRay D x) (-(sourceMatrix D x t).adjoint (sourceRay D x t))
      (Icc (0 : ℝ) D.T) t := by
  have h := EulerPacketPrimaryFactorization.canonicalNormal_equation (D := D) ⟨t,ht⟩ x
  have hc : D.clamp t=⟨t,ht⟩ := Data.clamp_coe D ⟨t,ht⟩
  unfold sourceMatrix sourceRay
  rw [hc]
  exact h

theorem initial_tangent (x : Space) : ⟪sourceRay D x 0,G.sourceVelocity x 0⟫_ℝ=0 := by
  rw [G.initial_normal,G.initial_velocity,real_inner_comm]
  exact inner_cross_second _ _

omit [CompleteSpace U] in
include G in
theorem scaled_ray_initial (x : Space) :
    scaledRay P.m P.v (sourceRay D x) 1 0 P.a P.epsilon 0=![0,0,1] :=
  scaledRay_initial one_ne_zero (P.ray_nonzero 0 ⟨le_rfl,D.T_pos.le⟩)
    (P.velocity_nonzero 0 ⟨le_rfl,D.T_pos.le⟩) (P.tangent 0 ⟨le_rfl,D.T_pos.le⟩)
    (by simpa only [one_smul] using G.initial_normal x)

theorem scaled_velocity_initial (x : Space) :
    scaledVelocity P.m P.v (G.sourceVelocity x) 0 P.a P.epsilon 0 0=0 ∧
    scaledVelocity P.m P.v (G.sourceVelocity x) 0 P.a P.epsilon 0 1=1 := by
  have hp : ⟪unit (P.m 0),G.sourceVelocity x 0⟫_ℝ=0 := by
    rw [G.initial_velocity]
    exact unit_inner_zero (P.tangent 0 ⟨le_rfl,D.T_pos.le⟩)
  have hq : ⟪unit (P.v 0),G.sourceVelocity x 0⟫_ℝ=1 := by
    rw [G.initial_velocity]
    exact unit_inner_self (P.velocity_nonzero 0 ⟨le_rfl,D.T_pos.le⟩)
  have h := activation_scaled_velocity (a := P.a) G.epsilon_pos
    (show -(0 : ℝ) ≤ 0 by norm_num) le_rfl hp hq
  simpa only [neg_zero,zero_div] using h.2.2

omit [CompleteSpace U] in
theorem sourceError_bound (x : Space) (hx : ‖x‖ ≤ G.radius)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D.T) : ‖P.sourceError x t‖ ≤ P.forwardError G.radius := by
  have hd := EulerPacketActivationHistory.coefficient_difference D.M (D.clamp t) x 0
  rw [sub_zero] at hd
  have hr := P.remainder_bound t ht
  calc
    ‖P.sourceError x t‖ = ‖(sourceMatrix D x t-sourceMatrix D 0 t)+P.sourceError 0 t‖ := by
      congr 1
      unfold ParentFrame.sourceError
      module
    _ ≤ ‖sourceMatrix D x t-sourceMatrix D 0 t‖+‖P.sourceError 0 t‖ := norm_add_le _ _
    _ ≤ ‖D.M.derivative.field‖*‖x‖+P.error := add_le_add hd hr
    _ ≤ ‖D.M.derivative.field‖*G.radius+P.error :=
      add_le_add (mul_le_mul_of_nonneg_left hx (norm_nonneg _)) le_rfl
    _ = P.forwardError G.radius := by unfold ParentFrame.forwardError; ring

end ForwardGuards
end EulerPacketSourceGeometry
