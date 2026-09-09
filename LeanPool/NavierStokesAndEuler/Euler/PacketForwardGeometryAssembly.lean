/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardGeometryData
public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometrySourceGrowth

@[expose] public section

/-! The first normal stage satisfies the full physical amplification
geometry. The source normal, primary and all ODEs are the actual forward
fields, including exact initial data at time zero. -/

noncomputable section

namespace EulerPacketSourceGeometry.ForwardGuards

open Set InnerProductSpace EulerSmoothLimit EulerTransversePacketProvider
  EulerPacketMovingFrame EulerPacketNormalizedPrimary EulerPacketRay
  EulerPacketGeometrySourceGrowth EulerPacketSourcePropagator

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {P : ParentFrame D 0} (G : ForwardGuards P)

omit [CompleteSpace U] in
theorem error_le_scaled_error : P.forwardError G.radius ≤
    16*(P.epsilon*P.horizon*(4*P.G)^2+P.forwardError G.radius) := by
  have he := G.error_nonneg
  have hbase : 0 ≤ P.epsilon*P.horizon*(4*P.G)^2 :=
    mul_nonneg (mul_nonneg G.epsilon_pos.le (zero_le_one.trans G.horizon_lower)) (sq_nonneg _)
  linarith only [he,hbase]

def geometryData (Ω : Set Space) (h0 : 0 ∈ Ω) (hΩ : ∀ x ∈ Ω, ‖x‖ ≤ G.radius) :
    PhysicalGeometryData {x : Space // x ∈ Ω} where
  center := ⟨0,h0⟩
  B := P.B
  B₁ := P.B₁
  M := fun x => sourceMatrix D x
  E := fun x => P.sourceError x
  m := P.m
  v := P.v
  r := fun x => sourceRay D x
  w := fun x => G.sourceVelocity x
  c := P.c
  s₀ := 1
  t₀ := 0
  a := P.a
  ε := P.epsilon
  σ := P.sigma
  y := G.y
  Θ := P.horizon
  H := P.horizon
  G := P.G
  d := P.forwardError G.radius
  lam := 0
  δ := G.δ
  hchild := G.hchild
  S := Icc 0 D.T
  sigma_pos := G.sigma_pos
  sigma_small := G.sigma_small
  y_pos := G.y_pos
  y_small := G.y_small
  target_le_horizon := G.target_le_horizon
  horizon_le_Theta := le_rfl
  short_extension := G.short_extension
  a_lower := G.coupling_lower
  epsilon_pos := G.epsilon_pos
  Theta_lower := G.horizon_lower
  G_lower := P.G_lower
  d_nonneg := G.error_nonneg
  ray_scale_pos := zero_lt_one
  slope_nonneg := le_rfl
  delta_nonneg := G.delta_nonneg
  child_nonneg := G.child_nonneg
  small := G.small
  compression_guard := G.compression_guard
  time_maps := activation_horizon_maps 0 D.T P.a P.epsilon G.a_pos G.epsilon_pos
  M_continuous := fun x => (sourceMatrix_continuous D x).continuousOn
  B_derivative := P.B_derivative
  old_ray_equation := P.ray_equation
  old_velocity_equation := P.velocity_equation
  ray_equation := fun x t ht => ForwardGuards.sourceRay_equation x t ht
  velocity_equation := fun x t ht => G.sourceVelocity_equation x t ht
  old_ray_nonzero := P.ray_nonzero
  old_velocity_nonzero := P.velocity_nonzero
  old_tangent := P.tangent
  initial_tangent := fun x => G.initial_tangent x
  B_bound := P.B_bound
  B_derivative_bound := P.B₁_bound
  E_bound := fun x t ht => G.sourceError_bound x (hΩ x x.property) t ht
  parent_decomposition := by
    intro x t _
    unfold ParentFrame.sourceError
    module
  initial_coupling := activation_coupling_match P.B P.m P.v 0 P.epsilon
  initial_tilt := activation_tilt_match P.B P.m P.v 0 P.epsilon G.a_pos.ne'
    (Real.sqrt_pos.mp G.sigma_pos).le
  initial_shear := (activation_shear_match P.c P.m P.v 0 P.a G.a_pos G.shear_pos).2
  initial_ray_error := by
    intro x
    rw [G.scaled_ray_initial]
    change |(0 : ℝ)|+|0|+|(1 : ℝ)-1| ≤ _
    norm_num only [abs_zero,sub_self,add_zero]
    exact G.error_nonneg.trans G.error_le_scaled_error
  initial_velocity_error := by
    intro x
    rw [(G.scaled_velocity_initial x).1,(G.scaled_velocity_initial x).2]
    norm_num only [sub_self,zero_add,abs_zero,add_zero]
    exact G.error_nonneg.trans G.error_le_scaled_error

theorem source_interval (Ω : Set Space) (h0 : 0 ∈ Ω) (hΩ : ∀ x ∈ Ω, ‖x‖ ≤ G.radius) :
    (G.geometryData Ω h0 hΩ).S=Icc (G.geometryData Ω h0 hΩ).t₀
      ((G.geometryData Ω h0 hΩ).t₀+D.T) := by
  change Icc 0 D.T=Icc 0 (0+D.T)
  rw [zero_add]

theorem source_horizon (Ω : Set Space) (h0 : 0 ∈ Ω) (hΩ : ∀ x ∈ Ω, ‖x‖ ≤ G.radius) :
    (G.geometryData Ω h0 hΩ).time (G.geometryData Ω h0 hΩ).H =
      (G.geometryData Ω h0 hΩ).t₀+D.T := by
  change physicalTime 0 P.a P.epsilon (P.a*(D.T-0)/P.epsilon)=0+D.T
  rw [activation_horizon_exact 0 D.T P.a P.epsilon G.a_pos.ne' G.epsilon_pos.ne',zero_add]

theorem exists_geometry_and_growth (Ω : Set Space) (h0 : 0 ∈ Ω)
    (hΩ : ∀ x ∈ Ω, ‖x‖ ≤ G.radius) :
    ∃ F F₁ Z Z₁ : ℝ → ℝ,
      ∃ J : PhysicalGeometryConclusion (G.geometryData Ω h0 hΩ) F F₁ Z Z₁,
        (∀ t, 0 < growthProfile D (G.geometryData Ω h0 hΩ) J t) ∧
        growthProfile D (G.geometryData Ω h0 hΩ) J ⟨0,le_rfl,D.T_pos.le⟩=1 ∧
        PhysicalGrowth D Ω (growthProfile D (G.geometryData Ω h0 hΩ) J)
          (560*P.horizon^10/P.epsilon) := by
  obtain ⟨F,F₁,Z,Z₁,J⟩ := (G.geometryData Ω h0 hΩ).exists_geometry
  refine ⟨F,F₁,Z,Z₁,J,
    growthProfile_pos D _ J (G.source_horizon Ω h0 hΩ),growthProfile_initial D _ J,?_⟩
  apply physicalGrowth_of_geometry D _ J (G.source_interval Ω h0 hΩ) (G.source_horizon Ω h0 hΩ)
  · intro x t
    change D.M.field (D.clamp (0+t)) x=D.M.field t x
    rw [zero_add,Data.clamp_coe]
  · intro x t
    change D.normal.field (D.clamp (0+t)) x=D.normal.field t x
    rw [zero_add,Data.clamp_coe]

theorem halfBall_physicalGrowth (hball : (1/2 : ℝ) ≤ G.radius) :
    ∃ g : C(Icc (0 : ℝ) D.T,ℝ), (∀ t, 0 < g t) ∧
      g ⟨0,le_rfl,D.T_pos.le⟩=1 ∧
      PhysicalGrowth D {x | ‖x‖ ≤ (1/2 : ℝ)} g (560*P.horizon^10/P.epsilon) := by
  obtain ⟨F,F₁,Z,Z₁,J,hpos,hzero,hgrowth⟩ :=
    G.exists_geometry_and_growth {x | ‖x‖ ≤ (1/2 : ℝ)} (by simp)
      (fun _ hx => hx.trans hball)
  exact ⟨_,hpos,hzero,hgrowth⟩

end EulerPacketSourceGeometry.ForwardGuards
