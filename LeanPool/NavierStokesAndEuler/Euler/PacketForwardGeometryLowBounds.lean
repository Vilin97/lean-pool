/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardGeometryData
public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometrySourceGrowth

/-! The actual forward primary has the same universal good-time size
and pressure sign as the joined primary. At time zero and on the early
interval its size has the exponential target-ratio gain. -/

section

/-! The first normal stage satisfies the full physical amplification
geometry. The source normal, primary and all ODEs are the actual forward
fields, including exact initial data at time zero. -/

@[expose] public section

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

/-- Geometry data, bundling `center`, `B`, `B₁`, `M` and the required compatibility proofs. -/
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

theorem halfBall_physicalGrowth (hball : (1 / 2 : ℝ) ≤ G.radius) :
    ∃ g : C(Icc (0 : ℝ) D.T,ℝ), (∀ t, 0 < g t) ∧
      g ⟨0,le_rfl,D.T_pos.le⟩=1 ∧
      PhysicalGrowth D {x | ‖x‖ ≤ (1/2 : ℝ)} g (560*P.horizon^10/P.epsilon) := by
  obtain ⟨F,F₁,Z,Z₁,J,hpos,hzero,hgrowth⟩ :=
    G.exists_geometry_and_growth {x | ‖x‖ ≤ (1/2 : ℝ)} (by simp)
      (fun _ hx => hx.trans hball)
  exact ⟨_,hpos,hzero,hgrowth⟩

end EulerPacketSourceGeometry.ForwardGuards

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketSourceGeometry.ForwardGuards

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerSpatialCutoffs
  EulerPacketMovingFrame EulerTransversePacketProvider EulerPacketGeometryLowBounds
  EulerPacketForwardFactorization

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {P : ParentFrame D 0} (G : ForwardGuards P)
  (hball : (1 / 2 : ℝ) ≤ G.radius)

/-- Low geometry, given by `G.geometryData {x | ‖x‖ ≤ (1/2 : ℝ)} (by norm_num) (fun _ hx =>
hx.trans hball)`. -/
def lowGeometry : PhysicalGeometryData {x : Space // ‖x‖ ≤ (1/2 : ℝ)} :=
  G.geometryData {x | ‖x‖ ≤ (1/2 : ℝ)} (by norm_num) (fun _ hx => hx.trans hball)

/-- Primary amplitude, given by `(G.lowGeometry hball).amplitude`. -/
def primaryAmplitude : ℝ := (G.lowGeometry hball).amplitude

theorem primaryAmplitude_nonneg : 0 ≤ G.primaryAmplitude hball :=
  EulerPacketGeometryLowBounds.amplitude_nonneg (G.lowGeometry hball)

/-- Early ratio, given by `cutoffBound*(8232*Real.exp 9*P.horizon^5*Real.exp
(-(1/(4*P.sigma))))`. -/
def earlyRatio (_G : ForwardGuards P) : ℝ :=
  cutoffBound*(8232*Real.exp 9*P.horizon^5*Real.exp (-(1/(4*P.sigma))))

omit [CompleteSpace U] in
theorem earlyRatio_nonneg : 0 ≤ G.earlyRatio := by
  unfold earlyRatio
  positivity [cutoffBound_pos,G.horizon_lower]

include G in
omit [CompleteSpace U] in
theorem scaledTime_mem (t : Icc (0 : ℝ) D.T) :
    scaledTime 0 P.a P.epsilon t ∈ Icc 0 P.horizon := by
  have ha := G.a_pos
  have he := G.epsilon_pos
  constructor
  · unfold scaledTime
    exact mul_nonneg (div_nonneg ha.le he.le) (by simpa using t.property.1)
  · have hh := mul_le_mul_of_nonneg_left t.property.2 (div_nonneg ha.le he.le)
    calc
      _ = (P.a/P.epsilon)*(t : ℝ) := by unfold scaledTime; ring
      _ ≤ (P.a/P.epsilon)*D.T := hh
      _ = _ := by unfold ParentFrame.horizon; ring

theorem lowGeometry_size (t : Icc (0 : ℝ) D.T) (x : Space) (hx : ‖x‖ ≤ (1 / 2 : ℝ)) :
    (G.lowGeometry hball).size ⟨x,hx⟩ (scaledTime 0 P.a P.epsilon t) =
      ‖D.normal.field t x‖*‖uncutVelocity D G.initialCoordinate t x‖ := by
  change ‖D.normal.field (D.clamp (physicalTime 0 P.a P.epsilon (scaledTime 0 P.a P.epsilon t))) x‖*
    ‖uncutVelocity D G.initialCoordinate (physicalTime 0 P.a P.epsilon (scaledTime 0 P.a P.epsilon
        t)) x‖ = _
  rw [physicalTime_scaledTime G.a_pos.ne' G.epsilon_pos.ne',Data.clamp_coe]

theorem cutoff_amplitude_size (t : Icc (0 : ℝ) D.T) (x : Space) :
    G.primaryAmplitude hball*(‖D.normal.field t x‖*‖canonicalVelocity D G.initialCoordinate t x‖) =
      innerCutoff x*(G.primaryAmplitude hball*(‖D.normal.field t x‖*‖uncutVelocity D
          G.initialCoordinate t x‖)) := by
  rw [canonicalVelocity,norm_smul,Real.norm_of_nonneg (innerCutoff_nonneg x)]
  ring

theorem good_primary_size (t : Icc (0 : ℝ) D.T)
    (ht : 1 ≤ scaledTime 0 P.a P.epsilon t) (x : Space) :
    G.primaryAmplitude hball*(‖D.normal.field t x‖*‖canonicalVelocity D G.initialCoordinate t x‖) ≤
      G.δ*G.hchild*goodRatio := by
  rw [G.cutoff_amplitude_size hball t x]
  by_cases hcut : innerCutoff x=0
  · rw [hcut,zero_mul]
    positivity [G.delta_nonneg,G.child_nonneg,goodRatio_pos]
  have hx : ‖x‖ ≤ (1/2 : ℝ) := by
    have hm := innerCutoff_support (subset_tsupport _ (Function.mem_support.mpr hcut))
    exact le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using hm)
  have hg := good_amplitude_size (G.lowGeometry hball) ⟨x,hx⟩ (scaledTime 0 P.a P.epsilon t)
    ⟨ht,(G.scaledTime_mem t).2⟩
  rw [G.lowGeometry_size hball t x hx] at hg
  change G.primaryAmplitude hball*(‖D.normal.field t x‖*‖uncutVelocity D G.initialCoordinate t x‖) ≤
    G.δ*G.hchild*(64*Real.exp 6) at hg
  calc
    _ ≤ innerCutoff x*(G.δ*G.hchild*(64*Real.exp 6)) :=
      mul_le_mul_of_nonneg_left hg (innerCutoff_nonneg x)
    _ ≤ cutoffBound*(G.δ*G.hchild*(64*Real.exp 6)) :=
      mul_le_mul_of_nonneg_right (cutoff_le x) (by positivity [G.delta_nonneg,G.child_nonneg])
    _ = _ := by unfold goodRatio; ring

include hball in
theorem good_primary_flux (t : Icc (0 : ℝ) D.T)
    (ht : 1 ≤ scaledTime 0 P.a P.epsilon t) (x : Space) :
    0 ≤ ⟪D.normal.field t x,D.M.field t x (canonicalVelocity D G.initialCoordinate t x)⟫_ℝ := by
  rw [canonicalVelocity,map_smul,real_inner_smul_right]
  by_cases hcut : innerCutoff x=0
  · simp only [hcut,zero_mul,le_refl]
  have hx : ‖x‖ ≤ (1/2 : ℝ) := by
    have hm := innerCutoff_support (subset_tsupport _ (Function.mem_support.mpr hcut))
    exact le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using hm)
  have hg := good_flux (G.lowGeometry hball) ⟨x,hx⟩ (scaledTime 0 P.a P.epsilon t)
    ⟨ht,(G.scaledTime_mem t).2⟩
  change 0 < ⟪D.normal.field (D.clamp (physicalTime 0 P.a P.epsilon (scaledTime 0 P.a P.epsilon
      t))) x,
    D.M.field (D.clamp (physicalTime 0 P.a P.epsilon (scaledTime 0 P.a P.epsilon t))) x
      (uncutVelocity D G.initialCoordinate (physicalTime 0 P.a P.epsilon (scaledTime 0 P.a
          P.epsilon t)) x)⟫_ℝ at hg
  rw [physicalTime_scaledTime G.a_pos.ne' G.epsilon_pos.ne',Data.clamp_coe] at hg
  exact mul_nonneg (innerCutoff_nonneg x) hg.le

theorem early_primary_size (t : Icc (0 : ℝ) D.T)
    (ht : scaledTime 0 P.a P.epsilon t ≤ 1) (x : Space) :
    G.primaryAmplitude hball*(‖D.normal.field t x‖*‖canonicalVelocity D G.initialCoordinate t x‖) ≤
      G.δ*G.hchild*G.earlyRatio := by
  rw [G.cutoff_amplitude_size hball t x]
  by_cases hcut : innerCutoff x=0
  · rw [hcut,zero_mul]
    positivity [G.delta_nonneg,G.child_nonneg,G.earlyRatio_nonneg]
  have hx : ‖x‖ ≤ (1/2 : ℝ) := by
    have hm := innerCutoff_support (subset_tsupport _ (Function.mem_support.mpr hcut))
    exact le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using hm)
  have hg := early_amplitude_size (G.lowGeometry hball) ⟨x,hx⟩ (scaledTime 0 P.a P.epsilon t)
    ⟨(G.scaledTime_mem t).1,ht⟩
  rw [G.lowGeometry_size hball t x hx] at hg
  change G.primaryAmplitude hball*(‖D.normal.field t x‖*‖uncutVelocity D G.initialCoordinate t x‖) ≤
    G.δ*G.hchild*(8232*Real.exp 9*P.horizon^5*Real.exp (-(1/(4*P.sigma)))) at hg
  calc
    _ ≤ innerCutoff x*(G.δ*G.hchild*(8232*Real.exp 9*P.horizon^5*Real.exp (-(1/(4*P.sigma))))) :=
      mul_le_mul_of_nonneg_left hg (innerCutoff_nonneg x)
    _ ≤ cutoffBound*(G.δ*G.hchild*(8232*Real.exp 9*P.horizon^5*Real.exp (-(1/(4*P.sigma))))) :=
      mul_le_mul_of_nonneg_right (cutoff_le x) (by
          positivity [G.delta_nonneg,G.child_nonneg,G.horizon_lower])
    _ = _ := by unfold earlyRatio; ring

end EulerPacketSourceGeometry.ForwardGuards
