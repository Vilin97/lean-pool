/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceGeometryData
public import LeanPool.NavierStokesAndEuler.Euler.PacketActivationNeighbor

@[expose] public section

/-! The actual source ray and selected primary satisfy every analytic
field of `PhysicalGeometryData`.  Neighbor errors follow from the source
coefficient derivatives and the genuine stationary-history estimate. -/

noncomputable section

namespace EulerPacketSourceGeometry

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransversePacketProvider EulerPacketMovingFrame EulerPacketNormalizedPrimary
  EulerPacketCrossProduct EulerPacketActivationHistory EulerTransverseActivationSelection
  EulerPacketPrimaryFactorization EulerPacketRay EulerVolterraConvolution
  EulerTransverseSourceCoefficientPath

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

def sourceMatrix (D : Data U) (x : Space) (t : ℝ) : Space →L[ℝ] Space := D.M.field (D.clamp t) x
def sourceRay (D : Data U) (x : Space) (t : ℝ) : Space := D.normal.field (D.clamp t) x

theorem sourceMatrix_continuous (D : Data U) (x : Space) : Continuous (sourceMatrix D x) :=
  extendPath_continuous D.T D.T_pos.le (pathEvaluation x D.M.field)

variable [CompleteSpace U] {D : Data U} {τ : ℝ}
  {hτ : 0 < τ} {hτT : τ < D.T} {P : ParentFrame D τ}
  {H : HistoryData (D.initial τ hτ hτT.le)}

def ParentFrame.sourceError (x : Space) (t : ℝ) : Space →L[ℝ] Space :=
  sourceMatrix D x t-P.B t-primaryShear P.c P.m P.v t • rankOne ℝ (unit (P.v t)) (unit (P.m t))

namespace Guards

variable (A : Guards hτ hτT P H)

def sourceVelocity (x : Space) (t : ℝ) : Space := uncutVelocity τ hτ hτT H A.terminal t x

omit [CompleteSpace U] in
include hτ in
theorem sourceRay_equation (x : Space) (t : ℝ) (ht : t ∈ Icc τ D.T) :
    HasDerivWithinAt (sourceRay D x) (-(sourceMatrix D x t).adjoint (sourceRay D x t))
      (Icc τ D.T) t := by
  have hsub : Icc τ D.T ⊆ Icc (0 : ℝ) D.T := fun _ hs => ⟨hτ.le.trans hs.1,hs.2⟩
  have hclamp : D.clamp t=⟨t,hsub ht⟩ := Data.clamp_coe D ⟨t,hsub ht⟩
  change HasDerivWithinAt (fun s => D.normal.field (D.clamp s) x)
    (-(D.M.field (D.clamp t) x).adjoint (D.normal.field (D.clamp t) x)) (Icc τ D.T) t
  rw [hclamp]
  exact (canonicalNormal_equation (D := D) ⟨t,hsub ht⟩ x).mono hsub

theorem sourceVelocity_equation (x : Space) (t : ℝ) (ht : t ∈ Icc τ D.T) :
    HasDerivWithinAt (A.sourceVelocity x)
      (-(sourceMatrix D x t) (A.sourceVelocity x t)+
        (2*⟪sourceRay D x t,(sourceMatrix D x t) (A.sourceVelocity x t)⟫_ℝ/
          ‖sourceRay D x t‖^2) • sourceRay D x t) (Icc τ D.T) t := by
  have hsub : Icc τ D.T ⊆ Icc (0 : ℝ) D.T := fun _ hs => ⟨hτ.le.trans hs.1,hs.2⟩
  have hclamp : D.clamp t=⟨t,hsub ht⟩ := Data.clamp_coe D ⟨t,hsub ht⟩
  unfold sourceVelocity sourceRay sourceMatrix
  rw [hclamp]
  have he := (uncutVelocity_equation τ hτ hτT H A.terminal ⟨t,hsub ht⟩ x).mono hsub
  rw [EulerPacketPrimaryFactorization.physicalGenerator_apply] at he
  exact he

theorem source_initial_tangent (x : Space) : ⟪sourceRay D x τ,A.sourceVelocity x τ⟫_ℝ=0 := by
  have hclamp : D.clamp τ=⟨τ,hτ.le,hτT.le⟩ := Data.clamp_coe D ⟨τ,hτ.le,hτT.le⟩
  simpa only [sourceRay,sourceVelocity,hclamp] using
    uncutVelocity_tangent τ hτ hτT H A.terminal ⟨τ,hτ.le,hτT.le⟩ x

theorem sourceVelocity_ne_zero (x : Space) (t : Icc (0 : ℝ) D.T) : A.sourceVelocity x t ≠ 0 :=
  uncutVelocity_ne_zero τ hτ hτT H A.terminal A.terminal_properties.1 t x

omit [CompleteSpace U] in
theorem neighbor_components :
    ‖D.M.derivative.field‖ ≤ P.neighborCost hτ hτT H A.CM A.CH ∧
      3*‖D.normal.derivative.field‖/(P.rayScale hτ hτT*P.epsilon) ≤
        P.neighborCost hτ hτT H A.CM A.CH ∧
      2*historyLabelDifferenceCost H*P.terminalBound A.CM A.CH/P.epsilon ≤
        P.neighborCost hτ hτT H A.CM A.CH := by
  have hs := rayScale_pos hτ hτT P
  have he := A.epsilon_pos
  have ht := A.terminalBound_nonneg
  have hc := historyLabelDifferenceCost_nonneg H
  have hn := norm_nonneg (D.M.derivative.field)
  have hr : 0 ≤ 3*‖D.normal.derivative.field‖/(P.rayScale hτ hτT*P.epsilon) := by positivity
  have hv : 0 ≤ 2*historyLabelDifferenceCost H*P.terminalBound A.CM A.CH/P.epsilon := by positivity
  unfold ParentFrame.neighborCost
  constructor
  · linarith only [hr,hv]
  constructor <;> linarith only [hn,hr,hv]

omit [CompleteSpace U] in
theorem radius_cost_le_error : P.neighborCost hτ hτT H A.CM A.CH*A.radius ≤
    P.totalError hτ hτT H A.CM A.CH A.radius := by
  change _ ≤ P.error+_
  linarith only [P.error_nonneg]

omit [CompleteSpace U] in
theorem sourceError_bound (x : Space) (hx : ‖x‖ ≤ A.radius) (t : ℝ) (ht : t ∈ Icc τ D.T) :
    ‖P.sourceError x t‖ ≤ P.totalError hτ hτT H A.CM A.CH A.radius := by
  have hd := coefficient_difference D.M (D.clamp t) x 0
  rw [sub_zero] at hd
  have hr := P.remainder_bound t ht
  have hm := mul_le_mul A.neighbor_components.1 hx (norm_nonneg x) A.neighborCost_nonneg
  calc
    ‖P.sourceError x t‖ = ‖(sourceMatrix D x t-sourceMatrix D 0 t)+P.sourceError 0 t‖ := by
      congr 1
      unfold ParentFrame.sourceError
      module
    _ ≤ ‖sourceMatrix D x t-sourceMatrix D 0 t‖+‖P.sourceError 0 t‖ := norm_add_le _ _
    _ ≤ ‖D.M.derivative.field‖*‖x‖+P.error := add_le_add hd hr
    _ ≤ P.neighborCost hτ hτT H A.CM A.CH*A.radius+P.error := add_le_add hm le_rfl
    _ = P.totalError hτ hτT H A.CM A.CH A.radius := by unfold ParentFrame.totalError; ring

theorem source_velocity_initial_error (x : Space) (hx : ‖x‖ ≤ A.radius) :
    |scaledVelocity P.m P.v (A.sourceVelocity x) τ P.a P.epsilon 0 1-1|+
      |scaledVelocity P.m P.v (A.sourceVelocity x) τ P.a P.epsilon 0 0+A.slope| ≤
      P.totalError hτ hτT H A.CM A.CH A.radius := by
  have hp := A.terminal_properties
  have he := actual_scaled_velocity_initial_error τ hτ hτT H P.m P.v
    (P.ray_nonzero τ ⟨le_rfl,hτT.le⟩) (P.velocity_nonzero τ ⟨le_rfl,hτT.le⟩)
    A.terminal P.a P.epsilon A.slope A.epsilon_pos A.epsilon_small hp.2.2.2.2.1 hp.2.2.2.2.2 x
  apply he.trans
  have hc := historyLabelDifferenceCost_nonneg H
  calc
    2*historyLabelDifferenceCost H*‖x‖*‖A.terminal‖/P.epsilon ≤
        2*historyLabelDifferenceCost H*‖x‖*P.terminalBound A.CM A.CH/P.epsilon := by
      apply div_le_div_of_nonneg_right _ A.epsilon_pos.le
      exact mul_le_mul_of_nonneg_left hp.2.2.2.1 (by positivity)
    _ = (2*historyLabelDifferenceCost H*P.terminalBound A.CM A.CH/P.epsilon)*‖x‖ := by ring
    _ ≤ P.neighborCost hτ hτT H A.CM A.CH*A.radius :=
      mul_le_mul A.neighbor_components.2.2 hx (norm_nonneg x) A.neighborCost_nonneg
    _ ≤ P.totalError hτ hτT H A.CM A.CH A.radius := A.radius_cost_le_error

omit [CompleteSpace U] in
theorem source_ray_initial_error (x : Space) (hx : ‖x‖ ≤ A.radius) :
    norm3 (scaledRay P.m P.v (sourceRay D x) (P.rayScale hτ hτT) τ P.a P.epsilon 0 0)
      (scaledRay P.m P.v (sourceRay D x) (P.rayScale hτ hτT) τ P.a P.epsilon 0 1)
      (scaledRay P.m P.v (sourceRay D x) (P.rayScale hτ hτT) τ P.a P.epsilon 0 2-1) ≤
      P.totalError hτ hτT H A.CM A.CH A.radius := by
  have he := actual_scaled_ray_initial_error (D := D) τ hτ hτT P.m P.v
    (P.ray_nonzero τ ⟨le_rfl,hτT.le⟩) (P.velocity_nonzero τ ⟨le_rfl,hτT.le⟩)
    (P.tangent τ ⟨le_rfl,hτT.le⟩) A.normal_choice P.a P.epsilon A.epsilon_pos A.epsilon_small x
  apply he.trans
  calc
    3*‖D.normal.derivative.field‖*‖x‖/(P.rayScale hτ hτT*P.epsilon) =
      (3*‖D.normal.derivative.field‖/(P.rayScale hτ hτT*P.epsilon))*‖x‖ := by ring
    _ ≤ P.neighborCost hτ hτT H A.CM A.CH*A.radius :=
      mul_le_mul A.neighbor_components.2.1 hx (norm_nonneg x) A.neighborCost_nonneg
    _ ≤ P.totalError hτ hτT H A.CM A.CH A.radius := A.radius_cost_le_error

omit [CompleteSpace U] in
theorem error_le_scaled_error : P.totalError hτ hτT H A.CM A.CH A.radius ≤
    16*(P.epsilon*P.horizon*(4*P.G)^2+P.totalError hτ hτT H A.CM A.CH A.radius) := by
  have he := A.totalError_nonneg
  have hbase : 0 ≤ P.epsilon*P.horizon*(4*P.G)^2 :=
    mul_nonneg (mul_nonneg A.epsilon_pos.le (zero_le_one.trans A.horizon_lower)) (sq_nonneg _)
  linarith only [he,hbase]

/-- Every new analytic component is the actual source field or the
selected stationary/forward primary.  The parent input and scalar guard
record contain none of this record's new-field conclusions. -/
def geometryData (Ω : Set Space) (h0 : 0 ∈ Ω) (hΩ : ∀ x ∈ Ω, ‖x‖ ≤ A.radius) :
    PhysicalGeometryData {x : Space // x ∈ Ω} where
  center := ⟨0,h0⟩
  B := P.B
  B₁ := P.B₁
  M := fun x => sourceMatrix D x
  E := fun x => P.sourceError x
  m := P.m
  v := P.v
  r := fun x => sourceRay D x
  w := fun x => A.sourceVelocity x
  c := P.c
  s₀ := P.rayScale hτ hτT
  t₀ := τ
  a := P.a
  ε := P.epsilon
  σ := P.sigma
  y := A.y
  Θ := P.horizon
  H := P.horizon
  G := P.G
  d := P.totalError hτ hτT H A.CM A.CH A.radius
  lam := A.slope
  δ := A.δ
  hchild := A.hchild
  S := Icc τ D.T
  sigma_pos := A.sigma_pos
  sigma_small := A.sigma_small
  y_pos := A.y_pos
  y_small := A.y_small
  target_le_horizon := A.target_le_horizon
  horizon_le_Theta := le_rfl
  short_extension := A.short_extension
  a_lower := A.coupling_lower
  epsilon_pos := A.epsilon_pos
  Theta_lower := A.horizon_lower
  G_lower := P.G_lower
  d_nonneg := A.totalError_nonneg
  ray_scale_pos := rayScale_pos hτ hτT P
  slope_nonneg := A.terminal_properties.2.1
  delta_nonneg := A.delta_nonneg
  child_nonneg := A.child_nonneg
  small := A.small
  compression_guard := A.compression_guard
  time_maps := activation_horizon_maps τ D.T P.a P.epsilon A.a_pos A.epsilon_pos
  M_continuous := fun x => (sourceMatrix_continuous D x).continuousOn
  B_derivative := P.B_derivative
  old_ray_equation := P.ray_equation
  old_velocity_equation := P.velocity_equation
  ray_equation := fun x t ht => sourceRay_equation (hτ := hτ) x t ht
  velocity_equation := fun x t ht => A.sourceVelocity_equation x t ht
  old_ray_nonzero := P.ray_nonzero
  old_velocity_nonzero := P.velocity_nonzero
  old_tangent := P.tangent
  initial_tangent := fun x => A.source_initial_tangent x
  B_bound := P.B_bound
  B_derivative_bound := P.B₁_bound
  E_bound := fun x t ht => A.sourceError_bound x (hΩ x x.property) t ht
  parent_decomposition := by
    intro x t _
    unfold ParentFrame.sourceError
    module
  initial_coupling := activation_coupling_match P.B P.m P.v τ P.epsilon
  initial_tilt := activation_tilt_match P.B P.m P.v τ P.epsilon A.a_pos.ne'
    (Real.sqrt_pos.mp A.sigma_pos).le
  initial_shear := (activation_shear_match P.c P.m P.v τ P.a A.a_pos A.shear_pos).2
  initial_ray_error := fun x => (A.source_ray_initial_error x (hΩ x x.property)).trans
    A.error_le_scaled_error
  initial_velocity_error := fun x =>
    (A.source_velocity_initial_error x (hΩ x x.property)).trans A.error_le_scaled_error

theorem geometryData_matrix (Ω : Set Space) (h0 : 0 ∈ Ω) (hΩ : ∀ x ∈ Ω, ‖x‖ ≤ A.radius)
    (x : {x : Space // x ∈ Ω}) (t : ℝ) :
    (A.geometryData Ω h0 hΩ).M x t=D.M.field (D.clamp t) x := rfl

theorem geometryData_ray (Ω : Set Space) (h0 : 0 ∈ Ω) (hΩ : ∀ x ∈ Ω, ‖x‖ ≤ A.radius)
    (x : {x : Space // x ∈ Ω}) (t : ℝ) :
    (A.geometryData Ω h0 hΩ).r x t=D.normal.field (D.clamp t) x := rfl

theorem geometryData_velocity (Ω : Set Space) (h0 : 0 ∈ Ω) (hΩ : ∀ x ∈ Ω, ‖x‖ ≤ A.radius)
    (x : {x : Space // x ∈ Ω}) (t : ℝ) :
    (A.geometryData Ω h0 hΩ).w x t=uncutVelocity τ hτ hτT H A.terminal t x := rfl

end Guards
end EulerPacketSourceGeometry
