/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketActivationLipschitz
public import LeanPool.NavierStokesAndEuler.Euler.PacketActivationRay
public import LeanPool.NavierStokesAndEuler.Euler.PacketFrameCoefficients
public import LeanPool.NavierStokesAndEuler.Euler.PacketNeighborControlled
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalSize
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryUncut
public import LeanPool.NavierStokesAndEuler.Euler.TransverseActivationSelection
import LeanPool.NavierStokesAndEuler.Euler.PacketActivationConstructed
import LeanPool.NavierStokesAndEuler.Euler.PacketActivationInitial

/-! Construction of geometric source data from the actual parent strain,
normal and stationary primary.  Only the older homogeneous frame, parent
center remainder, low source bounds and numerical guards are inputs. -/

@[expose] public section


noncomputable section

namespace EulerPacketSourceGeometry

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransversePacketProvider EulerPacketMovingFrame EulerPacketNormalizedPrimary
  EulerPacketCrossProduct EulerPacketActivationHistory EulerTransverseActivationSelection
  EulerPacketPrimaryFactorization EulerPacketRay EulerVolterraConvolution
  EulerTransverseSourceCoefficientPath

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {D : Data U} {τ : ℝ}

/-- The older frame at the fixed center, together with the actual parent
strain's center remainder.  It contains no new ray, new velocity or
amplification assertion. -/
structure ParentFrame (D : Data U) (τ : ℝ) where
  /-- Bound parameter of `ParentFrame`, of type `ℝ → Space →L[ℝ] Space`. -/
  B : ℝ → Space →L[ℝ] Space
  /-- B₁ of `ParentFrame`, of type `ℝ → Space →L[ℝ] Space`. -/
  B₁ : ℝ → Space →L[ℝ] Space
  /-- M of `ParentFrame`, of type `ℝ → Space`. -/
  m : ℝ → Space
  /-- V of `ParentFrame`, of type `ℝ → Space`. -/
  v : ℝ → Space
  /-- C of `ParentFrame`, of type `ℝ`. -/
  c : ℝ
  /-- Geometric data of `ParentFrame`, of type `ℝ`. -/
  G : ℝ
  /-- Error of `ParentFrame`, of type `ℝ`. -/
  error : ℝ
  G_lower : 1 ≤ G
  error_nonneg : 0 ≤ error
  B_derivative : ∀ t ∈ Icc τ D.T, HasDerivWithinAt B (B₁ t) (Icc τ D.T) t
  ray_equation : ∀ t ∈ Icc τ D.T,
    HasDerivWithinAt m (-(B t).adjoint (m t)) (Icc τ D.T) t
  velocity_equation : ∀ t ∈ Icc τ D.T, HasDerivWithinAt v
    (-(B t) (v t)+(2*⟪m t,(B t) (v t)⟫_ℝ/‖m t‖^2) • m t) (Icc τ D.T) t
  ray_nonzero : ∀ t ∈ Icc τ D.T, m t ≠ 0
  velocity_nonzero : ∀ t ∈ Icc τ D.T, v t ≠ 0
  tangent : ∀ t ∈ Icc τ D.T, ⟪m t,v t⟫_ℝ=0
  B_bound : ∀ t ∈ Icc τ D.T, ‖B t‖ ≤ G
  B₁_bound : ∀ t ∈ Icc τ D.T, ‖B₁ t‖ ≤ G^2
  remainder_bound : ∀ t ∈ Icc τ D.T,
    ‖D.M.field (D.clamp t) 0-B t -
      primaryShear c m v t • rankOne ℝ (unit (v t)) (unit (m t))‖ ≤ error

namespace ParentFrame

variable (P : ParentFrame D τ)

/-- A, given by `normalizedCoupling (P.B τ) (P.m τ) (P.v τ)`. -/
def a : ℝ := normalizedCoupling (P.B τ) (P.m τ) (P.v τ)
/-- Sigma, given by `Real.sqrt (normalizedTilt (P.B τ) (P.m τ) (P.v τ))`. -/
def sigma : ℝ := Real.sqrt (normalizedTilt (P.B τ) (P.m τ) (P.v τ))
/-- Shear, given by `primaryShear P.c P.m P.v τ`. -/
def shear : ℝ := primaryShear P.c P.m P.v τ
/-- Epsilon, given by `Real.sqrt (P.a/P.shear)`. -/
def epsilon : ℝ := Real.sqrt (P.a/P.shear)
/-- Horizon, given by `P.a*(D.T-τ)/P.epsilon`. -/
def horizon : ℝ := P.a*(D.T-τ)/P.epsilon
/-- Ray scale, given by `activationRayScale (D.deformationEquiv ⟨τ,hτ.le,hτT.le⟩ 0) (cross (unit
(P.m τ)) (unit (P.v τ)))`. -/
def rayScale (hτ : 0 < τ) (hτT : τ < D.T) : ℝ :=
  activationRayScale (D.deformationEquiv ⟨τ,hτ.le,hτT.le⟩ 0)
    (cross (unit (P.m τ)) (unit (P.v τ)))
/-- Terminal bound, given by `8*(activationConstant CM CH+1)*D.inverseBound/P.shear`. -/
def terminalBound (CM CH : ℝ) : ℝ :=
  8*(activationConstant CM CH+1)*D.inverseBound/P.shear

variable [CompleteSpace U] (hτ : 0 < τ) (hτT : τ < D.T)
  (H : HistoryData (D.initial τ hτ hτT.le))

/-- Neighbor cost as an element of `ℝ`. -/
def neighborCost (CM CH : ℝ) : ℝ :=
  ‖D.M.derivative.field‖+
    3*‖D.normal.derivative.field‖/(P.rayScale hτ hτT*P.epsilon) +
    2*historyLabelDifferenceCost H*P.terminalBound CM CH/P.epsilon

/-- Total error, given by `P.error+P.neighborCost hτ hτT H CM CH*ρ`. -/
def totalError (CM CH ρ : ℝ) : ℝ :=
  P.error+P.neighborCost hτ hτT H CM CH*ρ

end ParentFrame

variable [CompleteSpace U] (hτ : 0 < τ) (hτT : τ < D.T)
  (P : ParentFrame D τ) (H : HistoryData (D.initial τ hτ hτT.le))

/-- Source and scalar guards, all stated before the new primary is
constructed.  The neighbor cost is the explicit coefficient expression. -/
structure Guards where
  /-- CM of `Guards`, of type `ℝ`. -/
  CM : ℝ
  /-- CH of `Guards`, of type `ℝ`. -/
  CH : ℝ
  /-- Ζ of `Guards`, of type `ℝ`. -/
  ζ : ℝ
  /-- Radius of `Guards`, of type `ℝ`. -/
  radius : ℝ
  /-- Y of `Guards`, of type `ℝ`. -/
  y : ℝ
  /-- Δ of `Guards`, of type `ℝ`. -/
  δ : ℝ
  /-- Hchild of `Guards`, of type `ℝ`. -/
  hchild : ℝ
  CM_nonneg : 0 ≤ CM
  CH_nonneg : 0 ≤ CH
  zeta_nonneg : 0 ≤ ζ
  radius_nonneg : 0 ≤ radius
  delta_nonneg : 0 ≤ δ
  child_nonneg : 0 ≤ hchild
  coupling_lower : 1/2 ≤ P.a
  shear_pos : 0 < P.shear
  sigma_pos : 0 < P.sigma
  sigma_small : P.sigma ≤ 1/4
  epsilon_small : P.epsilon ≤ 1
  y_pos : 0 < y
  y_small : y ≤ 1/2
  target_le_horizon : y⁻¹/P.sigma ≤ P.horizon
  horizon_lower : 1 ≤ P.horizon
  short_extension : P.horizon-y⁻¹/P.sigma ≤ 1
  small : 1000000*neighborStabilityConstant *
    (16*(P.epsilon*P.horizon*(4*P.G)^2+P.totalError hτ hτT H CM CH radius))*P.horizon^40 ≤ 1
  compression_guard : 60*(P.G+P.totalError hτ hτT H CM CH radius)*(y⁻¹/P.sigma)*P.epsilon < P.a
  normal_choice : D.m₀=activationDirection (D.deformationEquiv ⟨τ,hτ.le,hτT.le⟩ 0)
    (cross (unit (P.m τ)) (unit (P.v τ)))
  history_symmetric : ∀ t, (H.H.field t 0).IsSymmetric
  history_layer : 1 ≤ P.shear*τ
  history_strain : ∀ t : Icc (0 : ℝ) τ,
    ‖(D.initial τ hτ hτT.le).M.field t 0‖ ≤ CM*P.shear
  history_hessian : ‖H.coefficients.labelHessian 0‖ ≤ CH*P.shear^2
  activation_small : 16*(activationConstant CM CH+1)*ζ ≤ 1
  activation_error : P.G+P.error ≤ ζ*P.shear
  activation_compression : ⟪D.M.field ⟨τ,hτ.le,hτT.le⟩ 0 (unit (P.m τ)),unit (P.m τ)⟫_ℝ < 0

namespace Guards

variable (A : Guards hτ hτT P H)

omit [CompleteSpace U] in
include A in
theorem a_pos : 0 < P.a := by linarith only [A.coupling_lower]

omit [CompleteSpace U] in
include A in
theorem epsilon_pos : 0 < P.epsilon := Real.sqrt_pos.mpr (div_pos A.a_pos A.shear_pos)

omit [CompleteSpace U] in
theorem rayScale_pos : 0 < P.rayScale hτ hτT := by
  exact activationRayScale_pos _ (activation_cross_ne_zero _ _
    (P.ray_nonzero τ ⟨le_rfl,hτT.le⟩) (P.velocity_nonzero τ ⟨le_rfl,hτT.le⟩)
    (P.tangent τ ⟨le_rfl,hτT.le⟩))

omit [CompleteSpace U] in
theorem terminalBound_nonneg : 0 ≤ P.terminalBound A.CM A.CH := by
  unfold ParentFrame.terminalBound activationConstant
  positivity [A.CM_nonneg,A.CH_nonneg,D.inverseBound_pos,A.shear_pos]

omit [CompleteSpace U] in
theorem neighborCost_nonneg : 0 ≤ P.neighborCost hτ hτT H A.CM A.CH := by
  have hc := historyLabelDifferenceCost_nonneg H
  have hs := rayScale_pos hτ hτT P
  have he := A.epsilon_pos
  have ht := A.terminalBound_nonneg
  unfold ParentFrame.neighborCost
  positivity

omit [CompleteSpace U] in
theorem totalError_nonneg : 0 ≤ P.totalError hτ hτT H A.CM A.CH A.radius :=
  add_nonneg P.error_nonneg (mul_nonneg A.neighborCost_nonneg A.radius_nonneg)

omit [CompleteSpace U] in
theorem activation_perturbation :
    ‖D.M.field ⟨τ,hτ.le,hτT.le⟩ 0-P.shear • rankOne ℝ (unit (P.v τ)) (unit (P.m τ))‖ ≤
      A.ζ*P.shear := by
  have ht : τ ∈ Icc τ D.T := ⟨le_rfl,hτT.le⟩
  have hr := P.remainder_bound τ ht
  have hclamp : D.clamp τ = ⟨τ,hτ.le,hτT.le⟩ := Data.clamp_coe D ⟨τ,hτ.le,hτT.le⟩
  rw [hclamp] at hr
  calc
    _ = ‖P.B τ+(D.M.field ⟨τ,hτ.le,hτT.le⟩ 0-P.B τ -
      P.shear • rankOne ℝ (unit (P.v τ)) (unit (P.m τ)))‖ := by congr 1; module
    _ ≤ ‖P.B τ‖+‖D.M.field ⟨τ,hτ.le,hτT.le⟩ 0-P.B τ -
      P.shear • rankOne ℝ (unit (P.v τ)) (unit (P.m τ))‖ := norm_add_le _ _
    _ ≤ P.G+P.error := add_le_add (P.B_bound τ ht) hr
    _ ≤ A.ζ*P.shear := A.activation_error

theorem selection :
    0 < P.rayScale hτ hτT ∧
      scaledRay P.m P.v (fun s => D.normal.field (D.clamp s) 0)
        (P.rayScale hτ hτT) τ P.a P.epsilon 0 = ![0,0,1] ∧
      ∃ ξ : U, ∃ lam : ℝ, ξ ≠ 0 ∧ 0 ≤ lam ∧
        lam ≤ 8*(activationConstant A.CM A.CH+1)/P.epsilon ∧
        ‖ξ‖ ≤ P.terminalBound A.CM A.CH ∧
        scaledVelocity P.m P.v (fun s => uncutVelocity τ hτ hτT H ξ s 0) τ P.a P.epsilon 0 0 = -lam
            ∧
        scaledVelocity P.m P.v (fun s => uncutVelocity τ hτ hτT H ξ s 0) τ P.a P.epsilon 0 1 = 1 :=
            by
  exact exists_activated_primary τ hτ hτT H P.m P.v
    (P.ray_nonzero τ ⟨le_rfl,hτT.le⟩) (P.velocity_nonzero τ ⟨le_rfl,hτT.le⟩)
    (P.tangent τ ⟨le_rfl,hτT.le⟩) A.normal_choice A.history_symmetric
    P.shear A.CM A.CH A.ζ P.a P.epsilon A.shear_pos A.history_layer
    A.CM_nonneg A.CH_nonneg A.zeta_nonneg A.epsilon_pos A.history_strain
    A.history_hessian A.activation_small A.activation_perturbation A.activation_compression

/-- Terminal, given by `A.selection.2.2.choose`. -/
def terminal : U := A.selection.2.2.choose
/-- Slope, given by `A.selection.2.2.choose_spec.choose`. -/
def slope : ℝ := A.selection.2.2.choose_spec.choose

theorem terminal_properties : A.terminal ≠ 0 ∧ 0 ≤ A.slope ∧
    A.slope ≤ 8*(activationConstant A.CM A.CH+1)/P.epsilon ∧
    ‖A.terminal‖ ≤ P.terminalBound A.CM A.CH ∧
    scaledVelocity P.m P.v (fun s => uncutVelocity τ hτ hτT H A.terminal s 0)
      τ P.a P.epsilon 0 0 = -A.slope ∧
    scaledVelocity P.m P.v (fun s => uncutVelocity τ hτ hτT H A.terminal s 0)
      τ P.a P.epsilon 0 1 = 1 := A.selection.2.2.choose_spec.choose_spec

end Guards
end EulerPacketSourceGeometry
