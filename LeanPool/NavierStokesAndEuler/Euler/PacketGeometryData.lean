/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalFamily
public import LeanPool.NavierStokesAndEuler.Euler.PacketAmplitudeBounds

@[expose] public section

/-!
Literal physical data and scale guards for one geometric propagation stage.
The record contains no amplification, sign, size, or frame-renewal conclusion.
-/

noncomputable section

namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay
  InnerProductSpace ContinuousLinearMap

structure PhysicalGeometryData (α : Type*) where
  center : α
  B : ℝ → Space →L[ℝ] Space
  B₁ : ℝ → Space →L[ℝ] Space
  M : α → ℝ → Space →L[ℝ] Space
  E : α → ℝ → Space →L[ℝ] Space
  m : ℝ → Space
  v : ℝ → Space
  r : α → ℝ → Space
  w : α → ℝ → Space
  c : ℝ
  s₀ : ℝ
  t₀ : ℝ
  a : ℝ
  ε : ℝ
  σ : ℝ
  y : ℝ
  Θ : ℝ
  H : ℝ
  G : ℝ
  d : ℝ
  lam : ℝ
  δ : ℝ
  hchild : ℝ
  S : Set ℝ
  sigma_pos : 0 < σ
  sigma_small : σ ≤ 1/4
  y_pos : 0 < y
  y_small : y ≤ 1/2
  target_le_horizon : y⁻¹/σ ≤ H
  horizon_le_Theta : H ≤ Θ
  short_extension : H-y⁻¹/σ ≤ 1
  a_lower : 1/2 ≤ a
  epsilon_pos : 0 < ε
  Theta_lower : 1 ≤ Θ
  G_lower : 1 ≤ G
  d_nonneg : 0 ≤ d
  ray_scale_pos : 0 < s₀
  slope_nonneg : 0 ≤ lam
  delta_nonneg : 0 ≤ δ
  child_nonneg : 0 ≤ hchild
  small : 1000000*neighborStabilityConstant*(16*(ε*Θ*(4*G)^2+d))*Θ^40 ≤ 1
  compression_guard : 60*(G+d)*(y⁻¹/σ)*ε < a
  time_maps : MapsTo (physicalTime t₀ a ε) (Icc 0 Θ) S
  M_continuous : ∀ ξ, ContinuousOn (M ξ) S
  B_derivative : ∀ t ∈ S, HasDerivWithinAt B (B₁ t) S t
  old_ray_equation : ∀ t ∈ S, HasDerivWithinAt m (-(B t).adjoint (m t)) S t
  old_velocity_equation : ∀ t ∈ S, HasDerivWithinAt v
    (-(B t) (v t)+(2*⟪m t,(B t) (v t)⟫_ℝ/‖m t‖^2) • m t) S t
  ray_equation : ∀ ξ t, t ∈ S → HasDerivWithinAt (r ξ) (-(M ξ t).adjoint (r ξ t)) S t
  velocity_equation : ∀ ξ t, t ∈ S → HasDerivWithinAt (w ξ)
    (-(M ξ t) (w ξ t)+(2*⟪r ξ t,(M ξ t) (w ξ t)⟫_ℝ/‖r ξ t‖^2) • r ξ t) S t
  old_ray_nonzero : ∀ t ∈ S, m t ≠ 0
  old_velocity_nonzero : ∀ t ∈ S, v t ≠ 0
  old_tangent : ∀ t ∈ S, ⟪m t,v t⟫_ℝ = 0
  initial_tangent : ∀ ξ, ⟪r ξ t₀,w ξ t₀⟫_ℝ = 0
  B_bound : ∀ t ∈ S, ‖B t‖ ≤ G
  B_derivative_bound : ∀ t ∈ S, ‖B₁ t‖ ≤ G^2
  E_bound : ∀ ξ t, t ∈ S → ‖E ξ t‖ ≤ d
  parent_decomposition : ∀ ξ t, t ∈ S → M ξ t = B t+
    primaryShear c m v t • rankOne ℝ (unit (v t)) (unit (m t))+E ξ t
  initial_coupling : rescaledFrame B m v t₀ a ε 0 0 1 = a
  initial_tilt : rescaledFrame B m v t₀ a ε 0 2 1 = a*σ^2
  initial_shear : rescaledShear c m v t₀ a ε 0 = a/ε^2
  initial_ray_error : ∀ ξ,
    norm3 (scaledRay m v (r ξ) s₀ t₀ a ε 0 0) (scaledRay m v (r ξ) s₀ t₀ a ε 0 1)
      (scaledRay m v (r ξ) s₀ t₀ a ε 0 2-1) ≤ 16*(ε*Θ*(4*G)^2+d)
  initial_velocity_error : ∀ ξ, |scaledVelocity m v (w ξ) t₀ a ε 0 1-1|+
    |scaledVelocity m v (w ξ) t₀ a ε 0 0+lam| ≤ 16*(ε*Θ*(4*G)^2+d)

namespace PhysicalGeometryData

variable {α : Type*}

def error (D : PhysicalGeometryData α) : ℝ := 16*(D.ε*D.Θ*(4*D.G)^2+D.d)

def target (D : PhysicalGeometryData α) : ℝ := D.y⁻¹/D.σ

def time (D : PhysicalGeometryData α) (τ : ℝ) : ℝ := physicalTime D.t₀ D.a D.ε τ

def targetTime (D : PhysicalGeometryData α) : ℝ := D.time D.target

def ray (D : PhysicalGeometryData α) (ξ : α) (τ : ℝ) : Fin 3 → ℝ :=
  scaledRay D.m D.v (D.r ξ) D.s₀ D.t₀ D.a D.ε τ

def velocity (D : PhysicalGeometryData α) (ξ : α) (τ : ℝ) : Fin 3 → ℝ :=
  scaledVelocity D.m D.v (D.w ξ) D.t₀ D.a D.ε τ

def size (D : PhysicalGeometryData α) (ξ : α) (τ : ℝ) : ℝ :=
  ‖D.r ξ (D.time τ)‖*‖D.w ξ (D.time τ)‖

def targetSize (D : PhysicalGeometryData α) : ℝ := D.size D.center D.target

def amplitude (D : PhysicalGeometryData α) : ℝ :=
  primaryAmplitude D.δ D.hchild (D.r D.center) (D.w D.center) D.targetTime

def nextCoupling (D : PhysicalGeometryData α) : ℝ :=
  normalizedCoupling (D.M D.center D.targetTime)
    (D.r D.center D.targetTime) (D.w D.center D.targetTime)

def nextTilt (D : PhysicalGeometryData α) : ℝ :=
  normalizedTilt (D.M D.center D.targetTime)
    (D.r D.center D.targetTime) (D.w D.center D.targetTime)

def nextCompression (D : PhysicalGeometryData α) : ℝ :=
  normalizedCoupling (D.M D.center D.targetTime)
    (D.r D.center D.targetTime) (D.r D.center D.targetTime)

def targetShear (D : PhysicalGeometryData α) : ℝ :=
  primaryShear D.c D.m D.v D.targetTime

end PhysicalGeometryData

end EulerPacketMovingFrame
