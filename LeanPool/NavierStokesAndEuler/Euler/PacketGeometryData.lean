/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketNeighborControlled
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalCoefficients
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalSize
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothLimit
public import LeanPool.NavierStokesAndEuler.Euler.PacketIdealSize
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketGrowth
import LeanPool.NavierStokesAndEuler.Euler.PacketHorizonSize
import LeanPool.NavierStokesAndEuler.Euler.PacketTargetAmplification
import Mathlib.Algebra.Order.Star.Real

/-!
Literal physical data and scale guards for one geometric propagation stage.
The record contains no amplification, sign, size, or frame-renewal conclusion.
-/

section

/-! Bounds for the actual source choice of the packet amplitude. -/

@[expose] public section

noncomputable section

namespace EulerPacketMovingFrame

open Set Real EulerSmoothLimit EulerPacketGrowth

/-- Primary amplitude, given by `δ*hchild/(‖r t‖*‖w t‖)`. -/
def primaryAmplitude (δ hchild : ℝ) (r w : ℝ → Space) (t : ℝ) : ℝ :=
  δ*hchild/(‖r t‖*‖w t‖)

theorem primaryAmplitude_nonneg (δ hchild : ℝ) (r w : ℝ → Space) (t : ℝ)
    (hδ : 0 ≤ δ) (hh : 0 ≤ hchild) : 0 ≤ primaryAmplitude δ hchild r w t := by
  unfold primaryAmplitude
  positivity

theorem primaryAmplitude_target_identity (δ hchild : ℝ) (r w : ℝ → Space) (t : ℝ)
    (ht : 0 < ‖r t‖ * ‖w t‖) :
    primaryAmplitude δ hchild r w t*(‖r t‖*‖w t‖) = δ*hchild := by
  unfold primaryAmplitude
  exact div_mul_cancel₀ _ (ne_of_gt ht)

theorem primaryAmplitude_exponential_bound (r w : ℝ → Space)
    {δ hchild s₀ Θ x t : ℝ} (hδ : 0 ≤ δ) (hh : 0 ≤ hchild) (hs₀ : 0 < s₀) (hΘ : 0 < Θ)
    (hgrowth : s₀ * exp x ≤ 4 * Θ * (‖r t‖ * ‖w t‖)) :
    primaryAmplitude δ hchild r w t ≤ (4*Θ*δ*hchild/s₀)*exp (-x) := by
  have hb := (ratio_bound_from_target_growth hs₀ hΘ (mul_nonneg hδ hh) le_rfl hgrowth).2
  simpa only [primaryAmplitude, mul_assoc] using hb

/-- The profile-weighted amplitude is bounded uniformly on the full
forward horizon, including before scaled time one. -/
theorem primaryAmplitude_profile_bound (r w : ℝ → Space)
    {δ hchild s₀ σ T H targetTime : ℝ} {Z Z₁ : ℝ → ℝ}
    (hδ : 0 ≤ δ) (hh : 0 ≤ hchild) (hs₀ : 0 < s₀)
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hT : 1 ≤ T) (hshort : H - T ≤ 1)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0)
    (hlower : s₀ * idealPrimarySize σ Z T / 4 ≤ ‖r targetTime‖ * ‖w targetTime‖) :
    ∀ τ ∈ Icc 0 H, primaryAmplitude δ hchild r w targetTime*Z τ ≤ 8*exp 6*δ*hchild/s₀ := by
  let A := primaryAmplitude δ hchild r w targetTime
  have hA : 0 ≤ A := primaryAmplitude_nonneg δ hchild r w targetTime hδ hh
  have hZpos := equation30_global_positive hσ hσsmall hZ hfluxZ hZ0 hZ₁0
  have hT0 : 0 ≤ T := by linarith only [hT]
  have hIpos : 0 < idealPrimarySize σ Z T :=
    mul_pos (sqrt_pos.mpr (by positivity)) (hZpos T hT0)
  have htarget : 0 < ‖r targetTime‖*‖w targetTime‖ :=
    lt_of_lt_of_le (div_pos (mul_pos hs₀ hIpos) (by norm_num)) hlower
  have hid : A*(‖r targetTime‖*‖w targetTime‖) = δ*hchild :=
    primaryAmplitude_target_identity δ hchild r w targetTime htarget
  have hl : s₀*A*idealPrimarySize σ Z T ≤ 4*δ*hchild := by
    have hb := mul_le_mul_of_nonneg_left hlower hA
    rw [hid] at hb
    nlinarith only [hb]
  intro τ hτ
  have hroot : 1 ≤ sqrt (1+(σ^2*τ^2)^2) := one_le_sqrt.mpr (by nlinarith [sq_nonneg (σ^2*τ^2)])
  have hz : Z τ ≤ idealPrimarySize σ Z τ := by
    have hb := mul_le_mul_of_nonneg_right hroot (hZpos τ hτ.1).le
    simpa only [one_mul, idealPrimarySize] using hb
  have hi := equation30_horizon_size_comparison hσ hσsmall hZ hfluxZ hZ0 hZ₁0 hT hshort hτ.1 hτ.2
  have hz' := hz.trans hi
  have h1 := mul_le_mul_of_nonneg_left hz' (mul_nonneg hs₀.le hA)
  have h2 := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*exp (6:ℝ) by positivity)
  apply (le_div_iff₀ hs₀).mpr
  change A*Z τ*s₀ ≤ 8*exp 6*δ*hchild
  nlinarith only [h1, h2]

end EulerPacketMovingFrame

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay
  InnerProductSpace ContinuousLinearMap

/-- Physical geometry data, collecting `center`, `B`, `B₁`, `M`, `E`, `m` and their
compatibility conditions. -/
structure PhysicalGeometryData (α : Type*) where
  /-- Center of `PhysicalGeometryData`, of type `α`. -/
  center : α
  /-- Bound parameter of `PhysicalGeometryData`, of type `ℝ → Space →L[ℝ] Space`. -/
  B : ℝ → Space →L[ℝ] Space
  /-- B₁ of `PhysicalGeometryData`, of type `ℝ → Space →L[ℝ] Space`. -/
  B₁ : ℝ → Space →L[ℝ] Space
  /-- M of `PhysicalGeometryData`, of type `α → ℝ → Space →L[ℝ] Space`. -/
  M : α → ℝ → Space →L[ℝ] Space
  /-- E of `PhysicalGeometryData`, of type `α → ℝ → Space →L[ℝ] Space`. -/
  E : α → ℝ → Space →L[ℝ] Space
  /-- M of `PhysicalGeometryData`, of type `ℝ → Space`. -/
  m : ℝ → Space
  /-- V of `PhysicalGeometryData`, of type `ℝ → Space`. -/
  v : ℝ → Space
  /-- R of `PhysicalGeometryData`, of type `α → ℝ → Space`. -/
  r : α → ℝ → Space
  /-- W of `PhysicalGeometryData`, of type `α → ℝ → Space`. -/
  w : α → ℝ → Space
  /-- C of `PhysicalGeometryData`, of type `ℝ`. -/
  c : ℝ
  /-- S₀ of `PhysicalGeometryData`, of type `ℝ`. -/
  s₀ : ℝ
  /-- T₀ of `PhysicalGeometryData`, of type `ℝ`. -/
  t₀ : ℝ
  /-- A of `PhysicalGeometryData`, of type `ℝ`. -/
  a : ℝ
  /-- Ε of `PhysicalGeometryData`, of type `ℝ`. -/
  ε : ℝ
  /-- Σ of `PhysicalGeometryData`, of type `ℝ`. -/
  σ : ℝ
  /-- Y of `PhysicalGeometryData`, of type `ℝ`. -/
  y : ℝ
  /-- Θ of `PhysicalGeometryData`, of type `ℝ`. -/
  Θ : ℝ
  /-- H of `PhysicalGeometryData`, of type `ℝ`. -/
  H : ℝ
  /-- Geometric data of `PhysicalGeometryData`, of type `ℝ`. -/
  G : ℝ
  /-- D of `PhysicalGeometryData`, of type `ℝ`. -/
  d : ℝ
  /-- Lam of `PhysicalGeometryData`, of type `ℝ`. -/
  lam : ℝ
  /-- Δ of `PhysicalGeometryData`, of type `ℝ`. -/
  δ : ℝ
  /-- Hchild of `PhysicalGeometryData`, of type `ℝ`. -/
  hchild : ℝ
  /-- Parameter `S` of `PhysicalGeometryData`, of type `Set ℝ`. -/
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
  parent_decomposition : ∀ ξ t, t ∈ S → M ξ t = B t +
    primaryShear c m v t • rankOne ℝ (unit (v t)) (unit (m t))+E ξ t
  initial_coupling : rescaledFrame B m v t₀ a ε 0 0 1 = a
  initial_tilt : rescaledFrame B m v t₀ a ε 0 2 1 = a*σ^2
  initial_shear : rescaledShear c m v t₀ a ε 0 = a/ε^2
  initial_ray_error : ∀ ξ,
    norm3 (scaledRay m v (r ξ) s₀ t₀ a ε 0 0) (scaledRay m v (r ξ) s₀ t₀ a ε 0 1)
      (scaledRay m v (r ξ) s₀ t₀ a ε 0 2-1) ≤ 16*(ε*Θ*(4*G)^2+d)
  initial_velocity_error : ∀ ξ, |scaledVelocity m v (w ξ) t₀ a ε 0 1-1| +
    |scaledVelocity m v (w ξ) t₀ a ε 0 0+lam| ≤ 16*(ε*Θ*(4*G)^2+d)

namespace PhysicalGeometryData

variable {α : Type*}

/-- Error, given by `16*(D.ε*D.Θ*(4*D.G)^2+D.d)`. -/
def error (D : PhysicalGeometryData α) : ℝ := 16*(D.ε*D.Θ*(4*D.G)^2+D.d)

/-- Target, given by `D.y⁻¹/D.σ`. -/
def target (D : PhysicalGeometryData α) : ℝ := D.y⁻¹/D.σ

/-- Time, given by `physicalTime D.t₀ D.a D.ε τ`. -/
def time (D : PhysicalGeometryData α) (τ : ℝ) : ℝ := physicalTime D.t₀ D.a D.ε τ

/-- Target time, given by `D.time D.target`. -/
def targetTime (D : PhysicalGeometryData α) : ℝ := D.time D.target

/-- Ray, given by `scaledRay D.m D.v (D.r ξ) D.s₀ D.t₀ D.a D.ε τ`. -/
def ray (D : PhysicalGeometryData α) (ξ : α) (τ : ℝ) : Fin 3 → ℝ :=
  scaledRay D.m D.v (D.r ξ) D.s₀ D.t₀ D.a D.ε τ

/-- Velocity, given by `scaledVelocity D.m D.v (D.w ξ) D.t₀ D.a D.ε τ`. -/
def velocity (D : PhysicalGeometryData α) (ξ : α) (τ : ℝ) : Fin 3 → ℝ :=
  scaledVelocity D.m D.v (D.w ξ) D.t₀ D.a D.ε τ

/-- Size, given by `‖D.r ξ (D.time τ)‖*‖D.w ξ (D.time τ)‖`. -/
def size (D : PhysicalGeometryData α) (ξ : α) (τ : ℝ) : ℝ :=
  ‖D.r ξ (D.time τ)‖*‖D.w ξ (D.time τ)‖

/-- Target size, given by `D.size D.center D.target`. -/
def targetSize (D : PhysicalGeometryData α) : ℝ := D.size D.center D.target

/-- Amplitude, given by `primaryAmplitude D.δ D.hchild (D.r D.center) (D.w D.center)
D.targetTime`. -/
def amplitude (D : PhysicalGeometryData α) : ℝ :=
  primaryAmplitude D.δ D.hchild (D.r D.center) (D.w D.center) D.targetTime

/-- Next coupling, given by `normalizedCoupling (D.M D.center D.targetTime) (D.r D.center
D.targetTime) (D.w D.center D.targetTime)`. -/
def nextCoupling (D : PhysicalGeometryData α) : ℝ :=
  normalizedCoupling (D.M D.center D.targetTime)
    (D.r D.center D.targetTime) (D.w D.center D.targetTime)

/-- Next tilt, given by `normalizedTilt (D.M D.center D.targetTime) (D.r D.center D.targetTime)
(D.w D.center D.targetTime)`. -/
def nextTilt (D : PhysicalGeometryData α) : ℝ :=
  normalizedTilt (D.M D.center D.targetTime)
    (D.r D.center D.targetTime) (D.w D.center D.targetTime)

/-- Next compression, given by `normalizedCoupling (D.M D.center D.targetTime) (D.r D.center
D.targetTime) (D.r D.center D.targetTime)`. -/
def nextCompression (D : PhysicalGeometryData α) : ℝ :=
  normalizedCoupling (D.M D.center D.targetTime)
    (D.r D.center D.targetTime) (D.r D.center D.targetTime)

/-- Target shear, given by `primaryShear D.c D.m D.v D.targetTime`. -/
def targetShear (D : PhysicalGeometryData α) : ℝ :=
  primaryShear D.c D.m D.v D.targetTime

end PhysicalGeometryData

end EulerPacketMovingFrame
