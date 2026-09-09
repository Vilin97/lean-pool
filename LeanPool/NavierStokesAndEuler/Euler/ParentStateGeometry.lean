/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentState
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketPrimaryCenter

/-! Geometric renewal between two actual Euler states. Their spatial
regularity, particle velocity laws and fixed origin are supplied by the
states themselves; only the quantitative packet expansion is an input. -/

@[expose] public section


noncomputable section

namespace EulerParentPacketFrames.SmoothState

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransverseFrameCoordinates EulerTransversePacketProvider
  EulerPacketSourceGeometry EulerSpatialCutoffs EulerPeriodicProfile
open scoped ContDiff

variable {A N : Parent} (S : SmoothState A) (T : SmoothState N) (hTime : N.T = A.T)

/-- Velocity increment, given by `T.evolution.velocity (t,x)-S.evolution.velocity (t,x)`. -/
def velocityIncrement (t : ℝ) (x : Space) : Space :=
  T.evolution.velocity (t,x)-S.evolution.velocity (t,x)

include hTime in
theorem velocityIncrement_smooth (t : Icc (0 : ℝ) N.T) :
    ContDiff ℝ ∞ (S.velocityIncrement T t) := by
  let ta : Icc (0 : ℝ) A.T := ⟨t,by simpa only [hTime] using t.property⟩
  exact (T.evolution.velocity_smooth t).sub (S.evolution.velocity_smooth ta)

theorem next_velocity (t : Icc (0 : ℝ) N.T) (x : Space) :
    N.velocity.field t x=S.evolution.velocity (t,N.position t x) +
      S.velocityIncrement T t (N.position t x) := by
  rw [T.evolution.velocity_match]
  unfold velocityIncrement
  module

theorem normalized_inverse_zero (t : Icc (0 : ℝ) A.T) :
    S.evolution.inverse.normalized t 0=0 := by
  simp only [ParticleInverse.normalized,Parent.packetInverse,
    projIcc_of_mem A.T_pos.le t.property,smul_zero,S.evolution.inverse.zero S.odd t]

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (mNext : Space) (hmNext : ‖mNext‖ = 1) (JNext : V ≃ₗᵢ[ℝ] referencePlane mNext)
  (supportNext : Set Space) (hSupportNext : IsCompact supportNext)
  (τ : ℝ) (hτ : 0 ≤ τ) (CM CH K error : ℝ)
  (hCM : 0 ≤ CM) (hK : 1 ≤ K) (he : 0 ≤ error)
  (hMK : CM ≤ K) (hHK : CM ^ 2 + CH ≤ K ^ 2)
  (hM : ∀ t ∈ Icc τ N.T, ‖A.centerStrain t‖ ≤ CM)
  (hH : ∀ t ∈ Icc τ N.T, ‖A.centerCurvature t‖ ≤ CH)
  (δ : ℝ) (hδ : 0 < δ) (α k : ℝ)

/-- Forward renewal, constructed using `A.forwardGeometryFrame`. -/
def forwardRenewal (ξ : U) (hξ : ξ ≠ 0)
    (hsource : ∀ t : Icc (0 : ℝ) A.T, τ ≤ (t : ℝ) →
      ‖fderiv ℝ (S.velocityIncrement T t) 0 -
        (α*deriv (profile δ) (k*⟪m,S.evolution.inverse.normalized t 0⟫_ℝ)) •
          rankOne ℝ (EulerPacketForwardFactorization.canonicalVelocity
            (A.transverseData m hm J support hSupport) ξ t (S.evolution.inverse.normalized t 0))
            ((A.transverseData m hm J support hSupport).normal.field t
              (S.evolution.inverse.normalized t 0))‖ ≤ error) :
    ParentFrame (N.transverseData mNext hmNext JNext supportNext hSupportNext) τ :=
  A.forwardGeometryFrame m hm J support hSupport N hTime
    (fun t x => S.evolution.velocity (t,x)) (S.velocityIncrement T)
    (fun t x => (S.evolution.velocity_smooth t).differentiable (by simp) x)
    (fun t x => (S.velocityIncrement_smooth T hTime t).differentiable (by simp) x)
    S.evolution.velocity_match (S.next_velocity T) S.odd.displacement T.odd.displacement
    mNext hmNext JNext supportNext hSupportNext τ hτ CM CH K error hCM hK he hMK hHK hM hH
    S.evolution.inverse.normalized S.normalized_inverse_zero δ hδ α k ξ hξ hsource

/-- Joined renewal, constructed using `A.joinedGeometryFrame`. -/
def joinedRenewal (s : ℝ) (hs : 0 < s) (hsT : s < A.T)
    (H : HistoryData ((A.transverseData m hm J support hSupport).initial s hs hsT.le))
    (ξ : U) (hξ : ξ ≠ 0) (hcut : tsupport innerCutoff ⊆ support)
    (hsource : ∀ t : Icc (0 : ℝ) A.T, τ ≤ (t : ℝ) →
      ‖fderiv ℝ (S.velocityIncrement T t) 0 -
        (α*deriv (profile δ) (k*⟪m,S.evolution.inverse.normalized t 0⟫_ℝ)) •
          rankOne ℝ (EulerPacketPrimaryFactorization.canonicalVelocity s hs hsT H ξ hcut t
            (S.evolution.inverse.normalized t 0))
            ((A.transverseData m hm J support hSupport).normal.field t
              (S.evolution.inverse.normalized t 0))‖ ≤ error) :
    ParentFrame (N.transverseData mNext hmNext JNext supportNext hSupportNext) τ :=
  A.joinedGeometryFrame m hm J support hSupport N hTime
    (fun t x => S.evolution.velocity (t,x)) (S.velocityIncrement T)
    (fun t x => (S.evolution.velocity_smooth t).differentiable (by simp) x)
    (fun t x => (S.velocityIncrement_smooth T hTime t).differentiable (by simp) x)
    S.evolution.velocity_match (S.next_velocity T) S.odd.displacement T.odd.displacement
    mNext hmNext JNext supportNext hSupportNext τ hτ CM CH K error hCM hK he hMK hHK hM hH
    S.evolution.inverse.normalized S.normalized_inverse_zero δ hδ α k s hs hsT H ξ hξ hcut hsource

end EulerParentPacketFrames.SmoothState
