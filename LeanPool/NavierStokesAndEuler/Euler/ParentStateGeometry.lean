/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.ParentState
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketGeometryFrame
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketPhysicalCoefficients

/-! Geometric renewal between two actual Euler states. Their spatial
regularity, particle velocity laws and fixed origin are supplied by the
states themselves; only the quantitative packet expansion is an input. -/

section

/-! The literal primary terms in source (20) initialize the next geometric
parent frame. The forward coordinate is prescribed; the joined coordinate
is the genuine stationary history trace and is proved nonzero. -/

section

/-! The next source's center expansion follows from the actual physical
velocity update. Odd particle displacements fix the origin, and the two
literal velocity laws identify the source matrices there. -/

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerTransversePacketProvider EulerTransverseFrameCoordinates EulerVolterraConvolution
  EulerPacketSourceGeometry
open scoped ContDiff

namespace Parent

variable (G : Parent)

theorem position_zero_of_odd
    (hodd : ∀ t, Function.Odd (G.displacement.field t : Space → Space))
    (t : Icc (0 : ℝ) G.T) : G.position t 0=0 := by
  have hz : G.displacement.field t 0 = 0 := by
    ext i
    have h := congrArg (fun v : Space => v i) (hodd t 0)
    simp only [neg_zero] at h
    change (G.displacement.field t 0) i = -(G.displacement.field t 0) i at h
    change (G.displacement.field t 0) i = 0
    linarith
  simp only [position,hz,zero_add]

variable (N : Parent) (hTime : N.T = G.T)
  (u w : ℝ → Space → Space)
  (hu : ∀ (t : Icc (0 : ℝ) G.T) x, DifferentiableAt ℝ (u t) x)
  (hw : ∀ (t : Icc (0 : ℝ) N.T) x, DifferentiableAt ℝ (w t) x)
  (hGvelocity : ∀ t x, G.velocity.field t x = u t (G.position t x))
  (hNvelocity : ∀ t x, N.velocity.field t x = u t (N.position t x) + w t (N.position t x))
  (hGodd : ∀ t, Function.Odd (G.displacement.field t : Space → Space))
  (hNodd : ∀ t, Function.Odd (N.displacement.field t : Space → Space))

include hTime hu hw hGvelocity hNvelocity hGodd hNodd

theorem center_update_of_odd (t : Icc (0 : ℝ) N.T) :
    N.strain.field t 0 = G.centerStrain t+fderiv ℝ (w t) 0 := by
  let tg : Icc (0 : ℝ) G.T := ⟨t,by simpa only [hTime] using t.property⟩
  have hsum : ∀ (s : Icc (0 : ℝ) N.T) x, DifferentiableAt ℝ (fun y => u s y+w s y) x := by
    intro s x
    exact (hu ⟨s,by simpa only [hTime] using s.property⟩ x).add (hw s x)
  have hn := N.strain_physical (fun s y => u s y+w s y) hsum hNvelocity t 0
  rw [smul_zero,N.position_zero_of_odd hNodd] at hn
  have hg := G.strain_physical (fun s => u s) hu hGvelocity tg 0
  rw [smul_zero,G.position_zero_of_odd hGodd] at hg
  have hb : G.centerStrain t=G.strain.field tg 0 := by
    change G.strain.realField G.T G.T_pos.le (tg : ℝ) 0 = G.strain.field tg 0
    exact G.strain.realField_apply G.T G.T_pos.le tg 0
  rw [hn,hb,hg]
  exact fderiv_fun_add (hu tg 0) (hw t 0)

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (S : Set Space) (hS : IsCompact S)
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (mNew : Space) (hmNew : ‖mNew‖ = 1) (RNew : V ≃ₗᵢ[ℝ] referencePlane mNew)
  (SNew : Set Space) (hSNew : IsCompact SNew)

/-- Concrete old/new-parent factory. The source matrix split is derived
from the two physical velocity identities. The remaining quantitative
inputs are the preceding packet's center shear error and parent low
norm bounds, as used by the geometric induction. -/
def geometryFrameOfPhysicalUpdate (τ : ℝ) (hτ : 0 ≤ τ)
    (η : U) (hη : η ≠ 0) (c CM CH K error : ℝ)
    (hCM : 0 ≤ CM) (hK : 1 ≤ K) (he : 0 ≤ error)
    (hMK : CM ≤ K) (hHK : CM ^ 2 + CH ≤ K ^ 2)
    (hM : ∀ t ∈ Icc τ N.T, ‖G.centerStrain t‖ ≤ CM)
    (hH : ∀ t ∈ Icc τ N.T, ‖G.centerCurvature t‖ ≤ CH)
    (hpacket : ∀ t ∈ Icc τ N.T,
      ‖fderiv ℝ (w t) 0 - c • rankOne ℝ (G.sourceVelocity m hm R S hS η t) (G.sourceNormal m t)‖ ≤
          error) :
    ParentFrame (N.transverseData mNew hmNew RNew SNew hSNew) τ :=
  G.geometryFrameOfCenterExpansion m hm R S hS
    (N.transverseData mNew hmNew RNew SNew hSNew) hTime τ hτ η hη w c CM CH K error
    hCM hK he hMK hHK hM hH
    (G.center_update_of_odd N hTime u w hu hw hGvelocity hNvelocity hGodd hNodd) hpacket

end Parent
end EulerParentPacketFrames

end
end

end

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerTransverseFrameCoordinates EulerPacketSourceGeometry
  EulerPeriodicProfile
open scoped ContDiff

namespace Parent

variable (G : Parent)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (S : Set Space) (hS : IsCompact S)

theorem forward_primary_center_term (η : U) (δ : ℝ) (hδ : 0 < δ) (α k : ℝ)
    (t : Icc (0 : ℝ) G.T) (Y : Space → Space) (hY : Y 0 = 0) :
    (α*deriv (profile δ) (k*⟪m,Y 0⟫_ℝ)) •
      rankOne ℝ (EulerPacketForwardFactorization.canonicalVelocity
        (G.transverseData m hm R S hS) η t (Y 0))
        ((G.transverseData m hm R S hS).normal.field t (Y 0)) =
      (α/δ) • rankOne ℝ (G.sourceVelocity m hm R S hS η t) (G.sourceNormal m t) := by
  rw [hY]
  simp only [inner_zero_right,mul_zero,profile_deriv_zero δ hδ,
    EulerPacketForwardFactorization.canonicalVelocity,innerCutoff_zero,one_smul,div_eq_mul_inv]
  rw [G.source_normal_eq m hm R S hS]
  rfl

theorem joined_primary_center_term
    (s : ℝ) (hs : 0 < s) (hsT : s < G.T)
    (B : HistoryData ((G.transverseData m hm R S hS).initial s hs hsT.le))
    (ξ : U) (hcut : tsupport innerCutoff ⊆ S)
    (δ : ℝ) (hδ : 0 < δ) (α k : ℝ)
    (t : Icc (0 : ℝ) G.T) (Y : Space → Space) (hY : Y 0 = 0) :
    (α*deriv (profile δ) (k*⟪m,Y 0⟫_ℝ)) •
      rankOne ℝ (EulerPacketPrimaryFactorization.canonicalVelocity s hs hsT B ξ hcut t (Y 0))
        ((G.transverseData m hm R S hS).normal.field t (Y 0)) =
      (α/δ) • rankOne ℝ
        (G.sourceVelocity m hm R S hS (B.coefficients.labelCoordinate 0 ξ ⟨0,le_rfl,hs.le⟩) t)
        (G.sourceNormal m t) := by
  rw [hY]
  simp only [inner_zero_right,mul_zero,profile_deriv_zero δ hδ,div_eq_mul_inv]
  erw [EulerPacketPrimaryFactorization.canonicalVelocity_eq_cutoff_uncut,
    innerCutoff_zero,one_smul,G.source_normal_eq m hm R S hS,
    G.joined_sourceVelocity m hm R S hS]

variable (N : Parent) (hTime : N.T = G.T)
  (u w : ℝ → Space → Space)
  (hu : ∀ (t : Icc (0 : ℝ) G.T) x, DifferentiableAt ℝ (u t) x)
  (hw : ∀ (t : Icc (0 : ℝ) N.T) x, DifferentiableAt ℝ (w t) x)
  (hGvelocity : ∀ t x, G.velocity.field t x = u t (G.position t x))
  (hNvelocity : ∀ t x, N.velocity.field t x = u t (N.position t x) + w t (N.position t x))
  (hGodd : ∀ t, Function.Odd (G.displacement.field t : Space → Space))
  (hNodd : ∀ t, Function.Odd (N.displacement.field t : Space → Space))
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (mNew : Space) (hmNew : ‖mNew‖ = 1) (RNew : V ≃ₗᵢ[ℝ] referencePlane mNew)
  (SNew : Set Space) (hSNew : IsCompact SNew)
  (τ : ℝ) (hτ : 0 ≤ τ)
  (CM CH K error : ℝ) (hCM : 0 ≤ CM) (hK : 1 ≤ K) (he : 0 ≤ error)
  (hMK : CM ≤ K) (hHK : CM ^ 2 + CH ≤ K ^ 2)
  (hM : ∀ t ∈ Icc τ N.T, ‖G.centerStrain t‖ ≤ CM)
  (hH : ∀ t ∈ Icc τ N.T, ‖G.centerCurvature t‖ ≤ CH)
  (Y : Icc (0 : ℝ) G.T → Space → Space) (hY : ∀ t, Y t 0 = 0)
  (δ : ℝ) (hδ : 0 < δ) (α k : ℝ)

/-- Forward geometry frame as an element of `ParentFrame (N.transverseData mNew hmNew RNew SNew
hSNew) τ`. -/
def forwardGeometryFrame (η : U) (hη : η ≠ 0)
    (hsource20 : ∀ t : Icc (0 : ℝ) G.T, τ ≤ (t : ℝ) →
      ‖fderiv ℝ (w t) 0-(α*deriv (profile δ) (k*⟪m,Y t 0⟫_ℝ)) •
        rankOne ℝ (EulerPacketForwardFactorization.canonicalVelocity
          (G.transverseData m hm R S hS) η t (Y t 0))
          ((G.transverseData m hm R S hS).normal.field t (Y t 0))‖ ≤ error) :
    ParentFrame (N.transverseData mNew hmNew RNew SNew hSNew) τ := by
  apply G.geometryFrameOfPhysicalUpdate N hTime u w hu hw hGvelocity hNvelocity hGodd hNodd
    m hm R S hS mNew hmNew RNew SNew hSNew τ hτ η hη (α/δ) CM CH K error
    hCM hK he hMK hHK hM hH
  intro t ht
  have htG : t ∈ Icc (0 : ℝ) G.T := ⟨hτ.trans ht.1,by simpa only [hTime] using ht.2⟩
  have h := hsource20 ⟨t,htG⟩ ht.1
  rw [G.forward_primary_center_term m hm R S hS η δ hδ α k ⟨t,htG⟩ (Y ⟨t,htG⟩) (hY _)] at h
  exact h

/-- Joined geometry frame as an element of `ParentFrame (N.transverseData mNew hmNew RNew SNew
hSNew) τ`. -/
def joinedGeometryFrame
    (s : ℝ) (hs : 0 < s) (hsT : s < G.T)
    (B : HistoryData ((G.transverseData m hm R S hS).initial s hs hsT.le))
    (ξ : U) (hξ : ξ ≠ 0) (hcut : tsupport innerCutoff ⊆ S)
    (hsource20 : ∀ t : Icc (0 : ℝ) G.T, τ ≤ (t : ℝ) →
      ‖fderiv ℝ (w t) 0-(α*deriv (profile δ) (k*⟪m,Y t 0⟫_ℝ)) •
        rankOne ℝ (EulerPacketPrimaryFactorization.canonicalVelocity s hs hsT B ξ hcut t (Y t 0))
          ((G.transverseData m hm R S hS).normal.field t (Y t 0))‖ ≤ error) :
    ParentFrame (N.transverseData mNew hmNew RNew SNew hSNew) τ := by
  apply G.geometryFrameOfPhysicalUpdate N hTime u w hu hw hGvelocity hNvelocity hGodd hNodd
    m hm R S hS mNew hmNew RNew SNew hSNew τ hτ
    (B.coefficients.labelCoordinate 0 ξ ⟨0,le_rfl,hs.le⟩)
    (G.joined_initialCoordinate_ne_zero m hm R S hS s hs hsT B ξ hξ) (α/δ) CM CH K error
    hCM hK he hMK hHK hM hH
  intro t ht
  have htG : t ∈ Icc (0 : ℝ) G.T := ⟨hτ.trans ht.1,by simpa only [hTime] using ht.2⟩
  have h := hsource20 ⟨t,htG⟩ ht.1
  rw [G.joined_primary_center_term m hm R S hS s hs hsT B ξ hcut δ hδ α k
    ⟨t,htG⟩ (Y ⟨t,htG⟩) (hY _)] at h
  exact h

end Parent
end EulerParentPacketFrames

end
end

end

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
