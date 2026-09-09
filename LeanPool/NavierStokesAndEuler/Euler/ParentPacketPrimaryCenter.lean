/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketPhysicalFrame

/-! The literal primary terms in source (20) initialize the next geometric
parent frame. The forward coordinate is prescribed; the joined coordinate
is the genuine stationary history trace and is proved nonzero. -/

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
