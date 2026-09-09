/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketStrainEvolution
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketHessianSymmetry
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceGeometryData
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardFactorization

@[expose] public section

/-! Actual parent source trajectories supply the older geometric frame.
Its matrix derivative is derived from the parent curvature, and its ray
and primary velocity are the constructed source trajectories. -/

noncomputable section

namespace EulerParentPacketFrames

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerTransversePacketProvider EulerTransverseFrameCoordinates EulerVolterraConvolution
  EulerPacketSourceGeometry EulerPacketNormalizedPrimary EulerPacketMovingFrame
  EulerPacketPrimaryShear EulerPacketRay
open scoped ContDiff

namespace Parent

variable (G : Parent)

def sourceNormal (m : Space) (t : ℝ) : Space :=
  (G.inverse.realField G.T G.T_pos.le t 0).adjoint m

theorem sourceNormal_apply (m : Space) (t : Icc (0 : ℝ) G.T) :
    G.sourceNormal m t = (G.inverse.field t 0).adjoint m := by
  simp only [sourceNormal,SmoothTimeField.realField_apply]

theorem sourceNormal_equation (m : Space) (t : Icc (0 : ℝ) G.T) :
    HasDerivWithinAt (G.sourceNormal m)
      (-(G.centerStrain t).adjoint (G.sourceNormal m t)) (Icc (0 : ℝ) G.T) t := by
  have h := (EulerTransverseBoundedFrame.normalMap m).hasFDerivAt.comp_hasDerivWithinAt
    (t : ℝ) (G.inverse_time t 0)
  change HasDerivWithinAt (G.sourceNormal m) ((G.inverseDerivative.field t 0).adjoint m)
    (Icc (0 : ℝ) G.T) t at h
  apply h.congr_deriv
  rw [G.inverseDerivative_apply,G.sourceNormal_apply]
  have hb : G.centerStrain t = G.strain.field t 0 := by
    simp only [centerStrain,extendPath,projIcc_of_mem G.T_pos.le t.property]
  rw [hb,G.strain_apply]
  simp only [map_neg,adjoint_comp,neg_apply,comp_apply]

theorem sourceNormal_ne_zero (m : Space) (hm : m ≠ 0) (t : Icc (0 : ℝ) G.T) :
    G.sourceNormal m t ≠ 0 := by
  have hi : (G.inverse.field t 0).comp (G.frame.field t 0) = ContinuousLinearMap.id ℝ Space := by
    apply ContinuousLinearMap.ext
    intro v
    exact G.inverse_left t 0 v
  have hc := congrArg (fun A : Space →L[ℝ] Space => A.adjoint m) hi
  rw [adjoint_comp,comp_apply,adjoint_id,id_apply] at hc
  intro hz
  rw [← G.sourceNormal_apply m t,hz,map_zero] at hc
  exact hm hc.symm

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖=1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (S : Set Space) (hS : IsCompact S)

def sourceVelocity (η : U) (t : ℝ) : Space :=
  EulerPacketForwardFactorization.uncutVelocity (G.transverseData m hm R S hS) η t 0

omit [CompleteSpace U] in
theorem source_normal_eq (t : Icc (0 : ℝ) G.T) :
    (G.transverseData m hm R S hS).normal.field t 0 = G.sourceNormal m t := by
  rw [G.sourceNormal_apply]
  rfl

omit [CompleteSpace U] in
theorem source_strain_eq (t : Icc (0 : ℝ) G.T) :
    (G.transverseData m hm R S hS).M.field t 0 = G.centerStrain t := by
  simp only [centerStrain,extendPath,projIcc_of_mem G.T_pos.le t.property]
  rfl

theorem sourceVelocity_equation (η : U) (t : Icc (0 : ℝ) G.T) :
    HasDerivWithinAt (G.sourceVelocity m hm R S hS η)
      (-(G.centerStrain t) (G.sourceVelocity m hm R S hS η t)+
        (2*⟪G.sourceNormal m t,(G.centerStrain t) (G.sourceVelocity m hm R S hS η t)⟫_ℝ/
          ‖G.sourceNormal m t‖^2) • G.sourceNormal m t) (Icc (0 : ℝ) G.T) t := by
  have h := EulerPacketForwardFactorization.uncutVelocity_equation
    (G.transverseData m hm R S hS) η t 0
  erw [EulerPacketPrimaryFactorization.physicalGenerator_apply,
    G.source_normal_eq m hm R S hS,G.source_strain_eq m hm R S hS] at h
  exact h

theorem sourceVelocity_ne_zero (η : U) (hη : η ≠ 0) (t : Icc (0 : ℝ) G.T) :
    G.sourceVelocity m hm R S hS η t ≠ 0 :=
  EulerPacketForwardFactorization.uncutVelocity_ne_zero (G.transverseData m hm R S hS) η hη t 0

theorem sourceVelocity_tangent (η : U) (t : Icc (0 : ℝ) G.T) :
    ⟪G.sourceNormal m t,G.sourceVelocity m hm R S hS η t⟫_ℝ = 0 := by
  rw [← G.source_normal_eq m hm R S hS]
  exact EulerPacketForwardFactorization.uncutVelocity_tangent (G.transverseData m hm R S hS) η t 0

/-- Both primary branches are the same actual homogeneous propagator
after inserting their constructed initial coordinate. -/
theorem joined_sourceVelocity (s : ℝ) (hs : 0 < s) (hsT : s < G.T)
    (B : HistoryData ((G.transverseData m hm R S hS).initial s hs hsT.le)) (ξ : U) (t : ℝ) :
    G.sourceVelocity m hm R S hS (B.coefficients.labelCoordinate 0 ξ ⟨0,le_rfl,hs.le⟩) t =
      EulerPacketPrimaryFactorization.uncutVelocity s hs hsT B ξ t 0 := rfl

theorem joined_initialCoordinate_ne_zero (s : ℝ) (hs : 0 < s) (hsT : s < G.T)
    (B : HistoryData ((G.transverseData m hm R S hS).initial s hs hsT.le)) (ξ : U) (hξ : ξ ≠ 0) :
    B.coefficients.labelCoordinate 0 ξ ⟨0,le_rfl,hs.le⟩ ≠ 0 := by
  intro hz
  have hn := EulerPacketPrimaryFactorization.uncutVelocity_ne_zero s hs hsT B ξ hξ
    ⟨0,le_rfl,G.T_pos.le⟩ 0
  have hv := G.joined_sourceVelocity m hm R S hS s hs hsT B ξ 0
  rw [hz] at hv
  have hv0 : G.sourceVelocity m hm R S hS 0 0 = 0 := by
    unfold sourceVelocity
    rw [EulerPacketForwardFactorization.uncutVelocity_initial,map_zero]
  exact hn (hv.symm.trans hv0)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (D : Data V) (hTime : D.T = G.T) (τ : ℝ) (hτ : 0 ≤ τ)

/-- The only error input is the literal center derivative estimate for
the already constructed perturbation. No ray, velocity or matrix ODE
is supplied as a hypothesis. -/
def geometryFrameOfCenterExpansion (η : U) (hη : η ≠ 0)
    (w : ℝ → Space → Space) (c CM CH K error : ℝ)
    (hCM : 0 ≤ CM) (hK : 1 ≤ K) (he : 0 ≤ error)
    (hMK : CM ≤ K) (hHK : CM^2+CH ≤ K^2)
    (hM : ∀ t ∈ Icc τ D.T, ‖G.centerStrain t‖ ≤ CM)
    (hH : ∀ t ∈ Icc τ D.T, ‖G.centerCurvature t‖ ≤ CH)
    (hupdate : ∀ t : Icc (0 : ℝ) D.T,
      D.M.field t 0 = G.centerStrain t+fderiv ℝ (w t) 0)
    (hpacket : ∀ t ∈ Icc τ D.T,
      ‖fderiv ℝ (w t) 0-c • rankOne ℝ (G.sourceVelocity m hm R S hS η t) (G.sourceNormal m t)‖ ≤
        error) :
    ParentFrame D τ where
  B := G.centerStrain
  B₁ := G.centerStrainDerivative
  m := G.sourceNormal m
  v := G.sourceVelocity m hm R S hS η
  c := c
  G := K
  error := error
  G_lower := hK
  error_nonneg := he
  B_derivative t ht := by
    rw [hTime] at ht ⊢
    exact G.centerStrain_derivative τ hτ t ht
  ray_equation t ht := by
    have ht0 : t ∈ Icc (0 : ℝ) G.T := ⟨hτ.trans ht.1,by simpa only [hTime] using ht.2⟩
    exact (G.sourceNormal_equation m ⟨t,ht0⟩).mono
      (fun r hr => ⟨hτ.trans hr.1,by simpa only [hTime] using hr.2⟩)
  velocity_equation t ht := by
    have ht0 : t ∈ Icc (0 : ℝ) G.T := ⟨hτ.trans ht.1,by simpa only [hTime] using ht.2⟩
    exact (G.sourceVelocity_equation m hm R S hS η ⟨t,ht0⟩).mono
      (fun r hr => ⟨hτ.trans hr.1,by simpa only [hTime] using hr.2⟩)
  ray_nonzero t ht := by
    have hm0 : m ≠ 0 := by intro h; simp [h] at hm
    exact G.sourceNormal_ne_zero m hm0 ⟨t,hτ.trans ht.1,by simpa only [hTime] using ht.2⟩
  velocity_nonzero t ht :=
    G.sourceVelocity_ne_zero m hm R S hS η hη ⟨t,hτ.trans ht.1,by simpa only [hTime] using ht.2⟩
  tangent t ht :=
    G.sourceVelocity_tangent m hm R S hS η ⟨t,hτ.trans ht.1,by simpa only [hTime] using ht.2⟩
  B_bound t ht := (hM t ht).trans hMK
  B₁_bound t ht := by
    rw [hTime] at hM hH ht
    exact G.centerStrainDerivative_bound τ CM CH K hτ hCM hM hH hHK t ht
  remainder_bound t ht := by
    have htD : t ∈ Icc (0 : ℝ) D.T := ⟨hτ.trans ht.1,ht.2⟩
    have htG : t ∈ Icc (0 : ℝ) G.T := by simpa only [hTime] using htD
    have hm0 : m ≠ 0 := by intro h; simp [h] at hm
    have hn := G.sourceNormal_ne_zero m hm0 ⟨t,htG⟩
    have hv := G.sourceVelocity_ne_zero m hm R S hS η hη ⟨t,htG⟩
    have hc := rankOne_normalized c (G.sourceVelocity m hm R S hS η t) (G.sourceNormal m t) hv hn
    have hu := hupdate ⟨t,htD⟩
    rw [show D.clamp t = ⟨t,htD⟩ from Data.clamp_coe D ⟨t,htD⟩,hu,
      add_sub_cancel_left,primaryShear,← hc]
    exact hpacket t ht

end Parent
end EulerParentPacketFrames
