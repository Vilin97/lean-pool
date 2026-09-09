/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketGeometryFrame
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketPhysicalCoefficients

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
