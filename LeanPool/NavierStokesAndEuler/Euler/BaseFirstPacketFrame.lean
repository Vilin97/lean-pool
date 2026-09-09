/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BaseFirstPacketEvolution
import LeanPool.NavierStokesAndEuler.Euler.BasePacketFrameValues

/-! The first actual packet has the precise initial frame parameters
a=1, sigma=sqrt(beta), and the prescribed polynomial shear. -/

@[expose] public section


noncomputable section

namespace EulerBaseDatum.FirstPacketChoice

open Set InnerProductSpace EulerSmoothLimit EulerParentPacketFrames EulerPacketSupport
  EulerPacketSourceFrequency EulerPacketSourceGeometry EulerTransverseFrameCoordinates

variable {β : ℝ} {hβ : |β| ≤ 1} {ell : ℝ} {hell : 0 < ell} {hell1 : ell ≤ 1}
  {T : ℝ} {hT : 0 < T} {hTB : T ≤ initialTime}
  {δ : ℝ} {hδ : 0 < δ} {hchild k : ℝ} {hk : UniversalFrequency k}
  {nextEll : ℝ} {hnext : 0 < nextEll} {hnext1 : nextEll ≤ 1}
  (F : FirstPacketChoice β hβ ell hell hell1 T hT hTB δ hδ hchild k hk nextEll hnext hnext1)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (S : Set Space) (hS : IsCompact S)

/-- Initial frame as an element of `ParentFrame (F.parent.transverseData m hm R S hS) 0`. -/
def initialFrame : ParentFrame (F.parent.transverseData m hm R S hS) 0 := by
  let B := packetBaseState β hβ ell hell hell1 T hT hTB
  have h0 := initialCoefficientCost_nonneg
  exact B.forwardRenewal F.state rfl firstNormal firstNormal_unit firstFrame support compact
    m hm R S hS 0 le_rfl initialCoefficientCost initialCoefficientCost (1+initialCoefficientCost)
    (k^(-(1/4 : ℝ))) h0 (le_add_of_nonneg_right h0) (Real.rpow_nonneg hk.pos.le _)
    (le_add_of_nonneg_left zero_le_one) (by nlinarith only [h0])
    (fun t _ => packetBase_strain_bound β hβ ell hell hell1 T hT hTB (projIcc 0 T hT.le t) 0)
    (fun t _ => packetBase_curvature_bound β hβ ell hell hell1 T hT hTB (projIcc 0 T hT.le t) 0)
    δ hδ (δ*hchild) k firstCoordinate
    (by intro h; have he := firstCoordinate_norm; rw [h,norm_zero] at he; norm_num at he)
    (fun t _ => F.center_error t)

theorem initialFrame_parameters :
    (F.initialFrame m hm R S hS).a=1 ∧
    (F.initialFrame m hm R S hS).sigma=Real.sqrt β ∧
    (F.initialFrame m hm R S hS).shear=hchild := by
  apply first_frame_parameters β hβ ell hell hell1 T hT hTB (F.initialFrame m hm R S hS) hchild
  · rfl
  · rfl
  · rfl
  · change (δ*hchild)/δ=hchild
    field_simp

theorem initialFrame_costs :
    (F.initialFrame m hm R S hS).G=1+initialCoefficientCost ∧
    (F.initialFrame m hm R S hS).error=k^(-(1/4 : ℝ)) := ⟨rfl,rfl⟩

end EulerBaseDatum.FirstPacketChoice
