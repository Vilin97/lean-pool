/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardPrimary
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryFactorization
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourcePropagator
import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryDynamics
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketInitialRepresentative

/-! The actual zero-history primary is the compact angular profile times
the genuine homogeneous physical propagator.  Its scalar pressure has the
literal normal residual as its angular derivative. -/

@[expose] public section


noncomputable section

namespace EulerPacketForwardFactorization

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLiftedGradientSpace EulerTransversePacketProvider EulerPacketForwardPrimary
  EulerSourceCylinderClassical EulerCylinderSmoothOrbit EulerLpCylinderPaths
  EulerPacketPrimaryFactorization EulerPacketSourcePropagator EulerLinearDuhamel
  EulerPacketTerminalDatum EulerSpatialCutoffs EulerPeriodicProfile EulerMetricTransport
open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U)

section General

variable {P : ℝ} [Fact (0 < P)] (Y : InitialData P D)

theorem scalar_angle (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    HasDerivAt (fun s => scalar D Y (t,(x,s)))
      (-(2*⟪D.normal.field t x,D.M.field t x (vector D Y (t,(x,θ)))⟫_ℝ)/
        ‖D.normal.field t x‖^2) θ := by
  let G := forcing (P := P) D
  have hforce : pointField P (includePath P D.support D.support_measurable G.path)
      G.path_orbit t (x,(θ : AddCircle P)) = 0 := (G.raw_eq t x θ).symm
  have hp := pressureField_angle P D.support D.support_measurable D.support_compact
    D.T D.T_pos.le D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower
    G.path Y.value G.path_orbit Y.orbit D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    G.mean_zero Y.mean_zero t x θ
  have hn : normalResidual P D.support D.support_measurable D.support_compact
      D.T D.T_pos.le D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower
      G.path Y.value G.path_orbit Y.orbit D.M D.normal t (x,(θ : AddCircle P)) =
      -(2*⟪D.normal.field t x,D.M.field t x (vector D Y (t,(x,θ)))⟫_ℝ)/
        ‖D.normal.field t x‖^2 := by
    unfold normalResidual
    rw [hforce]
    simp only [inner_zero_right,zero_sub,EulerPacketForwardPrimary.vector,
      Forcing.vector,Data.clamp_coe,G]
  convert! hp.congr_deriv hn using 1
  funext s
  simp only [EulerPacketForwardPrimary.scalar,Forcing.scalar,Data.clamp_coe,G]

theorem vector_homogeneous_time (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    HasDerivWithinAt (fun s => vector D Y (s,(x,θ)))
      (physicalGenerator D x t (vector D Y (t,(x,θ)))) (Icc (0 : ℝ) D.T) t := by
  have hb := (forcing D).equation Y t x θ
  simp only [Data.strain,Data.normalField,Data.clamp_coe,Pi.zero_apply] at hb
  change derivative D Y (t,(x,θ))+D.M.field t x (vector D Y (t,(x,θ))) +
    deriv (fun s => scalar D Y (t,(x,s))) θ • D.normal.field t x=0 at hb
  rw [(scalar_angle D Y t x θ).deriv] at hb
  simp only [neg_div,neg_smul] at hb
  apply ((forcing D).vector_hasDerivWithinAt Y t x θ).congr_deriv
  rw [physicalGenerator_apply]
  linear_combination (norm := module) hb

end General

/-- Uncut velocity, given by `physical D ⟨0,le_rfl,D.T_pos.le⟩ x ξ t`. -/
def uncutVelocity (ξ : U) (t : ℝ) (x : Space) : Space :=
  physical D ⟨0,le_rfl,D.T_pos.le⟩ x ξ t

/-- Canonical velocity, given by `innerCutoff x • uncutVelocity D ξ t x`. -/
def canonicalVelocity (ξ : U) (t : ℝ) (x : Space) : Space :=
  innerCutoff x • uncutVelocity D ξ t x

theorem uncutVelocity_initial (ξ : U) (x : Space) :
    uncutVelocity D ξ 0 x = D.frame.field ⟨0,le_rfl,D.T_pos.le⟩ x ξ := by
  change physical D ⟨0,le_rfl,D.T_pos.le⟩ x ξ ((⟨0,le_rfl,D.T_pos.le⟩ : Icc (0 : ℝ) D.T) : ℝ)=_
  rw [physical_at,propagator_self]

theorem uncutVelocity_equation (ξ : U) (t : Icc (0 : ℝ) D.T) (x : Space) :
    HasDerivWithinAt (fun s => uncutVelocity D ξ s x)
      (physicalGenerator D x t (uncutVelocity D ξ t x)) (Icc (0 : ℝ) D.T) t := by
  rw [physicalGenerator_apply]
  exact physical_hasDerivWithinAt D ⟨0,le_rfl,D.T_pos.le⟩ t x ξ

theorem uncutVelocity_tangent (ξ : U) (t : Icc (0 : ℝ) D.T) (x : Space) :
    ⟪D.normal.field t x,uncutVelocity D ξ t x⟫_ℝ=0 :=
  physical_tangent D ⟨0,le_rfl,D.T_pos.le⟩ t x ξ

private theorem homogeneous_unique (T : ℝ) (hT : 0 ≤ T)
    (G : C(Icc (0 : ℝ) T, Space →L[ℝ] Space)) (f g : ℝ → Space)
    (hf : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt f (G t (f t)) (Icc (0 : ℝ) T) t)
    (hg : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt g (G t (g t)) (Icc (0 : ℝ) T) t)
    (h0 : f 0=g 0) (t : Icc (0 : ℝ) T) : f t=g t := by
  let E := constructedEvolution T hT G
  have he (a : ℝ → Space) (ha : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt a (G t (a t)) (Icc (0 : ℝ) T) t) : a t=E.solution 0 (a 0) t :=
    E.solution_unique 0 (a 0) a
      (fun s => by simpa only [ContinuousMap.zero_apply,add_zero] using ha s) rfl t
  rw [he f hf,he g hg,h0]

theorem vector_initial (δ : ℝ) (hδ : 0 < δ) (ξ : U)
    (hs : tsupport innerCutoff ⊆ D.support) (x : Space) (θ : ℝ) :
    vector D (initialData D δ hδ ξ hs) (0,(x,θ)) =
      (innerCutoff x*profile δ θ) • D.frame.field ⟨0,le_rfl,D.T_pos.le⟩ x ξ := by
  change (forcing D).vector (initialData D δ hδ ξ hs) (0,(x,θ)) = _
  rw [(forcing D).vector_initial_of_representative
    (initialData D δ hδ ξ hs) (EulerPacketTerminalDatum.field δ ξ)
    (smoothField_continuous period _ (field_smooth δ hδ ξ)) (terminal_ae δ hδ ξ),
    field_coe,map_smul]

theorem vector_factorization (δ : ℝ) (hδ : 0 < δ) (ξ : U)
    (hs : tsupport innerCutoff ⊆ D.support) (a : ℝ)
    (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    vector D (initialData D δ hδ (a • ξ) hs) (t,(x,θ)) =
      (a*profile δ θ) • canonicalVelocity D ξ t x := by
  apply homogeneous_unique D.T D.T_pos.le (physicalGenerator D x)
    (fun s => vector D (initialData D δ hδ (a • ξ) hs) (s,(x,θ)))
    (fun s => (a*profile δ θ) • canonicalVelocity D ξ s x)
    (fun s => vector_homogeneous_time D _ s x θ) _ _ t
  · intro s
    simp only [canonicalVelocity,map_smul]
    convert! ((uncutVelocity_equation D ξ s x).const_smul (innerCutoff x)).const_smul
      (a*profile δ θ) using 1
  · rw [vector_initial]
    simp only [canonicalVelocity,uncutVelocity_initial,map_smul,smul_smul]
    congr 1
    ring

theorem uncutVelocity_ne_zero (ξ : U) (hξ : ξ ≠ 0) (t : Icc (0 : ℝ) D.T) (x : Space) :
    uncutVelocity D ξ t x ≠ 0 := by
  intro ht
  have hz := (constructedEvolution D.T D.T_pos.le (physicalGenerator D x)).homogeneous_zero_at
    (fun s => uncutVelocity D ξ s x) (fun s => uncutVelocity_equation D ξ s x)
    t ⟨0,le_rfl,D.T_pos.le⟩ ht
  change uncutVelocity D ξ 0 x=0 at hz
  rw [uncutVelocity_initial] at hz
  have hl := D.frame_lower ⟨0,le_rfl,D.T_pos.le⟩ x ξ
  rw [hz,norm_zero,zero_pow (by decide : 2 ≠ 0)] at hl
  have hn : 0 < D.frameLower*‖ξ‖^2 := mul_pos D.frameLower_pos
    (pow_pos (norm_pos_iff.mpr hξ) 2)
  exact (not_le_of_gt hn) hl

end EulerPacketForwardFactorization
