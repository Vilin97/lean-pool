/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketSourceData

/-! The coefficient factory agrees with the physical velocity gradient
and pressure Hessian. The only matching data are the literal Lagrangian
velocity and acceleration laws, not separate coefficient identities. -/

@[expose] public section


noncomputable section

namespace EulerParentPacketFrames

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerMeanCoefficients
  EulerMeanBoundary EulerMeanHarmonic
open scoped ContDiff

namespace Parent

variable (G : Parent)

/-- Position, given by `x+G.displacement.field t x`. -/
def position (t : Icc (0 : ℝ) G.T) (x : Space) : Space :=
  x+G.displacement.field t x

@[simp] theorem position_initial (x : Space) : G.position G.zeroTime x=x := by
  change x+G.displacement.field ⟨0,le_rfl,G.T_pos.le⟩ x=x
  rw [G.initial,add_zero]

theorem position_hasFDerivAt (t : Icc (0 : ℝ) G.T) (x : Space) :
    HasFDerivAt (G.position t) (ContinuousLinearMap.id ℝ Space +
      fderiv ℝ (G.displacement.field t : Space → Space) x) x :=
  (hasFDerivAt_id x).add ((G.displacement.smooth t).differentiable (by
      norm_num)).differentiableAt.hasFDerivAt

theorem position_frame (t : Icc (0 : ℝ) G.T) (x : Space) :
    HasFDerivAt (G.position t) (G.frame.field t x) (G.ell • x) := by
  rw [G.frame_apply]
  exact G.position_hasFDerivAt t (G.ell • x)

variable (u force : Icc (0 : ℝ) G.T → Space → Space)
  (hu : ∀ t x, DifferentiableAt ℝ (u t) x)
  (hf : ∀ t x, DifferentiableAt ℝ (force t) x)
  (hvelocity : ∀ t x, G.velocity.field t x = u t (G.position t x))
  (hacceleration : ∀ t x, G.acceleration.field t x = -(force t (G.position t x)))

include hu hvelocity in
theorem first_physical (t : Icc (0 : ℝ) G.T) (x : Space) :
    G.first.field t x =
      (fderiv ℝ (u t) (G.position t (G.ell • x))).comp (G.frame.field t x) := by
  rw [G.first_apply]
  have he : (G.velocity.field t : Space → Space) = (u t) ∘ G.position t :=
    funext (hvelocity t)
  rw [he]
  exact ((hu t (G.position t (G.ell • x))).hasFDerivAt.comp (G.ell • x)
    (G.position_frame t x)).fderiv

include hf hacceleration in
theorem second_physical (t : Icc (0 : ℝ) G.T) (x : Space) :
    G.second.field t x =
      -((fderiv ℝ (force t) (G.position t (G.ell • x))).comp (G.frame.field t x)) := by
  rw [G.second_apply]
  have he : (G.acceleration.field t : Space → Space) = fun y => -(force t (G.position t y)) :=
    funext (hacceleration t)
  rw [he]
  exact (((hf t (G.position t (G.ell • x))).hasFDerivAt.comp (G.ell • x)
    (G.position_frame t x)).neg).fderiv

include hu hvelocity in
theorem strain_physical (t : Icc (0 : ℝ) G.T) (x : Space) :
    G.strain.field t x = fderiv ℝ (u t) (G.position t (G.ell • x)) := by
  rw [G.strain_apply,G.first_physical u hu hvelocity]
  apply ContinuousLinearMap.ext
  intro v
  simp only [comp_apply,G.inverse_right]

include hf hacceleration in
theorem curvature_physical (t : Icc (0 : ℝ) G.T) (x : Space) :
    G.curvature.field t x = fderiv ℝ (force t) (G.position t (G.ell • x)) := by
  rw [G.curvature_apply,G.second_physical force hf hacceleration]
  apply ContinuousLinearMap.ext
  intro v
  simp only [neg_apply,comp_apply,G.inverse_right,neg_neg]

include hu hvelocity in
theorem initialStrain_physical (x : Space) :
    G.initialStrain.field x = fderiv ℝ (u G.zeroTime) (G.ell • x) := by
  rw [G.initialStrain_apply,G.first_physical u hu hvelocity,G.position_initial,G.frame_initial]
  exact ContinuousLinearMap.comp_id _

/-- The source low-order hypotheses follow from the actual physical
gradient at time zero and the actual physical pressure-force derivative. -/
def lowBoundsOfPhysical (Be Bc L r K : ℝ)
    (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc) (hL : boundaryLocalizationC1 * Bc ≤ L)
    (hr : 0 ≤ r) (hrq : r ≤ 1 / 4) (hK : 0 ≤ K)
    (hexterior : ∀ x, r ≤ ‖x‖ → ∀ v : Space,
      -Be*‖v‖^2 ≤ ⟪fderiv ℝ (u G.zeroTime) x v,v⟫_ℝ)
    (hcore : ∀ x, ‖x‖ < r → ∀ v : Space,
      -Bc*‖v‖^2 ≤ ⟪fderiv ℝ (u G.zeroTime) x v,v⟫_ℝ)
    (hpressure : ∀ t x v, ⟪fderiv ℝ (force t) x v,v⟫_ℝ ≤ K*‖v‖^2)
    (hsmall : K*(G.T^2/2)+Be*G.T+boundaryLocalizationC2*Bc*r^3*G.T ≤ 1/2) :
    LowBounds G where
  Be := Be
  Bc := Bc
  L := L
  r := r
  K := K
  Be_nonneg := hBe
  Bc_nonneg := hBc
  L_lower := hL
  r_nonneg := hr
  r_le_quarter := hrq
  K_nonneg := hK
  exterior_lower x hx v := by
    rw [G.initialStrain_physical u hu hvelocity]
    exact hexterior (G.ell • x) hx v
  core_lower x hx v := by
    rw [G.initialStrain_physical u hu hvelocity]
    exact hcore (G.ell • x) hx v
  curvature_upper t x v := by
    rw [G.curvature_physical force hf hacceleration]
    exact hpressure t (G.position t (G.ell • x)) v
  small := hsmall

end Parent
end EulerParentPacketFrames
