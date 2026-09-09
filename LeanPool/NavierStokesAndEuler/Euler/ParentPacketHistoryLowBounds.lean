/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketHessianSymmetry
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketJoinedInput
public import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointLabels

@[expose] public section

/-! Sharp physical low bounds give the actual center-history bounds used
in activation. These use the physical gradient and pressure Hessian;
they do not replace them by the high-order label envelope. -/

noncomputable section

namespace EulerParentPacketFrames.Parent

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransverseFrameCoordinates EulerTransversePacketProvider
  EulerTransverseSourceCoefficientPath EulerTimeIntervalRestriction
open scoped ContDiff

variable (G : Parent)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖=1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (S : Set Space) (hS : IsCompact S) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < G.T)

theorem history_strain_size_of_physical
    (u : Icc (0 : ℝ) G.T → Space → Space)
    (hu : ∀ t x, DifferentiableAt ℝ (u t) x)
    (hvelocity : ∀ t x, G.velocity.field t x=u t (G.position t x))
    (CM : ℝ) (hCM : 0 ≤ CM)
    (hbound : ∀ t x, ‖fderiv ℝ (u t) x‖ ≤ CM) :
    ‖pathEvaluation 0 ((G.transverseData m hm R S hS).initial τ hτ hτT.le).M.field‖ ≤ CM := by
  apply (ContinuousMap.norm_le _ hCM).2
  intro t
  change ‖G.strain.field (initialInclusion G.T τ hτT.le t) 0‖ ≤ CM
  rw [G.strain_physical u hu hvelocity]
  exact hbound _ _

theorem history_hessian_size_of_physical (H : LowBounds G)
    (p : Icc (0 : ℝ) G.T → Space → ℝ) (hp : ∀ t, ContDiff ℝ ∞ (p t))
    (hacceleration : ∀ t x, G.acceleration.field t x=-(gradient (p t) (G.position t x)))
    (CH : ℝ) (hCH : 0 ≤ CH)
    (hbound : ∀ t x, ‖fderiv ℝ (gradient (p t)) x‖ ≤ CH) :
    ‖(G.historyOn H m hm R S hS τ hτ hτT).coefficients.labelHessian 0‖ ≤ CH := by
  apply (ContinuousMap.norm_le _ hCH).2
  intro t
  change ‖G.curvature.field (initialInclusion G.T τ hτT.le t) 0‖ ≤ CH
  rw [G.curvature_physical (fun t => gradient (p t))
    (fun t x => ((EulerMeanSolenoidal.contDiff_gradient (hp t)).differentiable (by simp) x))
    hacceleration]
  exact hbound _ _

/-- The source's sharper pressure bound CH*hstar*hold supplies the
quadratic history bound when the older shear is at most hstar. -/
theorem activation_history_sizes_of_physical (H : LowBounds G)
    (u : Icc (0 : ℝ) G.T → Space → Space)
    (hu : ∀ t x, DifferentiableAt ℝ (u t) x)
    (hvelocity : ∀ t x, G.velocity.field t x=u t (G.position t x))
    (p : Icc (0 : ℝ) G.T → Space → ℝ) (hp : ∀ t, ContDiff ℝ ∞ (p t))
    (hacceleration : ∀ t x, G.acceleration.field t x=-(gradient (p t) (G.position t x)))
    (CM CH hstar hold : ℝ) (hCM : 0 ≤ CM) (hCH : 0 ≤ CH) (hhstar : 0 ≤ hstar)
    (hhold : 0 ≤ hold) (horder : hold ≤ hstar)
    (hM : ∀ t x, ‖fderiv ℝ (u t) x‖ ≤ CM*hstar)
    (hP : ∀ t x, ‖fderiv ℝ (gradient (p t)) x‖ ≤ CH*hstar*hold) :
    ‖pathEvaluation 0 ((G.transverseData m hm R S hS).initial τ hτ hτT.le).M.field‖ ≤ CM*hstar ∧
    ‖(G.historyOn H m hm R S hS τ hτ hτT).coefficients.labelHessian 0‖ ≤ CH*hstar^2 := by
  refine ⟨G.history_strain_size_of_physical m hm R S hS τ hτ hτT u hu hvelocity
    (CM*hstar) (mul_nonneg hCM hhstar) hM, ?_⟩
  refine (G.history_hessian_size_of_physical m hm R S hS τ hτ hτT H p hp hacceleration
    (CH*hstar*hold) (by positivity) hP).trans ?_
  nlinarith only [mul_le_mul_of_nonneg_left horder (mul_nonneg hCH hhstar)]

end EulerParentPacketFrames.Parent
