/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GraphInvariantFlow

@[expose] public section

/-! A graph-tangent lifted velocity has the same ordinary divergence
as its three-dimensional graph restriction. This identifies the
volume-preservation hypothesis for the actual physical-label flow. -/

noncomputable section

namespace EulerGraphInvariantFlow

open ContinuousLinearMap EulerLiftedGradientSpace

variable (k : ℝ) (m : Vector3) (f : LiftTangent → LiftTangent)

def graphVelocity (x : Vector3) : Vector3 := (f (graphLinear k m x)).1

theorem graphVelocity_trace (hf : Differentiable ℝ f)
    (hgraph : ∀ z, graphConstraint k m (f z)=0) (x : Vector3) :
    LinearMap.trace ℝ Vector3 (fderiv ℝ (graphVelocity k m f) x).toLinearMap =
      LinearMap.trace ℝ LiftTangent (fderiv ℝ f (graphLinear k m x)).toLinearMap := by
  let J := graphLinear k m
  let F := fst ℝ Vector3 ℝ
  let D := fderiv ℝ f (J x)
  have hfun : (J.comp F) ∘ f = f := by
    funext z
    apply Prod.ext
    · rfl
    · exact (sub_eq_zero.mp (hgraph z)).symm
  have hD : D = J.comp (F.comp D) := by
    have hd := ((J.comp F).hasFDerivAt.comp (J x) (hf (J x)).hasFDerivAt).fderiv
    rw [hfun] at hd
    exact hd
  have hg := (F.hasFDerivAt.comp x ((hf (J x)).hasFDerivAt.comp x J.hasFDerivAt)).fderiv
  change fderiv ℝ (graphVelocity k m f) x = F.comp (D.comp J) at hg
  rw [hg]
  calc
    _ = LinearMap.trace ℝ LiftTangent (J.comp (F.comp D)).toLinearMap :=
      LinearMap.trace_comp_comm' J.toLinearMap (F.comp D).toLinearMap
    _ = LinearMap.trace ℝ LiftTangent D.toLinearMap := by rw [← hD]

theorem graphVelocity_trace_zero (hf : Differentiable ℝ f)
    (hgraph : ∀ z, graphConstraint k m (f z)=0)
    (hdiv : ∀ z, LinearMap.trace ℝ LiftTangent (fderiv ℝ f z).toLinearMap=0)
    (x : Vector3) :
    LinearMap.trace ℝ Vector3 (fderiv ℝ (graphVelocity k m f) x).toLinearMap=0 := by
  rw [graphVelocity_trace k m f hf hgraph]
  exact hdiv _

end EulerGraphInvariantFlow
