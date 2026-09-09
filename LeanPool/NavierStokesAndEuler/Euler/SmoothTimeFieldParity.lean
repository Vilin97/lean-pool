/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldTimeJets
public import Mathlib.Algebra.Group.EvenFunction

@[expose] public section

/-! Spatial derivatives and genuine within-time derivatives preserve
the expected parity, including the closed interval's endpoints. -/

noncomputable section

namespace SmoothTimeField

open Set ContinuousLinearMap EulerVolterraConvolution
open scoped ContDiff

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem fderiv_even_of_odd (f : E → V) (hf : ContDiff ℝ ∞ f) (ho : Function.Odd f) :
    Function.Even (fderiv ℝ f) := by
  intro x
  have he : (fun y => f (-y)) = fun y => -f y := funext ho
  have h1 := ((hf.differentiable (by simp) (-x)).hasFDerivAt).comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).neg)
  have h2 := ((hf.differentiable (by simp) x).hasFDerivAt).neg
  have hfd : fderiv ℝ (fun y => -f y) x = -fderiv ℝ f x := h2.fderiv
  have hd : -fderiv ℝ f x = -fderiv ℝ f (-x) := by
    simpa only [Function.comp_def,he,hfd,comp_neg,comp_id] using h1.fderiv
  exact neg_injective hd.symm

theorem TimeDerivative.odd {T : ℝ} {hT : 0 ≤ T}
    {A A1 : SmoothTimeField (Icc (0 : ℝ) T) E V}
    (hd : TimeDerivative T hT A A1) (hTpos : 0 < T)
    (ho : ∀ t, Function.Odd (A.field t : E → V)) (t : Icc (0 : ℝ) T) :
    Function.Odd (A1.field t : E → V) := by
  intro x
  have h1 := hd t (-x)
  have h2 := (hd t x).neg
  have he : (fun r => A.realField T hT r (-x)) = fun r => -A.realField T hT r x :=
    funext fun r => ho (projIcc 0 T hT r) x
  rw [he] at h1
  have hs := uniqueDiffOn_Icc hTpos (t : ℝ) t.property
  exact (h1.derivWithin hs).symm.trans (h2.derivWithin hs)

end SmoothTimeField
