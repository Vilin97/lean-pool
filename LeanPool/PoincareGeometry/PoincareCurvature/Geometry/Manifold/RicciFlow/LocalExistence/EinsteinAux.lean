/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Auxiliary scalar-calculus lemma for the Einstein homothetic solution

This thin module proves scalar-linearity of the scalar exterior derivative in a
lightweight manifold context, so that the heavier `Einstein.lean` module can use
it without re-elaborating the proof in its much richer instance environment.
-/

@[expose] public noncomputable section

open scoped Manifold ContDiff
open NormedSpace

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Scalar-linearity of the scalar exterior derivative, applied to a tangent vector. -/
lemma extDerivFun_const_smul_apply (c : ℝ) {f : M → ℝ} {x : M} (u : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :
    mvfderiv (I := I) (fun y ↦ c * f y) x u = c * mvfderiv (I := I) f x u := by
  have hfun : (fun y : M ↦ c * f y) = (fun _ : M ↦ c) • f := by
    funext y; simp [smul_eq_mul]
  rw [hfun]
  rw [mvfderiv_smul mdifferentiableAt_const hf]
  simp [mvfderiv_const]


end RicciFlow
