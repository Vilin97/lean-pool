/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacian

/-!
# Change of the induced connection on covariant two-tensors

This file records the tensorial effect of adding a tangent-bundle-valued
one-form to an affine connection.  Mathlib's `CovariantDerivative.addOneForm`
uses `A x u X`, where `u` is the vector being differentiated and `X` is the
direction.  The order is made explicit in the formula below.
-/

@[expose] public section

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]

namespace CovariantDerivative

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)

/-- Adding `A` to a tangent-bundle connection changes its induced connection
on covariant two-tensors by applying `A` in each covariant tensor slot.

The argument order follows `CovariantDerivative.addOneForm`: in `A x u X`,
`u` is the vector being differentiated and `X` is the covariant-derivative
direction. -/
theorem covariantTwoTensorCovariantDerivative_addOneForm_apply
    (cov : CovariantDerivative I E TM)
    (A : Π x : M, TM x →L[ℝ] TM x →L[ℝ] TM x)
    {h : ∀ x : M, T₂ x} {x : M}
    (hh : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (h y)) x)
    (X u v : TM x) :
    covariantTwoTensorCovariantDerivative (CovariantDerivative.addOneForm cov A) h x X u v =
      covariantTwoTensorCovariantDerivative cov h x X u v
        - h x (A x u X) v - h x u (A x v X) := by
  rw [covariantTwoTensorCovariantDerivative_apply_of_mdifferentiableAt
      (CovariantDerivative.addOneForm cov A) hh X u v,
    covariantTwoTensorCovariantDerivative_apply_of_mdifferentiableAt cov hh X u v]
  simp only [CovariantDerivative.addOneForm, add_apply, smoothExtend_apply]
  simp only [map_add, add_apply]
  abel

end CovariantDerivative
