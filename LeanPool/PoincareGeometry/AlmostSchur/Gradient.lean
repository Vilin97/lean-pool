/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Tactic

/-!
# The intrinsic Riemannian gradient

The gradient is the Riesz representative of the actual manifold differential.
This module supplies infrastructure, not an almost-Schur inequality.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

local instance (x : M) : FiniteDimensional ℝ (TangentSpace I x) :=
  VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x

/-- Riesz representative of the scalar manifold differential. As with `mfderiv`,
the definition is total; its differential interpretation requires differentiability. -/
def gradient (f : M → ℝ) (x : M) : TangentSpace I x :=
  (InnerProductSpace.toDual ℝ (TangentSpace I x)).symm (mvfderiv (I := I) f x)

/-- The metric pairing of the gradient is the actual differential. -/
theorem inner_gradient (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    inner ℝ (gradient (I := I) f x) v = mvfderiv (I := I) f x v := by
  exact InnerProductSpace.toDual_symm_apply

/-- Intrinsic gradient uniqueness: no choice of coordinates or frame remains. -/
theorem gradient_eq_of_inner (f : M → ℝ) (x : M) (w : TangentSpace I x)
    (hw : ∀ v, inner ℝ w v = mvfderiv (I := I) f x v) :
    gradient (I := I) f x = w := by
  apply ext_inner_right ℝ
  intro v
  exact (inner_gradient f x v).trans (hw v).symm

/-- Zero gradient is exactly zero manifold differential. -/
theorem gradient_eq_zero_iff (f : M → ℝ) (x : M) :
    gradient (I := I) f x = 0 ↔ mvfderiv (I := I) f x = 0 := by
  constructor
  · intro h
    ext v
    simpa [h] using (inner_gradient (I := I) f x v).symm
  · intro h
    simp [gradient, h]

/-- Riesz duality preserves the norm, using the Riemannian tangent norm. -/
theorem norm_gradient (f : M → ℝ) (x : M) :
    ‖gradient (I := I) f x‖ = ‖mvfderiv (I := I) f x‖ := by
  exact (InnerProductSpace.toDual ℝ (TangentSpace I x)).symm.norm_map _

/-- Directional differentiation along the gradient gives its squared norm. -/
theorem differential_gradient (f : M → ℝ) (x : M) :
    mvfderiv (I := I) f x (gradient (I := I) f x) = ‖gradient (I := I) f x‖ ^ 2 := by
  rw [← inner_gradient]
  exact real_inner_self_eq_norm_sq _

end AlmostSchur
