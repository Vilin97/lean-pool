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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
public import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Sectional curvature

This file defines the sectional-curvature expression attached to a pair of
tangent vectors, using the bundled curvature tensor.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [cov.ContMDiffCovariantDerivative 1]

/-- The scalar numerator appearing in sectional curvature. -/
noncomputable def sectionalCurvatureNumerator (x : M)
    (u v : TangentSpace I x) : ℝ :=
  inner ℝ (curvatureTensor (cov := cov) x u v v) u

/-- The Gram determinant attached to two tangent vectors. -/
noncomputable def sectionalCurvatureDenominator (x : M)
    (u v : TangentSpace I x) : ℝ :=
  inner ℝ u u * inner ℝ v v - (inner ℝ u v) ^ 2

/-- The sectional curvature associated to a nondegenerate pair of tangent vectors. -/
noncomputable def sectionalCurvature (x : M) (u v : TangentSpace I x)
    (_h : sectionalCurvatureDenominator x u v ≠ 0) : ℝ :=
  sectionalCurvatureNumerator (cov := cov) x u v /
    sectionalCurvatureDenominator x u v

@[simp]
lemma sectionalCurvatureNumerator_def (x : M) (u v : TangentSpace I x) :
    sectionalCurvatureNumerator (cov := cov) x u v =
      inner ℝ (curvatureTensor (cov := cov) x u v v) u := rfl

@[simp]
lemma sectionalCurvatureDenominator_def (x : M) (u v : TangentSpace I x) :
    sectionalCurvatureDenominator x u v =
      inner ℝ u u * inner ℝ v v - (inner ℝ u v) ^ 2 := rfl

@[simp]
lemma sectionalCurvature_def (x : M) (u v : TangentSpace I x)
    (h : sectionalCurvatureDenominator x u v ≠ 0) :
    sectionalCurvature (cov := cov) x u v h =
      inner ℝ (curvatureTensor (cov := cov) x u v v) u /
        (inner ℝ u u * inner ℝ v v - (inner ℝ u v) ^ 2) := rfl

/-- On a zero-dimensional tangent fiber, the sectional-curvature numerator vanishes. -/
lemma sectionalCurvatureNumerator_eq_zero_of_subsingleton_tangent
    (x : M) [Subsingleton (TangentSpace I x)] (u v : TangentSpace I x) :
    sectionalCurvatureNumerator (cov := cov) x u v = 0 := by
  have hu : u = 0 := Subsingleton.elim u 0
  subst u
  simp [sectionalCurvatureNumerator]

/-- On a zero-dimensional tangent fiber, the sectional-curvature Gram determinant vanishes. -/
lemma sectionalCurvatureDenominator_eq_zero_of_subsingleton_tangent
    (x : M) [Subsingleton (TangentSpace I x)] (u v : TangentSpace I x) :
    sectionalCurvatureDenominator (I := I) x u v = 0 := by
  have hu : u = 0 := Subsingleton.elim u 0
  subst u
  simp [sectionalCurvatureDenominator]

/-- Zero-dimensional tangent fibers have no nondegenerate two-planes. -/
theorem not_sectionalCurvatureDenominator_ne_zero_of_subsingleton_tangent
    (x : M) [Subsingleton (TangentSpace I x)] (u v : TangentSpace I x) :
    ¬ sectionalCurvatureDenominator (I := I) x u v ≠ 0 := by
  intro h
  exact h (sectionalCurvatureDenominator_eq_zero_of_subsingleton_tangent
    (I := I) (M := M) x u v)

end CovariantDerivative
