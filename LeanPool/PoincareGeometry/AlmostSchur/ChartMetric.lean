/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.MetricDensity
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# The actual tangent metric in bundle coordinates

The Gram matrix below is built from the Riemannian inner product on the tangent
fibers and inverse tangent trivializations. Its positive definiteness and
coordinate transformation are consequences of the bundle API.
-/

@[expose] public noncomputable section
open Bundle Set
open scoped BigOperators Manifold

namespace AlmostSchur

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

omit [DecidableEq ι] in
/-- Gram matrices transform by congruence under a change of frame. -/
theorem gram_matrix_combination (u : ι → F) (P : Matrix ι ι ℝ) :
    Matrix.gram ℝ (fun i => ∑ j, P j i • u j) =
      P.transpose * Matrix.gram ℝ u * P := by
  ext i j
  simp only [Matrix.gram_apply, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem gram_linear_comp (b : Module.Basis ι ℝ E) (L : E →L[ℝ] F) (P : E →L[ℝ] E) :
    Matrix.gram ℝ (fun i => L (P (b i))) =
      (LinearMap.toMatrix b b P.toLinearMap).transpose *
        Matrix.gram ℝ (fun i => L (b i)) * LinearMap.toMatrix b b P.toLinearMap := by
  have heq (i : ι) : L (P (b i)) =
      ∑ j, LinearMap.toMatrix b b P.toLinearMap j i • L (b j) := by
    simpa only [LinearMap.toMatrix_apply, map_sum, map_smul] using!
      congrArg L (b.sum_repr (P (b i))).symm
  simp_rw [heq]
  exact gram_matrix_combination _ _

variable [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

/-- Coordinate Gram matrix of the actual tangent metric in a trivialization. -/
def tangentTrivializationGram
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I) → M))
    [e.IsLinear ℝ] (b : Module.Basis ι ℝ E) (x : M) : Matrix ι ι ℝ :=
  Matrix.gram ℝ (fun i => e.symmL ℝ x (b i))

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
theorem tangentTrivializationGram_posDef
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I) → M))
    [e.IsLinear ℝ] (b : Module.Basis ι ℝ E) (x : M) (hx : x ∈ e.baseSet) :
    (tangentTrivializationGram e b x).PosDef := by
  apply Matrix.posDef_gram_of_linearIndependent
  convert! (b.map (e.linearEquivAt ℝ x hx).symm).linearIndependent using 1
  ext i
  simp [Module.Basis.map_apply, e.symmL_apply hx]

omit [FiniteDimensional ℝ E] in
theorem tangentTrivializationGram_density_pos
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I) → M))
    [e.IsLinear ℝ] (b : Module.Basis ι ℝ E) (x : M) (hx : x ∈ e.baseSet) :
    0 < matrixDensity (tangentTrivializationGram e b x) :=
  matrixDensity_pos _ (tangentTrivializationGram_posDef e b x hx)

omit [FiniteDimensional ℝ E] [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- The same tangent vectors in two coordinate frames. -/
theorem tangentTrivialization_symmL_change
    (e e' : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I) → M))
    [e.IsLinear ℝ] [e'.IsLinear ℝ] (x : M) (hx : x ∈ e.baseSet ∩ e'.baseSet) (v : E) :
    e.symmL ℝ x v = e'.symmL ℝ x (e.coordChangeL ℝ e' x v) := by
  have h := e'.symmL_continuousLinearMapAt (R := ℝ) hx.2 (e.symmL ℝ x v)
  have hcoord : e'.continuousLinearMapAt ℝ x (e.symmL ℝ x v) =
      e.coordChangeL ℝ e' x v := by
    simpa only [e.symmL_apply hx.1, Trivialization.continuousLinearMapAt_apply_of_mem ℝ e' hx.2]
      using (e.coordChangeL_apply (R := ℝ) e' hx v).symm
  rw [hcoord] at h
  exact h.symm

omit [FiniteDimensional ℝ E] in
/-- Congruence of actual tangent Gram matrices on the overlap. -/
theorem tangentTrivializationGram_change
    (e e' : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I) → M))
    [e.IsLinear ℝ] [e'.IsLinear ℝ] (b : Module.Basis ι ℝ E) (x : M)
    (hx : x ∈ e.baseSet ∩ e'.baseSet) :
    tangentTrivializationGram e b x =
      (LinearMap.toMatrix b b (e.coordChangeL ℝ e' x).toLinearEquiv.toLinearMap).transpose *
        tangentTrivializationGram e' b x *
          LinearMap.toMatrix b b (e.coordChangeL ℝ e' x).toLinearEquiv.toLinearMap := by
  unfold tangentTrivializationGram
  have heq : (fun i => e.symmL ℝ x (b i)) =
      fun i => e'.symmL ℝ x (e.coordChangeL ℝ e' x (b i)) :=
    funext fun i => tangentTrivialization_symmL_change e e' x hx (b i)
  rw [heq]
  exact gram_linear_comp b (e'.symmL ℝ x) (e.coordChangeL ℝ e' x).toContinuousLinearMap

omit [FiniteDimensional ℝ E] in
theorem tangentTrivializationGram_density_change
    (e e' : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I) → M))
    [e.IsLinear ℝ] [e'.IsLinear ℝ] (b : Module.Basis ι ℝ E) (x : M)
    (hx : x ∈ e.baseSet ∩ e'.baseSet) :
    matrixDensity (tangentTrivializationGram e b x) =
      |(e.coordChangeL ℝ e' x).toLinearEquiv.toLinearMap.det| *
        matrixDensity (tangentTrivializationGram e' b x) := by
  rw [tangentTrivializationGram_change e e' b x hx, matrixDensity_congruence,
    LinearMap.det_toMatrix]

/-- Gram matrix of the Riemannian metric in the preferred tangent chart. -/
def tangentChartGram (b : Module.Basis ι ℝ E) (c x : M) : Matrix ι ι ℝ :=
  tangentTrivializationGram (trivializationAt E (TangentSpace I) c) b x

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
theorem tangentChartGram_posDef (b : Module.Basis ι ℝ E) (c x : M)
    (hx : x ∈ (chartAt H c).source) : (tangentChartGram (I := I) b c x).PosDef :=
  tangentTrivializationGram_posDef _ b x hx

variable [I.Boundaryless]

omit [FiniteDimensional ℝ E] [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- The tangent bundle transition is the actual derivative of the coordinate
change, with the boundaryless model's derivative taken on the whole space. -/
theorem tangentChart_transition_fderiv (c c' x : M)
    (hx : x ∈ (chartAt H c).source ∩ (chartAt H c').source) :
    ((trivializationAt E (TangentSpace I) c).coordChangeL ℝ
      (trivializationAt E (TangentSpace I) c') x).toContinuousLinearMap =
      fderiv ℝ (extChartAt I c' ∘ (extChartAt I c).symm) (extChartAt I c x) := by
  ext v
  have h := (tangentBundleCore I M).trivializationAt_coordChange_eq
    (b₀ := c) (b₁ := c') (b := x) hx v
  simpa only [tangentBundleCore_indexAt, tangentBundleCore_coordChange_achart, I.range_eq_univ,
    fderivWithin_univ] using! h

omit [FiniteDimensional ℝ E] in
/-- The density transformation for the actual Riemannian metric. -/
theorem tangentChart_density_transition (b : Module.Basis ι ℝ E) (c c' x : M)
    (hx : x ∈ (chartAt H c).source ∩ (chartAt H c').source) :
    matrixDensity (tangentChartGram (I := I) b c x) =
      |(fderiv ℝ (extChartAt I c' ∘ (extChartAt I c).symm) (extChartAt I c x)).det| *
        matrixDensity (tangentChartGram (I := I) b c' x) := by
  have h := tangentTrivializationGram_density_change
    (trivializationAt E (TangentSpace I) c) (trivializationAt E (TangentSpace I) c') b x hx
  change matrixDensity (tangentChartGram (I := I) b c x) =
    |((trivializationAt E (TangentSpace I) c).coordChangeL ℝ
      (trivializationAt E (TangentSpace I) c') x).toContinuousLinearMap.det| *
        matrixDensity (tangentChartGram (I := I) b c' x) at h
  rwa [tangentChart_transition_fderiv c c' x hx] at h

/-- The preferred-chart metric as a matrix field on the coordinate space.
Only its values on the chart target are used in local integration. -/
def coordinateMetric (b : Module.Basis ι ℝ E) (c : M) (y : E) : Matrix ι ι ℝ :=
  tangentChartGram (I := I) b c ((extChartAt I c).symm y)

omit [I.Boundaryless] [DecidableEq ι] [FiniteDimensional ℝ E] in
theorem coordinateMetric_posDef (b : Module.Basis ι ℝ E) (c : M) (y : E)
    (hy : y ∈ (extChartAt I c).target) : (coordinateMetric (I := I) b c y).PosDef := by
  apply tangentChartGram_posDef
  simpa only [extChartAt_source] using (extChartAt I c).map_target hy

omit [I.Boundaryless] [FiniteDimensional ℝ E] in
theorem coordinateMetric_density_pos (b : Module.Basis ι ℝ E) (c : M) (y : E)
    (hy : y ∈ (extChartAt I c).target) : 0 < matrixDensity (coordinateMetric (I := I) b c y) :=
  matrixDensity_pos _ (coordinateMetric_posDef b c y hy)

end AlmostSchur
