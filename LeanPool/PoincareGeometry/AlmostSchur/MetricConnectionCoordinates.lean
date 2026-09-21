/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.ConnectionCoordinates
public import LeanPool.PoincareGeometry.AlmostSchur.LocalMetricDivergence
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric

/-!
# Metric compatibility in actual tangent coordinates

The derivatives below concern the supplied Riemannian metric and connection.
They are consequences of metric compatibility, not an additional coordinate
compatibility hypothesis.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise

namespace AlmostSchur

section Gram

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A linear map on the first entry of a Gram pairing is left multiplication
by the transpose of its matrix. -/
theorem gram_inner_linear_left (b : Module.Basis ι ℝ V) (L : V →L[ℝ] F)
    (A : V →L[ℝ] V) (i j : ι) :
    inner ℝ (L (A (b i))) (L (b j)) =
      ((LinearMap.toMatrix b b A.toLinearMap).transpose *
        Matrix.gram ℝ (fun k => L (b k))) i j := by
  conv_lhs => rw [← b.sum_repr (A (b i))]
  simp only [map_sum, map_smul, sum_inner, real_inner_smul_left, Matrix.mul_apply,
    Matrix.transpose_apply, LinearMap.toMatrix_apply, Matrix.gram_apply]
  rfl

/-- A linear map on the second entry of a Gram pairing is right multiplication
by its matrix. -/
theorem gram_inner_linear_right (b : Module.Basis ι ℝ V) (L : V →L[ℝ] F)
    (A : V →L[ℝ] V) (i j : ι) :
    inner ℝ (L (b i)) (L (A (b j))) =
      (Matrix.gram ℝ (fun k => L (b k)) *
        LinearMap.toMatrix b b A.toLinearMap) i j := by
  conv_lhs => rw [← b.sum_repr (A (b j))]
  simp only [map_sum, map_smul, inner_sum, real_inner_smul_right, Matrix.mul_apply,
    LinearMap.toMatrix_apply, Matrix.gram_apply, mul_comm]
  rfl

end Gram

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Smoothness of the actual metric supplies its continuous-bundle property. -/
theorem continuousRiemannianBundle_of_contMDiff :
    IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) := by
  obtain ⟨g, hg, he⟩ :=
    IsContMDiffRiemannianBundle.exists_contMDiff (IB := I) (n := 1) (F := E) (E := TM)
  exact ⟨g, hg.continuous, he⟩

/-- Mathlib's metric-compatibility predicate specialized to the actual
Riemannian tangent fibers, with their norm instances fixed explicitly. -/
def tangentMetricCompatible (cov : CovariantDerivative I E TM) : Prop :=
  @CovariantDerivative.IsMetricCompatible E _ _ H _ I M _ _ E _ _ TM _
    (fun _x => inferInstance) (fun _x => inferInstance) _ cov _ _ _ _

/-- The chart derivative of a metric coefficient follows from the actual
connection's metric compatibility applied to the local frame. -/
theorem fderiv_coordinateMetric_entry
    (cov : CovariantDerivative I E TM)
    (hcov : tangentMetricCompatible cov)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    (c x : M) (hx : x ∈ (chartAt H c).source) (u : E) (i j : ι) :
    let e := trivializationAt E TM c
    fderiv ℝ (fun z => coordinateMetric (I := I) b c z i j) (extChartAt I c x) u =
      inner ℝ (cov (e.localFrame b i) x (e.symmL ℝ x u)) (e.symmL ℝ x (b j)) +
        inner ℝ (e.symmL ℝ x (b i)) (cov (e.localFrame b j) x (e.symmL ℝ x u)) := by
  let e := trivializationAt E TM c
  have hxe : x ∈ e.baseSet := hx
  have hs (k : ι) : MDiffAt (T% (e.localFrame b k)) x :=
    (contMDiffAt_localFrame_of_mem 1 e b k hxe).mdifferentiableAt (by simp)
  have hd := fderiv_chart_comp
    (fun y => inner ℝ (e.localFrame b i y) (e.localFrame b j y)) c x hx
    (MDifferentiableAt.inner_bundle (F := E) (E := TM) (hs i) (hs j)) u
  have hm := CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq hcov
    (fun y => e.symmL ℝ y u) (hs i) (hs j)
  simp only [localFrame_eq_symmL] at hd hm
  exact hd.trans hm

/-- A C1 Riemannian metric has a differentiable matrix in each tangent chart. -/
theorem differentiableAt_coordinateMetric
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    (c x : M) (hx : x ∈ (chartAt H c).source) :
    DifferentiableAt ℝ (coordinateMetric (I := I) b c) (extChartAt I c x) := by
  let e := trivializationAt E TM c
  have hxe : x ∈ e.baseSet := hx
  have hs (k : ι) : MDiffAt (T% (e.localFrame b k)) x :=
    (contMDiffAt_localFrame_of_mem 1 e b k hxe).mdifferentiableAt (by simp)
  have hx' : x ∈ (extChartAt I c).source := by simpa using hx
  have hi : MDiffAt (extChartAt I c).symm (extChartAt I c x) := by
    simpa only [I.range_eq_univ, mdifferentiableWithinAt_univ] using
      (mdifferentiableWithinAt_extChartAt_symm (I := I) (x := c)
        ((extChartAt I c).map_source hx'))
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  have hm := MDifferentiableAt.inner_bundle (F := E) (E := TM) (hs i) (hs j)
  have hc := mdifferentiableAt_iff_differentiableAt.mp
    (hm.comp_of_eq (extChartAt I c x) hi ((extChartAt I c).left_inv hx'))
  simpa only [Function.comp_def, localFrame_eq_symmL, coordinateMetric,
    tangentChartGram, tangentTrivializationGram, Matrix.gram_apply, e] using hc

/-- C1 regularity of the actual coordinate metric on its open chart domain. -/
theorem contDiffOn_coordinateMetric
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E) (c : M) :
    ContDiffOn ℝ 1 (coordinateMetric (I := I) b c) (extChartAt I c).target := by
  intro z hz
  let x := (extChartAt I c).symm z
  let e := trivializationAt E TM c
  have hx : x ∈ e.baseSet := by
    change (extChartAt I c).symm z ∈ (chartAt H c).source
    simpa only [extChartAt_source] using (extChartAt I c).map_target hz
  have hs (k : ι) : CMDiffAt 1 (T% (e.localFrame b k)) x :=
    contMDiffAt_localFrame_of_mem 1 e b k hx
  have hi : CMDiffAt 1 (extChartAt I c).symm z :=
    (contMDiffOn_extChartAt_symm c z hz).contMDiffAt ((isOpen_extChartAt_target c).mem_nhds hz)
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  have hm := ContMDiffAt.inner_bundle (F := E) (E := TM) (hs i) (hs j)
  have hc := (hm.comp z hi).contDiffAt
  simpa only [Function.comp_def, localFrame_eq_symmL, coordinateMetric,
    tangentChartGram, tangentTrivializationGram, Matrix.gram_apply, e] using hc

/-- The matrix derivative of the actual metric is the usual connection
compatibility expression, derived from the metric connection predicate. -/
theorem coordinateMetric_compatibility
    (cov : CovariantDerivative I E TM) (hcov : tangentMetricCompatible cov)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    (c x : M) (hx : x ∈ (chartAt H c).source) (u : E) :
    let e := trivializationAt E TM c
    let A := LinearMap.toMatrix b b (frameConnectionCoefficients cov e b x u).toLinearMap
    fderiv ℝ (coordinateMetric (I := I) b c) (extChartAt I c x) u =
      A.transpose * tangentChartGram (I := I) b c x +
        tangentChartGram (I := I) b c x * A := by
  let e := trivializationAt E TM c
  have hxe : x ∈ e.baseSet := hx
  have hG := differentiableAt_coordinateMetric (I := I) b c x hx
  have he (k : ι) : e.symmL ℝ x (frameConnectionCoefficients cov e b x u (b k)) =
      cov (e.localFrame b k) x (e.symmL ℝ x u) := by
    rw [frameConnectionCoefficients_basis, e.symmL_continuousLinearMapAt hxe]
  ext i j
  have hd := fderiv_coordinateMetric_entry cov hcov b c x hx u i j
  have hGi := (differentiableAt_pi.mp hG) i
  rw [fderiv_apply hGi j, fderiv_apply hG i] at hd
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at hd
  rw [← he i, ← he j, gram_inner_linear_left, gram_inner_linear_right] at hd
  exact hd

end AlmostSchur
