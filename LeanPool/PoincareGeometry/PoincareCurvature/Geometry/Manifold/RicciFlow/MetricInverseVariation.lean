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

public import LeanPool.PoincareGeometry.PoincareCurvature.Analysis.MatrixInverseDerivative
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.ScalarEvolution
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacianLocalFrame

/-!
# Time variation of the inverse metric

This file connects the finite inverse-matrix derivative to the actual metric
tensor of a time-dependent Riemannian metric.  In a genuine tangent-bundle
local frame it proves

`\partial_t g^{-1} = -g^{-1} (\partial_t g) g^{-1}`,

and, for an intrinsic Ricci flow, the geometric specialization

`\partial_t g^{ij} = 2 Ric^{ij}`.

The inverse regularity and nonsingularity are derived from the metric
components and positive definiteness; neither is assumed independently.
-/

@[expose] public section

noncomputable section

open Bundle Matrix
open scoped Manifold ContDiff

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Metric components in a genuine tangent-bundle local frame. -/
def localFrameMetricMatrix
    (g : MetricFamily (I := I) (M := M))
    (e : Trivialization E (π E TM)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι]
    (bas : Module.Basis ι ℝ E) (t : ℝ) (x : M) : Matrix ι ι ℝ :=
  fun i j => metricTensor (I := I) (M := M) g t x
    (e.localFrame bas i x) (e.localFrame bas j x)

/-- Components of a time-dependent covariant two-tensor in the same local frame. -/
def localFrameTensorMatrix
    (h : MetricTensorFamily (I := I) (M := M))
    (e : Trivialization E (π E TM)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι]
    (bas : Module.Basis ι ℝ E) (t : ℝ) (x : M) : Matrix ι ι ℝ :=
  fun i j => h t x (e.localFrame bas i x) (e.localFrame bas j x)

/-- Intrinsic Ricci components in the same genuine local frame. -/
def localFrameIntrinsicRicciMatrix
    [SigmaCompactSpace M]
    (g : MetricFamily (I := I) (M := M))
    (e : Trivialization E (π E TM)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι]
    (bas : Module.Basis ι ℝ E) (t : ℝ) (x : M) : Matrix ι ι ℝ :=
  fun i j => intrinsicRicciTensor (I := I) (M := M) g t x
    (e.localFrame bas i x) (e.localFrame bas j x)

/-- The local-frame inverse-metric contraction of intrinsic Ricci.  This is
kept explicitly as a coordinate presentation until it is identified with the
coordinate-free scalar curvature in a later bridge theorem. -/
def localFrameScalarCurvaturePresentation
    [SigmaCompactSpace M]
    (g : MetricFamily (I := I) (M := M))
    (e : Trivialization E (π E TM)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bas : Module.Basis ι ℝ E) (t : ℝ) (x : M) : ℝ :=
  PoincareCurvature.matrixContraction
    (localFrameMetricMatrix (I := I) (M := M) g e bas t x)⁻¹
    (localFrameIntrinsicRicciMatrix (I := I) (M := M) g e bas t x)

/-- The double inverse-metric contraction of two intrinsic Ricci tensors in a
local frame.  The later frame-invariance bridge will identify this presentation
with the coordinate-free squared Ricci norm. -/
def localFrameRicciNormSqPresentation
    [SigmaCompactSpace M]
    (g : MetricFamily (I := I) (M := M))
    (e : Trivialization E (π E TM)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bas : Module.Basis ι ℝ E) (t : ℝ) (x : M) : ℝ :=
  PoincareCurvature.matrixContraction
    ((localFrameMetricMatrix (I := I) (M := M) g e bas t x)⁻¹ *
      localFrameIntrinsicRicciMatrix (I := I) (M := M) g e bas t x *
      (localFrameMetricMatrix (I := I) (M := M) g e bas t x)⁻¹)
    (localFrameIntrinsicRicciMatrix (I := I) (M := M) g e bas t x)

/-- Positive definiteness makes every local-frame metric matrix nonsingular. -/
theorem localFrameMetricMatrix_det_ne_zero
    (g : MetricFamily (I := I) (M := M))
    (e : Trivialization E (π E TM)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ E)
    (t : ℝ) {x : M} (hx : x ∈ e.baseSet) :
    (localFrameMetricMatrix (I := I) (M := M) g e bas t x).det ≠ 0 := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  have hmatrix :
      localFrameMetricMatrix (I := I) (M := M) g e bas t x =
        CovariantDerivative.localFrameGramMatrix (I := I) e bas x := by
    ext i j
    rfl
  rw [hmatrix]
  exact CovariantDerivative.localFrameGramMatrix_det_ne_zero
    (I := I) (E := E) e bas hx

/-- A tensorial time derivative differentiates every local-frame metric
component with the corresponding tensor component as velocity. -/
theorem HasTimeDerivativeAt.hasDerivAt_localFrameMetricMatrix
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)} {t : ℝ}
    (h : HasTimeDerivativeAt (I := I) (M := M) g gdot t)
    (e : Trivialization E (π E TM)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι]
    (bas : Module.Basis ι ℝ E) (x : M) (i j : ι) :
    HasDerivAt
      (fun s => localFrameMetricMatrix (I := I) (M := M) g e bas s x i j)
      (localFrameTensorMatrix (I := I) (M := M) gdot e bas t x i j) t := by
  exact h x (e.localFrame bas i x) (e.localFrame bas j x)

/-- The inverse metric in a genuine local frame has the expected derivative.
This derives both inverse differentiability and invertibility from the evolving
Riemannian metric itself. -/
theorem HasTimeDerivativeAt.hasDerivAt_localFrameMetricMatrix_inv
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)} {t : ℝ}
    (h : HasTimeDerivativeAt (I := I) (M := M) g gdot t)
    (e : Trivialization E (π E TM)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ E)
    {x : M} (hx : x ∈ e.baseSet) (i j : ι) :
    HasDerivAt
      (fun s => (localFrameMetricMatrix (I := I) (M := M) g e bas s x)⁻¹ i j)
      ((-((localFrameMetricMatrix (I := I) (M := M) g e bas t x)⁻¹ *
          localFrameTensorMatrix (I := I) (M := M) gdot e bas t x *
          (localFrameMetricMatrix (I := I) (M := M) g e bas t x)⁻¹) : Matrix ι ι ℝ) i j) t := by
  apply PoincareCurvature.hasDerivAt_nonsing_inv_entry
  · intro k l
    exact h.hasDerivAt_localFrameMetricMatrix e bas x k l
  · intro s
    exact localFrameMetricMatrix_det_ne_zero g e bas s hx

/-- The trace of a genuine covariant two-tensor with respect to the metric at
time `t`.  This is defined intrinsically by pairing with the canonical inverse
metric tensor, rather than by choosing a frame. -/
def metricTraceAt
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (x : M)
    (B : TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ) : ℝ := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  exact TensorProduct.lift B (InnerProductSpace.canonicalCovariantTensor (TM x))

/-- Metric trace is linear under scalar multiplication of covariant
two-tensors. -/
theorem metricTraceAt_smul
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (x : M) (c : ℝ)
    (B : TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ) :
    metricTraceAt (I := I) (M := M) g t x (c • B) =
      c * metricTraceAt (I := I) (M := M) g t x B := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let o := stdOrthonormalBasis ℝ (TM x)
  unfold metricTraceAt
  rw [InnerProductSpace.canonicalCovariantTensor_eq_sum (TM x) o,
    map_sum, map_sum]
  simp [Finset.mul_sum]

/-- The intrinsic metric trace agrees with the inverse-Gram contraction in
every genuine local frame. -/
theorem matrixContraction_localFrameTensor_eq_metricTraceAt
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) {x : M}
    (B : TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    (e : Trivialization E (π E TM)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bas : Module.Basis ι ℝ E) (hx : x ∈ e.baseSet) :
    PoincareCurvature.matrixContraction
        (localFrameMetricMatrix (I := I) (M := M) g e bas t x)⁻¹
        (fun i j => B (e.localFrame bas i x) (e.localFrame bas j x)) =
      metricTraceAt (I := I) (M := M) g t x B := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  have hframe := CovariantDerivative.bilinearContraction_eq_sum_localFrame_inverseGram
    (I := I) (E := E) B e bas hx
  have hmatrix :
      localFrameMetricMatrix (I := I) (M := M) g e bas t x =
        CovariantDerivative.localFrameGramMatrix (I := I) e bas x := by
    ext i j
    rfl
  unfold metricTraceAt
  rw [hmatrix]
  simpa [PoincareCurvature.matrixContraction,
    CovariantDerivative.localFrameInverseGramMatrix] using hframe.symm

section IntrinsicFlow

variable [SigmaCompactSpace M]

/-- `ricciVelocity` is the intrinsic time derivative of the Ricci tensor at
`t` when every evaluation on fixed tangent vectors has the corresponding
ordinary real derivative.  Requiring a bilinear map on each tangent fiber
rules out arbitrary coordinate coefficient data. -/
def HasIntrinsicRicciTimeDerivativeAt
    (g : MetricFamily (I := I) (M := M))
    (ricciVelocity : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    (t : ℝ) : Prop :=
  ∀ (x : M) (u v : TM x),
    HasDerivAt
      (fun τ => intrinsicRicciTensor (I := I) (M := M) g τ x u v)
      (ricciVelocity x u v) t

/-- The intrinsic Ricci tensor with its bilinear structure retained.  The
older time-family API stores the same tensor only through its evaluations. -/
def intrinsicRicciBilinearAt
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (x : M) :
    TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
        (I := I) (M := M) g t) 1 :=
    CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g t
  exact CovariantDerivative.ricciCurvature
    (cov :=
      CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
        (I := I) (M := M) g t) x

@[simp] theorem intrinsicRicciBilinearAt_apply
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciBilinearAt (I := I) (M := M) g t x u v =
      intrinsicRicciTensor (I := I) (M := M) g t x u v := by
  simp [intrinsicRicciBilinearAt, intrinsicRicciTensor, ricciTensor]

/-- The local-frame contraction is exactly the coordinate-free scalar
curvature of the chosen intrinsic Levi-Civita slice.  Thus the presentation
used below is not an abstract coefficient surrogate. -/
theorem localFrameScalarCurvaturePresentation_eq_scalarCurvature
    (g : MetricFamily (I := I) (M := M))
    (e : Trivialization E (π E TM)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ E)
    (t : ℝ) {x : M} (hx : x ∈ e.baseSet) :
    localFrameScalarCurvaturePresentation (I := I) (M := M) g e bas t x =
      g.scalarCurvature
        (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
          (I := I) (M := M) g)
        (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
          (I := I) (M := M) g) t x := by
  let cov :=
    CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
      (I := I) (M := M) g
  let hcov :=
    CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1 := hcov t
  have hframe := CovariantDerivative.scalarCurvature_eq_sum_localFrame_inverseGram
    (I := I) (E := E) (cov t) e bas hx
  have hmatrix :
      localFrameMetricMatrix (I := I) (M := M) g e bas t x =
        CovariantDerivative.localFrameGramMatrix (I := I) e bas x := by
    ext i j
    rfl
  unfold localFrameScalarCurvaturePresentation
  rw [hmatrix]
  simpa [PoincareCurvature.matrixContraction,
    localFrameIntrinsicRicciMatrix,
    CovariantDerivative.localFrameInverseGramMatrix,
    intrinsicRicciTensor, ricciTensor, cov, hcov] using hframe.symm

/-- Scalar curvature is intrinsically the metric trace of the actual Ricci
bilinear form. -/
theorem metricTraceAt_intrinsicRicciBilinearAt_eq_scalarCurvature
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (x : M) :
    metricTraceAt (I := I) (M := M) g t x
        (intrinsicRicciBilinearAt (I := I) (M := M) g t x) =
      g.scalarCurvature
        (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
          (I := I) (M := M) g)
        (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
          (I := I) (M := M) g) t x := by
  let e : Trivialization E (π E TM) := trivializationAt E TM x
  let bas : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E TM x
  calc
    metricTraceAt (I := I) (M := M) g t x
        (intrinsicRicciBilinearAt (I := I) (M := M) g t x) =
        PoincareCurvature.matrixContraction
          (localFrameMetricMatrix (I := I) (M := M) g e bas t x)⁻¹
          (fun i j => intrinsicRicciBilinearAt (I := I) (M := M) g t x
            (e.localFrame bas i x) (e.localFrame bas j x)) :=
      (matrixContraction_localFrameTensor_eq_metricTraceAt
        (I := I) (M := M) g t
        (intrinsicRicciBilinearAt (I := I) (M := M) g t x) e bas hx).symm
    _ = localFrameScalarCurvaturePresentation
          (I := I) (M := M) g e bas t x := by
      unfold localFrameScalarCurvaturePresentation
      apply congrArg (PoincareCurvature.matrixContraction
        (localFrameMetricMatrix (I := I) (M := M) g e bas t x)⁻¹)
      ext i j
      exact intrinsicRicciBilinearAt_apply
        (I := I) (M := M) g t x (e.localFrame bas i x) (e.localFrame bas j x)
    _ = _ := localFrameScalarCurvaturePresentation_eq_scalarCurvature
      (I := I) (M := M) g e bas t hx

/-- The intrinsic Ricci-flow velocity is the genuine bilinear tensor
`-2 Ric`, with no coefficient presentation. -/
def intrinsicRicciFlowVelocityBilinearAt
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (x : M) :
    TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ :=
  (-2 : ℝ) • intrinsicRicciBilinearAt (I := I) (M := M) g t x

@[simp] theorem intrinsicRicciFlowVelocityBilinearAt_apply
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciFlowVelocityBilinearAt (I := I) (M := M) g t x u v =
      intrinsicRicciFlowRHS (I := I) (M := M) g t x u v := by
  simp [intrinsicRicciFlowVelocityBilinearAt, intrinsicRicciFlowRHS,
    ricciFlowRHS]

/-- The metric trace of the intrinsic Ricci-flow velocity is `-2 R`. -/
theorem metricTraceAt_intrinsicRicciFlowVelocityBilinearAt
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (x : M) :
    metricTraceAt (I := I) (M := M) g t x
        (intrinsicRicciFlowVelocityBilinearAt (I := I) (M := M) g t x) =
      -2 * g.scalarCurvature
        (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
          (I := I) (M := M) g)
        (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
          (I := I) (M := M) g) t x := by
  rw [intrinsicRicciFlowVelocityBilinearAt, metricTraceAt_smul,
    metricTraceAt_intrinsicRicciBilinearAt_eq_scalarCurvature]

/-- The double inverse-metric local-frame contraction is exactly the actual
Hilbert--Schmidt square of intrinsic Ricci. -/
theorem localFrameRicciNormSqPresentation_eq_ricciNormSq
    (g : MetricFamily (I := I) (M := M))
    (e : Trivialization E (π E TM)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ E)
    (t : ℝ) {x : M} (hx : x ∈ e.baseSet) :
    localFrameRicciNormSqPresentation (I := I) (M := M) g e bas t x =
      g.ricciNormSq
        (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
          (I := I) (M := M) g)
        (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
          (I := I) (M := M) g) t x := by
  let cov :=
    CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
      (I := I) (M := M) g
  let hcov :=
    CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1 := hcov t
  have hnorm := CovariantDerivative.bilinearNormSq_eq_sum_localFrame_inverseGram
    (I := I) (E := E) (CovariantDerivative.ricciCurvature (cov := cov t) x) e bas hx
  have hmatrix :
      localFrameMetricMatrix (I := I) (M := M) g e bas t x =
        CovariantDerivative.localFrameGramMatrix (I := I) e bas x := by
    ext i j
    rfl
  unfold localFrameRicciNormSqPresentation
  rw [hmatrix, PoincareCurvature.matrixContraction_mul_mul_eq_nested_sum]
  simpa [localFrameIntrinsicRicciMatrix, intrinsicRicciTensor, ricciTensor,
    CovariantDerivative.TimeDependentRiemannianMetric.ricciNormSq,
    CovariantDerivative.ricciNormSq,
    CovariantDerivative.localFrameInverseGramMatrix, cov, hcov] using hnorm.symm

/-- Along an intrinsic Ricci flow, the inverse metric evolves by twice the
fully raised intrinsic Ricci tensor, expressed here in a genuine local frame. -/
theorem IsIntrinsicRicciFlowOn.hasDerivAt_localFrameMetricMatrix_inv
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)} {s : Set ℝ}
    (hflow : IsIntrinsicRicciFlowOn (I := I) (M := M) g gdot s)
    {t : ℝ} (ht : t ∈ s)
    (e : Trivialization E (π E TM)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ E)
    {x : M} (hx : x ∈ e.baseSet) (i j : ι) :
    HasDerivAt
      (fun τ => (localFrameMetricMatrix (I := I) (M := M) g e bas τ x)⁻¹ i j)
      ((2 : ℝ) *
        (((localFrameMetricMatrix (I := I) (M := M) g e bas t x)⁻¹ *
          localFrameIntrinsicRicciMatrix (I := I) (M := M) g e bas t x *
          (localFrameMetricMatrix (I := I) (M := M) g e bas t x)⁻¹) i j)) t := by
  have hbase := (hflow.1 ht).hasDerivAt_localFrameMetricMatrix_inv e bas hx i j
  convert hbase using 1
  have hvelocity :
      localFrameTensorMatrix (I := I) (M := M) gdot e bas t x =
        (-2 : ℝ) • localFrameIntrinsicRicciMatrix (I := I) (M := M) g e bas t x := by
    ext k l
    simpa [localFrameTensorMatrix, localFrameIntrinsicRicciMatrix,
      intrinsicRicciFlowRHS, ricciFlowRHS, intrinsicRicciTensor] using
      hflow.2 ht x (e.localFrame bas k x) (e.localFrame bas l x)
  rw [hvelocity]
  simp [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]

/-- Product-rule decomposition for the local-frame scalar-curvature
presentation along Ricci flow.  It proves the complete contribution from the
evolving inverse metric, namely `2` times the double Ricci contraction.  The
remaining `g⁻¹ · ∂ₜ Ric` term is left explicit for the connection and
curvature-variation stage; no evolution identity is assumed here. -/
theorem IsIntrinsicRicciFlowOn.hasDerivAt_localFrameScalarCurvaturePresentation
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)} {s : Set ℝ}
    (hflow : IsIntrinsicRicciFlowOn (I := I) (M := M) g gdot s)
    {t : ℝ} (ht : t ∈ s)
    (e : Trivialization E (π E TM)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ E)
    {x : M} (hx : x ∈ e.baseSet)
    (ricciVelocity : Matrix ι ι ℝ)
    (hRicci : ∀ i j,
      HasDerivAt
        (fun τ => localFrameIntrinsicRicciMatrix (I := I) (M := M) g e bas τ x i j)
        (ricciVelocity i j) t) :
    HasDerivAt
      (fun τ => localFrameScalarCurvaturePresentation
        (I := I) (M := M) g e bas τ x)
      (2 * localFrameRicciNormSqPresentation
          (I := I) (M := M) g e bas t x +
        PoincareCurvature.matrixContraction
          (localFrameMetricMatrix (I := I) (M := M) g e bas t x)⁻¹ ricciVelocity) t := by
  have hcontract := PoincareCurvature.hasDerivAt_nonsing_inv_matrixContraction
    (A := fun τ => localFrameMetricMatrix (I := I) (M := M) g e bas τ x)
    (S := fun τ => localFrameIntrinsicRicciMatrix (I := I) (M := M) g e bas τ x)
    (Adot := localFrameTensorMatrix (I := I) (M := M) gdot e bas t x)
    (Sdot := ricciVelocity)
    (t := t)
    (fun i j => (hflow.1 ht).hasDerivAt_localFrameMetricMatrix e bas x i j)
    hRicci
    (fun τ => localFrameMetricMatrix_det_ne_zero g e bas τ hx)
  have hvelocity :
      localFrameTensorMatrix (I := I) (M := M) gdot e bas t x =
        (-2 : ℝ) • localFrameIntrinsicRicciMatrix (I := I) (M := M) g e bas t x := by
    ext i j
    simpa [localFrameTensorMatrix, localFrameIntrinsicRicciMatrix,
      intrinsicRicciFlowRHS, ricciFlowRHS, intrinsicRicciTensor] using
      hflow.2 ht x (e.localFrame bas i x) (e.localFrame bas j x)
  rw [hvelocity] at hcontract
  have hmatrix :
      -((localFrameMetricMatrix (I := I) (M := M) g e bas t x)⁻¹ *
          ((-2 : ℝ) • localFrameIntrinsicRicciMatrix (I := I) (M := M) g e bas t x) *
          (localFrameMetricMatrix (I := I) (M := M) g e bas t x)⁻¹) =
        (2 : ℝ) •
          ((localFrameMetricMatrix (I := I) (M := M) g e bas t x)⁻¹ *
            localFrameIntrinsicRicciMatrix (I := I) (M := M) g e bas t x *
            (localFrameMetricMatrix (I := I) (M := M) g e bas t x)⁻¹) := by
    ext i j
    simp [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [hmatrix] at hcontract
  simpa only [localFrameScalarCurvaturePresentation, localFrameRicciNormSqPresentation,
    PoincareCurvature.matrixContraction_smul_left] using hcontract

/-- Actual scalar-curvature variation along an intrinsic Ricci flow.  Both the
scalar curvature and the quadratic `2 |Ric|²` term are coordinate-free; only
the still-open Ricci-tensor variation trace is displayed in a local frame. -/
theorem IsIntrinsicRicciFlowOn.hasDerivAt_scalarCurvature_of_localFrameRicciDerivative
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)} {s : Set ℝ}
    (hflow : IsIntrinsicRicciFlowOn (I := I) (M := M) g gdot s)
    {t : ℝ} (ht : t ∈ s)
    (e : Trivialization E (π E TM)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ E)
    {x : M} (hx : x ∈ e.baseSet)
    (ricciVelocity : Matrix ι ι ℝ)
    (hRicci : ∀ i j,
      HasDerivAt
        (fun τ => localFrameIntrinsicRicciMatrix (I := I) (M := M) g e bas τ x i j)
        (ricciVelocity i j) t) :
    HasDerivAt
      (fun τ => g.scalarCurvature
        (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
          (I := I) (M := M) g)
        (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
          (I := I) (M := M) g) τ x)
      (2 * g.ricciNormSq
          (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
            (I := I) (M := M) g)
          (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
            (I := I) (M := M) g) t x +
        PoincareCurvature.matrixContraction
          (localFrameMetricMatrix (I := I) (M := M) g e bas t x)⁻¹ ricciVelocity) t := by
  have hpresentation :=
    hflow.hasDerivAt_localFrameScalarCurvaturePresentation
      ht e bas hx ricciVelocity hRicci
  have hreadout :
      (fun τ => localFrameScalarCurvaturePresentation
        (I := I) (M := M) g e bas τ x) =
      (fun τ => g.scalarCurvature
        (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
          (I := I) (M := M) g)
        (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
          (I := I) (M := M) g) τ x) := by
    funext τ
    exact localFrameScalarCurvaturePresentation_eq_scalarCurvature g e bas τ hx
  rw [hreadout] at hpresentation
  rw [localFrameRicciNormSqPresentation_eq_ricciNormSq g e bas t hx] at hpresentation
  exact hpresentation

/-- Coordinate-free scalar-curvature variation from a genuine intrinsic
Ricci-tensor time derivative.  The auxiliary local frame used in the proof is
eliminated from both the hypotheses and the conclusion. -/
theorem IsIntrinsicRicciFlowOn.hasDerivAt_scalarCurvature_of_intrinsicRicciTimeDerivative
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)} {s : Set ℝ}
    (hflow : IsIntrinsicRicciFlowOn (I := I) (M := M) g gdot s)
    {t : ℝ} (ht : t ∈ s) {x : M}
    (ricciVelocity : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ)
    (hRicci : HasIntrinsicRicciTimeDerivativeAt
      (I := I) (M := M) g ricciVelocity t) :
    HasDerivAt
      (fun τ => g.scalarCurvature
        (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
          (I := I) (M := M) g)
        (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
          (I := I) (M := M) g) τ x)
      (2 * g.ricciNormSq
          (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
            (I := I) (M := M) g)
          (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
            (I := I) (M := M) g) t x +
        metricTraceAt (I := I) (M := M) g t x (ricciVelocity x)) t := by
  let e : Trivialization E (π E TM) := trivializationAt E TM x
  let bas : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E TM x
  let V : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun i j => ricciVelocity x (e.localFrame bas i x) (e.localFrame bas j x)
  have hcomponents : ∀ i j,
      HasDerivAt
        (fun τ => localFrameIntrinsicRicciMatrix
          (I := I) (M := M) g e bas τ x i j)
        (V i j) t := by
    intro i j
    exact hRicci x (e.localFrame bas i x) (e.localFrame bas j x)
  have hlocal :=
    hflow.hasDerivAt_scalarCurvature_of_localFrameRicciDerivative
      ht e bas hx V hcomponents
  have htrace :
      PoincareCurvature.matrixContraction
          (localFrameMetricMatrix (I := I) (M := M) g e bas t x)⁻¹ V =
        metricTraceAt (I := I) (M := M) g t x (ricciVelocity x) := by
    exact matrixContraction_localFrameTensor_eq_metricTraceAt
      (I := I) (M := M) g t (ricciVelocity x) e bas hx
  rw [htrace] at hlocal
  exact hlocal

end IntrinsicFlow

end RicciFlow
