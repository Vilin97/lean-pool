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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.RieszCovariantDerivative

/-!
# Affine derivative of a metric trace

For an arbitrary affine connection, differentiating the metric trace of a
covariant two-tensor produces the trace of its covariant derivative together
with the explicit contraction of the connection's metric defect.  This avoids
silently imposing metric compatibility when a metric is used to raise an
index before taking the ordinary endomorphism trace.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff BigOperators

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "EndTM" => (fun x : M => TM x →L[ℝ] TM x)

/-- The affine derivative of the metric trace of a genuine covariant
 two-tensor.  The second summand is the exact inverse-metric correction:
 it vanishes precisely when the chosen connection is metric-compatible. -/
theorem mvfderiv_covariantTwoTensorTraceFunction_eq_sum_covariantDerivative_sub_metricDefect
    (cov : CovariantDerivative I E TM)
    (h : ∀ y : M, T₂ y) {x : M}
    (hh : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (h y)) x)
    (X : TM x) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TM x)) :
    mvfderiv (I := I)
        (covariantTwoTensorTraceFunction (I := I) (E := E) h) x X =
      ∑ i, (covariantTwoTensorCovariantDerivative cov h x X (b i) (b i) -
        cov.metricDefect x
          (raisedCovariantTwoTensor (I := I) (E := E) h x (b i)) (b i) X) := by
  let A : ∀ y : M, EndTM y :=
    raisedCovariantTwoTensor (I := I) (E := E) h
  have hA : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] E) (E := EndTM) y (A y)) x := by
    simpa [A] using
      (raisedCovariantTwoTensor_mdifferentiableAt (I := I) (E := E) (M := M)
        (h := h) hh)
  have htrace :
      covariantTwoTensorTraceFunction (I := I) (E := E) h =
        endomorphismTrace (F := E) (V := TM) A := by
    simpa [A] using
      (covariantTwoTensorTraceFunction_eq_endomorphismTrace_raised
        (I := I) (E := E) (M := M) h)
  rw [htrace,
    mvfderiv_endomorphismTrace_eq_trace_endomorphismCovariantDerivativeAt
      (I := I) (E := E) (M := M) cov A hA X,
    LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm]
  change inner ℝ
    (endomorphismCovariantDerivativeApply cov A x X (b i)) (b i) = _
  simpa [A] using
    (inner_endomorphismCovariantDerivative_raisedCovariantTwoTensor_eq
      (I := I) (E := E) (M := M) cov hh X (b i) (b i))

/-- The same affine trace derivative, with the metric-defect contraction
 collected outside the trace of the covariant derivative. -/
theorem mvfderiv_covariantTwoTensorTraceFunction_eq_sum_covariantDerivative_sub_sum_metricDefect
    (cov : CovariantDerivative I E TM)
    (h : ∀ y : M, T₂ y) {x : M}
    (hh : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (h y)) x)
    (X : TM x) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TM x)) :
    mvfderiv (I := I)
        (covariantTwoTensorTraceFunction (I := I) (E := E) h) x X =
      (∑ i, covariantTwoTensorCovariantDerivative cov h x X (b i) (b i)) -
        ∑ i, cov.metricDefect x
          (raisedCovariantTwoTensor (I := I) (E := E) h x (b i)) (b i) X := by
  rw [mvfderiv_covariantTwoTensorTraceFunction_eq_sum_covariantDerivative_sub_metricDefect
    (I := I) (E := E) (M := M) cov h hh X b,
    Finset.sum_sub_distrib]

end CovariantDerivative
