/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.StandardDeTurck

/-!
# Background-covariant principal part for standard Ricci--DeTurck flow

This file names the genuine background-covariant second-order operator that
will supply the principal part of the standard Ricci--DeTurck equation. It is
the metric trace of the background covariant Hessian of the evolving metric.
The input is a connection family and may vary with time; a later analytic
construction must select and freeze an appropriate background. No claim is
made here that the remaining Ricci--DeTurck terms have already been
identified with a lower-order reaction.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff Topology

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The background-covariant principal part for the standard Ricci--DeTurck
equation: the trace, with respect to the evolving metric, of the background
covariant Hessian of that metric. -/
noncomputable def standardDeTurckBackgroundLaplacian
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M)) :
    MetricTensorFamily (I := I) (M := M) :=
  fun t x u v ↦ by
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    exact CovariantDerivative.connectionLaplacian (background t) ((g t).toSection) x u v

@[simp] theorem standardDeTurckBackgroundLaplacian_apply
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    standardDeTurckBackgroundLaplacian (I := I) (M := M) g background t x u v = by
      letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      exact CovariantDerivative.connectionLaplacian (background t) ((g t).toSection) x u v := rfl

/-- In a local frame, the background-covariant principal part is the inverse
Gram-matrix contraction of the genuine background covariant Hessian. -/
theorem standardDeTurckBackgroundLaplacian_eq_sum_localFrame_inverseGram
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet) :
    standardDeTurckBackgroundLaplacian (I := I) (M := M) g background t x =
      (letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
       fun u v ↦ ∑ i : ι, ∑ j : ι,
         CovariantDerivative.localFrameInverseGramMatrix (I := I) e b x i j *
           CovariantDerivative.covariantHessianTwoTensor (background t) ((g t).toSection) x
             (e.localFrame b i x) (e.localFrame b j x) u v) := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  funext u v
  change CovariantDerivative.connectionLaplacian (background t) ((g t).toSection) x u v = _
  have h := CovariantDerivative.connectionLaplacian_eq_sum_localFrame_inverseGram
    (background t) ((g t).toSection) e b hx
  simpa [sum_apply, smul_eq_mul] using congrArg (fun q => q u v) h

/-- The background-covariant principal part preserves the metric symmetry in its
two untraced tensor slots. -/
theorem standardDeTurckBackgroundLaplacian_symm
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    standardDeTurckBackgroundLaplacian (I := I) (M := M) g background t x u v =
      standardDeTurckBackgroundLaplacian (I := I) (M := M) g background t x v u := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  rw [standardDeTurckBackgroundLaplacian_apply,
    standardDeTurckBackgroundLaplacian_apply]
  exact CovariantDerivative.connectionLaplacian_swap (background t)
    (fun y a b ↦ (g t).symm y a b) x u v

end RicciFlow
