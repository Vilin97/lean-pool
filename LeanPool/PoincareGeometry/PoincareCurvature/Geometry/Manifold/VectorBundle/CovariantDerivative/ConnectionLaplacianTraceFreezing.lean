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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacianLocalFrame

/-!
# Freezing a metric trace in a local frame

This file isolates the algebra used when a quasilinear metric trace is frozen
at a fixed background metric.  The result is expressed in a genuine local
tangent frame: the difference between the two traces is exactly the
difference of their inverse Gram matrices contracted with the same covariant
Hessian.  Thus the principal second-order operator can be frozen without
hiding any second derivatives in the resulting coefficient difference.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

namespace CovariantDerivative

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)

/-- The inverse local Gram matrix determined by an explicitly supplied
Riemannian metric.  This wrapper makes it possible to put two metric traces in
one statement without relying on an ambient choice of `RiemannianBundle`. -/
noncomputable def localFrameInverseGramMatrixWith
    (g : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (x : M) : Matrix ι ι ℝ := by
  letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  exact localFrameInverseGramMatrix (I := I) e b x

/-- The connection Laplacian obtained by tracing with an explicitly supplied
Riemannian metric. -/
noncomputable def connectionLaplacianWith
    (g : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (cov : CovariantDerivative I E TM) (h : ∀ x : M, T₂ x) (x : M) : T₂ x := by
  letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  exact connectionLaplacian cov h x

/-- **Local-frame trace freezing for the covariant Hessian.**  Tracing with
`g` equals the trace with the fixed metric `g₀`, plus the inverse-Gram
difference contracted against the unchanged covariant Hessian. -/
theorem connectionLaplacianWith_eq_connectionLaplacianWith_add_sum_localFrame_inverseGram_sub
    (g g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (cov : CovariantDerivative I E TM) (h : ∀ x : M, T₂ x)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet) :
    connectionLaplacianWith (I := I) g cov h x =
      connectionLaplacianWith (I := I) g₀ cov h x +
        ∑ i : ι, ∑ j : ι,
          (localFrameInverseGramMatrixWith (I := I) g e b x i j -
            localFrameInverseGramMatrixWith (I := I) g₀ e b x i j) •
            covariantHessianTwoTensor cov h x
              (e.localFrame b i x) (e.localFrame b j x) := by
  have hg :
      connectionLaplacianWith (I := I) g cov h x =
        ∑ i : ι, ∑ j : ι,
          localFrameInverseGramMatrixWith (I := I) g e b x i j •
            covariantHessianTwoTensor cov h x
              (e.localFrame b i x) (e.localFrame b j x) := by
    letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    simpa [connectionLaplacianWith, localFrameInverseGramMatrixWith] using
      (connectionLaplacian_eq_sum_localFrame_inverseGram
        (I := I) (E := E) cov h e b hx)
  have hg₀ :
      connectionLaplacianWith (I := I) g₀ cov h x =
        ∑ i : ι, ∑ j : ι,
          localFrameInverseGramMatrixWith (I := I) g₀ e b x i j •
            covariantHessianTwoTensor cov h x
              (e.localFrame b i x) (e.localFrame b j x) := by
    letI : Bundle.RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩
    simpa [connectionLaplacianWith, localFrameInverseGramMatrixWith] using
      (connectionLaplacian_eq_sum_localFrame_inverseGram
        (I := I) (E := E) cov h e b hx)
  rw [hg, hg₀]
  simp_rw [sub_smul]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_sub_distrib]
  abel

/-- Pointwise scalar form of
`connectionLaplacianWith_eq_connectionLaplacianWith_add_sum_localFrame_inverseGram_sub`.
The only Hessian terms in the trace-freezing error are the displayed genuine
background covariant Hessian entries. -/
theorem connectionLaplacianWith_apply_eq_connectionLaplacianWith_apply_add_sum_localFrame_inverseGram_sub
    (g g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (cov : CovariantDerivative I E TM) (h : ∀ x : M, T₂ x)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet) (u v : TM x) :
    connectionLaplacianWith (I := I) g cov h x u v =
      connectionLaplacianWith (I := I) g₀ cov h x u v +
        ∑ i : ι, ∑ j : ι,
          (localFrameInverseGramMatrixWith (I := I) g e b x i j -
            localFrameInverseGramMatrixWith (I := I) g₀ e b x i j) *
            covariantHessianTwoTensor cov h x
              (e.localFrame b i x) (e.localFrame b j x) u v := by
  have htrace := connectionLaplacianWith_eq_connectionLaplacianWith_add_sum_localFrame_inverseGram_sub
    (I := I) (E := E) g g₀ cov h e b hx
  have hvalue := congrArg (fun q : T₂ x => q u v) htrace
  simpa [sum_apply, smul_eq_mul] using hvalue

end CovariantDerivative
