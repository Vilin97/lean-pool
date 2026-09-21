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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.StandardDeTurckDerivative

/-!
# Local trace-derivative formula for the standard DeTurck field

This file records the local-frame form of the derivative of the genuine
standard DeTurck trace.  It uses an actual differentiability hypothesis for
the complete explicit Levi-Civita correction, derives differentiability of
its frame components, and keeps the derivative of the inverse Gram matrix
visible.  The formula is deliberately prior to any normal-frame reduction,
derivative commutation, or Ricci--DeTurck cancellation.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Filter
open scoped Manifold ContDiff Topology

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "TCorr" =>
  (fun x : M => TM x →L[ℝ] TM x →L[ℝ] TM x)

/-- Differentiability of the complete explicit Levi-Civita correction gives
differentiability of every local component used in the standard DeTurck
trace. -/
theorem standardDeTurckCorrectionLocalComponent_mdifferentiableAt_of_mdiff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet)
    (hA : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] E)) (E := TCorr) y
        (explicitLeviCivitaCorrection (I := I) (M := M) g background t y)) x)
    (k i j : ι) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (standardDeTurckCorrectionLocalComponent (I := I) (M := M)
        g background t e b k i j) x := by
  have hframe (q : ι) : MDiffAt (T% (e.localFrame b q)) x :=
    (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
      (n := 1) (i := q) (hx := hx)).mdifferentiableAt one_ne_zero
  have hAij : MDiffAt (T% (fun y =>
      explicitLeviCivitaCorrection (I := I) (M := M) g background t y
        (e.localFrame b j y) (e.localFrame b i y))) x :=
    (hA.clm_bundle_apply (hframe j)).clm_bundle_apply (hframe i)
  change MDiffAt (fun y => e.localFrameCoeff I b k y
    (explicitLeviCivitaCorrection (I := I) (M := M) g background t y
      (e.localFrame b j y) (e.localFrame b i y))) x
  exact mdifferentiableAt_localFrameCoeff (I := I) (e := e) (b := b)
    hx hAij k

/-- **Exact local inverse-Gram trace derivative.**

The derivative of the standard DeTurck trace is the derivative of the
correction components plus the full inverse-Gram derivative
`-G⁻¹ (dG) G⁻¹`.  The hypothesis is differentiability of the complete
correction tensor, rather than independently assumed component regularity.
This is the local-frame precursor to the intrinsic orthonormal-frame trace
identity. -/
theorem mvfderiv_standardDeTurckVectorField_localFrameCoeff_apply_of_mdiff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet)
    (X : TM x) (k : ι)
    (hA : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] E)) (E := TCorr) y
        (explicitLeviCivitaCorrection (I := I) (M := M) g background t y)) x) :
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
    mvfderiv (I := I)
        (fun y => e.localFrameCoeff I b k y
          (standardDeTurckVectorField (I := I) (M := M) g background t y)) x X =
      ∑ i : ι, ∑ j : ι, (
        CovariantDerivative.localFrameInverseGramMatrix (I := I) e b x i j *
          mvfderiv (I := I)
            (standardDeTurckCorrectionLocalComponent (I := I) (M := M)
              g background t e b k i j) x X +
        standardDeTurckCorrectionLocalComponent (I := I) (M := M)
            g background t e b k i j x *
          (-(
            (show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) e b x)⁻¹ *
            (show Matrix ι ι ℝ from fun p q => mvfderiv (I := I)
              (fun y => CovariantDerivative.localFrameGramMatrix (I := I) e b y p q)
              x X) *
            (show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) e b x)⁻¹)) i j) := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  apply mvfderiv_standardDeTurckVectorField_localFrameCoeff_apply
    (I := I) (M := M) g background t e b hx X k
  intro i j
  exact standardDeTurckCorrectionLocalComponent_mdifferentiableAt_of_mdiff
    (I := I) (M := M) g background t e b hx hA k i j

end RicciFlow
