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
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.ExplicitLeviCivitaCorrectionLocalFrame

/-!
# Torsion-free local expansion of the differentiated standard DeTurck field

This file substitutes the torsion-free Koszul formula for the explicit
Levi-Civita correction into the local derivative formula for the standard
DeTurck field.  The result retains both the derivative of the correction
component and the inverse-Gram derivative term.  It makes no derivative
commutation, cancellation, principal-symbol, or reaction-term assertion.
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
/-- **Torsion-free Koszul expansion of the derivative of a standard DeTurck
component.**

At a point in the local frame domain, the correction component in each of the
two product-rule summands is replaced by its inverse-Gram Koszul formula.  In
particular, the first summand still visibly differentiates that complete
formula, while the second still visibly contains the derivative of the outer
inverse Gram matrix. -/
theorem mvfderiv_standardDeTurckVectorField_localFrameCoeff_apply_eq_sum_torsionFreeKoszul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (hbackground : (background t).IsTorsionFree)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet)
    (X : TM x) (k : ι)
    (hCorrection : ∀ i j : ι,
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (standardDeTurckCorrectionLocalComponent (I := I) (M := M)
          g background t e b k i j) x) :
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
    mvfderiv (I := I)
        (fun y => e.localFrameCoeff I b k y
          (standardDeTurckVectorField (I := I) (M := M) g background t y)) x X =
      ∑ i : ι, ∑ j : ι, (
        CovariantDerivative.localFrameInverseGramMatrix (I := I) e b x i j *
          mvfderiv (I := I)
            (fun y => ∑ l : ι,
              CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y k l *
                ((1 / 2 : ℝ) *
                  ((background t).metricDefect y
                      (e.localFrame b j y) (e.localFrame b l y) (e.localFrame b i y) +
                    (background t).metricDefect y
                      (e.localFrame b i y) (e.localFrame b l y) (e.localFrame b j y) -
                    (background t).metricDefect y
                      (e.localFrame b i y) (e.localFrame b j y) (e.localFrame b l y)))) x X +
        (∑ l : ι,
          CovariantDerivative.localFrameInverseGramMatrix (I := I) e b x k l *
            ((1 / 2 : ℝ) *
              ((background t).metricDefect x
                  (e.localFrame b j x) (e.localFrame b l x) (e.localFrame b i x) +
                (background t).metricDefect x
                  (e.localFrame b i x) (e.localFrame b l x) (e.localFrame b j x) -
                (background t).metricDefect x
                  (e.localFrame b i x) (e.localFrame b j x) (e.localFrame b l x)))) *
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
  let C : ι → ι → M → ℝ := fun i j =>
    standardDeTurckCorrectionLocalComponent (I := I) (M := M)
      g background t e b k i j
  let K : ι → ι → M → ℝ := fun i j y =>
    ∑ l : ι,
      CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y k l *
        ((1 / 2 : ℝ) *
          ((background t).metricDefect y
              (e.localFrame b j y) (e.localFrame b l y) (e.localFrame b i y) +
            (background t).metricDefect y
              (e.localFrame b i y) (e.localFrame b l y) (e.localFrame b j y) -
            (background t).metricDefect y
              (e.localFrame b i y) (e.localFrame b j y) (e.localFrame b l y)))
  have hCK : ∀ i j : ι, C i j =ᶠ[𝓝 x] K i j := by
    intro i j
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    simpa only [C, K, standardDeTurckCorrectionLocalComponent] using
      (explicitLeviCivitaCorrection_localFrameCoeff_of_isTorsionFree
        (I := I) (M := M) g background t hbackground e b hy i j k)
  have hCpoint : ∀ i j : ι, C i j x = K i j x := by
    intro i j
    exact (hCK i j).eq_of_nhds
  have hCderiv : ∀ i j : ι,
      mvfderiv (I := I) (C i j) x X = mvfderiv (I := I) (K i j) x X := by
    intro i j
    have hderiv : mvfderiv (I := I) (C i j) x = mvfderiv (I := I) (K i j) x := by
      unfold mvfderiv
      rw [(hCK i j).eq_of_nhds, (hCK i j).mfderiv_eq]
      rfl
    exact congrArg (fun L : TM x →L[ℝ] ℝ => L X) hderiv
  have hbase :=
    mvfderiv_standardDeTurckVectorField_localFrameCoeff_apply
      (I := I) (M := M) g background t e b hx X k hCorrection
  calc
    mvfderiv (I := I)
        (fun y => e.localFrameCoeff I b k y
          (standardDeTurckVectorField (I := I) (M := M) g background t y)) x X =
        ∑ i : ι, ∑ j : ι, (
          CovariantDerivative.localFrameInverseGramMatrix (I := I) e b x i j *
            mvfderiv (I := I) (C i j) x X +
          C i j x *
            (-(
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b x)⁻¹ *
              (show Matrix ι ι ℝ from fun p q => mvfderiv (I := I)
                (fun y => CovariantDerivative.localFrameGramMatrix (I := I) e b y p q)
                x X) *
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b x)⁻¹)) i j) := by
          simpa only [C] using hbase
    _ = ∑ i : ι, ∑ j : ι, (
          CovariantDerivative.localFrameInverseGramMatrix (I := I) e b x i j *
            mvfderiv (I := I) (K i j) x X +
          K i j x *
            (-(
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b x)⁻¹ *
              (show Matrix ι ι ℝ from fun p q => mvfderiv (I := I)
                (fun y => CovariantDerivative.localFrameGramMatrix (I := I) e b y p q)
                x X) *
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b x)⁻¹)) i j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [hCderiv i j, hCpoint i j]
    _ = _ := by rfl

end RicciFlow
