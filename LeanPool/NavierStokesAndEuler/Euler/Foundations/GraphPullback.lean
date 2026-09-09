/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Tactic.Abel
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Analysis.Distribution.Sobolev
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Tactic.Module
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.WeightedEnergy

@[expose] public section

noncomputable section

namespace EulerGraphPullback

open InnerProductSpace Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The linear graph carrying the oscillating phase. -/
def graphMap (k : ℝ) (m : E) : E →L[ℝ] (E × ℝ) :=
  (ContinuousLinearMap.id ℝ E).prod (k • toDual ℝ E m)

/-- The constant lifted differential direction associated with a spatial vector. -/
def liftedDirection (κ : ℝ) (m : E) : E →L[ℝ] (E × ℝ) :=
  (κ • ContinuousLinearMap.id ℝ E).prod (toDual ℝ E m)

theorem graphMap_apply (k : ℝ) (m v : E) : graphMap k m v = (v, k * ⟪m, v⟫_ℝ) := rfl

theorem liftedDirection_apply (κ : ℝ) (m v : E) :
    liftedDirection κ m v = (κ • v, ⟪m, v⟫_ℝ) := rfl

theorem graph_direction_identity (k κ : ℝ) (hκ : k * κ = 1) (m v : E) :
    graphMap k m v = k • liftedDirection κ m v := by
  rw [graphMap_apply, liftedDirection_apply]
  ext <;> simp [smul_smul, hκ]

theorem graph_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E × ℝ → F) (k κ : ℝ) (hκ : k * κ = 1) (m x v : E)
    (hf : DifferentiableAt ℝ f (graphMap k m x)) :
    fderiv ℝ (fun y => f (graphMap k m y)) x v =
      k • fderiv ℝ f (graphMap k m x) (liftedDirection κ m v) := by
  have h : HasFDerivAt (fun y => f (graphMap k m y))
      ((fderiv ℝ f (graphMap k m x)).comp (graphMap k m)) x :=
    hf.hasFDerivAt.comp x (graphMap k m).hasFDerivAt
  rw [h.fderiv, ContinuousLinearMap.comp_apply, graph_direction_identity k κ hκ m v, map_smul]

/-- A smooth vector field with symmetric derivative has a genuine smooth scalar potential. -/
theorem smooth_gradient_potential (v : E → E) (hv : ContDiff ℝ ∞ v)
    (hsymm : ∀ x a b, ⟪fderiv ℝ v x a, b⟫_ℝ = ⟪fderiv ℝ v x b, a⟫_ℝ) :
    ∃ p : E → ℝ, ContDiff ℝ ∞ p ∧ ∀ x, gradient p x = v x := by
  let form : E → E →L[ℝ] ℝ := fun x => toDual ℝ E (v x)
  have hω : ContDiff ℝ ∞ form := (toDual ℝ E).toContinuousLinearEquiv.contDiff.comp hv
  have hωd (x : E) : HasFDerivAt form
      ((toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap.comp (fderiv ℝ v x)) x :=
    (toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp x
      ((hv.differentiable (by simp)) x).hasFDerivAt
  obtain ⟨p, hp⟩ := (convex_univ : Convex ℝ (univ : Set
    E)).exists_forall_hasFDerivAt_of_fderiv_symmetric
    isOpen_univ (hω.differentiable (by simp)).differentiableOn (fun x _ a b => by
      rw [(hωd x).fderiv]
      change ⟪fderiv ℝ v x a, b⟫_ℝ = ⟪fderiv ℝ v x b, a⟫_ℝ
      exact hsymm x a b)
  have hp' (x : E) : HasFDerivAt p (form x) x := hp x (mem_univ _)
  have hpd : Differentiable ℝ p := fun x => (hp' x).differentiableAt
  have hpf : fderiv ℝ p = form := funext (fun x => (hp' x).fderiv)
  refine ⟨p, ?_, ?_⟩
  · rw [contDiff_infty_iff_fderiv]
    exact ⟨hpd, by rwa [hpf]⟩
  · intro x
    rw [gradient, (hp' x).fderiv]
    exact (toDual ℝ E).symm_apply_apply (v x)

/-- Closedness for the lifted derivatives becomes a scalar pressure potential on the graph. -/
theorem lifted_closed_field_has_graph_potential (p : E × ℝ → E)
    (hp : ContDiff ℝ ∞ p) (k κ : ℝ) (hκ : k * κ = 1) (m : E)
    (hclosed : ∀ z a b,
      ⟪fderiv ℝ p z (liftedDirection κ m a), b⟫_ℝ =
        ⟪fderiv ℝ p z (liftedDirection κ m b), a⟫_ℝ) :
    ∃ q : E → ℝ, ContDiff ℝ ∞ q ∧
      ∀ x, gradient q x = κ • p (graphMap k m x) := by
  let v : E → E := fun x => κ • p (graphMap k m x)
  have hv : ContDiff ℝ ∞ v := (hp.comp (graphMap k m).contDiff).const_smul κ
  apply smooth_gradient_potential v hv
  intro x a b
  have hg := (hp.differentiable (by simp)) (graphMap k m x)
  have hd : fderiv ℝ v x = κ • fderiv ℝ (fun y => p (graphMap k m y)) x := by
    exact ((hg.comp x (graphMap k m).differentiableAt).hasFDerivAt.const_smul κ).fderiv
  rw [hd]
  simp only [smul_apply, real_inner_smul_left, graph_fderiv p k κ hκ m x a hg,
    graph_fderiv p k κ hκ m x b hg]
  rw [hclosed]

end EulerGraphPullback
