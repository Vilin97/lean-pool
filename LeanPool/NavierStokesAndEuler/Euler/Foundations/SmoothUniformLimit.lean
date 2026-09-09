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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Gevrey

@[expose] public section

noncomputable section

namespace EulerSmoothUniformLimit

open Filter
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]

/-- An infinite compatible derivative tower is smooth at every level. -/
theorem contDiff_of_derivative_tower (J : ∀ n, E → F n)
    (L : ∀ n, F (n + 1) →L[ℝ] (E →L[ℝ] F n))
    (hJ : ∀ n x, HasFDerivAt (J n) (L n (J (n + 1) x)) x) :
    ∀ n, ContDiff ℝ ∞ (J n) := by
  have hfinite : ∀ k : ℕ, ∀ n, ContDiff ℝ k (J n) := by
    intro k
    induction k with
    | zero =>
      intro n
      exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr
        (fun x => (hJ n x).continuousAt))
    | succ k ih =>
      intro n
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
      refine ⟨fun x => (hJ n x).differentiableAt, by simp, ?_⟩
      have he : fderiv ℝ (J n) = fun x => L n (J (n + 1) x) :=
        funext (fun x => (hJ n x).fderiv)
      rw [he]
      exact (L n).contDiff.comp (ih (n + 1))
  intro n
  exact contDiff_infty.mpr (fun k => hfinite k n)

/-- Uniform limits of a compatible smooth derivative tower are again smooth.
This is the completion step for Sobolev mollifications. -/
theorem contDiff_of_uniform_derivative_limits
    (f : ∀ n, ℕ → E → F n) (J : ∀ n, E → F n)
    (L : ∀ n, F (n + 1) →L[ℝ] (E →L[ℝ] F n))
    (hf : ∀ n k x, HasFDerivAt (f n k) (L n (f (n + 1) k x)) x)
    (hlim : ∀ n, TendstoUniformly (f n) (J n) atTop) :
    ∀ n, ContDiff ℝ ∞ (J n) := by
  apply contDiff_of_derivative_tower J L
  intro n x
  have hd := (L n).uniformContinuous.comp_tendstoUniformly (hlim (n + 1))
  exact hasFDerivAt_of_tendstoUniformly hd (hf n) (fun y => (hlim n).tendsto_at y) x

/-- Completeness constructs every limit in a uniformly Cauchy derivative tower;
the limit and all of its compatible derivatives are smooth. -/
theorem exists_smooth_limit_of_uniform_cauchy_tower [∀ n, CompleteSpace (F n)]
    (f : ∀ n, ℕ → E → F n)
    (L : ∀ n, F (n + 1) →L[ℝ] (E →L[ℝ] F n))
    (hf : ∀ n k x, HasFDerivAt (f n k) (L n (f (n + 1) k x)) x)
    (hC : ∀ n, UniformCauchySeqOn (f n) atTop Set.univ) :
    ∃ J : ∀ n, E → F n,
      (∀ n, TendstoUniformly (f n) (J n) atTop) ∧ (∀ n, ContDiff ℝ ∞ (J n)) := by
  have hp : ∀ n x, ∃ v : F n, Tendsto (fun k => f n k x) atTop (nhds v) := by
    intro n x
    exact cauchy_map_iff_exists_tendsto.mp ((hC n).cauchy_map (Set.mem_univ x))
  choose J hJ using hp
  have hlim : ∀ n, TendstoUniformly (f n) (J n) atTop := by
    intro n
    rw [← tendstoUniformlyOn_univ]
    exact (hC n).tendstoUniformlyOn_of_tendsto (fun x _ => hJ n x)
  exact ⟨J, hlim, contDiff_of_uniform_derivative_limits f J L hf hlim⟩

end EulerSmoothUniformLimit
