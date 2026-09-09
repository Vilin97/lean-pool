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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.MollifierUniform

@[expose] public section

noncomputable section

/-! Full Fréchet tensor convergence from the genuine cylinder derivative words. -/

namespace EulerMollifierTensors

open MeasureTheory Filter EulerSobolev EulerCylinderSobolev EulerCylinderCoordinates
open EulerLiftedGradientSpace EulerMetricTransport EulerSobolevDerivativeNorm
open scoped ContDiff Topology

variable (period : ℝ)

/-- The operator norm of a difference of derivative tensors is controlled by the finite coordinate sum. -/
theorem tensor_difference_le_word_sum (m : ℕ) (f g : LiftDomain period → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (x : LiftDomain period) (z : Domain 4) :
    ‖iteratedFDeriv ℝ m (euclideanLift period f x) z -
      iteratedFDeriv ℝ m (euclideanLift period g x) z‖ ≤
    ∑ w : Fin m → Fin 4,
      ‖iteratedFieldDerivative period w f (euclideanCover period z + x) -
        iteratedFieldDerivative period w g (euclideanCover period z + x)‖ := by
  have h := multilinear_norm_le_coordinate_sum 4 m
    (iteratedFDeriv ℝ m (euclideanLift period f x) z -
      iteratedFDeriv ℝ m (euclideanLift period g x) z)
  simpa only [sub_apply,
    ← euclideanLift_iteratedFieldDerivative period _ f hf,
    ← euclideanLift_iteratedFieldDerivative period _ g hg,
    euclideanLift_eq_translated_cover, translated] using h

/-- Uniform Cauchy convergence of every coordinate word gives uniform Cauchy convergence of the full tensor. -/
theorem tensor_uniformCauchy_of_words (m : ℕ) (f : ℕ → LiftDomain period → Vector3)
    (hf : ∀ k x, ContDiff ℝ ∞ (localFieldLift period (f k) x))
    (hC : ∀ w : Fin m → Fin 4,
      UniformCauchySeqOn (fun k => iteratedFieldDerivative period w (f k)) atTop Set.univ)
    (x : LiftDomain period) :
    UniformCauchySeqOn
      (fun k => iteratedFDeriv ℝ m (euclideanLift period (f k) x)) atTop Set.univ := by
  classical
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hc : 0 < (4 : ℝ)^m := pow_pos (by norm_num) _
  have hsmall := fun w : Fin m → Fin 4 =>
    Metric.uniformCauchySeqOn_iff.mp (hC w) (ε / (4 : ℝ)^m) (div_pos hε hc)
  choose N hN using hsmall
  refine ⟨Finset.univ.sup N, ?_⟩
  intro k hk l hl z _
  have hword (w : Fin m → Fin 4) :
      ‖iteratedFieldDerivative period w (f k) (euclideanCover period z + x) -
        iteratedFieldDerivative period w (f l) (euclideanCover period z + x)‖ < ε / (4 : ℝ)^m := by
    simpa only [dist_eq_norm] using hN w k
      ((Finset.le_sup (f := N) (Finset.mem_univ w)).trans hk) l
      ((Finset.le_sup (f := N) (Finset.mem_univ w)).trans hl)
      (euclideanCover period z + x) (Set.mem_univ _)
  rw [dist_eq_norm]
  apply (tensor_difference_le_word_sum period m (f k) (f l) (hf k) (hf l) x z).trans_lt
  calc
    _ < ∑ _w : Fin m → Fin 4, ε / (4 : ℝ)^m := by
      apply Finset.sum_lt_sum (fun w _ => (hword w).le)
      exact ⟨fun _ => 0, Finset.mem_univ _, hword _⟩
    _ = ε := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul]
      push_cast
      exact mul_div_cancel₀ ε hc.ne'

end EulerMollifierTensors
