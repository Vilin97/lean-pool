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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PeriodicProfile

@[expose] public section

noncomputable section

namespace EulerAnglePartition

open EulerGevreyCutoff Set
open scoped ContDiff

/-- A compact smooth partition function whose period translates telescope. -/
def partition (T t : ℝ) : ℝ := transition (t / T) - transition (t / T - 1)

theorem partition_contDiff (T : ℝ) : ContDiff ℝ ∞ (partition T) :=
  (transition_contDiff.comp (contDiff_id.div_const T)).sub
    (transition_contDiff.comp ((contDiff_id.div_const T).sub contDiff_const))

theorem partition_nonneg (T t : ℝ) : 0 ≤ partition T t := by
  exact sub_nonneg.mpr (transition_monotone (by linarith))

theorem partition_support (T : ℝ) (hT : 0 < T) :
    tsupport (partition T) ⊆ Icc (-T) (2 * T) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  constructor
  · by_contra h
    have hq : t / T ≤ -1 := (div_le_iff₀ hT).2 (by linarith)
    exact ht (by simp [partition, transition_zero_of_le _ hq,
      transition_zero_of_le _ (show t / T - 1 ≤ -1 by linarith)])
  · by_contra h
    have hq : 2 ≤ t / T := (le_div_iff₀ hT).2 (by linarith)
    exact ht (by simp [partition, transition_one_of_ge _ (show 1 ≤ t / T by linarith),
      transition_one_of_ge _ (show 1 ≤ t / T - 1 by linarith)])

theorem partition_compactSupport (T : ℝ) (hT : 0 < T) : HasCompactSupport (partition T) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (partition_support T hT)

theorem seven_translate_identity (T t : ℝ) (hT : T ≠ 0) :
    (∑ k ∈ Finset.range 7, partition T (t + (3 - (k : ℝ)) * T)) =
      transition (t / T + 3) - transition (t / T - 4) := by
  unfold partition
  simp only [add_div, mul_div_cancel_right₀ _ hT]
  norm_num [Finset.sum_range_succ]
  ring_nf

theorem seven_translate_partition (T : ℝ) (hT : 0 < T) (t : ℝ)
    (ht : t ∈ Icc (-2 * T) (2 * T)) :
    (∑ k ∈ Finset.range 7, partition T (t + (3 - (k : ℝ)) * T)) = 1 := by
  rw [seven_translate_identity T t hT.ne']
  have hlo : -2 ≤ t / T := (le_div_iff₀ hT).2 ht.1
  have hhi : t / T ≤ 2 := (div_le_iff₀ hT).2 ht.2
  rw [transition_one_of_ge _ (show 1 ≤ t / T + 3 by linarith),
    transition_zero_of_le _ (show t / T - 4 ≤ -1 by linarith)]
  norm_num

end EulerAnglePartition
