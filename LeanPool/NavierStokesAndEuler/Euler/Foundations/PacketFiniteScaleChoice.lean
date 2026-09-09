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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketUniformScaleChoice

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace EulerPacketFiniteScaleChoice

open Real EulerPacketUniformScaleChoice EulerPacketUniformScaleSums

/-- Every finite collection of scale inequalities allows the same
choices of `J` and then `x₀`. Thus the source's different coefficient,
neighbor, time, and pressure-cost requirements can be imposed together. -/
theorem finite_source_uniform_small_sum_choice
    {ι : Type*} [Fintype ι] (d B N : ι → ℕ) (a b c C p q : ι → ℝ)
    (haB : ∀ i, a i < B i) (haN : ∀ i, a i ≤ N i) (hb : ∀ i, 0 < b i) :
    ∃ J : ℕ, 3 ≤ J ∧ ∀ δ : ℝ, 0 < δ → ∃ X₀ : ℝ, 1 ≤ X₀ ∧
      ∀ x : ℕ → ℝ, X₀ ≤ x 0 →
        (∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) → ∀ i,
        (∑' n, exp (-(b i) * (x n / ((J + n : ℕ) : ℝ) ^ (a i)) +
          c i * (x n / ((J - d i + n : ℕ) : ℝ) ^ (B i)) +
          C i + p i * log ((J + n : ℕ) : ℝ) + q i * log (x n))) ≤ δ := by
  classical
  choose Ji hJi3 hJid hJiN hJiC using fun i =>
    exists_uniform_stage_choice (d i) (B i) (N i) (a i) (c i) (b i) (haB i) (hb i)
  let J := max 3 (Finset.univ.sup Ji)
  have hJ3 : 3 ≤ J := le_max_left _ _
  have hJ1 : 1 ≤ J := by omega
  have hJiLe (i : ι) : Ji i ≤ J :=
    (Finset.le_sup (f := Ji) (Finset.mem_univ i)).trans (le_max_right _ _)
  have hdJ (i : ι) : d i < J := lt_of_lt_of_le (hJid i) (hJiLe i)
  have hJN (i : ι) : (2 : ℝ) ^ (2 * N i + 3) ≤ (J : ℝ) ^ 2 := by
    exact (hJiN i).trans (pow_le_pow_left₀ (by positivity)
      (by exact_mod_cast hJiLe i) 2)
  have hcoeff (i : ι) (n : ℕ) :
      c i * (((J + n : ℕ) : ℝ) ^ (a i) / ((J - d i + n : ℕ) : ℝ) ^ (B i)) ≤ b i / 4 := by
    have hh := hJiC i (J - Ji i + n)
    have hj : Ji i + (J - Ji i + n) = J + n := by have hi := hJiLe i; omega
    have hp : Ji i - d i + (J - Ji i + n) = J - d i + n := by
      have hi := hJiLe i
      have hid := hJid i
      omega
    simpa only [hj, hp] using hh
  refine ⟨J, hJ3, ?_⟩
  intro δ hδ
  have hboth : ∀ᶠ X : ℝ in atTop, ∀ i : ι,
      (4 * (|C i| + |p i| + 2 * |q i|) / b i) ^ 2 * (J : ℝ) ^ (2 * N i + 2) ≤ X ∧
      exp (-(b i / 2) * (X / (J : ℝ) ^ N i)) /
        (1 - exp (-(b i / 2) * (X / (J : ℝ) ^ N i))) ≤ δ := by
    apply eventually_all.2
    intro i
    have hi := source_exponential_bound_tendsto_zero J (N i) hJ1 (b i / 2)
      (div_pos (hb i) (by norm_num))
    exact (eventually_ge_atTop _).and (hi.eventually_le_const hδ)
  obtain ⟨X, hX⟩ := eventually_atTop.1 hboth
  refine ⟨max 1 X, le_max_left _ _, ?_⟩
  intro x hx0 hx i
  have hx1 : 1 ≤ x 0 := (le_max_left 1 X).trans hx0
  have hall := hX (x 0) ((le_max_right 1 X).trans hx0) i
  exact (uniform_source_cost_tsum_bound J (d i) (B i) (N i) hJ1 (hdJ i) (hJN i)
    x hx1 hx (a i) (b i) (c i) (C i) (p i) (q i) (haN i) (hb i) (hcoeff i) hall.1).trans hall.2

end EulerPacketFiniteScaleChoice
