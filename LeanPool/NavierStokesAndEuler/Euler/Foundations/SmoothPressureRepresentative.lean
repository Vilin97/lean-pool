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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothTensorLimit

@[expose] public section

noncomputable section

/-! Actual C∞ representatives obtained from all-order strong cylinder jets. -/


namespace EulerSmoothPressureRepresentative

open MeasureTheory EulerLiftedGradientSpace EulerMetricTransport EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerMollifierRepresentative EulerMollifierUniform
open scoped ContDiff Topology

variable (period : ℝ) [Fact (0 < period)]

/-- All-order strong cylinder jets produce an actual C∞ representative of the L² field. -/
theorem exists_smooth_representative (U : LiftL2 period)
    (J : ∀ s : ℕ, SpatialJet period standardDirection s U) :
    ∃ g : LiftDomain period → Vector3,
      (∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) ∧
      (U : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g := by
  let w : Fin 0 → Fin 4 := Fin.elim0
  obtain ⟨g, hg⟩ := exists_smoothMollifier_word_uniform_limit period U (J 3) w
  have hpoint : ∀ x, Filter.Tendsto (fun n => smoothMollifier period n U x)
      Filter.atTop (𝓝 (g x)) := fun x => hg.tendsto_at x
  have hC : ∀ m (v : Fin m → Fin 4), UniformCauchySeqOn
      (fun n => iteratedFieldDerivative period v (smoothMollifier period n U)) Filter.atTop
        Set.univ :=
    fun m v => smoothMollifier_word_uniformCauchy period U (J (m + 3)) v
  refine ⟨g, ?_, ?_⟩
  · exact EulerSmoothTensorLimit.cylinder_smooth_of_uniformCauchy_words period
      (fun n => smoothMollifier period n U) (fun n => smoothMollifier_smooth period n U) hC g hpoint
  · simpa only [SpatialJet.word_zero] using smoothMollifier_word_limit_ae period U (J 3) w g hg

/-- The genuine coercive pressure inverse has a C∞ representative when its actual coefficients
and forcing possess strong derivative jets at every finite order. -/
theorem exists_smooth_pressure (A : SmoothCoefficient period) (f : LiftL2 period)
    (K : ∀ s : ℕ, CoefficientJet period standardDirection s A)
    (J : ∀ s : ℕ, SpatialJet period standardDirection s f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ (A.coefficient x v) v) :
    ∃ p : LiftDomain period → Vector3,
      (∀ x, ContDiff ℝ ∞ (localFieldLift period p x)) ∧
      (A.pressure κ m c hc hpos f : LiftDomain period → Vector3) =ᵐ[liftMeasure period] p :=
  exists_smooth_representative period (A.pressure κ m c hc hpos f)
    (fun s => (J s).solvePressure (K s) κ m c hc hpos)

end EulerSmoothPressureRepresentative
