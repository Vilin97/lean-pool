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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CoverMollificationFubini

@[expose] public section

noncomputable section

/-! Actual classical smooth representatives of the strong L² cylinder mollifiers. -/

namespace EulerMollifierRepresentative

open MeasureTheory EulerSobolev EulerCylinderCoordinates EulerCylinderSobolev
open EulerLiftedGradientSpace EulerMetricTransport EulerCoverMollification
open EulerCoverMollificationFubini EulerCylinderMollifier EulerSpatialSobolevInverse
  EulerStrongSmoothJet
open scoped ContDiff ENNReal

variable (period : ℝ) [Fact (0 < period)]

/-- The concrete classical convolution representing the Bochner L² mollifier. -/
noncomputable def smoothMollifier (n : ℕ) (U : LiftL2 period) : LiftDomain period → Vector3 :=
  cylinderConvolution period (mollifierBump n) U

/-- The smooth convolution and the Bochner convolution are the same almost everywhere. -/
theorem mollify_ae_smoothMollifier (n : ℕ) (U : LiftL2 period) :
    (mollify period n U : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      smoothMollifier period n U := by
  apply ae_eq_cylinderConvolution_of_setIntegrals period (mollifierBump n) U (mollify period n U)
  intro K hK hfin
  simpa only [mollifierKernel, integral_smul] using
    EulerSetIntegralL2.mollify_setIntegral period n U K hK hfin.ne

/-- Every strong L² mollifier has an actual C∞ representative on the cylinder. -/
theorem smoothMollifier_smooth (n : ℕ) (U : LiftL2 period) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (smoothMollifier period n U) x) :=
  cylinderConvolution_smooth period (mollifierBump n) U (Lp.memLp U)

/-- Strong mollified jets are precisely the classical derivatives of the smooth convolution. -/
theorem smoothMollifier_word_ae {s k : ℕ} (hk : k ≤ s) (U : LiftL2 period)
    (J : SpatialJet period standardDirection s U) (n : ℕ) (w : Fin k → Fin 4) :
    (mollify period n (J.word w) : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      iteratedFieldDerivative period w (smoothMollifier period n U) := by
  rw [← mollifyJet_word period J n w]
  exact jet_word_ae period hk _ (mollifyJet period J n) w _
    (mollify_ae_smoothMollifier period n U) (smoothMollifier_smooth period n U)

/-- All available classical derivatives of the smooth mollifier are genuinely in L². -/
theorem smoothMollifier_word_memLp {s k : ℕ} (hk : k ≤ s) (U : LiftL2 period)
    (J : SpatialJet period standardDirection s U) (n : ℕ) (w : Fin k → Fin 4) :
    MemLp (iteratedFieldDerivative period w (smoothMollifier period n U)) 2 (liftMeasure period) :=
  (Lp.memLp _).ae_eq (smoothMollifier_word_ae period hk U J n w)

/-- The strong and classical Sobolev norms of each mollifier agree exactly. -/
theorem smoothMollifier_sobolevNorm {s : ℕ} (U : LiftL2 period)
    (J : SpatialJet period standardDirection s U) (n : ℕ) :
    (mollifyJet period J n).sobolevNorm = liftSobolevNorm period s (smoothMollifier period n U) :=
  jet_sobolevNorm_eq period _ (mollifyJet period J n) _
    (mollify_ae_smoothMollifier period n U) (smoothMollifier_smooth period n U)

end EulerMollifierRepresentative
