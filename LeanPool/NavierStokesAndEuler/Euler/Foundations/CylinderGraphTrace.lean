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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.DeformationVolume

@[expose] public section

noncomputable section

namespace EulerCylinderGraphTrace

open MeasureTheory EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
open Set
open scoped ContDiff

variable (period : ℝ) [Fact (0 < period)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [Fact (0 < period)] [CompleteSpace F] in
theorem angular_hasDerivAt (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : Vector3) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x, (s : AddCircle period)))
      (fieldDerivative period (0, 1) f (x, (t : AddCircle period))) t := by
  have hd := ((hf 0).differentiable (by simp) (x, t)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
  have he := fderiv_localFieldLift_cover period f (x, t)
  change fderiv ℝ (localFieldLift period f (x, (t : AddCircle period))) 0 =
    fderiv ℝ (localFieldLift period f 0) (x, t) at he
  change HasDerivAt _ ((fderiv ℝ (localFieldLift period f (x, (t : AddCircle period))) 0) (0, 1)) t
  rw [he]
  simpa [Function.comp_def, localFieldLift] using hd

/-- Point evaluation in the periodic coordinate costs one angular derivative,
with a bound independent of the chosen phase. -/
theorem cylinder_pointwise_trace (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (x : Vector3) (θ : AddCircle period) :
    ‖f (x, θ)‖ ^ 2 ≤
      (2 / period) * (∫ s : AddCircle period, ‖f (x, s)‖ ^ 2) +
      (2 * period) * (∫ s : AddCircle period,
        ‖fieldDerivative period (0, 1) f (x, s)‖ ^ 2) := by
  have hT : 0 < period := Fact.out
  let θ₀ := AddCircle.equivIco period 0 θ
  have hθ : (θ₀ : ℝ) ∈ Icc 0 period := by
    have hh := θ₀.property
    simp only [zero_add] at hh
    exact ⟨hh.1, hh.2.le⟩
  have hcont : Continuous (fun s : ℝ => fieldDerivative period (0, 1) f
      (x, (s : AddCircle period))) := by
    exact (smoothField_continuous period _
      (fieldDerivative_smooth period (0, 1) f hf)).comp
      (continuous_const.prodMk (AddCircle.continuous_mk' period))
  have h := EulerIntervalTrace.pointwise_H1_trace
    (fun s : ℝ => f (x, (s : AddCircle period)))
    (fun s : ℝ => fieldDerivative period (0, 1) f (x, (s : AddCircle period)))
    0 period hT hcont.continuousOn (fun s _ => angular_hasDerivAt period f hf x s)
    θ₀ hθ
  have hcoe : ((θ₀ : ℝ) : AddCircle period) = θ := AddCircle.coe_equivIco
  rw [hcoe] at h
  have hfi := AddCircle.intervalIntegral_preimage period 0
    (fun s : AddCircle period => ‖f (x, s)‖ ^ 2)
  have hdi := AddCircle.intervalIntegral_preimage period 0
    (fun s : AddCircle period => ‖fieldDerivative period (0, 1) f (x, s)‖ ^ 2)
  simp only [zero_add] at hfi hdi
  simpa only [sub_zero, hfi, hdi] using h

/-- Pullback to any continuous phase graph preserves square integrability.
The estimate has no dependence on the phase frequency. -/
theorem graph_memLp_and_energy_bound (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : MemLp f 2 (liftMeasure period))
    (hdL2 : MemLp (fieldDerivative period (0, 1) f) 2 (liftMeasure period))
    (θ : Vector3 → AddCircle period) (hθ : Continuous θ) :
    MemLp (fun x => f (x, θ x)) 2 volume ∧
      (∫ x : Vector3, ‖f (x, θ x)‖ ^ 2) ≤
        (2 / period) * (∫ z, ‖f z‖ ^ 2 ∂liftMeasure period) +
        (2 * period) * (∫ z, ‖fieldDerivative period (0, 1) f z‖ ^ 2
          ∂liftMeasure period) := by
  have hfc : Continuous (fun x => f (x, θ x)) :=
    (smoothField_continuous period f hf).comp (continuous_id.prodMk hθ)
  have hfint := hfL2.norm.integrable_sq
  have hdint := hdL2.norm.integrable_sq
  have hi := (hfint.integral_prod_left.const_mul (2 / period)).add
    (hdint.integral_prod_left.const_mul (2 * period))
  have hgraph : Integrable (fun x => ‖f (x, θ x)‖ ^ 2) volume := by
    apply hi.mono' (hfc.norm.pow 2).aestronglyMeasurable
    filter_upwards [] with x
    change ‖‖f (x, θ x)‖ ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖f (x, θ x)‖)]
    exact cylinder_pointwise_trace period f hf x (θ x)
  refine ⟨(memLp_two_iff_integrable_sq_norm hfc.aestronglyMeasurable).mpr hgraph, ?_⟩
  have hbound := integral_mono hgraph hi (fun x => cylinder_pointwise_trace period f hf x (θ x))
  simp only [Pi.add_apply] at hbound
  rw [integral_add (hfint.integral_prod_left.const_mul (2 / period))
    (hdint.integral_prod_left.const_mul (2 * period)), integral_const_mul, integral_const_mul,
    integral_integral hfint, integral_integral hdint] at hbound
  exact hbound

end EulerCylinderGraphTrace
