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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderMollifier

@[expose] public section

noncomputable section

/-! Set integration as a bounded functional on L², and its commutation with Bochner averages. -/


namespace EulerSetIntegralL2

open MeasureTheory
open scoped ENNReal NNReal Topology

variable {X V : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Integration on a finite-measure set as a genuine bounded linear map on L². -/
def setIntegralL2 (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) : Lp V 2 μ →L[ℝ] V :=
  (ContinuousLinearMap.lsmul ℝ ℝ).lpPairing μ 2 2
    (indicatorConstLp 2 hs hμs (1 : ℝ))

theorem setIntegralL2_apply (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ⊤)
    (f : Lp V 2 μ) : setIntegralL2 s hs hμs f = ∫ x in s, f x ∂μ := by
  rw [setIntegralL2, ContinuousLinearMap.lpPairing_eq_integral]
  calc
    _ = ∫ x, s.indicator (fun y => f y) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := (1 : ℝ))] with
        x hx
      rw [hx]
      by_cases hxs : x ∈ s
      · simp [hxs]
      · simp [hxs]
    _ = _ := integral_indicator hs

/-- Bochner averaging of L² elements commutes with integration on every finite-measure set. -/
theorem setIntegral_integral_L2 {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ⊤)
    (F : Y → Lp V 2 μ) (hF : Integrable F ν) :
    (∫ x in s, (∫ y, F y ∂ν) x ∂μ) = ∫ y, ∫ x in s, F y x ∂μ ∂ν := by
  rw [← setIntegralL2_apply s hs hμs,
    ← (setIntegralL2 s hs hμs).integral_comp_comm hF]
  simp_rw [setIntegralL2_apply]

section Cylinder

open EulerLiftedGradientSpace EulerCylinderCoordinates EulerCylinderMollifier EulerSobolev

variable (period : ℝ) [Fact (0 < period)]

omit [Fact (0 < period)] in
theorem euclideanCover_neg (y : Domain 4) : euclideanCover period (-y) = -euclideanCover period y
  := by
  simp [euclideanCover, coveringMap, map_neg]

/-- The Bochner L² mollifier and the classical convolution have the same iterated finite-set integrals. -/
theorem mollify_setIntegral (n : ℕ) (f : LiftL2 period) (s : Set (LiftDomain period))
    (hs : MeasurableSet s) (hμs : liftMeasure period s ≠ ⊤) :
    (∫ x in s, mollify period n f x ∂liftMeasure period) =
      ∫ y : Domain 4, ∫ x in s, mollifierKernel n y • f (x - euclideanCover period y)
        ∂liftMeasure period := by
  rw [mollify_eq_integral, setIntegral_integral_L2 s hs hμs _ (kernel_orbit_integrable period n f)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul (mollifierKernel n y) (orbit period f (-y))),
    ae_restrict_of_ae (translation_ae period (euclideanCover period (-y)) f)] with x hx hy
  rw [hx]
  change mollifierKernel n y • (translation period (euclideanCover period (-y)) f) x = _
  rw [hy, euclideanCover_neg, sub_eq_add_neg]

end Cylinder

end EulerSetIntegralL2
