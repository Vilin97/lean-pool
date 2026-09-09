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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SobolevBreakdown

@[expose] public section

noncomputable section

namespace EulerDeformationVolume

open Matrix Set MeasureTheory

/-- Jacobi's formula along the three-dimensional deformation equation, including
singular matrices; no inverse determinant is used. -/
theorem determinant_hasDerivAt (F M : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ)
    (hF : ∀ i j, HasDerivAt (fun s => F s i j) ((M t * F t) i j) t) :
    HasDerivAt (fun s => (F s).det) ((M t).trace * (F t).det) t := by
  have h := (((((hF 0 0).mul (hF 1 1)).mul (hF 2 2)).sub
    (((hF 0 0).mul (hF 1 2)).mul (hF 2 1))).sub
    (((hF 0 1).mul (hF 1 0)).mul (hF 2 2))).add
    (((hF 0 1).mul (hF 1 2)).mul (hF 2 0))
  have h' := (h.add (((hF 0 2).mul (hF 1 0)).mul (hF 2 1))).sub
    (((hF 0 2).mul (hF 1 1)).mul (hF 2 0))
  have hd := h'.congr_deriv (g' := (M t).trace * (F t).det) (by
    simp only [Pi.mul_apply, mul_apply, Fin.sum_univ_three, trace, diag, det_fin_three]
    ring)
  convert hd using 1 <;> first | rfl | (funext s; exact det_fin_three (F s))

/-- A trace-free velocity gradient preserves the actual deformation determinant. -/
theorem determinant_eq_one (F M : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (a b : ℝ)
    (hF : ∀ t ∈ Icc a b, ∀ i j,
      HasDerivAt (fun s => F s i j) ((M t * F t) i j) t)
    (htrace : ∀ t ∈ Ico a b, (M t).trace = 0) (hinit : (F a).det = 1) :
    ∀ t ∈ Icc a b, (F t).det = 1 := by
  have hc : ContinuousOn (fun t => (F t).det) (Icc a b) :=
    fun t ht => (determinant_hasDerivAt F M t (hF t ht)).continuousAt.continuousWithinAt
  have hz : ∀ t ∈ Ico a b, HasDerivWithinAt (fun s => (F s).det) 0 (Ici t) t := by
    intro t ht
    have hd := determinant_hasDerivAt F M t (hF t ⟨ht.1, ht.2.le⟩)
    rw [htrace t ht, zero_mul] at hd
    exact hd.hasDerivWithinAt
  intro t ht
  exact (constant_of_has_deriv_right_zero hc hz t ht).trans hinit

section ChangeOfVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A bijective differentiable map with unit Jacobian preserves Lebesgue measure. -/
theorem measurePreserving_of_det_one (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (f : E → E) (F : E → E →L[ℝ] E)
    (hf : ∀ x, HasFDerivAt f (F x) x) (hbij : Function.Bijective f)
    (hdet : ∀ x, (F x).det = 1) : MeasurePreserving f μ μ := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  refine ⟨hc.measurable, ?_⟩
  have hm := map_withDensity_abs_det_fderiv_eq_addHaar μ
    (s := (univ : Set E)) (f' := F) MeasurableSet.univ.nullMeasurableSet
    (fun x _ => (hf x).hasFDerivWithinAt) hbij.1.injOn
  simp only [hdet, abs_one, ENNReal.ofReal_one, Measure.restrict_univ,
    image_univ, hbij.2.range_eq] at hm
  change Measure.map f (μ.withDensity 1) = μ at hm
  rwa [withDensity_one] at hm

end ChangeOfVariables

end EulerDeformationVolume
