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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.MollifierTensors

@[expose] public section

noncomputable section

/-! Smoothness of uniform limits of complete Fréchet derivative towers. -/

namespace EulerSmoothTensorLimit

open Filter
open scoped ContDiff Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A uniformly Cauchy sequence at every actual Fréchet derivative order has a genuine smooth limit. -/
theorem exists_smooth_limit (f : ℕ → E → F) (hf : ∀ k, ContDiff ℝ ∞ (f k))
    (hC : ∀ m, UniformCauchySeqOn (fun k => iteratedFDeriv ℝ m (f k)) atTop Set.univ) :
    ∃ g : E → F, TendstoUniformly f g atTop ∧ ContDiff ℝ ∞ g := by
  let L (m : ℕ) : (E [×(m+1)]→L[ℝ] F) →L[ℝ] (E →L[ℝ] (E [×m]→L[ℝ] F)) :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => E)
      F).toContinuousLinearEquiv.toContinuousLinearMap
  have hD (m k : ℕ) (x : E) : HasFDerivAt (iteratedFDeriv ℝ m (f k))
      (L m (iteratedFDeriv ℝ (m+1) (f k) x)) x := by
    have hd := (hf k).differentiable_iteratedFDeriv
      (show (m : ℕ∞ω) < (∞ : ℕ∞ω) by exact_mod_cast ENat.natCast_lt_top m) x
    exact hd.hasFDerivAt
  obtain ⟨J, hJ, hJs⟩ := EulerSmoothUniformLimit.exists_smooth_limit_of_uniform_cauchy_tower
    (fun m k => iteratedFDeriv ℝ m (f k)) L hD hC
  let A := (continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨fun x => A (J 0 x), ?_, A.contDiff.comp (hJs 0)⟩
  have h := A.uniformContinuous.comp_tendstoUniformly (hJ 0)
  simpa only [A, Function.comp_def, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    continuousMultilinearCurryFin0_apply, iteratedFDeriv_zero_apply] using h

section Cylinder

open EulerSobolev EulerCylinderCoordinates EulerCylinderSobolev EulerLiftedGradientSpace
open EulerMetricTransport EulerMollifierTensors

/-- A pointwise cylinder limit is C∞ when every coordinate derivative word is uniformly Cauchy. -/
theorem cylinder_smooth_of_uniformCauchy_words (period : ℝ)
    (f : ℕ → LiftDomain period → Vector3)
    (hf : ∀ k x, ContDiff ℝ ∞ (localFieldLift period (f k) x))
    (hC : ∀ m (w : Fin m → Fin 4),
      UniformCauchySeqOn (fun k => iteratedFieldDerivative period w (f k)) atTop Set.univ)
    (g : LiftDomain period → Vector3)
    (hpoint : ∀ y, Tendsto (fun k => f k y) atTop (𝓝 (g y))) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period g x) := by
  intro x
  obtain ⟨G, hG, hGs⟩ := exists_smooth_limit
    (fun k => euclideanLift period (f k) x)
    (fun k => euclideanLift_smooth period (f k) (hf k) x)
    (fun m => tensor_uniformCauchy_of_words period m f hf (hC m) x)
  have he : euclideanLift period g x = G := by
    funext z
    have hp : Tendsto (fun k => euclideanLift period (f k) x z) atTop
        (𝓝 (euclideanLift period g x z)) := by
      simpa only [euclideanLift_eq_translated_cover, translated] using
        hpoint (euclideanCover period z + x)
    exact tendsto_nhds_unique hp (hG.tendsto_at z)
  have hlocal : localFieldLift period g x = G ∘ coordinateEquiv.symm := by
    rw [← he]
    funext v
    simp only [euclideanLift, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [hlocal]
  exact hGs.comp coordinateEquiv.symm.contDiff

end Cylinder

end EulerSmoothTensorLimit
