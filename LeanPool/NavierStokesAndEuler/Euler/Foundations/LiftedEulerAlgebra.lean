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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderGraphTrace

@[expose] public section

noncomputable section

namespace EulerLiftedEulerAlgebra

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Forget the angle while retaining time and the particle label. -/
def parameterProjection : (ℝ × (E × ℝ)) →L[ℝ] (ℝ × E) :=
  (ContinuousLinearMap.fst ℝ ℝ (E × ℝ)).prod
    ((ContinuousLinearMap.fst ℝ E ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (E × ℝ)))

/-- The velocity in particle coordinates associated with the lifted unknown. -/
def liftedVelocity (κ : ℝ) (F : ℝ × E → E →L[ℝ] E)
    (z : ℝ × (E × ℝ) → E) (q : ℝ × (E × ℝ)) : E :=
  κ • F (q.1, q.2.1) (z q)

omit [CompleteSpace E] in
theorem liftedVelocity_fderiv (κ : ℝ) (F : ℝ × E → E →L[ℝ] E)
    (z : ℝ × (E × ℝ) → E) (q : ℝ × (E × ℝ))
    (DF : (ℝ × E) →L[ℝ] (E →L[ℝ] E)) (Dz : (ℝ × (E × ℝ)) →L[ℝ] E)
    (hF : HasFDerivAt F DF (q.1, q.2.1)) (hz : HasFDerivAt z Dz q)
    (v : ℝ × (E × ℝ)) :
    fderiv ℝ (liftedVelocity κ F z) q v =
      κ • (DF (v.1, v.2.1) (z q) + F (q.1, q.2.1) (Dz v)) := by
  have hp : HasFDerivAt (fun r : ℝ × (E × ℝ) => F (r.1, r.2.1))
      (DF.comp parameterProjection) q := hF.comp q (parameterProjection (E := E)).hasFDerivAt
  have hd : HasFDerivAt (fun r => κ • F (r.1, r.2.1) (z r))
      (κ • ((F (q.1, q.2.1)).comp Dz + (DF.comp parameterProjection).flip (z q))) q :=
    (hp.clm_apply hz).const_smul κ
  rw [show liftedVelocity κ F z = (fun r => κ • F (r.1, r.2.1) (z r)) from rfl,
    hd.fderiv]
  simp only [smul_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, parameterProjection, ContinuousLinearMap.prod_apply]
  congr 1
  exact add_comm _ _

/-- Exact transformation of the normalized Euler residual into the lifted
equation (16), using the actual derivatives of F and z. -/
theorem lifted_euler_residual (κ : ℝ) (F : ℝ × E → E →L[ℝ] E)
    (z : ℝ × (E × ℝ) → E) (q : ℝ × (E × ℝ))
    (DF : (ℝ × E) →L[ℝ] (E →L[ℝ] E)) (Dz : (ℝ × (E × ℝ)) →L[ℝ] E)
    (hF : HasFDerivAt F DF (q.1, q.2.1)) (hz : HasFDerivAt z Dz q)
    (A : E ≃L[ℝ] E) (hA : F (q.1, q.2.1) = A.toContinuousLinearMap)
    (m p : E) :
    fderiv ℝ (liftedVelocity κ F z) q (1, (0, 0)) +
      DF (1, 0) (A.symm (liftedVelocity κ F z q)) +
      fderiv ℝ (liftedVelocity κ F z) q (0, (κ • z q, ⟪m, z q⟫_ℝ)) +
      κ • A.symm.toContinuousLinearMap.adjoint p =
    κ • A (Dz (1, (0, 0)) + (2 : ℝ) • A.symm (DF (1, 0) (z q)) +
      Dz (0, (κ • z q, ⟪m, z q⟫_ℝ)) +
      κ • A.symm (DF (0, z q) (z q)) +
      A.symm (A.symm.toContinuousLinearMap.adjoint p)) := by
  rw [liftedVelocity_fderiv κ F z q DF Dz hF hz,
    liftedVelocity_fderiv κ F z q DF Dz hF hz]
  have harg : ((0 : ℝ), κ • z q) = κ • ((0 : ℝ), z q) := by simp
  simp only [liftedVelocity, hA, ContinuousLinearEquiv.coe_coe, map_smul,
    ContinuousLinearEquiv.symm_apply_apply, harg, smul_apply, map_add,
    ContinuousLinearEquiv.apply_symm_apply]
  module

end EulerLiftedEulerAlgebra
