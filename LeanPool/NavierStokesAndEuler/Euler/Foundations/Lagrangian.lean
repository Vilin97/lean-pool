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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.DNSelection

@[expose] public section

noncomputable section

namespace EulerLagrangian

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The unforced Euler momentum residual, with space-time derivative and the
canonical real gradient. -/
def momentumResidual (u : ℝ × E → E) (p : ℝ × E → ℝ) (z : ℝ × E) : E :=
  fderiv ℝ u z (1, u z) + gradient (fun x => p (z.1, x)) z.2

omit [CompleteSpace E] in
theorem material_derivative (w : ℝ × E → E) (X : ℝ → E) (t : ℝ)
    (U : E) (D : (ℝ × E) →L[ℝ] E)
    (hX : HasDerivAt X U t) (hw : HasFDerivAt w D (t, X t)) :
    HasDerivAt (fun s => w (s, X s)) (D (1, U)) t :=
  hw.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hX)

theorem gradient_add (f g : E → ℝ) (x : E)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y + g y) x = gradient f x + gradient g x := by
  have hs : HasFDerivAt (fun y => f y + g y) (fderiv ℝ f x + fderiv ℝ g x) x :=
    hf.hasFDerivAt.add hg.hasFDerivAt
  simp only [gradient, hs.fderiv, map_add]

theorem momentum_perturbation (u w : ℝ × E → E) (p q : ℝ × E → ℝ)
    (z : ℝ × E) (Du Dw : (ℝ × E) →L[ℝ] E)
    (hu : HasFDerivAt u Du z) (hw : HasFDerivAt w Dw z)
    (hp : DifferentiableAt ℝ (fun x => p (z.1, x)) z.2)
    (hq : DifferentiableAt ℝ (fun x => q (z.1, x)) z.2) :
    momentumResidual (fun y => u y + w y) (fun y => p y + q y) z =
      momentumResidual u p z + Dw (1, u z) + Du (0, w z) + Dw (0, w z) +
        gradient (fun x => q (z.1, x)) z.2 := by
  have hsplit : ((1 : ℝ), u z + w z) = (1, u z) + (0, w z) := by simp
  have hs : HasFDerivAt (fun y => u y + w y) (Du + Dw) z := hu.add hw
  simp only [momentumResidual, hs.fderiv, hu.fderiv,
    add_apply, hsplit, map_add,
    gradient_add _ _ _ hp hq]
  abel

theorem euler_perturbation_along_flow (u w : ℝ × E → E)
    (p q : ℝ × E → ℝ) (X : ℝ → E) (t : ℝ)
    (Du Dw : (ℝ × E) →L[ℝ] E) (V : E)
    (hX : HasDerivAt X (u (t, X t)) t)
    (hu : HasFDerivAt u Du (t, X t)) (hw : HasFDerivAt w Dw (t, X t))
    (hW : HasDerivAt (fun s => w (s, X s)) V t)
    (hp : DifferentiableAt ℝ (fun x => p (t, x)) (X t))
    (hq : DifferentiableAt ℝ (fun x => q (t, x)) (X t))
    (hparent : momentumResidual u p (t, X t) = 0) :
    momentumResidual (fun y => u y + w y) (fun y => p y + q y) (t, X t) =
      V + Du (0, w (t, X t)) + Dw (0, w (t, X t)) +
        gradient (fun x => q (t, x)) (X t) := by
  have hV := hW.unique (material_derivative w X t _ Dw hX hw)
  rw [momentum_perturbation u w p q (t, X t) Du Dw hu hw hp hq, hparent,
    zero_add, ← hV]

omit [CompleteSpace E] in
theorem deformation_acceleration (F M H : ℝ → E →L[ℝ] E) (t : ℝ)
    (hF : HasDerivAt F ((M t).comp (F t)) t)
    (hM : HasDerivAt M (-((M t).comp (M t)) - H t) t) :
    HasDerivAt (fun s => (M s).comp (F s)) (-((H t).comp (F t))) t := by
  convert hM.clm_comp hF using 1
  ext v
  simp only [add_apply, sub_apply, neg_apply, ContinuousLinearMap.comp_apply]
  abel

omit [CompleteSpace E] in
theorem derivative_pullback_inverse (f X : E → E) (F : E ≃L[ℝ] E) (x : E)
    (hX : HasFDerivAt X F.toContinuousLinearMap x)
    (hf : DifferentiableAt ℝ f (X x)) :
    fderiv ℝ f (X x) = (fderiv ℝ (f ∘ X) x).comp F.symm.toContinuousLinearMap := by
  rw [(hf.hasFDerivAt.comp x hX).fderiv]
  ext v
  simp

theorem gradient_pullback (f : E → ℝ) (X : E → E) (F : E →L[ℝ] E) (x : E)
    (hX : HasFDerivAt X F x) (hf : DifferentiableAt ℝ f (X x)) :
    gradient (f ∘ X) x = F.adjoint (gradient f (X x)) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, ContinuousLinearMap.adjoint_inner_left, inner_gradient_left,
    (hf.hasFDerivAt.comp x hX).fderiv]
  rfl

theorem gradient_pullback_inverse (f : E → ℝ) (X : E → E) (F : E ≃L[ℝ] E) (x : E)
    (hX : HasFDerivAt X F.toContinuousLinearMap x)
    (hf : DifferentiableAt ℝ f (X x)) :
    gradient f (X x) = F.symm.toContinuousLinearMap.adjoint (gradient (f ∘ X) x) := by
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left, gradient_pullback f X _ x hX hf,
    ContinuousLinearMap.adjoint_inner_left]
  simp

end EulerLagrangian
