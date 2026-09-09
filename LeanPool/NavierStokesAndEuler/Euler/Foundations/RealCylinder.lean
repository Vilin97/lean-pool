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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderAlgebra

@[expose] public section

noncomputable section

/-! Real-valued forms of the cylinder Sobolev and multiplication estimates. -/

namespace EulerRealCylinder

open MeasureTheory EulerCylinderSobolev EulerCylinderAlgebra
open EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
open scoped ENNReal NNReal ContDiff

variable (period : ℝ)

section LinearMaps
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem fieldDerivative_postcomp (L : F →L[ℝ] G) (a : LiftTangent)
    (f : LiftDomain period → F) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    fieldDerivative period a (L ∘ f) = L ∘ fieldDerivative period a f := by
  funext x
  have h := L.hasFDerivAt.comp 0 (((hf x).differentiable (by simp)) 0).hasFDerivAt
  exact congrArg (fun A : LiftTangent →L[ℝ] G => A a) h.fderiv

theorem iteratedFieldDerivative_postcomp {n : ℕ} (L : F →L[ℝ] G) (w : Fin n → Fin 4)
    (f : LiftDomain period → F) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    iteratedFieldDerivative period w (L ∘ f) = L ∘ iteratedFieldDerivative period w f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedFieldDerivative_succ, ih (Fin.tail w), fieldDerivative_postcomp period L _ _
      (iteratedFieldDerivative_smooth period (Fin.tail w) f hf)]
    rfl

end LinearMaps

/-- Isometric complexification of a real scalar cylinder field. -/
noncomputable def complexField (f : LiftDomain period → ℝ) : LiftDomain period → ℂ :=
  Complex.ofRealCLM ∘ f

theorem complexField_smooth (f : LiftDomain period → ℝ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (complexField period f) x) :=
  fun x => Complex.ofRealCLM.contDiff.comp (hf x)

theorem complexField_word {n : ℕ} (w : Fin n → Fin 4) (f : LiftDomain period → ℝ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    iteratedFieldDerivative period w (complexField period f) =
      complexField period (iteratedFieldDerivative period w f) :=
  iteratedFieldDerivative_postcomp period Complex.ofRealCLM w f hf

variable [Fact (0 < period)]

theorem complexField_eLpNorm (f : LiftDomain period → ℝ) :
    eLpNorm (complexField period f) 2 (liftMeasure period) = eLpNorm f 2 (liftMeasure period) := by
  apply eLpNorm_congr_norm_ae
  filter_upwards [] with x
  exact Complex.norm_real _

theorem complexField_memLp (f : LiftDomain period → ℝ) (hf : MemLp f 2 (liftMeasure period)) :
    MemLp (complexField period f) 2 (liftMeasure period) :=
  Complex.ofRealCLM.comp_memLp' hf

theorem complexField_sobolevNorm (s : ℕ) (f : LiftDomain period → ℝ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    liftSobolevNorm period s (complexField period f) = liftSobolevNorm period s f := by
  unfold liftSobolevNorm
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro w _
  rw [complexField_word period w f hf, complexField_eLpNorm]

/-- The actual real H³ to L∞ embedding on the cylinder. -/
theorem real_cylinder_pointwise_le_H3 (f : LiftDomain period → ℝ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ 3, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖f x‖ ≤ cylinderEmbeddingConstant period * liftSobolevNorm period 3 f := by
  have h := cylinder_pointwise_le_H3 period (complexField period f) (complexField_smooth period f
    hf)
    (fun j hj w => by rw [complexField_word period w f hf]; exact complexField_memLp period _ (hfL2
      j hj w)) x
  rw [complexField_sobolevNorm period 3 f hf] at h
  simpa only [complexField, Function.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real] using h

/-- The real H⁶ algebra estimate on the actual cylinder. -/
theorem real_cylinder_H6_algebra (f g : LiftDomain period → ℝ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ j ≤ 6, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period))
    (hgL2 : ∀ j ≤ 6, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure period)) :
    liftSobolevNorm period 6 (f*g) ≤ (5461 * 128 * lowDerivativeConstant period) *
      liftSobolevNorm period 6 f * liftSobolevNorm period 6 g := by
  have h := cylinder_H6_algebra period (complexField period f) (complexField period g)
    (complexField_smooth period f hf) (complexField_smooth period g hg)
    (fun j hj w => by rw [complexField_word period w f hf]; exact complexField_memLp period _ (hfL2
      j hj w))
    (fun j hj w => by rw [complexField_word period w g hg]; exact complexField_memLp period _ (hgL2
      j hj w))
  have he : complexField period f * complexField period g = complexField period (f*g) := by
    ext x
    exact (Complex.ofReal_mul _ _).symm
  rw [he, complexField_sobolevNorm period 6 (f*g) (fun x => (hf x).mul (hg x)),
    complexField_sobolevNorm period 6 f hf, complexField_sobolevNorm period 6 g hg] at h
  exact h

end EulerRealCylinder
