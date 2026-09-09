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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderTransport

@[expose] public section

noncomputable section

/-! Smooth compact cylinder fields realize the strong-translation Sobolev jets. -/

namespace EulerCompactSmoothJet

open MeasureTheory EulerCylinderSobolev EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives EulerLiftedWeakDerivative EulerSpatialSobolevInverse
    EulerPressureSpatialRegularity
open scoped ContDiff ENNReal

variable (period : ℝ) [Fact (0 < period)]

omit [Fact (0 < period)] in
theorem iteratedFieldDerivative_compact {n : ℕ} (w : Fin n → Fin 4)
    (f : LiftDomain period → Vector3) (hfc : HasCompactSupport f) :
    HasCompactSupport (iteratedFieldDerivative period w f) := by
  induction n with
  | zero => exact hfc
  | succ n ih => exact fieldDerivative_compact period _ _ (ih (Fin.tail w))

omit [Fact (0 < period)] in
/-- Splitting off the last direction agrees with the jet's derivative-word convention. -/
theorem iteratedFieldDerivative_init_last {n : ℕ} (w : Fin (n+1) → Fin 4)
    (f : LiftDomain period → Vector3) :
    iteratedFieldDerivative period w f = iteratedFieldDerivative period (Fin.init w)
      (fieldDerivative period (standardDirection (w (Fin.last n))) f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change fieldDerivative period (standardDirection (w 0))
      (iteratedFieldDerivative period (Fin.tail w) f) =
      fieldDerivative period (standardDirection (w 0))
        (iteratedFieldDerivative period (Fin.tail (Fin.init w))
          (fieldDerivative period (standardDirection (w (Fin.last (n+1)))) f))
    rw [ih (Fin.tail w)]
    rfl

theorem translation_hasDerivAt_smoothFieldLp (a : LiftTangent)
    (f : LiftDomain period → Vector3) (hfc : HasCompactSupport f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    HasDerivAt (fun t => translation period (translationPath period a t)
      (smoothFieldLp period f hfc hf))
      (smoothFieldLp period (fieldDerivative period a f)
        (fieldDerivative_compact period a f hfc) (fieldDerivative_smooth period a f hf)) 0 :=
  smoothFieldLp_translation_hasDerivAt period a f hfc hf

/-- The actual strong L² translation jet of a smooth compact field. -/
noncomputable def compactSmoothJet (n : ℕ) (f : LiftDomain period → Vector3)
    (hfc : HasCompactSupport f) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    SpatialJet period standardDirection n (smoothFieldLp period f hfc hf) :=
  match n with
  | 0 => .zero _
  | n+1 => .succ (fun i => smoothFieldLp period (fieldDerivative period (standardDirection i) f)
      (fieldDerivative_compact period _ f hfc) (fieldDerivative_smooth period _ f hf))
      (fun i => compactSmoothJet n (fieldDerivative period (standardDirection i) f)
        (fieldDerivative_compact period _ f hfc) (fieldDerivative_smooth period _ f hf))
      (fun i => translation_hasDerivAt_smoothFieldLp period (standardDirection i) f hfc hf)

theorem smoothFieldLp_congr (f g : LiftDomain period → Vector3) (he : f = g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    smoothFieldLp period f hfc hf = smoothFieldLp period g hgc hg := by
  subst g
  rfl

/-- Every word in the strong jet is represented by the corresponding actual smooth derivative. -/
theorem compactSmoothJet_word {s n : ℕ} (hn : n ≤ s) (w : Fin n → Fin 4)
    (f : LiftDomain period → Vector3) (hfc : HasCompactSupport f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    (compactSmoothJet period s f hfc hf).word w =
      smoothFieldLp period (iteratedFieldDerivative period w f)
        (iteratedFieldDerivative_compact period w f hfc) (iteratedFieldDerivative_smooth period w f
          hf) := by
  induction n generalizing s f with
  | zero => simp only [SpatialJet.word_zero, iteratedFieldDerivative_zero]
  | succ n ih =>
    cases s with
    | zero => omega
    | succ s =>
      rw [compactSmoothJet, SpatialJet.word_succ]
      rw [ih (by omega : n ≤ s)]
      exact smoothFieldLp_congr period _ _ (iteratedFieldDerivative_init_last period w f).symm _ _
        _ _

/-- The L² norm of each jet word is exactly the norm of the actual classical derivative. -/
theorem compactSmoothJet_word_norm {s n : ℕ} (hn : n ≤ s) (w : Fin n → Fin 4)
    (f : LiftDomain period → Vector3) (hfc : HasCompactSupport f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    ‖(compactSmoothJet period s f hfc hf).word w‖ =
      (eLpNorm (iteratedFieldDerivative period w f) 2 (liftMeasure period)).toReal := by
  rw [compactSmoothJet_word period hn w f hfc hf]
  rw [smoothFieldLp, Lp.norm_toLp]

/-- The strong Sobolev jet norm is exactly the actual derivative-word Sobolev norm. -/
theorem compactSmoothJet_sobolevNorm (s : ℕ) (f : LiftDomain period → Vector3)
    (hfc : HasCompactSupport f) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    (compactSmoothJet period s f hfc hf).sobolevNorm = liftSobolevNorm period s f := by
  rw [SpatialJet.sobolevNorm_eq_sum_words]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro w _
  exact compactSmoothJet_word_norm period (by have := Finset.mem_range.1 hn; omega) w f hfc hf

end EulerCompactSmoothJet
