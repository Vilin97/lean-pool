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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothSobolev

@[expose] public section

noncomputable section

/-! Strong L² derivatives of smooth representatives are their actual classical derivatives. -/

namespace EulerStrongSmoothJet

open MeasureTheory Filter EulerCylinderSobolev EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives EulerLiftedWeakDerivative EulerSpatialSobolevInverse
    EulerPressureSpatialRegularity
open scoped ContDiff ENNReal Topology

section General
variable {X F : Type*} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A strong L² derivative agrees almost everywhere with a pointwise derivative.
The proof extracts an almost-everywhere convergent subsequence of the difference quotients. -/
theorem lp_derivative_ae (U : ℝ → Lp F 2 μ) (V : Lp F 2 μ)
    (u : ℝ → X → F) (v : X → F) (hrep : ∀ t, (U t : X → F) =ᵐ[μ] u t)
    (hU : HasDerivAt U V 0) (hu : ∀ x, HasDerivAt (fun t => u t x) (v x) 0) :
    (V : X → F) =ᵐ[μ] v := by
  have hQ (t : ℝ) : (slope U 0 t : X → F) =ᵐ[μ] (fun x => slope (fun r => u r x) 0 t) := by
    filter_upwards [Lp.coeFn_smul (t-0)⁻¹ (U t-U 0), Lp.coeFn_sub (U t) (U 0), hrep t, hrep 0]
      with x hsm hsub ht hzero
    simp only [Pi.smul_apply, Pi.sub_apply] at hsm hsub
    simp only [slope, vsub_eq_sub]
    rw [hsm, hsub, ht, hzero]
  obtain ⟨ts, hts, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hU.tendsto_slope).exists_seq_tendsto_ae'
  have hrepseq : ∀ᵐ x ∂μ, ∀ n : ℕ,
      (slope U 0 (ts n)) x = slope (fun r => u r x) 0 (ts n) :=
    ae_all_iff.mpr (fun n => hQ (ts n))
  filter_upwards [hlim, hrepseq] with x hx hqx
  have hpoint := (hu x).tendsto_slope.comp hts
  have he : (fun n => (slope U 0 (ts n)) x) = (fun n => slope (fun r => u r x) 0 (ts n)) :=
    funext hqx
  rw [he] at hx
  exact tendsto_nhds_unique hx hpoint

end General

variable (period : ℝ) [Fact (0 < period)]

omit [Fact (0 < period)] in
/-- The pointwise translation orbit of a smooth cylinder field has its actual directional derivative. -/
theorem pointwise_translation_hasDerivAt (a : LiftTangent)
    (f : LiftDomain period → Vector3) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (x : LiftDomain period) :
    HasDerivAt (fun t => f (x + translationPath period a t)) (fieldDerivative period a f x) 0 := by
  have hF := (((hf x).differentiable (by simp)) ((0 : ℝ) • a)).hasFDerivAt
  have h := hF.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).smul_const a)
  convert! h using 1
  simp [fieldDerivative]

/-- Any strong translation derivative of a smooth representative is its classical derivative,
without compactness or a priori integrability of that classical derivative. -/
theorem translation_derivative_ae (a : LiftTangent) (U V : LiftL2 period)
    (f : LiftDomain period → Vector3) (hrep : (U : LiftDomain period → Vector3) =ᵐ[liftMeasure
      period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hD : HasDerivAt (fun t => translation period (translationPath period a t) U) V 0) :
    (V : LiftDomain period → Vector3) =ᵐ[liftMeasure period] fieldDerivative period a f := by
  apply lp_derivative_ae (liftMeasure period)
    (fun t => translation period (translationPath period a t) U) V
    (fun t x => f (x + translationPath period a t)) (fieldDerivative period a f)
    ?_ hD (pointwise_translation_hasDerivAt period a f hf)
  intro t
  filter_upwards [translation_ae period (translationPath period a t) U,
    (measurePreserving_translation period (translationPath period a t)).quasiMeasurePreserving.ae
      hrep]
    with x htrans hx
  exact htrans.trans hx

/-- Every word of a strong Sobolev jet agrees with the actual classical word of a smooth representative. -/
theorem jet_word_ae {s n : ℕ} (hn : n ≤ s) (U : LiftL2 period)
    (J : SpatialJet period standardDirection s U) (w : Fin n → Fin 4)
    (f : LiftDomain period → Vector3) (hrep : (U : LiftDomain period → Vector3) =ᵐ[liftMeasure
      period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    (J.word w : LiftDomain period → Vector3) =ᵐ[liftMeasure period] iteratedFieldDerivative period
      w f := by
  induction n with
  | zero => simpa only [SpatialJet.word_zero, iteratedFieldDerivative_zero] using hrep
  | succ n ih =>
    have hbase := ih (by omega : n ≤ s) (Fin.tail w)
    have hD := J.word_hasDerivAt (by omega : n < s) (Fin.tail w) (w 0)
    have h := translation_derivative_ae period (standardDirection (w 0)) (J.word (Fin.tail w))
      (J.word (Fin.cons (w 0) (Fin.tail w))) (iteratedFieldDerivative period (Fin.tail w) f)
      hbase (iteratedFieldDerivative_smooth period (Fin.tail w) f hf) hD
    simpa only [Fin.cons_self_tail, iteratedFieldDerivative_succ] using h

/-- Strong jets force all actual classical derivatives through the corresponding order to lie in L². -/
theorem jet_classical_memLp {s n : ℕ} (hn : n ≤ s) (U : LiftL2 period)
    (J : SpatialJet period standardDirection s U) (w : Fin n → Fin 4)
    (f : LiftDomain period → Vector3) (hrep : (U : LiftDomain period → Vector3) =ᵐ[liftMeasure
      period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period) :=
  (Lp.memLp (J.word w)).ae_eq (jet_word_ae period hn U J w f hrep hf)

/-- The strong Sobolev jet norm is exactly the classical derivative Sobolev norm for any smooth representative. -/
theorem jet_sobolevNorm_eq {s : ℕ} (U : LiftL2 period)
    (J : SpatialJet period standardDirection s U)
    (f : LiftDomain period → Vector3) (hrep : (U : LiftDomain period → Vector3) =ᵐ[liftMeasure
      period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    J.sobolevNorm = liftSobolevNorm period s f := by
  rw [SpatialJet.sobolevNorm_eq_sum_words]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro w _
  have h := eLpNorm_congr_ae (p := (2 : ℝ≥0∞))
    (jet_word_ae period (by have := Finset.mem_range.1 hn; omega) U J w f hrep hf)
  simpa only [Lp.norm_def] using congrArg ENNReal.toReal h

end EulerStrongSmoothJet
