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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CoverMollification

@[expose] public section

noncomputable section

/-! The finite-set Fubini bridge identifying classical and L² cylinder mollification. -/

namespace EulerCoverMollificationFubini

open MeasureTheory EulerSobolev EulerCylinderCoordinates EulerCoverMollification
  EulerLiftedGradientSpace
open scoped ENNReal ContDiff Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The elementary L²-to-L¹ bound on an arbitrary finite-measure set. -/
theorem finite_set_integral_norm_le (f : LiftDomain period → Vector3)
    (hf : MemLp f 2 (liftMeasure period)) (K : Set (LiftDomain period))
    (hK : liftMeasure period K < ⊤) :
    (∫ x in K, ‖f x‖ ∂liftMeasure period) ≤
      (eLpNorm f 2 (liftMeasure period)).toReal * (liftMeasure period K).toReal ^ (1/2 : ℝ) := by
  have hA := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := (1 : ℝ≥0∞)) (q := 2)
    (by norm_num) (hf.restrict K).1
  norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat, one_div, inv_one,
    Measure.restrict_apply_univ] at hA
  have hB : eLpNorm f 2 ((liftMeasure period).restrict K) * (liftMeasure period K)^(1/2 : ℝ) ≤
      eLpNorm f 2 (liftMeasure period) * (liftMeasure period K)^(1/2 : ℝ) :=
    mul_le_mul' (eLpNorm_mono_measure f (Measure.restrict_le_self (s := K))) le_rfl
  have hfin : eLpNorm f 2 (liftMeasure period) * (liftMeasure period K) ^ (1/2 : ℝ) ≠ ⊤ := by
    finiteness
  have hC := ENNReal.toReal_mono hfin (hA.trans hB)
  rw [integral_norm_eq_lintegral_enorm (hf.restrict K).1, ← eLpNorm_one_eq_lintegral_enorm]
  convert hC using 1
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]

omit [Fact (0 < period)] in
/-- The Euclidean covering map is continuous. -/
theorem euclideanCover_continuous : Continuous (euclideanCover period) :=
  (coveringMap_isOpenQuotient period).isQuotientMap.continuous.comp coordinateEquiv.continuous

/-- The convolution kernel is jointly integrable over the kernel variable and any finite cylinder set. -/
theorem kernel_integrable_prod (φ : ContDiffBump (0 : Domain 4)) (U : LiftL2 period)
    (K : Set (LiftDomain period)) (hK : liftMeasure period K < ⊤) :
    Integrable (fun p : Domain 4 × LiftDomain period =>
      φ.normed volume p.1 • U (p.2 - euclideanCover period p.1))
      ((volume : Measure (Domain 4)).prod ((liftMeasure period).restrict K)) := by
  have : Fact (liftMeasure period K < ⊤) := ⟨hK⟩
  have hmap : Measurable (fun p : Domain 4 × LiftDomain period => p.2 - euclideanCover period p.1)
    :=
    (continuous_snd.sub ((euclideanCover_continuous period).comp continuous_fst)).measurable
  have hsm : StronglyMeasurable (fun p : Domain 4 × LiftDomain period =>
      φ.normed volume p.1 • U (p.2 - euclideanCover period p.1)) :=
    ((φ.contDiff_normed (n := (⊤ : ℕ∞))).continuous.comp continuous_fst).stronglyMeasurable.smul
      ((Lp.stronglyMeasurable U).comp_measurable hmap)
  have hshift (y : Domain 4) : MemLp (fun x => U (x - euclideanCover period y)) 2 (liftMeasure
    period) := by
    convert! (Lp.memLp U).comp_measurePreserving
      (measurePreserving_translation period (-euclideanCover period y)) using 1
  apply (integrable_prod_iff hsm.aestronglyMeasurable).2
  constructor
  · filter_upwards [] with y
    have hint : Integrable (fun x => U (x-euclideanCover period y)) ((liftMeasure period).restrict
      K) :=
      ((hshift y).restrict K).integrable (by norm_num)
    exact hint.smul (φ.normed volume y)
  · have hbound (y : Domain 4) : (∫ x in K, ‖φ.normed volume y • U (x - euclideanCover period y)‖
    ∂liftMeasure period) ≤
        ‖φ.normed volume y‖ * (‖U‖ * (liftMeasure period K).toReal ^ (1/2 : ℝ)) := by
      simp only [norm_smul, integral_const_mul]
      have he : eLpNorm (fun x => U (x - euclideanCover period y)) 2 (liftMeasure period) =
          eLpNorm U 2 (liftMeasure period) := by
        simpa only [Function.comp_def, sub_eq_add_neg] using
          eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞)) (Lp.aestronglyMeasurable U)
            (measurePreserving_translation period (-euclideanCover period y))
      have h := finite_set_integral_norm_le period _ (hshift y) K hK
      rw [he, ← Lp.norm_def] at h
      exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
    exact (φ.integrable_normed.norm.mul_const (‖U‖ * (liftMeasure period K).toReal ^ (1/2 :
      ℝ))).mono'
      hsm.norm.integral_prod_right'.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
        exact hbound y))

/-- The classical cylinder convolution is integrable on each finite-measure set. -/
theorem cylinderConvolution_integrableOn (φ : ContDiffBump (0 : Domain 4)) (U : LiftL2 period)
    (K : Set (LiftDomain period)) (hK : liftMeasure period K < ⊤) :
    IntegrableOn (cylinderConvolution period φ U) K (liftMeasure period) := by
  exact (kernel_integrable_prod period φ U K hK).integral_prod_right

/-- Exact Fubini identity for every finite cylinder set. -/
theorem setIntegral_cylinderConvolution (φ : ContDiffBump (0 : Domain 4)) (U : LiftL2 period)
    (K : Set (LiftDomain period)) (hK : liftMeasure period K < ⊤) :
    (∫ x in K, cylinderConvolution period φ U x ∂liftMeasure period) =
      ∫ y : Domain 4, φ.normed volume y • (∫ x in K, U (x-euclideanCover period y) ∂liftMeasure
        period) := by
  have h := integral_integral_swap (f := fun (y : Domain 4) (x : LiftDomain period) =>
      φ.normed volume y • U (x-euclideanCover period y))
    (μ := (volume : Measure (Domain 4))) (ν := (liftMeasure period).restrict K)
    (kernel_integrable_prod period φ U K hK)
  change (∫ x in K, ∫ y : Domain 4, φ.normed volume y • U (x-euclideanCover period y) ∂volume
    ∂liftMeasure period) = _
  rw [← h]
  simp only [integral_smul]

/-- Equality of finite-set integrals identifies a Bochner L² mollifier with the classical smooth field. -/
theorem ae_eq_cylinderConvolution_of_setIntegrals (φ : ContDiffBump (0 : Domain 4)) (U V : LiftL2
  period)
    (hV : ∀ K : Set (LiftDomain period), MeasurableSet K → liftMeasure period K < ⊤ →
      (∫ x in K, V x ∂liftMeasure period) =
        ∫ y : Domain 4, φ.normed volume y • (∫ x in K, U (x-euclideanCover period y) ∂liftMeasure
          period)) :
    (V : LiftDomain period → Vector3) =ᵐ[liftMeasure period] cylinderConvolution period φ U := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro K _ hK
    have : Fact (liftMeasure period K < ⊤) := ⟨hK⟩
    exact ((Lp.memLp V).restrict K).integrable (by norm_num)
  · intro K _ hK
    exact cylinderConvolution_integrableOn period φ U K hK
  · intro K hK hfin
    exact (hV K hK hfin).trans (setIntegral_cylinderConvolution period φ U K hfin).symm

end EulerCoverMollificationFubini
