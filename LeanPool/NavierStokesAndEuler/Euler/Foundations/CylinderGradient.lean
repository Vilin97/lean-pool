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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.MixedCylinderTransport

@[expose] public section

noncomputable section

/-! Actual full cylinder gradients from the coordinate derivative Sobolev norms. -/

namespace EulerCylinderGradient

open MeasureTheory EulerSobolev EulerCylinderSobolev EulerCylinderCoordinates EulerVectorCylinder
open EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
  EulerLiftedWeakDerivative
open scoped ENNReal ContDiff

variable (period : ℝ) [Fact (0 < period)]

/-- All low-order real vector derivative words are bounded by the actual H⁶ norm. -/
theorem vector_word_pointwise_le_H6 (q : ℕ) {m : ℕ} (hm : m ≤ 3) (w : Fin m → Fin 4)
    (f : LiftDomain period → Domain q) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ 6, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure
      period))
    (x : LiftDomain period) :
    ‖iteratedFieldDerivative period w f x‖ ≤
      ((q : ℝ) * cylinderEmbeddingConstant period) * (85 * liftSobolevNorm period 6 f) := by
  have hA := vector_cylinder_pointwise_le_H3 period q (iteratedFieldDerivative period w f)
    (iteratedFieldDerivative_smooth period w f hf)
    (fun j hj v => word_memLp period (by omega : m+j ≤ 6) v w f hfL2) x
  exact hA.trans (mul_le_mul_of_nonneg_left (word_H3_le_H6 period hm w f)
    (mul_nonneg (Nat.cast_nonneg _) (cylinderEmbeddingConstant_nonneg period)))

section General
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [Fact (0 < period)] in
theorem tangent_coordinate_norm_le (v : LiftTangent) (i : Fin 4) :
    ‖coordinateEquiv.symm v i‖ ≤ ‖v‖ := by
  cases i using Fin.cases with
  | zero => simpa using norm_snd_le v
  | succ i => exact (PiLp.norm_apply_le v.1 i).trans (norm_fst_le v)

omit [Fact (0 < period)] in
/-- The full product-tangent operator norm is bounded by its four coordinate values. -/
theorem linear_norm_le_standard_sum (A : LiftTangent →L[ℝ] F) :
    ‖A‖ ≤ ∑ i : Fin 4, ‖A (standardDirection i)‖ := by
  apply A.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro v
  have he : (∑ i : Fin 4, (coordinateEquiv.symm v i) • EuclideanSpace.single i (1 : ℝ)) =
    coordinateEquiv.symm v := by
    ext i
    simp [Pi.single_apply, mul_ite]
  have hv : (∑ i : Fin 4, (coordinateEquiv.symm v i) • standardDirection i) = v := by
    change (∑ i : Fin 4, (coordinateEquiv.symm v i) • coordinateEquiv (EuclideanSpace.single i (1 :
      ℝ))) = v
    simp_rw [← map_smul]
    rw [← map_sum, he, ContinuousLinearEquiv.apply_symm_apply]
  have hA : A v = ∑ i : Fin 4, (coordinateEquiv.symm v i) • A (standardDirection i) := by
    simp_rw [← map_smul]
    rw [← map_sum, hv]
  rw [hA]
  calc
    _ ≤ ∑ i : Fin 4, ‖(coordinateEquiv.symm v i) • A (standardDirection i)‖ := norm_sum_le _ _
    _ = ∑ i : Fin 4, ‖coordinateEquiv.symm v i‖ * ‖A (standardDirection i)‖ := by simp only
      [norm_smul]
    _ ≤ ∑ i : Fin 4, ‖v‖ * ‖A (standardDirection i)‖ := by
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (tangent_coordinate_norm_le v
        i) (norm_nonneg _))
    _ = _ := by rw [← Finset.mul_sum]; ring

omit [Fact (0 < period)] in
theorem fieldFDeriv_norm_le_standard_sum (f : LiftDomain period → F) (x : LiftDomain period) :
    ‖fieldFDeriv period f x‖ ≤ ∑ i : Fin 4, ‖fieldDerivative period (standardDirection i) f x‖ :=
  linear_norm_le_standard_sum (fieldFDeriv period f x)

/-- Actual full gradient integrability follows from the four genuine coordinate derivatives. -/
theorem fieldFDeriv_memLp_of_coordinates (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hD : ∀ i : Fin 4, MemLp (fieldDerivative period (standardDirection i) f) 2 (liftMeasure
      period)) :
    MemLp (fieldFDeriv period f) 2 (liftMeasure period) := by
  have hsum : MemLp (fun x => ∑ i : Fin 4, ‖fieldDerivative period (standardDirection i) f x‖) 2
    (liftMeasure period) :=
    memLp_finsetSum _ (fun i _ => (hD i).norm)
  have hc : Continuous (fieldFDeriv period f) := smoothField_continuous period _
    (fieldFDeriv_smooth period f hf)
  apply hsum.of_le hc.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
  exact fieldFDeriv_norm_le_standard_sum period f x

/-- The full-gradient L² norm is quantitatively bounded by the coordinate-gradient L² sum. -/
theorem fieldFDeriv_L2_le_coordinate_sum (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hD : ∀ i : Fin 4, MemLp (fieldDerivative period (standardDirection i) f) 2 (liftMeasure
      period)) :
    ‖(fieldFDeriv_memLp_of_coordinates period f hf hD).toLp (fieldFDeriv period f)‖ ≤
      ∑ i : Fin 4, (eLpNorm (fieldDerivative period (standardDirection i) f) 2 (liftMeasure
        period)).toReal := by
  have hA : eLpNorm (fieldFDeriv period f) 2 (liftMeasure period) ≤
      eLpNorm (fun x => ∑ i : Fin 4, ‖fieldDerivative period (standardDirection i) f x‖) 2
        (liftMeasure period) := by
    apply eLpNorm_mono
    intro x
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    exact fieldFDeriv_norm_le_standard_sum period f x
  have he : (fun x => ∑ i : Fin 4, ‖fieldDerivative period (standardDirection i) f x‖) =
      ∑ i : Fin 4, (fun x => ‖fieldDerivative period (standardDirection i) f x‖) := by funext x;
        simp
  rw [he] at hA
  have hB := eLpNorm_sum_le (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) => (hD i).1.norm)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  simp only [eLpNorm_norm] at hB
  have hC := ENNReal.toReal_mono (ENNReal.sum_ne_top.2 (fun i _ => (hD i).eLpNorm_ne_top))
    (hA.trans hB)
  rw [ENNReal.toReal_sum (fun i _ => (hD i).eLpNorm_ne_top)] at hC
  rw [Lp.norm_toLp]
  exact hC

end General
end EulerCylinderGradient
