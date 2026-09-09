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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.JetProductBounds

@[expose] public section

noncomputable section

/-! Gevrey pressure regularity derived from actual cylinder derivative jets and coercivity. -/


namespace EulerPressureGevrey

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerSpatialSobolevInverse
  EulerJetProductBounds EulerGevrey

variable (period : ℝ) [Fact (0 < period)]

/-- Every finite pressure solve obeys a Gevrey bound uniform in the cutoff order.
The triangular recurrence is derived from genuine strong translation derivatives. -/
theorem pressure_gevrey_majorant {directions : Fin 4 → LiftTangent}
    {s : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions s A) (J : SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (M Rc R : ℝ) (hM : 1 ≤ M) (hcM : c⁻¹ ≤ M) (hRc : 0 ≤ Rc)
    (hR : 2 * M * (Rc + 1) ≤ R) (d : ℕ)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ s → boundLevel period K l ≤ majorant Rc 0 l)
    (hsource : ∀ n ≤ s, levelNorm period J n ≤ majorant R d n) (n : ℕ) :
    levelNorm period (J.solvePressure K κ m c hc hpos) n ≤ majorant R (d + 1) n := by
  let P := J.solvePressure K κ m c hc hpos
  have hM0 : 0 ≤ M := by linarith
  have hR0 : 0 ≤ R := by nlinarith
  have hz : ∀ j, 0 ≤ levelNorm period P j := fun _ => levelNorm_nonneg P
  have hf : ∀ j, 0 ≤ levelNorm period J j := fun _ => levelNorm_nonneg J
  apply triangular_inverse_majorant M Rc R hM hRc hR d
    (levelNorm period J) (levelNorm period P) _ _ n
  · intro j
    by_cases hj : j ≤ s
    · exact hsource j hj
    · rw [levelNorm_eq_zero_of_lt J (by omega)]
      exact majorant_nonneg R hR0 d j
  · intro j
    have hsum0 : 0 ≤ ∑ l ∈ Finset.range j,
        (j.choose (l + 1) : ℝ) * Rc ^ (l + 1) * ((l + 1).factorial : ℝ) ^ 2 *
          levelNorm period P (j - (l + 1)) := by
      apply Finset.sum_nonneg
      intro l _
      exact mul_nonneg (by positivity) (hz _)
    by_cases hj : j ≤ s
    · have hrec := pressure_level_recurrence K J κ m c hc hpos hj
      have hsum : (∑ l ∈ Finset.range j,
          (j.choose (l + 1) : ℝ) * boundLevel period K (l + 1) *
            levelNorm period P (j - (l + 1))) ≤
          ∑ l ∈ Finset.range j,
            (j.choose (l + 1) : ℝ) * Rc ^ (l + 1) * ((l + 1).factorial : ℝ) ^ 2 *
              levelNorm period P (j - (l + 1)) := by
        apply Finset.sum_le_sum
        intro l hl
        have hlj : l < j := Finset.mem_range.mp hl
        have hcoef := hcoeff (l + 1) (by omega) (by omega)
        have hm := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg (j.choose (l + 1)))) (hz (j - (l + 1)))
        simpa only [majorant, Nat.add_zero, mul_assoc] using hm
      exact hrec.trans ((mul_le_mul_of_nonneg_left (add_le_add_right hsum _) (inv_nonneg.mpr
        hc.le)).trans
        (mul_le_mul_of_nonneg_right hcM (add_nonneg (hf j) hsum0)))
    · rw [levelNorm_eq_zero_of_lt P (by omega)]
      exact mul_nonneg hM0 (add_nonneg (hf j) hsum0)

/-- The same Gevrey inverse estimate written as the actual sum over all coordinate derivative words. -/
theorem pressure_word_sum_majorant {directions : Fin 4 → LiftTangent}
    {s : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions s A) (J : SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (M Rc R : ℝ) (hM : 1 ≤ M) (hcM : c⁻¹ ≤ M) (hRc : 0 ≤ Rc)
    (hR : 2 * M * (Rc + 1) ≤ R) (d : ℕ)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ s → boundLevel period K l ≤ majorant Rc 0 l)
    (hsource : ∀ n ≤ s, levelNorm period J n ≤ majorant R d n) (n : ℕ) :
    (∑ w : Fin n → Fin 4, ‖(J.solvePressure K κ m c hc hpos).word w‖) ≤ majorant R (d + 1) n := by
  rw [← levelNorm_eq_words]
  exact pressure_gevrey_majorant period K J κ m c hc hpos M Rc R hM hcM hRc hR d hcoeff hsource n

end EulerPressureGevrey
