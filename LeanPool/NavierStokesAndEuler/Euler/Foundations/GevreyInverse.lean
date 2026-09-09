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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.GevreyFunctions

@[expose] public section

noncomputable section

namespace EulerGevreyInverse

open EulerGevrey Finset
open scoped ContDiff

theorem reciprocal_derivative_recurrence (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hnz : ∀ x, f x ≠ 0) (n : ℕ) (x : ℝ) :
    iteratedDeriv (n + 1) (fun y => (f y)⁻¹) x = -(f x)⁻¹ *
      ∑ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ℝ) *
        iteratedDeriv (k + 1) f x * iteratedDeriv (n + 1 - (k + 1)) (fun y => (f y)⁻¹) x := by
  have hi : ContDiff ℝ ∞ (fun y => (f y)⁻¹) := hf.inv hnz
  have he : (fun y => f y * (f y)⁻¹) = fun _ => (1 : ℝ) := by
    funext y
    exact mul_inv_cancel₀ (hnz y)
  have hp := congrArg (fun g : ℝ → ℝ => iteratedDeriv (n + 1) g x) he
  have hmul : (fun y => f y * (f y)⁻¹) = f * (fun y => (f y)⁻¹) := rfl
  rw [hmul] at hp
  rw [iteratedDeriv_mul (hf.contDiffAt.of_le (by simp)) (hi.contDiffAt.of_le (by simp)),
    sum_range_succ'] at hp
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero,
    Nat.sub_zero, iteratedDeriv_const, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    ↓reduceIte] at hp
  have h := congrArg (fun z : ℝ => (f x)⁻¹ * z) hp
  field_simp [hnz x] at h ⊢
  nlinarith

theorem reciprocal_gevrey_shift (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hnz : ∀ x, f x ≠ 0) (A Rc R : ℝ) (hA : 1 ≤ A) (hRc : 0 ≤ Rc)
    (hR : 2 * A * (Rc + 1) ≤ R)
    (hb : ∀ x, |(f x)⁻¹| ≤ A)
    (hc : ∀ n x, |iteratedDeriv (n + 1) f x| ≤ majorant Rc 0 (n + 1))
    (n : ℕ) (x : ℝ) :
    |iteratedDeriv n (fun y => (f y)⁻¹) x| ≤ majorant R 1 n := by
  have hA0 : 0 ≤ A := by linarith
  have hR0 : 0 ≤ R := by nlinarith
  apply triangular_inverse_majorant A Rc R hA hRc hR 0
    (fun n => if n = 0 then 1 else 0)
    (fun n => |iteratedDeriv n (fun y => (f y)⁻¹) x|) _ _ n
  · intro k
    split_ifs with hk
    · subst k
      simp [majorant]
    · exact majorant_nonneg R hR0 0 k
  · intro k
    cases k with
    | zero => simpa using hb x
    | succ k =>
      rw [reciprocal_derivative_recurrence f hf hnz k x, abs_mul, abs_neg]
      simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add]
      apply mul_le_mul (hb x) _ (abs_nonneg _) hA0
      calc
        _ ≤ ∑ j ∈ range (k + 1), |((k + 1).choose (j + 1) : ℝ) *
            iteratedDeriv (j + 1) f x *
            iteratedDeriv (k + 1 - (j + 1)) (fun y => (f y)⁻¹) x| := abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply sum_le_sum
          intro j _
          have hj : (0 : ℝ) ≤ (k + 1).choose (j + 1) := by positivity
          have h := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hc j x) hj)
            (abs_nonneg (iteratedDeriv (k + 1 - (j + 1)) (fun y => (f y)⁻¹) x))
          simpa only [abs_mul, abs_of_nonneg hj, majorant, Nat.add_zero, mul_assoc] using h

theorem shift_one_bound (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    majorant R 1 n ≤ R * majorant (4 * R) 0 n := by
  have hnat : n + 1 ≤ 2 ^ n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      have : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
      omega
  have hn : (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by exact_mod_cast hnat
  have hs : ((n : ℝ) + 1) ^ 2 ≤ (4 : ℝ) ^ n := by
    calc
      _ ≤ ((2 : ℝ) ^ n) ^ 2 := by gcongr
      _ = _ := by rw [← pow_mul, mul_comm n 2, pow_mul]; norm_num
  simp only [majorant, Nat.add_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, mul_pow, pow_succ]
  have hp := mul_le_mul_of_nonneg_right hs
    (mul_nonneg (pow_nonneg hR n) (mul_nonneg hR (sq_nonneg (n.factorial : ℝ))))
  nlinarith

theorem reciprocal_gevrey (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hnz : ∀ x, f x ≠ 0) (A Rc R : ℝ) (hA : 1 ≤ A) (hRc : 0 ≤ Rc)
    (hR : 2 * A * (Rc + 1) ≤ R)
    (hb : ∀ x, |(f x)⁻¹| ≤ A)
    (hc : ∀ n x, |iteratedDeriv (n + 1) f x| ≤ majorant Rc 0 (n + 1))
    (n : ℕ) (x : ℝ) :
    |iteratedDeriv n (fun y => (f y)⁻¹) x| ≤ R * majorant (4 * R) 0 n := by
  have hR0 : 0 ≤ R := by nlinarith
  exact (reciprocal_gevrey_shift f hf hnz A Rc R hA hRc hR hb hc n x).trans
    (shift_one_bound R hR0 n)

end EulerGevreyInverse
