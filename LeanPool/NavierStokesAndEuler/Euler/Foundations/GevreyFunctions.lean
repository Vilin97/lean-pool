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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.GevreyCutoff

@[expose] public section

noncomputable section

namespace EulerGevreyFunctions

open EulerGevreyCutoff EulerGevrey
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem product_bound (f g : E → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (R A B : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb₁ : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ A * majorant R 0 n)
    (hb₂ : ∀ n x, ‖iteratedFDeriv ℝ n g x‖ ≤ B * majorant R 0 n)
    (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤ (3 * A * B) * majorant R 0 n := by
  have hp := sequence_product_majorant R A B hR hA hB 0 0
    (fun k => ‖iteratedFDeriv ℝ k f x‖) (fun k => ‖iteratedFDeriv ℝ k g x‖)
    (fun k => by simpa only [abs_norm] using hb₁ k x)
    (fun k => by simpa only [abs_norm] using hb₂ k x) n
  exact (norm_iteratedFDeriv_mul_le hf hg x (by simp)).trans
    ((le_abs_self _).trans (by simpa using hp))

theorem linear_composition_bound (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] ℝ) (R A C : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hL : ‖L‖ ≤ C) (hb : ∀ n x, |iteratedDeriv n f x| ≤ A * majorant R 0 n)
    (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ A * majorant (R * C) 0 n := by
  rw [L.iteratedFDeriv_comp_right hf x (by simp)]
  have hnorm := (iteratedFDeriv ℝ n f (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hnorm
  calc
    _ ≤ |iteratedDeriv n f (L x)| * ‖L‖ ^ n := hnorm
    _ ≤ (A * majorant R 0 n) * C ^ n :=
      mul_le_mul (hb n (L x)) (pow_le_pow_left₀ (norm_nonneg _) hL n)
        (pow_nonneg (norm_nonneg _) n) (mul_nonneg hA (majorant_nonneg R hR 0 n))
    _ = A * majorant (R * C) 0 n := by simp [majorant, mul_pow]; ring

theorem affine_composition_bound (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] ℝ) (a R A C : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hL : ‖L‖ ≤ C) (hb : ∀ n x, |iteratedDeriv n f x| ≤ A * majorant R 0 n)
    (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => f (L y + a)) x‖ ≤ A * majorant (R * C) 0 n := by
  exact linear_composition_bound (fun t => f (t + a))
    (hf.comp (contDiff_id.add contDiff_const)) L R A C hR hA hC hL
    (fun k y => by simpa only [iteratedDeriv_comp_add_const] using hb k (y + a)) n x

theorem finite_product_bound {ι : Type*} [DecidableEq ι] (u : Finset ι)
    (f : ι → E → ℝ) (hf : ∀ i ∈ u, ContDiff ℝ ∞ (f i))
    (R A : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hb : ∀ i ∈ u, ∀ n x, ‖iteratedFDeriv ℝ n (f i) x‖ ≤ A * majorant R 0 n)
    (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => ∏ i ∈ u, f i y) x‖ ≤
      (3 * A) ^ u.card * majorant R 0 n := by
  induction u using Finset.induction_on generalizing n x with
  | empty =>
    cases n with
    | zero => simp [majorant]
    | succ n => simp [iteratedFDeriv_succ_const, majorant_nonneg R hR]
  | @insert i u hi ih =>
    have hfu : ∀ j ∈ u, ContDiff ℝ ∞ (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hbu : ∀ j ∈ u, ∀ n x, ‖iteratedFDeriv ℝ n (f j) x‖ ≤ A * majorant R 0 n :=
      fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have he : (fun y => ∏ j ∈ insert i u, f j y) =
        fun y => f i y * ∏ j ∈ u, f j y := by
      funext y
      rw [Finset.prod_insert hi]
    rw [he, Finset.card_insert_of_notMem hi]
    have hp := product_bound (f i) (fun y => ∏ j ∈ u, f j y)
      (hf i (Finset.mem_insert_self _ _)) (contDiff_prod hfu)
      R A ((3 * A) ^ u.card) hR hA (by positivity)
      (hb i (Finset.mem_insert_self _ _)) (fun k y => ih hfu hbu k y) n x
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hp

end EulerGevreyFunctions
