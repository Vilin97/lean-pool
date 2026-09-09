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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SobolevProducts

@[expose] public section

noncomputable section

/-! The Fourier H³ norm is controlled by genuine third directional derivatives in L². -/

namespace EulerSobolevDerivativeNorm

open MeasureTheory FourierTransform EulerSobolev EulerSobolevProducts
open scoped SchwartzMap ENNReal ContDiff LineDeriv


theorem norm_le_sum_coordinates (d : ℕ) (ξ : Domain d) : ‖ξ‖ ≤ ∑ i, ‖ξ i‖ := by
  have he : (∑ i : Fin d, EuclideanSpace.single i (ξ i)) = ξ := by
    ext j
    simp
  calc
    ‖ξ‖ = ‖∑ i : Fin d, EuclideanSpace.single i (ξ i)‖ := by rw [he]
    _ ≤ ∑ i : Fin d, ‖EuclideanSpace.single i (ξ i)‖ := norm_sum_le _ _
    _ = _ := by simp

/-- The operator norm of a derivative tensor is bounded by the sum of its coordinate entries. -/
theorem multilinear_norm_le_coordinate_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (d n : ℕ) (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Domain d) F) :
    ‖T‖ ≤ ∑ w : Fin n → Fin d,
      ‖T (fun j => EuclideanSpace.single (w j) 1)‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro m
  have hm (j : Fin n) : (∑ i : Fin d, (m j i) • EuclideanSpace.single i (1 : ℝ)) = m j := by
    ext i
    simp [Pi.single_apply, mul_ite]
  have hexpand : T m = ∑ w : Fin n → Fin d,
      T (fun j => (m j (w j)) • EuclideanSpace.single (w j) (1 : ℝ)) := by
    change T.toMultilinearMap m = ∑ w : Fin n → Fin d,
      T.toMultilinearMap (fun j => (m j (w j)) • EuclideanSpace.single (w j) (1 : ℝ))
    have h := T.toMultilinearMap.map_sum
      (fun (j : Fin n) (i : Fin d) => (m j i) • EuclideanSpace.single i (1 : ℝ))
    simpa only [hm] using h
  rw [hexpand]
  calc
    _ ≤ ∑ w : Fin n → Fin d,
        ‖T (fun j => (m j (w j)) • EuclideanSpace.single (w j) (1 : ℝ))‖ := norm_sum_le _ _
    _ = ∑ w : Fin n → Fin d, (∏ j, ‖m j (w j)‖) *
        ‖T (fun j => EuclideanSpace.single (w j) (1 : ℝ))‖ := by
      apply Finset.sum_congr rfl
      intro w _
      rw [T.map_smul_univ, norm_smul, norm_prod]
    _ ≤ ∑ w : Fin n → Fin d, (∏ j, ‖m j‖) *
        ‖T (fun j => EuclideanSpace.single (w j) (1 : ℝ))‖ := by
      apply Finset.sum_le_sum
      intro w _
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => PiLp.norm_apply_le (m j) (w
        j))
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem besselWeight_one_le_coordinate_sum (d : ℕ) (ξ : Domain d) :
    besselWeight d 1 ξ ≤ 1 + ∑ i, ‖ξ i‖ := by
  have h : besselWeight d 1 ξ ≤ 1 + ‖ξ‖ := by
    unfold besselWeight
    rw [← Real.sqrt_eq_rpow]
    apply (Real.sqrt_le_left (by positivity)).2
    nlinarith [norm_nonneg ξ]
  exact h.trans (by linarith [norm_le_sum_coordinates d ξ])

theorem besselWeight_three_le_pure_three (d : ℕ) (ξ : Domain d) :
    besselWeight d 3 ξ ≤ ((d : ℝ) + 1) ^ 2 * (1 + ∑ i, ‖ξ i‖ ^ 3) := by
  let a : Option (Fin d) → ℝ := fun i => match i with
    | none => 1
    | some i => ‖ξ i‖
  have ha : ∀ i ∈ (Finset.univ : Finset (Option (Fin d))), 0 ≤ a i := by
    intro i _
    cases i <;> simp only [a] <;> positivity
  have h := pow_sum_le_card_mul_sum_pow ha 2
  have he : besselWeight d 3 ξ = (besselWeight d 1 ξ) ^ 3 := by
    unfold besselWeight
    rw [← Real.rpow_mul_natCast (by positivity)]
    congr 1
    norm_num
  rw [he]
  apply (pow_le_pow_left₀ (besselWeight_pos d 1 ξ).le
    (besselWeight_one_le_coordinate_sum d ξ) 3).trans
  simpa [a, Fintype.sum_option] using h

theorem sobolevNorm_three_le_pure_derivatives (d : ℕ) (f : 𝓢(Domain d, ℂ)) :
    sobolevNorm d 3 f ≤ ((d : ℝ) + 1) ^ 2 *
      (‖f.toLp 2‖ + (2 * Real.pi) ^ (-3 : ℤ) *
        ∑ i : Fin d, ‖(directional d 3 (EuclideanSpace.single i 1) f).toLp 2‖) := by
  let g : Option (Fin d) → 𝓢(Domain d, ℂ) := fun i => match i with
    | none => 𝓕 f
    | some i => ((2 * Real.pi) ^ (-3 : ℤ) : ℝ) •
        𝓕 (directional d 3 (EuclideanSpace.single i 1) f)
  have hpoint (ξ : Domain d) :
      ‖weightedFourier d 3 f ξ‖ ≤ ((d : ℝ) + 1) ^ 2 * ∑ i, ‖g i ξ‖ := by
    rw [weightedFourier_apply, norm_smul, Real.norm_of_nonneg (besselWeight_pos d 3 ξ).le]
    have hg : ∑ i, ‖g i ξ‖ = (1 + ∑ i, ‖ξ i‖ ^ 3) * ‖𝓕 f ξ‖ := by
      rw [Fintype.sum_option]
      simp only [g, smul_apply, norm_smul,
        Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi) ^ (-3 : ℤ)),
        fourier_directional_norm, EuclideanSpace.inner_single_right,
        starRingEnd_apply, star_trivial]
      have hp : (2 * Real.pi) ^ (-3 : ℤ) * (2 * Real.pi) ^ (3 : ℕ) = 1 := by
        rw [show (-3 : ℤ) = -(3 : ℤ) from rfl, zpow_neg]
        exact inv_mul_cancel₀ (by positivity)
      simp_rw [← mul_assoc, hp, one_mul]
      rw [add_mul, one_mul, Finset.sum_mul]
    rw [hg]
    nlinarith [mul_le_mul_of_nonneg_right (besselWeight_three_le_pure_three d ξ) (norm_nonneg (𝓕 f
      ξ))]
  have h := normLp_le_sum d (weightedFourier d 3 f) g (((d : ℝ) + 1) ^ 2)
    (sq_nonneg _) hpoint
  have hnorm : ∑ i, ‖(g i).toLp 2‖ = ‖f.toLp 2‖ +
      (2 * Real.pi) ^ (-3 : ℤ) * ∑ i : Fin d,
        ‖(directional d 3 (EuclideanSpace.single i 1) f).toLp 2‖ := by
    rw [Fintype.sum_option]
    simp only [g]
    change ‖(𝓕 f).toLp 2‖ + ∑ i,
      ‖SchwartzMap.toLpCLM ℝ ℂ 2 volume (((2 * Real.pi) ^ (-3 : ℤ)) •
        𝓕 (directional d 3 (EuclideanSpace.single i 1) f))‖ = _
    simp only [map_smul, norm_smul,
      Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi) ^ (-3 : ℤ)),
      SchwartzMap.toLpCLM_apply, SchwartzMap.norm_fourier_toL2_eq, Finset.mul_sum]
  rw [hnorm] at h
  exact h

/-- Four-dimensional Sobolev embedding stated solely with actual L² derivative norms. -/
theorem pointwise_le_L2_third_derivatives (f : 𝓢(Domain 4, ℂ)) (x : Domain 4) :
    ‖f x‖ ≤ embeddingConstant 4 3 (by norm_num) * 25 *
      (‖f.toLp 2‖ + (2 * Real.pi) ^ (-3 : ℤ) *
        ∑ i : Fin 4, ‖(directional 4 3 (EuclideanSpace.single i 1) f).toLp 2‖) := by
  have hA := norm_apply_le_sobolevNorm 4 3 (by norm_num) f x
  have hB := mul_le_mul_of_nonneg_left (sobolevNorm_three_le_pure_derivatives 4 f)
    (show 0 ≤ embeddingConstant 4 3 (by norm_num) from norm_nonneg _)
  refine hA.trans (hB.trans_eq ?_)
  norm_num
  ring

end EulerSobolevDerivativeNorm
