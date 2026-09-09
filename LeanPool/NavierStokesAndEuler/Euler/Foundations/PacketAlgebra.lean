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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.WeightedPressure

@[expose] public section

noncomputable section

/-!
Partial verification of algebra in the sample's proposed Euler packet construction.
This file does not prove existence of an Euler packet or finite-time Euler blowup.
The equations assumed below are the finite-dimensional ODEs in the source, not
assumptions that assert the unproved PDE construction.
-/

namespace EulerPacketAlgebra

open Matrix

/-- The ray-amplitude pairing is conserved on the whole interval of the ODE. -/
theorem pairing_conserved {n : Type*} [Fintype n]
    (M : ℝ → Matrix n n ℝ) (m v : ℝ → n → ℝ) (a b : ℝ)
    (hm : ∀ t ∈ Set.Icc a b, m t ⬝ᵥ m t ≠ 0)
    (hmd : ∀ t ∈ Set.Icc a b, ∀ i, HasDerivAt (fun s => m s i)
      ((-(M t).transpose *ᵥ m t) i) t)
    (hvd : ∀ t ∈ Set.Icc a b, ∀ i, HasDerivAt (fun s => v s i)
      ((-(M t *ᵥ v t) + (2 * (m t ⬝ᵥ (M t *ᵥ v t)) /
        (m t ⬝ᵥ m t)) • m t) i) t) :
    ∀ t ∈ Set.Icc a b, m t ⬝ᵥ v t = m a ⬝ᵥ v a := by
  have hp : ∀ t ∈ Set.Icc a b, HasDerivAt (fun s => m s ⬝ᵥ v s) 0 t := by
    intro t ht
    apply (HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => (hmd t ht i).mul (hvd t ht i))).congr_deriv
    rw [Finset.sum_add_distrib]
    change ((-(M t).transpose *ᵥ m t) ⬝ᵥ v t) +
      m t ⬝ᵥ (-(M t *ᵥ v t) + (2 * (m t ⬝ᵥ (M t *ᵥ v t)) /
        (m t ⬝ᵥ m t)) • m t) = 0
    rw [neg_mulVec, neg_dotProduct, dotProduct_add, dotProduct_neg, dotProduct_smul]
    rw [dotProduct_comm ((M t).transpose *ᵥ m t) (v t), dotProduct_transpose_mulVec]
    simp only [smul_eq_mul]
    field_simp [hm t ht]
    ring
  exact constant_of_has_deriv_right_zero
    (fun t ht => (hp t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hp t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)

/-- Equation (30), derived from the ideal two-component ODE with its actual coefficients. -/
theorem scalar_equation (β : ℝ) (U V : ℝ → ℝ)
    (hU : ∀ t, HasDerivAt U
      (-2 * V t + 2 * (β * t ^ 2) *
        (((β * t ^ 2) + β) * V t + (-2 * β * t) * U t) /
          (1 + (β * t ^ 2) ^ 2)) t)
    (hV : ∀ t, HasDerivAt V (-U t) t) (t : ℝ) :
    HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * deriv V s)
      (2 * (1 - β * (β * t ^ 2)) * V t) t := by
  have hv : deriv V = fun s => -U s := funext fun s => (hV s).deriv
  rw [hv]
  have hD : HasDerivAt (fun s : ℝ => 1 + (β * s ^ 2) ^ 2)
      (4 * β ^ 2 * t ^ 3) t := by
    apply (((((hasDerivAt_id t).fun_pow 2).const_mul β).fun_pow 2).const_add 1).congr_deriv
    dsimp
    ring
  have hd : 1 + (β * t ^ 2) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  apply (hD.mul (hU t).neg).congr_deriv
  simp only [Pi.neg_apply]
  field_simp
  ring

/-- The inversion symmetry used after (30), including the derivative of the transformed solution. -/
theorem inversion_equation (β : ℝ) (V V₁ : ℝ → ℝ)
    (hV : ∀ x, x ≠ 0 → HasDerivAt V (V₁ x) x)
    (hV₁ : ∀ x, x ≠ 0 → HasDerivAt V₁
      (((2 / β - 2 * x ^ 2) * V x - 4 * x ^ 3 * V₁ x) / (1 + x ^ 4)) x)
    (y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun z => V z⁻¹ / z)
      (-V y⁻¹ / y ^ 2 - V₁ y⁻¹ / y ^ 3) y ∧
    HasDerivAt (fun z => (1 + z ^ 4) * (-V z⁻¹ / z ^ 2 - V₁ z⁻¹ / z ^ 3))
      ((2 / β - 2 * y ^ 2) * (V y⁻¹ / y)) y := by
  have hi := hasDerivAt_inv hy
  have h0 := (hV y⁻¹ (inv_ne_zero hy)).comp y hi
  have h1 := (hV₁ y⁻¹ (inv_ne_zero hy)).comp y hi
  have h2 := (hasDerivAt_id y).fun_pow 2
  have h3 := (hasDerivAt_id y).fun_pow 3
  have h4 := ((hasDerivAt_id y).fun_pow 4).const_add 1
  constructor
  · apply (h0.div (hasDerivAt_id y) hy).congr_deriv
    dsimp
    field_simp
    ring
  · apply (h4.mul ((h0.neg.div h2 (pow_ne_zero 2 hy)).sub
      (h1.div h3 (pow_ne_zero 3 hy)))).congr_deriv
    have hd : 1 + (y⁻¹) ^ 4 ≠ 0 := ne_of_gt (by positivity)
    dsimp
    field_simp
    ring

end EulerPacketAlgebra
