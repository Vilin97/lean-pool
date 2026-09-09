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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.VectorCylinder

@[expose] public section

noncomputable section

/-! A genuine coordinate transport commutator on R³ × T without derivative loss. -/

namespace EulerCylinderTransport

open MeasureTheory EulerSobolev EulerCylinderSobolev EulerCylinderAlgebra EulerCylinderCoordinates
open EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
open scoped ENNReal NNReal ContDiff Topology

variable (period : ℝ)

/-- Repeated differentiation in one of the four actual cylinder coordinate directions. -/
noncomputable def pureFieldDerivative (n : ℕ) (i : Fin 4) (f : LiftDomain period → ℂ) :=
  iteratedFieldDerivative period (fun _ : Fin n => i) f

@[simp] theorem pureFieldDerivative_zero (i : Fin 4) (f : LiftDomain period → ℂ) :
    pureFieldDerivative period 0 i f = f := rfl

@[simp] theorem pureFieldDerivative_succ (n : ℕ) (i : Fin 4) (f : LiftDomain period → ℂ) :
    pureFieldDerivative period (n+1) i f =
      fieldDerivative period (standardDirection i) (pureFieldDerivative period n i f) := rfl

theorem pureFieldDerivative_succ_right (n : ℕ) (i : Fin 4) (f : LiftDomain period → ℂ) :
    pureFieldDerivative period (n+1) i f =
      pureFieldDerivative period n i (pureFieldDerivative period 1 i f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pureFieldDerivative_succ, ih, pureFieldDerivative_succ]
    rfl

theorem pureFieldDerivative_eq_iteratedDeriv (n : ℕ) (i : Fin 4) (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    pureFieldDerivative period n i f x = iteratedDeriv n
      (fun t : ℝ => euclideanLift period f x (t • EuclideanSpace.single i 1)) 0 := by
  have hA := euclideanLift_iteratedFieldDerivative period (fun _ : Fin n => i) f hf x 0
  rw [euclideanLift_zero] at hA
  rw [pureFieldDerivative, hA, iteratedDeriv_eq_iteratedFDeriv]
  let L : ℝ →L[ℝ] Domain 4 := (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single i 1)
  have hB := L.iteratedFDeriv_comp_right (euclideanLift_smooth period f hf x)
    (0 : ℝ) (by simp : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  change _ = iteratedFDeriv ℝ n (euclideanLift period f x ∘ L) 0 (fun _ => 1)
  rw [hB]
  simp [L, ContinuousMultilinearMap.compContinuousLinearMap_apply]

theorem pureFieldDerivative_product (n : ℕ) (i : Fin 4) (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    pureFieldDerivative period n i (f*g) =
      ∑ j ∈ Finset.range (n+1), (n.choose j : ℂ) •
        (pureFieldDerivative period j i f * pureFieldDerivative period (n-j) i g) := by
  funext x
  rw [pureFieldDerivative_eq_iteratedDeriv period n i (f*g) (product_smooth period f g hf hg)]
  have hline : ContDiff ℝ ∞ (fun t : ℝ => t • (EuclideanSpace.single i 1 : Domain 4)) :=
    contDiff_id.smul contDiff_const
  have hF := ((euclideanLift_smooth period f hf x).comp hline).of_le
    (by simp : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  have hG := ((euclideanLift_smooth period g hg x).comp hline).of_le
    (by simp : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  have h := iteratedDeriv_mul (x := (0 : ℝ)) hF.contDiffAt hG.contDiffAt
  have he : (fun t : ℝ => euclideanLift period (f*g) x (t • EuclideanSpace.single i 1)) =
      (euclideanLift period f x ∘ (fun t : ℝ => t • EuclideanSpace.single i 1)) *
      (euclideanLift period g x ∘ (fun t : ℝ => t • EuclideanSpace.single i 1)) := rfl
  rw [he]
  simpa only [Function.comp_def, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply,
    pureFieldDerivative_eq_iteratedDeriv period _ i f hf,
    pureFieldDerivative_eq_iteratedDeriv period _ i g hg, mul_assoc] using h


/-- The actual commutator of pure coordinate differentiation with multiplication. -/
noncomputable def coordinateCommutator (n : ℕ) (i : Fin 4) (b h : LiftDomain period → ℂ) :=
  pureFieldDerivative period n i (b*h) - b * pureFieldDerivative period n i h

theorem coordinateCommutator_expansion (n : ℕ) (i : Fin 4) (b h : LiftDomain period → ℂ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x)) :
    coordinateCommutator period n i b h = ∑ j ∈ Finset.range n, (n.choose (j+1) : ℂ) •
      (pureFieldDerivative period j i (pureFieldDerivative period 1 i b) *
        pureFieldDerivative period (n-(j+1)) i h) := by
  unfold coordinateCommutator
  rw [pureFieldDerivative_product period n i b h hb hh, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, pureFieldDerivative_zero, Nat.sub_zero,
    one_smul, add_sub_cancel_right]
  apply Finset.sum_congr rfl
  intro j _
  rw [pureFieldDerivative_succ_right]

variable [Fact (0 < period)]

theorem word_H3_le_H5 {m : ℕ} (hm : m ≤ 2) (w : Fin m → Fin 4)
    (f : LiftDomain period → ℂ) :
    liftSobolevNorm period 3 (iteratedFieldDerivative period w f) ≤
      85 * liftSobolevNorm period 5 f := by
  have hA : liftSobolevNorm period 3 (iteratedFieldDerivative period w f) ≤
      ∑ n ∈ Finset.range 4, ∑ _v : Fin n → Fin 4, liftSobolevNorm period 5 f := by
    apply Finset.sum_le_sum
    intro n hn
    apply Finset.sum_le_sum
    intro v _
    obtain ⟨u, hu⟩ := iteratedFieldDerivative_comp_exists period v w f
    rw [hu]
    exact word_L2_le_liftSobolevNorm period (by have := Finset.mem_range.1 hn; omega) u f
  have he (A : ℝ) : (∑ n ∈ Finset.range 4, ∑ _v : Fin n → Fin 4, A) = 85*A := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
    norm_num [Finset.sum_range_succ]
    ring
  exact hA.trans_eq (he _)

theorem pureFieldDerivative_le_H5 {m : ℕ} (hm : m ≤ 2) (i : Fin 4)
    (f : LiftDomain period → ℂ) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ 5, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖pureFieldDerivative period m i f x‖ ≤
      (85 * cylinderEmbeddingConstant period) * liftSobolevNorm period 5 f := by
  have hA := cylinder_pointwise_le_H3 period (pureFieldDerivative period m i f)
    (iteratedFieldDerivative_smooth period _ f hf)
    (fun j hj v => word_memLp period (by omega : m+j ≤ 5) v (fun _ => i) f hfL2) x
  have hB := mul_le_mul_of_nonneg_left (word_H3_le_H5 period hm (fun _ => i) f)
    (cylinderEmbeddingConstant_nonneg period)
  have he (C A : ℝ) : C*(85*A) = (85*C)*A := by ring
  exact hA.trans (hB.trans_eq (he _ _))

/-- An L² envelope depending only on five derivatives of each argument. -/
noncomputable def commutatorEnvelope (f g : LiftDomain period → ℂ) : LiftDomain period → ℝ :=
  liftSobolevNorm period 5 f • totalMagnitude period 5 g +
    liftSobolevNorm period 5 g • totalMagnitude period 5 f

theorem commutatorEnvelope_nonneg (f g : LiftDomain period → ℂ) (x : LiftDomain period) :
    0 ≤ commutatorEnvelope period f g x :=
  add_nonneg (mul_nonneg (liftSobolevNorm_nonneg period 5 f) (totalMagnitude_nonneg period 5 g x))
    (mul_nonneg (liftSobolevNorm_nonneg period 5 g) (totalMagnitude_nonneg period 5 f x))

omit [Fact (0 < period)] in
theorem pureFieldDerivative_le_total {n : ℕ} (hn : n ≤ 5) (i : Fin 4)
    (f : LiftDomain period → ℂ) (x : LiftDomain period) :
    ‖pureFieldDerivative period n i f x‖ ≤ totalMagnitude period 5 f x := by
  have hA : ‖pureFieldDerivative period n i f x‖ ≤ wordMagnitude period n f x :=
    Finset.single_le_sum (f := fun w : Fin n → Fin 4 => ‖iteratedFieldDerivative period w f x‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ (fun _ => i))
  exact hA.trans (wordMagnitude_le_total period 5 n hn f x)

theorem pure_product_le_envelope {j k : ℕ} (hjk : j+k ≤ 5) (i : Fin 4)
    (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ n ≤ 5, ∀ w : Fin n → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure
      period))
    (hgL2 : ∀ n ≤ 5, ∀ w : Fin n → Fin 4, MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure
      period))
    (x : LiftDomain period) :
    ‖pureFieldDerivative period j i f x * pureFieldDerivative period k i g x‖ ≤
      (85 * cylinderEmbeddingConstant period) * commutatorEnvelope period f g x := by
  rw [norm_mul]
  have hc : 0 ≤ 85 * cylinderEmbeddingConstant period :=
    mul_nonneg (by norm_num) (cylinderEmbeddingConstant_nonneg period)
  by_cases hj : j ≤ 2
  · have hA := mul_le_mul (pureFieldDerivative_le_H5 period hj i f hf hfL2 x)
      (pureFieldDerivative_le_total period (by omega : k ≤ 5) i g x) (norm_nonneg _)
      (mul_nonneg hc (liftSobolevNorm_nonneg period 5 f))
    have hB : liftSobolevNorm period 5 f * totalMagnitude period 5 g x ≤ commutatorEnvelope period
      f g x :=
      le_add_of_nonneg_right (mul_nonneg (liftSobolevNorm_nonneg period 5 g) (totalMagnitude_nonneg
        period 5 f x))
    rw [mul_assoc] at hA
    exact hA.trans (mul_le_mul_of_nonneg_left hB hc)
  · have hA := mul_le_mul (pureFieldDerivative_le_total period (by omega : j ≤ 5) i f x)
      (pureFieldDerivative_le_H5 period (by omega : k ≤ 2) i g hg hgL2 x) (norm_nonneg _)
      (totalMagnitude_nonneg period 5 f x)
    have hB : liftSobolevNorm period 5 g * totalMagnitude period 5 f x ≤ commutatorEnvelope period
      f g x :=
      le_add_of_nonneg_left (mul_nonneg (liftSobolevNorm_nonneg period 5 f) (totalMagnitude_nonneg
        period 5 g x))
    have he (A B C : ℝ) : A*(B*C)=B*(C*A) := by ring
    exact hA.trans ((he _ _ _).trans_le (mul_le_mul_of_nonneg_left hB hc))

theorem coordinateCommutator_pointwise_le {n : ℕ} (hn : n ≤ 6) (i : Fin 4)
    (b h : LiftDomain period → ℂ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x))
    (hbL2 : ∀ k ≤ 5, ∀ w : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period w (pureFieldDerivative period 1 i b)) 2 (liftMeasure
        period))
    (hhL2 : ∀ k ≤ 5, ∀ w : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period w h) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖coordinateCommutator period n i b h x‖ ≤
      (64 * (85 * cylinderEmbeddingConstant period)) *
        commutatorEnvelope period (pureFieldDerivative period 1 i b) h x := by
  rw [coordinateCommutator_expansion period n i b h hb hh]
  have hA := norm_sum_le (Finset.range n) (fun j => (n.choose (j+1) : ℂ) •
    (pureFieldDerivative period j i (pureFieldDerivative period 1 i b) x *
      pureFieldDerivative period (n-(j+1)) i h x))
  simp only [norm_smul, Complex.norm_natCast] at hA
  have hB : (∑ j ∈ Finset.range n, (n.choose (j+1) : ℝ) *
      ‖pureFieldDerivative period j i (pureFieldDerivative period 1 i b) x *
        pureFieldDerivative period (n-(j+1)) i h x‖) ≤
      (∑ j ∈ Finset.range n, (n.choose (j+1) : ℝ)) *
        ((85 * cylinderEmbeddingConstant period) *
          commutatorEnvelope period (pureFieldDerivative period 1 i b) h x) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (pure_product_le_envelope period
      (by have := Finset.mem_range.1 hj; omega : j+(n-(j+1)) ≤ 5) i
      (pureFieldDerivative period 1 i b) h (iteratedFieldDerivative_smooth period _ b hb)
      hh hbL2 hhL2 x) (Nat.cast_nonneg _)
  have hchoose := EulerSobolevTransport.sum_choose_successors_le n
  have hp : (2 : ℝ)^n ≤ 64 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
    norm_num at h ⊢
    exact h
  have hc : 0 ≤ (85 * cylinderEmbeddingConstant period) *
      commutatorEnvelope period (pureFieldDerivative period 1 i b) h x :=
    mul_nonneg (mul_nonneg (by norm_num) (cylinderEmbeddingConstant_nonneg period))
      (commutatorEnvelope_nonneg period _ _ x)
  have hC := mul_le_mul_of_nonneg_right (hchoose.trans hp) hc
  simpa only [Finset.sum_apply, Pi.smul_apply, Pi.mul_apply] using
    hA.trans (hB.trans (hC.trans_eq (mul_assoc _ _ _).symm))

theorem commutatorEnvelope_memLp (f g : LiftDomain period → ℂ)
    (hfL2 : ∀ k ≤ 5, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (hgL2 : ∀ k ≤ 5, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure period)) :
    MemLp (commutatorEnvelope period f g) 2 (liftMeasure period) :=
  ((totalMagnitude_memLp period 5 g hgL2).const_smul (liftSobolevNorm period 5 f)).add
    ((totalMagnitude_memLp period 5 f hfL2).const_smul (liftSobolevNorm period 5 g))

theorem commutatorEnvelope_L2_le (f g : LiftDomain period → ℂ)
    (hfL2 : ∀ k ≤ 5, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (hgL2 : ∀ k ≤ 5, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure period)) :
    ‖(commutatorEnvelope_memLp period f g hfL2 hgL2).toLp (commutatorEnvelope period f g)‖ ≤
      2 * liftSobolevNorm period 5 f * liftSobolevNorm period 5 g := by
  change ‖liftSobolevNorm period 5 f • (totalMagnitude_memLp period 5 g hgL2).toLp _ +
    liftSobolevNorm period 5 g • (totalMagnitude_memLp period 5 f hfL2).toLp _‖ ≤ _
  have hA := norm_add_le
    (liftSobolevNorm period 5 f • (totalMagnitude_memLp period 5 g hgL2).toLp (totalMagnitude
      period 5 g))
    (liftSobolevNorm period 5 g • (totalMagnitude_memLp period 5 f hfL2).toLp (totalMagnitude
      period 5 f))
  simp only [norm_smul, Real.norm_of_nonneg (liftSobolevNorm_nonneg period 5 f),
    Real.norm_of_nonneg (liftSobolevNorm_nonneg period 5 g)] at hA
  have hB := add_le_add
    (mul_le_mul_of_nonneg_left (totalMagnitude_L2_le period 5 g hgL2) (liftSobolevNorm_nonneg
      period 5 f))
    (mul_le_mul_of_nonneg_left (totalMagnitude_L2_le period 5 f hfL2) (liftSobolevNorm_nonneg
      period 5 g))
  have he (A B : ℝ) : A*B+B*A = 2*A*B := by ring
  exact hA.trans (hB.trans_eq (he _ _))

omit [Fact (0 < period)] in
theorem coordinateCommutator_smooth (n : ℕ) (i : Fin 4) (b h : LiftDomain period → ℂ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x)) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (coordinateCommutator period n i b h) x) := by
  intro x
  exact (iteratedFieldDerivative_smooth period _ (b*h) (product_smooth period b h hb hh) x).sub
    ((hb x).mul (iteratedFieldDerivative_smooth period _ h hh x))

/-- The commutator is in L²; neither factor needs compact support or decay assumptions beyond H⁵. -/
theorem coordinateCommutator_memLp {n : ℕ} (hn : n ≤ 6) (i : Fin 4)
    (b h : LiftDomain period → ℂ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x))
    (hbL2 : ∀ k ≤ 5, ∀ w : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period w (pureFieldDerivative period 1 i b)) 2 (liftMeasure
        period))
    (hhL2 : ∀ k ≤ 5, ∀ w : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period w h) 2 (liftMeasure period)) :
    MemLp (coordinateCommutator period n i b h) 2 (liftMeasure period) := by
  apply (commutatorEnvelope_memLp period (pureFieldDerivative period 1 i b) h hbL2 hhL2).of_le_mul
    ((smoothField_continuous period _ (coordinateCommutator_smooth period n i b h hb
      hh)).aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (commutatorEnvelope_nonneg period _ _ x)]
  exact coordinateCommutator_pointwise_le period hn i b h hb hh hbL2 hhL2 x

/-- No derivative is lost: `[D_i^n,b]h` is controlled by H⁵ of `D_i b` and H⁵ of `h`. -/
theorem cylinder_transport_commutator_L2 {n : ℕ} (hn : n ≤ 6) (i : Fin 4)
    (b h : LiftDomain period → ℂ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x))
    (hbL2 : ∀ k ≤ 5, ∀ w : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period w (pureFieldDerivative period 1 i b)) 2 (liftMeasure
        period))
    (hhL2 : ∀ k ≤ 5, ∀ w : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period w h) 2 (liftMeasure period)) :
    (eLpNorm (coordinateCommutator period n i b h) 2 (liftMeasure period)).toReal ≤
      (128 * 85 * cylinderEmbeddingConstant period) *
        liftSobolevNorm period 5 (pureFieldDerivative period 1 i b) * liftSobolevNorm period 5 h :=
          by
  have hq := commutatorEnvelope_memLp period (pureFieldDerivative period 1 i b) h hbL2 hhL2
  have hA := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := liftMeasure period)
    (Filter.Eventually.of_forall (fun x => show ‖coordinateCommutator period n i b h x‖ ≤
      (64 * (85 * cylinderEmbeddingConstant period)) *
        ‖commutatorEnvelope period (pureFieldDerivative period 1 i b) h x‖ by
        rw [Real.norm_of_nonneg (commutatorEnvelope_nonneg period _ _ x)]
        exact coordinateCommutator_pointwise_le period hn i b h hb hh hbL2 hhL2 x)) (2 : ℝ≥0∞)
  have hc : 0 ≤ 64 * (85 * cylinderEmbeddingConstant period) :=
    mul_nonneg (by norm_num) (mul_nonneg (by norm_num) (cylinderEmbeddingConstant_nonneg period))
  have hfin : ENNReal.ofReal (64 * (85 * cylinderEmbeddingConstant period)) *
      eLpNorm (commutatorEnvelope period (pureFieldDerivative period 1 i b) h) 2 (liftMeasure
        period) ≠ ⊤ := by
    finiteness
  have hB := ENNReal.toReal_mono hfin hA
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at hB
  have hC := mul_le_mul_of_nonneg_left
    (commutatorEnvelope_L2_le period (pureFieldDerivative period 1 i b) h hbL2 hhL2) hc
  rw [Lp.norm_toLp] at hC
  have he (C A B : ℝ) : (64*(85*C))*(2*A*B) = (128*85*C)*A*B := by ring
  exact hB.trans (hC.trans_eq (he _ _ _))

end EulerCylinderTransport
