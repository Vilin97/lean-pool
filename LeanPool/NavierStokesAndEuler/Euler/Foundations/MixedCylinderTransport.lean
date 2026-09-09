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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.StrongSmoothJet

@[expose] public section

noncomputable section

/-! Mixed coordinate transport commutators on the genuine cylinder. -/

namespace EulerMixedCylinderTransport

open MeasureTheory EulerSobolev EulerCylinderSobolev EulerCylinderAlgebra EulerCylinderTransport
open EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
open scoped ENNReal NNReal ContDiff Topology

variable (period : ℝ)

/-- Ordered cylinder differentiation indexed by a list. -/
noncomputable def listDerivative : List (Fin 4) → (LiftDomain period → ℂ) → LiftDomain period → ℂ
  | [], f => f
  | i::l, f => fieldDerivative period (standardDirection i) (listDerivative l f)

/-- The same list as a finite derivative word. -/
def listWord : (l : List (Fin 4)) → Fin l.length → Fin 4
  | [], i => Fin.elim0 i
  | i::l, j => Fin.cases i (listWord l) j

@[simp] theorem listDerivative_nil (f : LiftDomain period → ℂ) : listDerivative period [] f = f :=
  rfl
@[simp] theorem listDerivative_cons (i : Fin 4) (l : List (Fin 4)) (f : LiftDomain period → ℂ) :
    listDerivative period (i::l) f = fieldDerivative period (standardDirection i) (listDerivative
      period l f) := rfl

theorem listDerivative_eq_word (l : List (Fin 4)) (f : LiftDomain period → ℂ) :
    listDerivative period l f = iteratedFieldDerivative period (listWord l) f := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [listDerivative_cons, ih]
    rfl

theorem listDerivative_smooth (l : List (Fin 4)) (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (listDerivative period l f) x) := by
  rw [listDerivative_eq_word]
  exact iteratedFieldDerivative_smooth period _ f hf

theorem listDerivative_append (l m : List (Fin 4)) (f : LiftDomain period → ℂ) :
    listDerivative period (l++m) f = listDerivative period l (listDerivative period m f) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.cons_append, listDerivative_cons, ih]

theorem fieldDerivative_add (a : LiftTangent) (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    fieldDerivative period a (f+g) = fieldDerivative period a f + fieldDerivative period a g := by
  funext x
  have h := (((hf x).differentiable (by simp)) 0).hasFDerivAt.add
    (((hg x).differentiable (by simp)) 0).hasFDerivAt
  exact congrArg (fun A : LiftTangent →L[ℝ] ℂ => A a) h.fderiv

theorem fieldDerivative_sub (a : LiftTangent) (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    fieldDerivative period a (f-g) = fieldDerivative period a f - fieldDerivative period a g := by
  funext x
  have h := (((hf x).differentiable (by simp)) 0).hasFDerivAt.sub
    (((hg x).differentiable (by simp)) 0).hasFDerivAt
  exact congrArg (fun A : LiftTangent →L[ℝ] ℂ => A a) h.fderiv

theorem fieldDerivative_mul (a : LiftTangent) (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    fieldDerivative period a (f*g) = fieldDerivative period a f * g + f * fieldDerivative period a
      g := by
  funext x
  have h := (((hf x).differentiable (by simp)) 0).hasFDerivAt.mul
    (((hg x).differentiable (by simp)) 0).hasFDerivAt
  have he := congrArg (fun A : LiftTangent →L[ℝ] ℂ => A a) h.fderiv
  have hfg : localFieldLift period (f*g) x = localFieldLift period f x * localFieldLift period g x
    := rfl
  change fderiv ℝ (localFieldLift period (f*g) x) 0 a = _
  rw [hfg]
  have hzf : localFieldLift period f x 0 = f x := by simp [localFieldLift]
  have hzg : localFieldLift period g x 0 = g x := by simp [localFieldLift]
  rw [hzf, hzg] at he
  simpa [fieldDerivative, add_comm, mul_comm] using he

theorem listDerivative_add (l : List (Fin 4)) (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    listDerivative period l (f+g) = listDerivative period l f + listDerivative period l g := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [listDerivative_cons, ih, fieldDerivative_add period _ _ _
      (listDerivative_smooth period l f hf) (listDerivative_smooth period l g hg)]
    rfl

theorem listDerivative_zero (l : List (Fin 4)) : listDerivative period l 0 = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [listDerivative_cons, ih]
    ext x
    change fderiv ℝ (fun _ : LiftTangent => (0 : ℂ)) 0 (standardDirection i) = 0
    simp

/-- The commutator of an arbitrary coordinate word and multiplication. -/
noncomputable def mixedCommutator (l : List (Fin 4)) (b h : LiftDomain period → ℂ) :=
  listDerivative period l (b*h) - b * listDerivative period l h

theorem mixedCommutator_smooth (l : List (Fin 4)) (b h : LiftDomain period → ℂ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x)) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (mixedCommutator period l b h) x) :=
  fun x => (listDerivative_smooth period l (b*h) (product_smooth period b h hb hh) x).sub
    ((hb x).mul (listDerivative_smooth period l h hh x))

/-- Exact telescoping step; the top derivative on the transported field cancels. -/
theorem mixedCommutator_cons (i : Fin 4) (l : List (Fin 4)) (b h : LiftDomain period → ℂ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x)) :
    mixedCommutator period (i::l) b h =
      fieldDerivative period (standardDirection i) b * listDerivative period l h +
      fieldDerivative period (standardDirection i) (mixedCommutator period l b h) := by
  unfold mixedCommutator
  rw [fieldDerivative_sub period _ _ _
    (listDerivative_smooth period l (b*h) (product_smooth period b h hb hh))
    (product_smooth period b _ hb (listDerivative_smooth period l h hh)),
    fieldDerivative_mul period _ _ _ hb (listDerivative_smooth period l h hh)]
  simp only [listDerivative_cons]
  ext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  ring

variable [Fact (0 < period)]

theorem word_pointwise_le_H5 {m : ℕ} (hm : m ≤ 2) (w : Fin m → Fin 4)
    (f : LiftDomain period → ℂ) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ 5, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure
      period))
    (x : LiftDomain period) :
    ‖iteratedFieldDerivative period w f x‖ ≤
      (85 * cylinderEmbeddingConstant period) * liftSobolevNorm period 5 f := by
  have hA := cylinder_pointwise_le_H3 period (iteratedFieldDerivative period w f)
    (iteratedFieldDerivative_smooth period w f hf)
    (fun j hj v => word_memLp period (by omega : m+j ≤ 5) v w f hfL2) x
  have hB := mul_le_mul_of_nonneg_left (word_H3_le_H5 period hm w f)
    (cylinderEmbeddingConstant_nonneg period)
  have he (C A : ℝ) : C*(85*A) = (85*C)*A := by ring
  exact hA.trans (hB.trans_eq (he _ _))

omit [Fact (0 < period)] in
theorem tensor_list_le_total {j : ℕ} (l : List (Fin 4)) (hjl : l.length+j ≤ 5)
    (f : LiftDomain period → ℂ) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x :
      LiftDomain period) :
    ‖iteratedFDeriv ℝ j (euclideanLift period (listDerivative period l f) x) 0‖ ≤
      1024 * totalMagnitude period 5 f x := by
  have hA := euclideanLift_tensor_norm_le period j (listDerivative period l f)
    (listDerivative_smooth period l f hf) x 0
  simp only [euclideanLift_zero] at hA
  have hB : (∑ w : Fin j → Fin 4, ‖iteratedFieldDerivative period w (listDerivative period l f) x‖)
    ≤
      (4 : ℝ)^j * totalMagnitude period 5 f x := by
    have hb (w : Fin j → Fin 4) : ‖iteratedFieldDerivative period w (listDerivative period l f) x‖ ≤
        totalMagnitude period 5 f x := by
      rw [listDerivative_eq_word]
      obtain ⟨u, hu⟩ := iteratedFieldDerivative_comp_exists period w (listWord l) f
      rw [hu]
      exact (Finset.single_le_sum (f := fun v : Fin (l.length+j) → Fin 4 =>
        ‖iteratedFieldDerivative period v f x‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ u)).trans
          (wordMagnitude_le_total period 5 (l.length+j) hjl f x)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] using Finset.sum_le_sum (fun w (_ : w ∈
        (Finset.univ : Finset (Fin j → Fin 4))) => hb w)
  have hp : (4 : ℝ)^j ≤ 1024 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (show j ≤ 5 by omega)
    norm_num at h ⊢
    exact h
  exact hA.trans (hB.trans (mul_le_mul_of_nonneg_right hp (totalMagnitude_nonneg period 5 f x)))

theorem tensor_list_low_le_H5 {j : ℕ} (l : List (Fin 4)) (hjl : l.length+j ≤ 2)
    (f : LiftDomain period → ℂ) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ k ≤ 5, ∀ v : Fin k → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure
      period))
    (x : LiftDomain period) :
    ‖iteratedFDeriv ℝ j (euclideanLift period (listDerivative period l f) x) 0‖ ≤
      1024 * ((85 * cylinderEmbeddingConstant period) * liftSobolevNorm period 5 f) := by
  have hA := euclideanLift_tensor_norm_le period j (listDerivative period l f)
    (listDerivative_smooth period l f hf) x 0
  simp only [euclideanLift_zero] at hA
  have hb (w : Fin j → Fin 4) : ‖iteratedFieldDerivative period w (listDerivative period l f) x‖ ≤
      (85 * cylinderEmbeddingConstant period) * liftSobolevNorm period 5 f := by
    rw [listDerivative_eq_word]
    obtain ⟨u, hu⟩ := iteratedFieldDerivative_comp_exists period w (listWord l) f
    rw [hu]
    exact word_pointwise_le_H5 period hjl u f hf hfL2 x
  have hB := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset (Fin j → Fin 4))) => hb w)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at hB
  have hp : (4 : ℝ)^j ≤ 1024 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (show j ≤ 5 by omega)
    norm_num at h ⊢
    exact h
  exact hA.trans (hB.trans (mul_le_mul_of_nonneg_right hp
    (mul_nonneg (mul_nonneg (by norm_num) (cylinderEmbeddingConstant_nonneg period))
      (liftSobolevNorm_nonneg period 5 f))))

/-- A fixed finite constant for differentiated products of total order at most five. -/
noncomputable def mixedProductConstant : ℝ :=
  32 * (1024 * 1024 * (85 * cylinderEmbeddingConstant period))

theorem mixedProductConstant_nonneg : 0 ≤ mixedProductConstant period := by
  unfold mixedProductConstant
  exact mul_nonneg (by norm_num) (mul_nonneg (by norm_num)
    (mul_nonneg (by norm_num) (cylinderEmbeddingConstant_nonneg period)))

theorem tensor_list_product_term_le (l m : List (Fin 4)) {j k : ℕ}
    (horder : (l.length+j)+(m.length+k) ≤ 5) (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ r ≤ 5, ∀ w : Fin r → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure
      period))
    (hgL2 : ∀ r ≤ 5, ∀ w : Fin r → Fin 4, MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure
      period))
    (x : LiftDomain period) :
    ‖iteratedFDeriv ℝ j (euclideanLift period (listDerivative period l f) x) 0‖ *
      ‖iteratedFDeriv ℝ k (euclideanLift period (listDerivative period m g) x) 0‖ ≤
        (1024 * 1024 * (85 * cylinderEmbeddingConstant period)) * commutatorEnvelope period f g x
          := by
  have hc : 0 ≤ 85 * cylinderEmbeddingConstant period :=
    mul_nonneg (by norm_num) (cylinderEmbeddingConstant_nonneg period)
  have hK : 0 ≤ 1024 * 1024 * (85 * cylinderEmbeddingConstant period) := mul_nonneg (by norm_num) hc
  by_cases hl : l.length+j ≤ 2
  · have hA := mul_le_mul (tensor_list_low_le_H5 period l hl f hf hfL2 x)
      (tensor_list_le_total period m (by omega : m.length+k ≤ 5) g hg x) (norm_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg hc (liftSobolevNorm_nonneg period 5 f)))
    have he (C A M : ℝ) : (1024*(C*A))*(1024*M) = (1024*1024*C)*(A*M) := by ring
    have hB : liftSobolevNorm period 5 f * totalMagnitude period 5 g x ≤ commutatorEnvelope period
      f g x :=
      le_add_of_nonneg_right (mul_nonneg (liftSobolevNorm_nonneg period 5 g) (totalMagnitude_nonneg
        period 5 f x))
    exact hA.trans ((he _ _ _).trans_le (mul_le_mul_of_nonneg_left hB hK))
  · have hA := mul_le_mul (tensor_list_le_total period l (by omega : l.length+j ≤ 5) f hf x)
      (tensor_list_low_le_H5 period m (by omega : m.length+k ≤ 2) g hg hgL2 x) (norm_nonneg _)
      (mul_nonneg (by norm_num) (totalMagnitude_nonneg period 5 f x))
    have he (C A M : ℝ) : (1024*M)*(1024*(C*A)) = (1024*1024*C)*(A*M) := by ring
    have hB : liftSobolevNorm period 5 g * totalMagnitude period 5 f x ≤ commutatorEnvelope period
      f g x :=
      le_add_of_nonneg_left (mul_nonneg (liftSobolevNorm_nonneg period 5 f) (totalMagnitude_nonneg
        period 5 g x))
    exact hA.trans ((he _ _ _).trans_le (mul_le_mul_of_nonneg_left hB hK))

/-- Every prefixed product occurring in the telescoping commutator has a uniform H⁵ envelope. -/
theorem list_product_pointwise_le (l m : List (Fin 4)) (horder : l.length+m.length ≤ 5)
    (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ r ≤ 5, ∀ w : Fin r → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure
      period))
    (hgL2 : ∀ r ≤ 5, ∀ w : Fin r → Fin 4, MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure
      period))
    (x : LiftDomain period) :
    ‖listDerivative period l (f * listDerivative period m g) x‖ ≤
      mixedProductConstant period * commutatorEnvelope period f g x := by
  have hmg := listDerivative_smooth period m g hg
  have hprod := product_smooth period f (listDerivative period m g) hf hmg
  have he := euclideanLift_iteratedFieldDerivative period (listWord l) (f * listDerivative period m
    g) hprod x 0
  rw [euclideanLift_zero] at he
  rw [listDerivative_eq_word, he]
  have hA := (iteratedFDeriv ℝ l.length (euclideanLift period (f * listDerivative period m g) x)
    0).le_opNorm
    (fun j => EuclideanSpace.single (listWord l j) (1 : ℝ))
  simp only [PiLp.norm_single, norm_one, Finset.prod_const_one, mul_one] at hA
  have hB := norm_iteratedFDeriv_mul_le (euclideanLift_smooth period f hf x)
    (euclideanLift_smooth period (listDerivative period m g) hmg x) 0
    (by simp : (l.length : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  have hC : (∑ j ∈ Finset.range (l.length+1), (l.length.choose j : ℝ) *
      ‖iteratedFDeriv ℝ j (euclideanLift period f x) 0‖ *
      ‖iteratedFDeriv ℝ (l.length-j) (euclideanLift period (listDerivative period m g) x) 0‖) ≤
      2^l.length * ((1024*1024*(85*cylinderEmbeddingConstant period)) * commutatorEnvelope period f
        g x) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (l.length+1), (l.length.choose j : ℝ) *
          ((1024*1024*(85*cylinderEmbeddingConstant period)) * commutatorEnvelope period f g x) :=
            by
        apply Finset.sum_le_sum
        intro j hj
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (tensor_list_product_term_le period [] m
          (by have := Finset.mem_range.1 hj; omega : (0+j)+(m.length+(l.length-j)) ≤ 5)
          f g hf hg hfL2 hgL2 x) (Nat.cast_nonneg _)
      _ = _ := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose l.length
  have hp : (2 : ℝ)^l.length ≤ 32 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show l.length ≤ 5 by omega)
    norm_num at h ⊢
    exact h
  have hD := mul_le_mul_of_nonneg_right hp (mul_nonneg
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1024*1024)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 85) (cylinderEmbeddingConstant_nonneg period)))
    (commutatorEnvelope_nonneg period f g x))
  exact hA.trans (hB.trans (hC.trans (hD.trans_eq (mul_assoc _ _ _).symm)))

/-- Sum of the H⁵ norms of all four actual first derivatives of the coefficient. -/
noncomputable def gradientSobolevNorm (b : LiftDomain period → ℂ) : ℝ :=
  ∑ i : Fin 4, liftSobolevNorm period 5 (fieldDerivative period (standardDirection i) b)

/-- Pointwise sum of all words of order at most five applied to the first coefficient derivatives. -/
noncomputable def gradientMagnitude (b : LiftDomain period → ℂ) (x : LiftDomain period) : ℝ :=
  ∑ i : Fin 4, totalMagnitude period 5 (fieldDerivative period (standardDirection i) b) x

theorem gradientSobolevNorm_nonneg (b : LiftDomain period → ℂ) : 0 ≤ gradientSobolevNorm period b :=
  Finset.sum_nonneg (fun _ _ => liftSobolevNorm_nonneg period 5 _)

omit [Fact (0 < period)] in
theorem gradientMagnitude_nonneg (b : LiftDomain period → ℂ) (x : LiftDomain period) :
    0 ≤ gradientMagnitude period b x := Finset.sum_nonneg (fun _ _ => totalMagnitude_nonneg period
      5 _ x)

/-- One square-integrable envelope controls every mixed transport commutator through order six. -/
noncomputable def mixedEnvelope (b h : LiftDomain period → ℂ) : LiftDomain period → ℝ :=
  gradientSobolevNorm period b • totalMagnitude period 5 h + liftSobolevNorm period 5 h •
    gradientMagnitude period b

theorem mixedEnvelope_nonneg (b h : LiftDomain period → ℂ) (x : LiftDomain period) :
    0 ≤ mixedEnvelope period b h x :=
  add_nonneg (mul_nonneg (gradientSobolevNorm_nonneg period b) (totalMagnitude_nonneg period 5 h x))
    (mul_nonneg (liftSobolevNorm_nonneg period 5 h) (gradientMagnitude_nonneg period b x))

theorem commutatorEnvelope_le_mixed (i : Fin 4) (b h : LiftDomain period → ℂ) (x : LiftDomain
  period) :
    commutatorEnvelope period (fieldDerivative period (standardDirection i) b) h x ≤ mixedEnvelope
      period b h x := by
  have hS : liftSobolevNorm period 5 (fieldDerivative period (standardDirection i) b) ≤
    gradientSobolevNorm period b :=
    Finset.single_le_sum (f := fun i : Fin 4 => liftSobolevNorm period 5 (fieldDerivative period
      (standardDirection i) b))
      (fun _ _ => liftSobolevNorm_nonneg period 5 _) (Finset.mem_univ i)
  have hM : totalMagnitude period 5 (fieldDerivative period (standardDirection i) b) x ≤
    gradientMagnitude period b x :=
    Finset.single_le_sum (f := fun i : Fin 4 => totalMagnitude period 5 (fieldDerivative period
      (standardDirection i) b) x)
      (fun _ _ => totalMagnitude_nonneg period 5 _ x) (Finset.mem_univ i)
  exact add_le_add (mul_le_mul_of_nonneg_right hS (totalMagnitude_nonneg period 5 h x))
    (mul_le_mul_of_nonneg_left hM (liftSobolevNorm_nonneg period 5 h))

/-- The telescoping estimate remains valid under an arbitrary derivative prefix. -/
theorem prefixed_commutator_pointwise_le (outer inner : List (Fin 4))
    (horder : outer.length+inner.length ≤ 6) (b h : LiftDomain period → ℂ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x))
    (hbL2 : ∀ i : Fin 4, ∀ r ≤ 5, ∀ w : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period w (fieldDerivative period (standardDirection i) b)) 2
        (liftMeasure period))
    (hhL2 : ∀ r ≤ 5, ∀ w : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period w h) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖listDerivative period outer (mixedCommutator period inner b h) x‖ ≤
      (inner.length : ℝ) * mixedProductConstant period * mixedEnvelope period b h x := by
  induction inner generalizing outer with
  | nil =>
    have he : mixedCommutator period [] b h = 0 := by simp [mixedCommutator]
    rw [he, listDerivative_zero]
    simp
  | cons i inner ih =>
    rw [mixedCommutator_cons period i inner b h hb hh,
      listDerivative_add period outer _ _
        (product_smooth period _ _ (fieldDerivative_smooth period _ b hb) (listDerivative_smooth
          period inner h hh))
        (fieldDerivative_smooth period _ _ (mixedCommutator_smooth period inner b h hb hh))]
    have hA := norm_add_le
      (listDerivative period outer (fieldDerivative period (standardDirection i) b * listDerivative
        period inner h) x)
      (listDerivative period outer (fieldDerivative period (standardDirection i) (mixedCommutator
        period inner b h)) x)
    have hfirst := list_product_pointwise_le period outer inner
      (by simp only [List.length_cons] at horder; omega)
      (fieldDerivative period (standardDirection i) b) h (fieldDerivative_smooth period _ b hb) hh
        (hbL2 i) hhL2 x
    have hfirst' := hfirst.trans (mul_le_mul_of_nonneg_left (commutatorEnvelope_le_mixed period i b
      h x)
      (mixedProductConstant_nonneg period))
    have hsecond := ih (outer ++ [i]) (by simp only [List.length_append, List.length_cons,
      List.length_nil] at *; omega)
    rw [listDerivative_append] at hsecond
    have hB := add_le_add hfirst' hsecond
    have he (n B Q : ℝ) : B*Q+n*B*Q=(n+1)*B*Q := by ring
    have hC := hA.trans (hB.trans_eq (he _ _ _))
    simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, Pi.add_apply] using hC

theorem gradientMagnitude_memLp (b : LiftDomain period → ℂ)
    (hbL2 : ∀ i : Fin 4, ∀ r ≤ 5, ∀ w : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period w (fieldDerivative period (standardDirection i) b)) 2
        (liftMeasure period)) :
    MemLp (gradientMagnitude period b) 2 (liftMeasure period) :=
  memLp_finsetSum _ (fun i _ => totalMagnitude_memLp period 5 _ (hbL2 i))

theorem gradientMagnitude_L2_le (b : LiftDomain period → ℂ)
    (hbL2 : ∀ i : Fin 4, ∀ r ≤ 5, ∀ w : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period w (fieldDerivative period (standardDirection i) b)) 2
        (liftMeasure period)) :
    ‖(gradientMagnitude_memLp period b hbL2).toLp (gradientMagnitude period b)‖ ≤
      gradientSobolevNorm period b := by
  have he : gradientMagnitude period b = ∑ i : Fin 4,
      totalMagnitude period 5 (fieldDerivative period (standardDirection i) b) := by
    funext x
    simp [gradientMagnitude]
  have hA : eLpNorm (gradientMagnitude period b) 2 (liftMeasure period) ≤
      ∑ i : Fin 4, eLpNorm (totalMagnitude period 5 (fieldDerivative period (standardDirection i)
        b)) 2 (liftMeasure period) := by
    rw [he]
    exact eLpNorm_sum_le (fun i _ => (totalMagnitude_memLp period 5 _ (hbL2 i)).1) (by norm_num)
  have hfin (i : Fin 4) (_hi : i ∈ (Finset.univ : Finset (Fin 4))) :
      eLpNorm (totalMagnitude period 5 (fieldDerivative period (standardDirection i) b)) 2
        (liftMeasure period) ≠ ⊤ :=
    (totalMagnitude_memLp period 5 _ (hbL2 i)).eLpNorm_ne_top
  have hB := ENNReal.toReal_mono (ENNReal.sum_ne_top.2 hfin) hA
  rw [ENNReal.toReal_sum hfin] at hB
  rw [Lp.norm_toLp]
  apply hB.trans
  apply Finset.sum_le_sum
  intro i _
  have h := totalMagnitude_L2_le period 5 (fieldDerivative period (standardDirection i) b) (hbL2 i)
  rw [Lp.norm_toLp] at h
  exact h

theorem mixedEnvelope_memLp (b h : LiftDomain period → ℂ)
    (hbL2 : ∀ i : Fin 4, ∀ r ≤ 5, ∀ w : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period w (fieldDerivative period (standardDirection i) b)) 2
        (liftMeasure period))
    (hhL2 : ∀ r ≤ 5, ∀ w : Fin r → Fin 4, MemLp (iteratedFieldDerivative period w h) 2 (liftMeasure
      period)) :
    MemLp (mixedEnvelope period b h) 2 (liftMeasure period) :=
  ((totalMagnitude_memLp period 5 h hhL2).const_smul (gradientSobolevNorm period b)).add
    ((gradientMagnitude_memLp period b hbL2).const_smul (liftSobolevNorm period 5 h))

theorem mixedEnvelope_L2_le (b h : LiftDomain period → ℂ)
    (hbL2 : ∀ i : Fin 4, ∀ r ≤ 5, ∀ w : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period w (fieldDerivative period (standardDirection i) b)) 2
        (liftMeasure period))
    (hhL2 : ∀ r ≤ 5, ∀ w : Fin r → Fin 4, MemLp (iteratedFieldDerivative period w h) 2 (liftMeasure
      period)) :
    ‖(mixedEnvelope_memLp period b h hbL2 hhL2).toLp (mixedEnvelope period b h)‖ ≤
      2 * gradientSobolevNorm period b * liftSobolevNorm period 5 h := by
  change ‖gradientSobolevNorm period b • (totalMagnitude_memLp period 5 h hhL2).toLp _ +
    liftSobolevNorm period 5 h • (gradientMagnitude_memLp period b hbL2).toLp _‖ ≤ _
  have hA := norm_add_le
    (gradientSobolevNorm period b • (totalMagnitude_memLp period 5 h hhL2).toLp (totalMagnitude
      period 5 h))
    (liftSobolevNorm period 5 h • (gradientMagnitude_memLp period b hbL2).toLp (gradientMagnitude
      period b))
  simp only [norm_smul, Real.norm_of_nonneg (gradientSobolevNorm_nonneg period b),
    Real.norm_of_nonneg (liftSobolevNorm_nonneg period 5 h)] at hA
  have hB := add_le_add
    (mul_le_mul_of_nonneg_left (totalMagnitude_L2_le period 5 h hhL2) (gradientSobolevNorm_nonneg
      period b))
    (mul_le_mul_of_nonneg_left (gradientMagnitude_L2_le period b hbL2) (liftSobolevNorm_nonneg
      period 5 h))
  have he (A B : ℝ) : A*B+B*A = 2*A*B := by ring
  exact hA.trans (hB.trans_eq (he _ _))

theorem mixedCommutator_pointwise_le (l : List (Fin 4)) (hl : l.length ≤ 6)
    (b h : LiftDomain period → ℂ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x))
    (hbL2 : ∀ i : Fin 4, ∀ r ≤ 5, ∀ w : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period w (fieldDerivative period (standardDirection i) b)) 2
        (liftMeasure period))
    (hhL2 : ∀ r ≤ 5, ∀ w : Fin r → Fin 4, MemLp (iteratedFieldDerivative period w h) 2 (liftMeasure
      period))
    (x : LiftDomain period) :
    ‖mixedCommutator period l b h x‖ ≤ (6 * mixedProductConstant period) * mixedEnvelope period b h
      x := by
  have hA := prefixed_commutator_pointwise_le period [] l (by simpa using hl) b h hb hh hbL2 hhL2 x
  have hB := mul_le_mul_of_nonneg_right (show (l.length : ℝ) ≤ 6 by exact_mod_cast hl)
    (mul_nonneg (mixedProductConstant_nonneg period) (mixedEnvelope_nonneg period b h x))
  rw [← mul_assoc, ← mul_assoc] at hB
  exact hA.trans hB

/-- Every mixed commutator through order six is a genuine L² function. -/
theorem mixedCommutator_memLp (l : List (Fin 4)) (hl : l.length ≤ 6)
    (b h : LiftDomain period → ℂ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x))
    (hbL2 : ∀ i : Fin 4, ∀ r ≤ 5, ∀ w : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period w (fieldDerivative period (standardDirection i) b)) 2
        (liftMeasure period))
    (hhL2 : ∀ r ≤ 5, ∀ w : Fin r → Fin 4, MemLp (iteratedFieldDerivative period w h) 2 (liftMeasure
      period)) :
    MemLp (mixedCommutator period l b h) 2 (liftMeasure period) := by
  apply (mixedEnvelope_memLp period b h hbL2 hhL2).of_le_mul
    ((smoothField_continuous period _ (mixedCommutator_smooth period l b h hb
      hh)).aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (mixedEnvelope_nonneg period b h x)]
  exact mixedCommutator_pointwise_le period l hl b h hb hh hbL2 hhL2 x

/-- The full mixed coordinate commutator bound, with no derivative loss. -/
theorem mixed_transport_commutator_L2 (l : List (Fin 4)) (hl : l.length ≤ 6)
    (b h : LiftDomain period → ℂ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x))
    (hbL2 : ∀ i : Fin 4, ∀ r ≤ 5, ∀ w : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period w (fieldDerivative period (standardDirection i) b)) 2
        (liftMeasure period))
    (hhL2 : ∀ r ≤ 5, ∀ w : Fin r → Fin 4, MemLp (iteratedFieldDerivative period w h) 2 (liftMeasure
      period)) :
    (eLpNorm (mixedCommutator period l b h) 2 (liftMeasure period)).toReal ≤
      (12 * mixedProductConstant period) * gradientSobolevNorm period b * liftSobolevNorm period 5
        h := by
  have hq := mixedEnvelope_memLp period b h hbL2 hhL2
  have hA := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := liftMeasure period)
    (Filter.Eventually.of_forall (fun x => show ‖mixedCommutator period l b h x‖ ≤
      (6 * mixedProductConstant period) * ‖mixedEnvelope period b h x‖ by
      rw [Real.norm_of_nonneg (mixedEnvelope_nonneg period b h x)]
      exact mixedCommutator_pointwise_le period l hl b h hb hh hbL2 hhL2 x)) (2 : ℝ≥0∞)
  have hc : 0 ≤ 6 * mixedProductConstant period := mul_nonneg (by norm_num)
    (mixedProductConstant_nonneg period)
  have hfin : ENNReal.ofReal (6 * mixedProductConstant period) *
      eLpNorm (mixedEnvelope period b h) 2 (liftMeasure period) ≠ ⊤ := by finiteness
  have hB := ENNReal.toReal_mono hfin hA
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at hB
  have hC := mul_le_mul_of_nonneg_left (mixedEnvelope_L2_le period b h hbL2 hhL2) hc
  rw [Lp.norm_toLp] at hC
  have he (C A B : ℝ) : (6*C)*(2*A*B)=(12*C)*A*B := by ring
  exact hB.trans (hC.trans_eq (he _ _ _))

omit [Fact (0 < period)] in
theorem listDerivative_ofFn {n : ℕ} (w : Fin n → Fin 4) (f : LiftDomain period → ℂ) :
    listDerivative period (List.ofFn w) f = iteratedFieldDerivative period w f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, listDerivative_cons, ih]
    rfl

/-- The same no-loss estimate in the finite-word convention used by the Sobolev jets. -/
theorem word_transport_commutator_L2 {n : ℕ} (hn : n ≤ 6) (w : Fin n → Fin 4)
    (b h : LiftDomain period → ℂ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x))
    (hbL2 : ∀ i : Fin 4, ∀ r ≤ 5, ∀ v : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period v (fieldDerivative period (standardDirection i) b)) 2
        (liftMeasure period))
    (hhL2 : ∀ r ≤ 5, ∀ v : Fin r → Fin 4, MemLp (iteratedFieldDerivative period v h) 2 (liftMeasure
      period)) :
    (eLpNorm (iteratedFieldDerivative period w (b*h) - b*iteratedFieldDerivative period w h) 2
      (liftMeasure period)).toReal ≤
      (12 * mixedProductConstant period) * gradientSobolevNorm period b * liftSobolevNorm period 5
        h := by
  have hA := mixed_transport_commutator_L2 period (List.ofFn w) (by simpa using hn) b h hb hh hbL2
    hhL2
  simpa only [mixedCommutator, listDerivative_ofFn] using hA

end EulerMixedCylinderTransport
