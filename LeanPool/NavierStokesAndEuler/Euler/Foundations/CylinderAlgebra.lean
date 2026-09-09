/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderSobolev
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Actual H⁶ multiplication on the three-dimensional cylinder. -/

@[expose] public section

noncomputable section

namespace EulerCylinderAlgebra

open MeasureTheory EulerSobolev EulerCylinderSobolev EulerCylinderCoordinates
open EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
open scoped ENNReal NNReal ContDiff Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The low-order tensor bound furnished by the cylinder embedding. -/
noncomputable def lowDerivativeConstant : ℝ := 64 * 85 * cylinderEmbeddingConstant period

theorem lowDerivativeConstant_nonneg : 0 ≤ lowDerivativeConstant period :=
  mul_nonneg (by norm_num) (cylinderEmbeddingConstant_nonneg period)

theorem tensor_low_le_H6 {m : ℕ} (hm : m ≤ 3) (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ 6, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖iteratedFDeriv ℝ m (euclideanLift period f x) 0‖ ≤
      lowDerivativeConstant period * liftSobolevNorm period 6 f := by
  have hA := euclideanLift_tensor_norm_le period m f hf x 0
  simp only [euclideanLift_zero] at hA
  have hB := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset (Fin m → Fin 4))) =>
    cylinder_word_pointwise_le_H6 period hm w f hf hfL2 x)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at hB
  have hp : (4 : ℝ) ^ m ≤ 64 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hm
    norm_num at h ⊢
    exact h
  have hC := mul_le_mul_of_nonneg_right hp (mul_nonneg
    (cylinderEmbeddingConstant_nonneg period) (mul_nonneg (by
        norm_num : (0 : ℝ) ≤ 85) (liftSobolevNorm_nonneg period 6 f)))
  have he (C A : ℝ) : 64 * (C * (85 * A)) = (64 * 85 * C) * A := by ring
  exact hA.trans (hB.trans (hC.trans_eq (he _ _)))

omit [Fact (0 < period)] in
theorem tensor_le_totalMagnitude {n : ℕ} (hn : n ≤ 6) (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    ‖iteratedFDeriv ℝ n (euclideanLift period f x) 0‖ ≤ totalMagnitude period 6 f x := by
  have hA := euclideanLift_tensor_norm_le period n f hf x 0
  simp only [euclideanLift_zero] at hA
  exact hA.trans (wordMagnitude_le_total period 6 n hn f x)

/-- The real-valued envelope arising from the low/high derivative split. -/
noncomputable def productEnvelope (f g : LiftDomain period → ℂ) : LiftDomain period → ℝ :=
  liftSobolevNorm period 6 f • totalMagnitude period 6 g +
    liftSobolevNorm period 6 g • totalMagnitude period 6 f

theorem productEnvelope_nonneg (f g : LiftDomain period → ℂ) (x : LiftDomain period) :
    0 ≤ productEnvelope period f g x :=
  add_nonneg (mul_nonneg (liftSobolevNorm_nonneg period 6 f) (totalMagnitude_nonneg period 6 g x))
    (mul_nonneg (liftSobolevNorm_nonneg period 6 g) (totalMagnitude_nonneg period 6 f x))

omit [Fact (0 < period)] in
theorem product_smooth (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (f*g) x) := fun x => (hf x).mul (hg x)

theorem product_tensor_term_le {n j : ℕ} (hn : n ≤ 6) (hj : j ≤ n)
    (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ k ≤ 6, ∀ w : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period))
    (hgL2 : ∀ k ≤ 6, ∀ w : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖iteratedFDeriv ℝ j (euclideanLift period f x) 0‖ *
      ‖iteratedFDeriv ℝ (n-j) (euclideanLift period g x) 0‖ ≤
        lowDerivativeConstant period * productEnvelope period f g x := by
  by_cases hj3 : j ≤ 3
  · have hA := mul_le_mul (tensor_low_le_H6 period hj3 f hf hfL2 x)
      (tensor_le_totalMagnitude period (by omega : n-j ≤ 6) g hg x) (norm_nonneg _)
      (mul_nonneg (lowDerivativeConstant_nonneg period) (liftSobolevNorm_nonneg period 6 f))
    have hB : liftSobolevNorm period 6 f * totalMagnitude period 6 g x ≤ productEnvelope period f g
        x := by
      exact le_add_of_nonneg_right (mul_nonneg (liftSobolevNorm_nonneg period 6 g)
        (totalMagnitude_nonneg period 6 f x))
    have hC := mul_le_mul_of_nonneg_left hB (lowDerivativeConstant_nonneg period)
    rw [mul_assoc] at hA
    exact hA.trans hC
  · have hA := mul_le_mul (tensor_le_totalMagnitude period (by omega : j ≤ 6) f hf x)
      (tensor_low_le_H6 period (by omega : n-j ≤ 3) g hg hgL2 x) (norm_nonneg _)
      (totalMagnitude_nonneg period 6 f x)
    have hB : liftSobolevNorm period 6 g * totalMagnitude period 6 f x ≤ productEnvelope period f g
        x := by
      exact le_add_of_nonneg_left (mul_nonneg (liftSobolevNorm_nonneg period 6 f)
        (totalMagnitude_nonneg period 6 g x))
    have hC := mul_le_mul_of_nonneg_left hB (lowDerivativeConstant_nonneg period)
    have he (A B C : ℝ) : A * (B*C) = B*(C*A) := by ring
    exact hA.trans ((he _ _ _).trans_le hC)

/-- Actual Leibniz derivatives of a product have a square-integrable low/high envelope. -/
theorem product_word_pointwise_le {n : ℕ} (hn : n ≤ 6) (w : Fin n → Fin 4)
    (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (hgL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖iteratedFieldDerivative period w (f*g) x‖ ≤
      64 * lowDerivativeConstant period * productEnvelope period f g x := by
  have he := euclideanLift_iteratedFieldDerivative period w (f*g) (product_smooth period f g hf hg)
      x 0
  rw [euclideanLift_zero] at he
  rw [he]
  have hA := (iteratedFDeriv ℝ n (euclideanLift period (f*g) x) 0).le_opNorm
    (fun j => EuclideanSpace.single (w j) (1 : ℝ))
  simp only [PiLp.norm_single, norm_one, Finset.prod_const_one, mul_one] at hA
  have hB := norm_iteratedFDeriv_mul_le (euclideanLift_smooth period f hf x)
    (euclideanLift_smooth period g hg x) 0 (by simp : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  have hC : (∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
      ‖iteratedFDeriv ℝ j (euclideanLift period f x) 0‖ *
      ‖iteratedFDeriv ℝ (n-j) (euclideanLift period g x) 0‖) ≤
        2^n * (lowDerivativeConstant period * productEnvelope period f g x) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
          (lowDerivativeConstant period * productEnvelope period f g x) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (product_tensor_term_le period hn
          (by simpa using Finset.mem_range.1 hj) f g hf hg hfL2 hgL2 x) (Nat.cast_nonneg _)
      _ = _ := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose n
  have hp : (2 : ℝ)^n ≤ 64 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
    norm_num at h ⊢
    exact h
  have hD := mul_le_mul_of_nonneg_right hp (mul_nonneg
    (lowDerivativeConstant_nonneg period) (productEnvelope_nonneg period f g x))
  exact hA.trans (hB.trans (hC.trans (hD.trans_eq (mul_assoc _ _ _).symm)))

theorem productEnvelope_memLp (f g : LiftDomain period → ℂ)
    (hfL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (hgL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure period)) :
    MemLp (productEnvelope period f g) 2 (liftMeasure period) :=
  ((totalMagnitude_memLp period 6 g hgL2).const_smul (liftSobolevNorm period 6 f)).add
    ((totalMagnitude_memLp period 6 f hfL2).const_smul (liftSobolevNorm period 6 g))

theorem productEnvelope_L2_le (f g : LiftDomain period → ℂ)
    (hfL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (hgL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure period)) :
    ‖(productEnvelope_memLp period f g hfL2 hgL2).toLp (productEnvelope period f g)‖ ≤
      2 * liftSobolevNorm period 6 f * liftSobolevNorm period 6 g := by
  change ‖liftSobolevNorm period 6 f • (totalMagnitude_memLp period 6 g hgL2).toLp _ +
    liftSobolevNorm period 6 g • (totalMagnitude_memLp period 6 f hfL2).toLp _‖ ≤ _
  have hA := norm_add_le
    (liftSobolevNorm period 6 f • (totalMagnitude_memLp period 6 g hgL2).toLp (totalMagnitude
        period 6 g))
    (liftSobolevNorm period 6 g • (totalMagnitude_memLp period 6 f hfL2).toLp (totalMagnitude
        period 6 f))
  simp only [norm_smul, Real.norm_of_nonneg (liftSobolevNorm_nonneg period 6 f),
    Real.norm_of_nonneg (liftSobolevNorm_nonneg period 6 g)] at hA
  have hB := add_le_add
    (mul_le_mul_of_nonneg_left (totalMagnitude_L2_le period 6 g hgL2) (liftSobolevNorm_nonneg
        period 6 f))
    (mul_le_mul_of_nonneg_left (totalMagnitude_L2_le period 6 f hfL2) (liftSobolevNorm_nonneg
        period 6 g))
  have he (A B : ℝ) : A*B+B*A = 2*A*B := by ring
  exact hA.trans (hB.trans_eq (he _ _))

/-- Every derivative word through order six of the product is genuinely square-integrable. -/
theorem product_word_memLp {n : ℕ} (hn : n ≤ 6) (w : Fin n → Fin 4)
    (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (hgL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure period)) :
    MemLp (iteratedFieldDerivative period w (f*g)) 2 (liftMeasure period) := by
  apply (productEnvelope_memLp period f g hfL2 hgL2).of_le_mul
    ((smoothField_continuous period _ (iteratedFieldDerivative_smooth period w (f*g)
      (product_smooth period f g hf hg))).aestronglyMeasurable)
  · filter_upwards [] with x
    rw [Real.norm_of_nonneg (productEnvelope_nonneg period f g x)]
    exact product_word_pointwise_le period hn w f g hf hg hfL2 hgL2 x

/-- An explicit bound for each actual product derivative in L². -/
theorem product_word_L2_le {n : ℕ} (hn : n ≤ 6) (w : Fin n → Fin 4)
    (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (hgL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure period)) :
    (eLpNorm (iteratedFieldDerivative period w (f*g)) 2 (liftMeasure period)).toReal ≤
      128 * lowDerivativeConstant period * liftSobolevNorm period 6 f * liftSobolevNorm period 6 g
          := by
  have hq := productEnvelope_memLp period f g hfL2 hgL2
  have hA := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := liftMeasure period)
    (Filter.Eventually.of_forall (fun x => show ‖iteratedFieldDerivative period w (f*g) x‖ ≤
      (64 * lowDerivativeConstant period) * ‖productEnvelope period f g x‖ by
        rw [Real.norm_of_nonneg (productEnvelope_nonneg period f g x)]
        exact product_word_pointwise_le period hn w f g hf hg hfL2 hgL2 x)) (2 : ℝ≥0∞)
  have hc : 0 ≤ 64 * lowDerivativeConstant period := mul_nonneg (by
      norm_num) (lowDerivativeConstant_nonneg period)
  have hfin : ENNReal.ofReal (64 * lowDerivativeConstant period) *
      eLpNorm (productEnvelope period f g) 2 (liftMeasure period) ≠ ⊤ := by finiteness
  have hB := ENNReal.toReal_mono hfin hA
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at hB
  have hC := mul_le_mul_of_nonneg_left (productEnvelope_L2_le period f g hfL2 hgL2) hc
  rw [Lp.norm_toLp] at hC
  have he (L A B : ℝ) : (64*L)*(2*A*B) = 128*L*A*B := by ring
  exact hB.trans (hC.trans_eq (he _ _ _))

/-- The H⁶ algebra estimate on the actual cylinder, with a finite explicit constant. -/
theorem cylinder_H6_algebra (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (hgL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure period)) :
    liftSobolevNorm period 6 (f*g) ≤
      (5461 * 128 * lowDerivativeConstant period) *
        liftSobolevNorm period 6 f * liftSobolevNorm period 6 g := by
  have hA : liftSobolevNorm period 6 (f*g) ≤
      ∑ n ∈ Finset.range 7, ∑ _w : Fin n → Fin 4,
        128 * lowDerivativeConstant period * liftSobolevNorm period 6 f * liftSobolevNorm period 6
            g := by
    apply Finset.sum_le_sum
    intro n hn
    apply Finset.sum_le_sum
    intro w _
    exact product_word_L2_le period (by have := Finset.mem_range.1 hn; omega) w f g hf hg hfL2 hgL2
  have hcard (A : ℝ) : (∑ n ∈ Finset.range 7, ∑ _w : Fin n → Fin 4, A) = 5461*A := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
    norm_num [Finset.sum_range_succ]
    ring
  rw [hcard] at hA
  have he (L A B : ℝ) : 5461*(128*L*A*B) = (5461*128*L)*A*B := by ring
  exact hA.trans_eq (he _ _ _)

end EulerCylinderAlgebra
