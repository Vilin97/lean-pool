/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GeneralRealCylinderAlgebra

@[expose] public section

/-! The additional H⁵ cylinder algebra estimate needed for the base transport commutator. -/

noncomputable section

namespace EulerH5CylinderAlgebra

open MeasureTheory EulerSobolev EulerCylinderSobolev EulerCylinderCoordinates
  EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
    EulerGeneralCylinderAlgebra
open scoped ENNReal NNReal ContDiff Topology

variable (period : ℝ) [Fact (0 < period)]

/-- In every Leibniz term through order q≥5, one factor has three spare derivatives. -/
theorem product_tensor_term_le {q n j : ℕ} (hq : 5 ≤ q) (hn : n ≤ q) (hj : j ≤ n)
    (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ k ≤ q, ∀ w : Fin k → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure
      period))
    (hgL2 : ∀ k ≤ q, ∀ w : Fin k → Fin 4, MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure
      period))
    (x : LiftDomain period) :
    ‖iteratedFDeriv ℝ j (euclideanLift period f x) 0‖ *
      ‖iteratedFDeriv ℝ (n - j) (euclideanLift period g x) 0‖ ≤
        lowDerivativeConstant period q * productEnvelope period q f g x := by
  by_cases hjlow : j + 3 ≤ q
  · have hA := mul_le_mul (tensor_low_le_Hq period hjlow f hf hfL2 x)
      (tensor_le_totalMagnitude period (by omega : n - j ≤ q) g hg x) (norm_nonneg _)
      (mul_nonneg (lowDerivativeConstant_nonneg period q) (liftSobolevNorm_nonneg period q f))
    have hB : liftSobolevNorm period q f * totalMagnitude period q g x ≤ productEnvelope period q f
      g x :=
      le_add_of_nonneg_right (mul_nonneg (liftSobolevNorm_nonneg period q g) (totalMagnitude_nonneg
        period q f x))
    rw [mul_assoc] at hA
    exact hA.trans (mul_le_mul_of_nonneg_left hB (lowDerivativeConstant_nonneg period q))
  · have hA := mul_le_mul (tensor_le_totalMagnitude period (by omega : j ≤ q) f hf x)
      (tensor_low_le_Hq period (by omega : n - j + 3 ≤ q) g hg hgL2 x) (norm_nonneg _)
      (totalMagnitude_nonneg period q f x)
    have hB : liftSobolevNorm period q g * totalMagnitude period q f x ≤ productEnvelope period q f
      g x :=
      le_add_of_nonneg_left (mul_nonneg (liftSobolevNorm_nonneg period q f) (totalMagnitude_nonneg
        period q g x))
    have hC := mul_le_mul_of_nonneg_left hB (lowDerivativeConstant_nonneg period q)
    exact hA.trans ((by ring : _ = lowDerivativeConstant period q *
      (liftSobolevNorm period q g * totalMagnitude period q f x)).trans_le hC)


/-- Every actual product derivative is bounded pointwise by the low/high Sobolev envelope. -/
theorem product_word_pointwise_le {q n : ℕ} (hq : 5 ≤ q) (hn : n ≤ q) (w : Fin n → Fin 4)
    (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ k ≤ q, ∀ v : Fin k → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure
      period))
    (hgL2 : ∀ k ≤ q, ∀ v : Fin k → Fin 4, MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure
      period))
    (x : LiftDomain period) :
    ‖iteratedFieldDerivative period w (f * g) x‖ ≤
      (2 : ℝ) ^ q * lowDerivativeConstant period q * productEnvelope period q f g x := by
  have he := euclideanLift_iteratedFieldDerivative period w (f * g)
    (EulerCylinderAlgebra.product_smooth period f g hf hg) x 0
  rw [euclideanLift_zero] at he
  rw [he]
  have hA := (iteratedFDeriv ℝ n (euclideanLift period (f * g) x) 0).le_opNorm
    (fun j => EuclideanSpace.single (w j) (1 : ℝ))
  simp only [PiLp.norm_single, norm_one, Finset.prod_const_one, mul_one] at hA
  have hB := norm_iteratedFDeriv_mul_le (euclideanLift_smooth period f hf x)
    (euclideanLift_smooth period g hg x) 0 (by simp : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  have hC : (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
      ‖iteratedFDeriv ℝ j (euclideanLift period f x) 0‖ *
      ‖iteratedFDeriv ℝ (n - j) (euclideanLift period g x) 0‖) ≤
        2 ^ n * (lowDerivativeConstant period q * productEnvelope period q f g x) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
          (lowDerivativeConstant period q * productEnvelope period q f g x) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (product_tensor_term_le period hq hn
          (by simpa using Finset.mem_range.1 hj) f g hf hg hfL2 hgL2 x) (Nat.cast_nonneg _)
      _ = _ := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose n
  have hp : (2 : ℝ) ^ n ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hn
  have hD := mul_le_mul_of_nonneg_right hp (mul_nonneg
    (lowDerivativeConstant_nonneg period q) (productEnvelope_nonneg period q f g x))
  exact hA.trans (hB.trans (hC.trans (hD.trans_eq (mul_assoc _ _ _).symm)))


/-- Every derivative word through order q of the actual product belongs to L². -/
theorem product_word_memLp {q n : ℕ} (hq : 5 ≤ q) (hn : n ≤ q) (w : Fin n → Fin 4)
    (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ k ≤ q, ∀ v : Fin k → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure
      period))
    (hgL2 : ∀ k ≤ q, ∀ v : Fin k → Fin 4, MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure
      period)) :
    MemLp (iteratedFieldDerivative period w (f * g)) 2 (liftMeasure period) := by
  apply (productEnvelope_memLp period q f g hfL2 hgL2).of_le_mul
    ((smoothField_continuous period _ (iteratedFieldDerivative_smooth period w (f * g)
      (EulerCylinderAlgebra.product_smooth period f g hf hg))).aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (productEnvelope_nonneg period q f g x)]
  exact product_word_pointwise_le period hq hn w f g hf hg hfL2 hgL2 x


/-- Every product derivative has an explicit L² bound by the product of fixed-order Sobolev norms. -/
theorem product_word_L2_le {q n : ℕ} (hq : 5 ≤ q) (hn : n ≤ q) (w : Fin n → Fin 4)
    (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ k ≤ q, ∀ v : Fin k → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure
      period))
    (hgL2 : ∀ k ≤ q, ∀ v : Fin k → Fin 4, MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure
      period)) :
    (eLpNorm (iteratedFieldDerivative period w (f * g)) 2 (liftMeasure period)).toReal ≤
      ((2 : ℝ) ^ q * lowDerivativeConstant period q * 2) *
        liftSobolevNorm period q f * liftSobolevNorm period q g := by
  have henv := productEnvelope_memLp period q f g hfL2 hgL2
  have hA := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := liftMeasure period)
    (Filter.Eventually.of_forall (fun x => show ‖iteratedFieldDerivative period w (f * g) x‖ ≤
      ((2 : ℝ) ^ q * lowDerivativeConstant period q) * ‖productEnvelope period q f g x‖ by
        rw [Real.norm_of_nonneg (productEnvelope_nonneg period q f g x)]
        exact product_word_pointwise_le period hq hn w f g hf hg hfL2 hgL2 x)) (2 : ℝ≥0∞)
  have hc : 0 ≤ (2 : ℝ) ^ q * lowDerivativeConstant period q :=
    mul_nonneg (pow_nonneg (by norm_num) _) (lowDerivativeConstant_nonneg period q)
  have hfin : ENNReal.ofReal ((2 : ℝ) ^ q * lowDerivativeConstant period q) *
      eLpNorm (productEnvelope period q f g) 2 (liftMeasure period) ≠ ⊤ := by finiteness
  have hB := ENNReal.toReal_mono hfin hA
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at hB
  have hC := mul_le_mul_of_nonneg_left (productEnvelope_L2_le period q f g hfL2 hgL2) hc
  rw [Lp.norm_toLp] at hC
  exact hB.trans (hC.trans_eq (by ring))


/-- The genuine complex cylinder Sobolev algebra estimate at every integer order q≥5. -/
theorem cylinder_Hq_algebra {q : ℕ} (hq : 5 ≤ q) (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ k ≤ q, ∀ v : Fin k → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure
      period))
    (hgL2 : ∀ k ≤ q, ∀ v : Fin k → Fin 4, MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure
      period)) :
    liftSobolevNorm period q (f * g) ≤
      algebraConstant period q * liftSobolevNorm period q f * liftSobolevNorm period q g := by
  have hA : liftSobolevNorm period q (f * g) ≤
      ∑ n ∈ Finset.range (q + 1), ∑ _w : Fin n → Fin 4,
        ((2 : ℝ) ^ q * lowDerivativeConstant period q * 2) *
          liftSobolevNorm period q f * liftSobolevNorm period q g := by
    apply Finset.sum_le_sum
    intro n hn
    apply Finset.sum_le_sum
    intro w _
    exact product_word_L2_le period hq (by have := Finset.mem_range.1 hn; omega) w f g hf hg hfL2
      hgL2
  apply hA.trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Finset.sum_mul]
  unfold algebraConstant
  ring


end EulerH5CylinderAlgebra
