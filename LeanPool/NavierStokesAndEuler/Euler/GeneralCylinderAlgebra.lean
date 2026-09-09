/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EulerProof

@[expose] public section

/-! Actual cylinder Sobolev multiplication at every fixed integer order q ≥ 6. -/

noncomputable section

namespace EulerGeneralCylinderAlgebra

open MeasureTheory EulerSobolev EulerCylinderSobolev EulerCylinderCoordinates
  EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
open scoped ENNReal NNReal ContDiff Topology

variable (period : ℝ) [Fact (0 < period)]

/-- An explicit low-derivative tensor embedding constant for fixed Sobolev order q. -/
def lowDerivativeConstant (q : ℕ) : ℝ := (4 : ℝ) ^ q * 85 * cylinderEmbeddingConstant period

/-- The low-derivative embedding constant is nonnegative. -/
theorem lowDerivativeConstant_nonneg (q : ℕ) : 0 ≤ lowDerivativeConstant period q :=
  mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (by norm_num))
    (cylinderEmbeddingConstant_nonneg period)

/-- Three additional derivatives control the H³ norm of an arbitrary derivative word. -/
theorem word_H3_le_Hq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {q m : ℕ} (hm : m + 3 ≤ q) (w : Fin m → Fin 4) (f : LiftDomain period → F) :
    liftSobolevNorm period 3 (iteratedFieldDerivative period w f) ≤ 85 * liftSobolevNorm period q f
      := by
  have hA : (∑ n ∈ Finset.range (3 + 1), ∑ v : Fin n → Fin 4,
      (eLpNorm (iteratedFieldDerivative period v (iteratedFieldDerivative period w f)) 2
        (liftMeasure period)).toReal) ≤
      ∑ n ∈ Finset.range (3 + 1), ∑ _v : Fin n → Fin 4, liftSobolevNorm period q f := by
    apply Finset.sum_le_sum
    intro n hn
    apply Finset.sum_le_sum
    intro v _
    obtain ⟨u, hu⟩ := iteratedFieldDerivative_comp_exists period v w f
    rw [hu]
    exact word_L2_le_liftSobolevNorm period (by have := Finset.mem_range.1 hn; omega) u f
  apply hA.trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  norm_num [Finset.sum_range_succ]
  ring

/-- Actual derivative words with three derivatives to spare are uniformly bounded pointwise. -/
theorem word_pointwise_le_Hq {q m : ℕ} (hm : m + 3 ≤ q) (w : Fin m → Fin 4)
    (f : LiftDomain period → ℂ) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ q, ∀ u : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period u f) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖iteratedFieldDerivative period w f x‖ ≤
      cylinderEmbeddingConstant period * (85 * liftSobolevNorm period q f) := by
  have hA := cylinder_pointwise_le_H3 period (iteratedFieldDerivative period w f)
    (iteratedFieldDerivative_smooth period w f hf)
    (fun j hj v => word_memLp period (by omega : m + j ≤ q) v w f hfL2) x
  exact hA.trans (mul_le_mul_of_nonneg_left (word_H3_le_Hq period hm w f)
    (cylinderEmbeddingConstant_nonneg period))

/-- The actual low-order Fréchet tensor is bounded by the fixed-order cylinder Sobolev norm. -/
theorem tensor_low_le_Hq {q m : ℕ} (hm : m + 3 ≤ q) (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ q, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖iteratedFDeriv ℝ m (euclideanLift period f x) 0‖ ≤
      lowDerivativeConstant period q * liftSobolevNorm period q f := by
  have hA := euclideanLift_tensor_norm_le period m f hf x 0
  simp only [euclideanLift_zero] at hA
  have hB := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset (Fin m → Fin 4))) =>
    word_pointwise_le_Hq period hm w f hf hfL2 x)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at hB
  have hp : (4 : ℝ) ^ m ≤ 4 ^ q := pow_le_pow_right₀ (by norm_num) (by omega)
  have hC := mul_le_mul_of_nonneg_right hp (mul_nonneg
    (cylinderEmbeddingConstant_nonneg period)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 85) (liftSobolevNorm_nonneg period q f)))
  exact hA.trans (hB.trans (hC.trans_eq (by unfold lowDerivativeConstant; ring)))

omit [Fact (0 < period)] in
/-- Every tensor through the fixed Sobolev order is dominated by the actual derivative envelope. -/
theorem tensor_le_totalMagnitude {q n : ℕ} (hn : n ≤ q) (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    ‖iteratedFDeriv ℝ n (euclideanLift period f x) 0‖ ≤ totalMagnitude period q f x := by
  have hA := euclideanLift_tensor_norm_le period n f hf x 0
  simp only [euclideanLift_zero] at hA
  exact hA.trans (wordMagnitude_le_total period q n hn f x)

/-- The square-integrable envelope obtained by putting one factor in L∞ and the other in L². -/
def productEnvelope (q : ℕ) (f g : LiftDomain period → ℂ) : LiftDomain period → ℝ :=
  liftSobolevNorm period q f • totalMagnitude period q g +
    liftSobolevNorm period q g • totalMagnitude period q f

/-- The product envelope is pointwise nonnegative. -/
theorem productEnvelope_nonneg (q : ℕ) (f g : LiftDomain period → ℂ) (x : LiftDomain period) :
    0 ≤ productEnvelope period q f g x :=
  add_nonneg (mul_nonneg (liftSobolevNorm_nonneg period q f) (totalMagnitude_nonneg period q g x))
    (mul_nonneg (liftSobolevNorm_nonneg period q g) (totalMagnitude_nonneg period q f x))

/-- In every Leibniz term through order q≥6, one factor has three spare derivatives. -/
theorem product_tensor_term_le {q n j : ℕ} (hq : 6 ≤ q) (hn : n ≤ q) (hj : j ≤ n)
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
theorem product_word_pointwise_le {q n : ℕ} (hq : 6 ≤ q) (hn : n ≤ q) (w : Fin n → Fin 4)
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

/-- The actual low/high envelope is square-integrable. -/
theorem productEnvelope_memLp (q : ℕ) (f g : LiftDomain period → ℂ)
    (hfL2 : ∀ k ≤ q, ∀ v : Fin k → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure
      period))
    (hgL2 : ∀ k ≤ q, ∀ v : Fin k → Fin 4, MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure
      period)) :
    MemLp (productEnvelope period q f g) 2 (liftMeasure period) :=
  ((totalMagnitude_memLp period q g hgL2).const_smul (liftSobolevNorm period q f)).add
    ((totalMagnitude_memLp period q f hfL2).const_smul (liftSobolevNorm period q g))

/-- The L² norm of the low/high envelope is bounded by twice the product of Sobolev norms. -/
theorem productEnvelope_L2_le (q : ℕ) (f g : LiftDomain period → ℂ)
    (hfL2 : ∀ k ≤ q, ∀ v : Fin k → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure
      period))
    (hgL2 : ∀ k ≤ q, ∀ v : Fin k → Fin 4, MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure
      period)) :
    ‖(productEnvelope_memLp period q f g hfL2 hgL2).toLp (productEnvelope period q f g)‖ ≤
      2 * liftSobolevNorm period q f * liftSobolevNorm period q g := by
  change ‖liftSobolevNorm period q f • (totalMagnitude_memLp period q g hgL2).toLp _ +
    liftSobolevNorm period q g • (totalMagnitude_memLp period q f hfL2).toLp _‖ ≤ _
  have hA := norm_add_le
    (liftSobolevNorm period q f • (totalMagnitude_memLp period q g hgL2).toLp (totalMagnitude
      period q g))
    (liftSobolevNorm period q g • (totalMagnitude_memLp period q f hfL2).toLp (totalMagnitude
      period q f))
  simp only [norm_smul, Real.norm_of_nonneg (liftSobolevNorm_nonneg period q f),
    Real.norm_of_nonneg (liftSobolevNorm_nonneg period q g)] at hA
  have hB := add_le_add
    (mul_le_mul_of_nonneg_left (totalMagnitude_L2_le period q g hgL2) (liftSobolevNorm_nonneg
      period q f))
    (mul_le_mul_of_nonneg_left (totalMagnitude_L2_le period q f hfL2) (liftSobolevNorm_nonneg
      period q g))
  exact hA.trans (hB.trans_eq (by ring))

/-- Every derivative word through order q of the actual product belongs to L². -/
theorem product_word_memLp {q n : ℕ} (hq : 6 ≤ q) (hn : n ≤ q) (w : Fin n → Fin 4)
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
theorem product_word_L2_le {q n : ℕ} (hq : 6 ≤ q) (hn : n ≤ q) (w : Fin n → Fin 4)
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

/-- A finite explicit algebra constant for each fixed Sobolev order. -/
def algebraConstant (q : ℕ) : ℝ :=
  (∑ n ∈ Finset.range (q + 1), (4 : ℝ) ^ n) * ((2 : ℝ) ^ q * lowDerivativeConstant period q * 2)

/-- The fixed-order algebra constant is nonnegative. -/
theorem algebraConstant_nonneg (q : ℕ) : 0 ≤ algebraConstant period q := by
  unfold algebraConstant
  exact mul_nonneg (Finset.sum_nonneg fun _ _ => pow_nonneg (by norm_num) _)
    (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (lowDerivativeConstant_nonneg period q))
      (by norm_num))

/-- The genuine complex cylinder Sobolev algebra estimate at every integer order q≥6. -/
theorem cylinder_Hq_algebra {q : ℕ} (hq : 6 ≤ q) (f g : LiftDomain period → ℂ)
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

end EulerGeneralCylinderAlgebra
