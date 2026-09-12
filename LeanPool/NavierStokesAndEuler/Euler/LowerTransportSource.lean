/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.GeneralCylinderAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.H6TransportSource
import LeanPool.NavierStokesAndEuler.Euler.ExternalTransportCommutator
import LeanPool.NavierStokesAndEuler.Euler.Foundations.RealCylinder
import LeanPool.NavierStokesAndEuler.Euler.Foundations.VectorCylinder
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderAlgebra
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Actual lower-base Sobolev bounds for the transport pressure, without an external derivative
loss. -/

section

/-! The additional H⁵ cylinder algebra estimate needed for the base transport commutator. -/

@[expose] public section

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
  · filter_upwards [] with x
    rw [Real.norm_of_nonneg (productEnvelope_nonneg period q f g x)]
    exact product_word_pointwise_le period hq hn w f g hf hg hfL2 hgL2 x

/-- Every product derivative has an explicit L² bound by the product of fixed-order Sobolev norms.
-/
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
    exact product_word_L2_le period hq (by
        have := Finset.mem_range.1 hn; omega) w f g hf hg hfL2 hgL2
  apply hA.trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Finset.sum_mul]
  unfold algebraConstant
  ring

end EulerH5CylinderAlgebra

end
end

end

section

/-! Actual real and scalar-vector cylinder multiplication at every fixed Sobolev order q≥5. -/

@[expose] public section

noncomputable section

namespace EulerH5CylinderAlgebra

open MeasureTheory EulerSobolev EulerCylinderSobolev EulerLiftedGradientSpace EulerMetricTransport
  EulerRealCylinder EulerVectorCylinder EulerGeneralCylinderAlgebra
open scoped ENNReal NNReal ContDiff Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual real cylinder algebra estimate at every fixed order q≥5. -/
theorem real_cylinder_Hq_algebra {q : ℕ} (hq : 5 ≤ q) (f g : LiftDomain period → ℝ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ j ≤ q, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure
        period))
    (hgL2 : ∀ j ≤ q, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure
        period)) :
    liftSobolevNorm period q (f * g) ≤
      algebraConstant period q * liftSobolevNorm period q f * liftSobolevNorm period q g := by
  have h := cylinder_Hq_algebra period hq (complexField period f) (complexField period g)
    (complexField_smooth period f hf) (complexField_smooth period g hg)
    (fun j hj w => by
        rw [complexField_word period w f hf]; exact complexField_memLp period _ (hfL2 j hj w))
    (fun j hj w => by
        rw [complexField_word period w g hg]; exact complexField_memLp period _ (hgL2 j hj w))
  have he : complexField period f * complexField period g = complexField period (f * g) := by
    ext x
    exact (Complex.ofReal_mul _ _).symm
  rw [he, complexField_sobolevNorm period q (f * g) (fun x => (hf x).mul (hg x)),
    complexField_sobolevNorm period q f hf, complexField_sobolevNorm period q g hg] at h
  exact h

/-- Every real product derivative through order q is genuinely square-integrable. -/
theorem real_product_word_memLp {q n : ℕ} (hq : 5 ≤ q) (hn : n ≤ q) (w : Fin n → Fin 4)
    (f g : LiftDomain period → ℝ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ j ≤ q, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure
        period))
    (hgL2 : ∀ j ≤ q, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure
        period)) :
    MemLp (iteratedFieldDerivative period w (f * g)) 2 (liftMeasure period) := by
  have h := product_word_memLp period hq hn w (complexField period f) (complexField period g)
    (complexField_smooth period f hf) (complexField_smooth period g hg)
    (fun j hj v => by
        rw [complexField_word period v f hf]; exact complexField_memLp period _ (hfL2 j hj v))
    (fun j hj v => by
        rw [complexField_word period v g hg]; exact complexField_memLp period _ (hgL2 j hj v))
  have he : complexField period f * complexField period g = complexField period (f * g) := by
    ext x
    exact (Complex.ofReal_mul _ _).symm
  rw [he, complexField_word period w (f * g) (fun x => (hf x).mul (hg x))] at h
  apply h.of_le
    ((smoothField_continuous period _ (iteratedFieldDerivative_smooth period w (f * g)
      (fun x => (hf x).mul (hg x)))).aestronglyMeasurable)
  filter_upwards [] with x
  exact (Complex.norm_real _).ge

/-- Every scalar-vector product derivative through order q is genuinely in L². -/
theorem scalar_vector_product_word_memLp {q n : ℕ} (hq : 5 ≤ q) (hn : n ≤ q) (d : ℕ)
    (w : Fin n → Fin 4) (f : LiftDomain period → ℝ) (g : LiftDomain period → Domain d)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ j ≤ q, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure
        period))
    (hgL2 : ∀ j ≤ q, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure
        period)) :
    MemLp (iteratedFieldDerivative period w (fun x => f x • g x)) 2 (liftMeasure period) := by
  apply MemLp.of_eval_piLp
  intro i
  have h := real_product_word_memLp period hq hn w f (coordinate d i ∘ g) hf
    (postcomp_smooth period _ g hg) hfL2
    (fun j hj v => postcomp_word_memLp period hj _ g hg hgL2 v)
  rw [← coordinate_smul period d i f g] at h
  have he : (fun x => iteratedFieldDerivative period w (fun x => f x • g x) x i) =
      iteratedFieldDerivative period w (coordinate d i ∘ (fun x => f x • g x)) := by
    funext x
    exact (coordinate_word period d i w (fun x => f x • g x) (fun x => (hf x).smul (hg x)) x).symm
  rw [he]
  exact h

/-- Multiplication of an actual vector field by a scalar field is bounded in every Hq, q≥5. -/
theorem cylinder_Hq_scalar_vector_product {q : ℕ} (hq : 5 ≤ q) (d : ℕ)
    (f : LiftDomain period → ℝ) (g : LiftDomain period → Domain d)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ j ≤ q, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure
        period))
    (hgL2 : ∀ j ≤ q, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure
        period)) :
    liftSobolevNorm period q (fun x => f x • g x) ≤
      ((d : ℝ) * algebraConstant period q) * liftSobolevNorm period q f * liftSobolevNorm period q
          g := by
  have hs : ∀ x, ContDiff ℝ ∞ (localFieldLift period (fun x => f x • g x) x) :=
    fun x => (hf x).smul (hg x)
  have hcomp (i : Fin d) : ∀ j ≤ q, ∀ v : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period v (coordinate d i ∘ g)) 2 (liftMeasure period) :=
    fun j hj v => postcomp_word_memLp period hj _ g hg hgL2 v
  have hA := vector_sobolevNorm_le_sum_coordinates period d q (fun x => f x • g x) hs
    (fun i j hj v => by
      rw [coordinate_smul]
      exact real_product_word_memLp period hq hj v f (coordinate d i ∘ g) hf
        (postcomp_smooth period _ g hg) hfL2 (hcomp i))
  have hB (i : Fin d) : liftSobolevNorm period q (coordinate d i ∘ (fun x => f x • g x)) ≤
      algebraConstant period q * liftSobolevNorm period q f * liftSobolevNorm period q g := by
    rw [coordinate_smul]
    have h := real_cylinder_Hq_algebra period hq f (coordinate d i ∘ g) hf
      (postcomp_smooth period _ g hg) hfL2 (hcomp i)
    exact h.trans (mul_le_mul_of_nonneg_left
      (postcomp_sobolevNorm_le period q _ (coordinate_norm_le d i) g hg hgL2)
      (mul_nonneg (algebraConstant_nonneg period q) (liftSobolevNorm_nonneg period q f)))
  have hC := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hB i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hC
  exact hA.trans (hC.trans_eq (by ring))

end EulerH5CylinderAlgebra

end
end

end

@[expose] public section

noncomputable section

namespace EulerH6Nonlinear

open MeasureTheory EulerSobolev EulerCylinderSobolev EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives EulerVectorCylinder EulerJetProductBounds EulerSpatialSobolevInverse
  EulerExternalTransportCommutator
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual H⁵ algebra constant for scalar-vector fields. -/
def lowerProductConstant (d : ℕ) : ℝ := (d : ℝ)*EulerGeneralCylinderAlgebra.algebraConstant period 5

theorem lowerProductConstant_nonneg (d : ℕ) : 0 ≤ lowerProductConstant period d :=
  mul_nonneg (Nat.cast_nonneg d) (EulerGeneralCylinderAlgebra.algebraConstant_nonneg period 5)

/-- External derivatives of the genuine product obey the same binomial rule at base H⁵. -/
theorem product_wordH5Norm_bound (q n : ℕ)
    (f : LiftDomain period → ℝ) (g : LiftDomain period → Domain q)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure
        period))
    (hgL2 : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure
        period)) :
    wordSobolevNorm period 5 n (fun x => f x • g x) ≤
      lowerProductConstant period q * leibnizConvolution
        (fun l => wordSobolevNorm period 5 l f) (fun l => wordSobolevNorm period 5 l g) n := by
  induction n generalizing f g with
  | zero =>
    simpa [leibnizConvolution, lowerProductConstant, mul_assoc] using
      EulerH5CylinderAlgebra.cylinder_Hq_scalar_vector_product period (by
          norm_num : 5 ≤ 5) q f g hf hg (fun j _ w => hfL2 j w) (fun j _ w => hgL2 j w)
  | succ n ih =>
    rw [wordSobolevNorm_succ]
    calc
      _ ≤ ∑ i : Fin 4, lowerProductConstant period q *
          (leibnizConvolution
            (fun l => wordSobolevNorm period 5 l (fieldDerivative period (standardDirection i) f))
            (fun l => wordSobolevNorm period 5 l g) n +
           leibnizConvolution
            (fun l => wordSobolevNorm period 5 l f)
            (fun l => wordSobolevNorm period 5 l (fieldDerivative period (standardDirection i) g))
                n) := by
        apply Finset.sum_le_sum
        intro i _
        rw [fieldDerivative_smul period _ f g hf hg]
        have hdf := fieldDerivative_smooth period (standardDirection i) f hf
        have hdg := fieldDerivative_smooth period (standardDirection i) g hg
        have hdfL2 := derivative_all_memLp period f hfL2 i
        have hdgL2 := derivative_all_memLp period g hgL2 i
        exact (wordSobolevNorm_add_le period 5 n
          (fun x => fieldDerivative period (standardDirection i) f x • g x)
          (fun x => f x • fieldDerivative period (standardDirection i) g x)
          (fun x => (hdf x).smul (hg x))
          (fun x => (hf x).smul (hdg x))
          (product_all_memLp period q _ g hdf hg hdfL2 hgL2)
          (product_all_memLp period q f _ hf hdg hfL2 hdgL2)).trans
          ((add_le_add (ih _ _ hdf hg hdfL2 hgL2) (ih _ _ hf hdg hfL2 hdgL2)).trans_eq (mul_add
              ..).symm)
      _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib,
          sum_leibnizConvolution_left, sum_leibnizConvolution_right]
        simp_rw [← wordSobolevNorm_succ]
        rw [leibnizConvolution_succ, add_comm]

/-- One fixed coordinate derivative in H⁵ is controlled by the actual H⁶ norm. -/
theorem derivative_H5_le_H6 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : Fin 4) (f : LiftDomain period → F) :
    liftSobolevNorm period 5 (fieldDerivative period (standardDirection i) f) ≤ 1365 *
        liftSobolevNorm period 6 f := by
  have h : liftSobolevNorm period 5 (fieldDerivative period (standardDirection i) f) ≤
      ∑ r ∈ Finset.range (5+1), ∑ _w : Fin r → Fin 4, liftSobolevNorm period 6 f := by
    apply Finset.sum_le_sum
    intro r hr
    apply Finset.sum_le_sum
    intro w _
    obtain ⟨v, hv⟩ := iteratedFieldDerivative_comp_exists period w (fun _ : Fin 1 => i) f
    change (eLpNorm (iteratedFieldDerivative period w (iteratedFieldDerivative period (fun _ : Fin
        1 => i) f)) 2 (liftMeasure period)).toReal ≤ _
    rw [hv]
    exact word_L2_le_liftSobolevNorm period (by have := Finset.mem_range.mp hr; omega) v f
  apply h.trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  norm_num [Finset.sum_range_succ]
  ring

/-- Raising the external count by one while lowering the fixed base index consumes no higher Sobolev
norm. -/
theorem lower_word_shift_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    wordSobolevNorm period 5 (n+1) f ≤ 5460 * wordSobolevNorm period 6 n f := by
  rw [wordSobolevNorm_succ]
  unfold wordSobolevNorm
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w _
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
    derivative_H5_le_H6 period i (iteratedFieldDerivative period w f))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have he : (∑ i : Fin 4, liftSobolevNorm period 5
      (iteratedFieldDerivative period w (fieldDerivative period (standardDirection i) f))) =
      ∑ i : Fin 4, liftSobolevNorm period 5 (fieldDerivative period (standardDirection i)
          (iteratedFieldDerivative period w f)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [word_derivative_comm period w (standardDirection i) f hf]
  rw [he]
  exact h.trans_eq (by ring)

/-- Monotonicity in the fixed Sobolev index, at every external word order. -/
theorem wordSobolevNorm_mono {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p q : ℕ} (hpq : p ≤ q) (n : ℕ) (f : LiftDomain period → F) :
    wordSobolevNorm period p n f ≤ wordSobolevNorm period q n f :=
  Finset.sum_le_sum fun _ _ => liftSobolevNorm_mono period hpq _

/-- The actual transport source in the lower fixed Sobolev norm. -/
theorem transport_wordH5Norm_bound (q n : ℕ)
    (b : LiftDomain period → Domain 4) (e : LiftDomain period → Domain q)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hbL2 : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w b) 2 (liftMeasure
        period))
    (heL2 : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w e) 2 (liftMeasure
        period)) :
    wordSobolevNorm period 5 n (transportField period q b e) ≤
      lowerProductConstant period q * leibnizConvolution
        (fun l => wordSobolevNorm period 5 l b) (fun l => wordSobolevNorm period 5 (l + 1) e) n :=
            by
  have hbi (i : Fin 4) := postcomp_smooth period (coordinate 4 i) b hb
  have hbiL2 (i : Fin 4) : ∀ j, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w (coordinate 4 i ∘ b)) 2 (liftMeasure period) :=
    fun j w => postcomp_word_memLp period (show j ≤ j by omega) _ b hb (fun r _ v => hbL2 r v) w
  have hs := wordSobolevNorm_sum_le period Finset.univ 5 n
    (fun i x => b x i • fieldDerivative period (standardDirection i) e x)
    (fun i _ x => (hbi i x).smul (fieldDerivative_smooth period _ e he x))
    (fun i _ => product_all_memLp period q (coordinate 4 i ∘ b) _ (hbi i)
      (fieldDerivative_smooth period _ e he) (hbiL2 i) (derivative_all_memLp period e heL2 i))
  apply hs.trans
  calc
    _ ≤ ∑ i : Fin 4, lowerProductConstant period q * leibnizConvolution
        (fun l => wordSobolevNorm period 5 l b)
        (fun l => wordSobolevNorm period 5 l (fieldDerivative period (standardDirection i) e)) n :=
            by
      apply Finset.sum_le_sum
      intro i _
      have hp := product_wordH5Norm_bound period q n (coordinate 4 i ∘ b) _ (hbi i)
        (fieldDerivative_smooth period _ e he) (hbiL2 i) (derivative_all_memLp period e heL2 i)
      apply hp.trans
      apply mul_le_mul_of_nonneg_left _ (lowerProductConstant_nonneg period q)
      apply Finset.sum_le_sum
      intro l _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (wordSobolevNorm_postcomp_le period 5 l (coordinate 4 i) (coordinate_norm_le 4 i) b hb
              hbL2)
          (Nat.cast_nonneg _)) (wordSobolevNorm_nonneg period 5 (n-l) _)
    _ = _ := by
      rw [← Finset.mul_sum, sum_leibnizConvolution_right]
      simp_rw [← wordSobolevNorm_succ]

/-- The pressure's H⁵ source uses only H⁶ velocity at the same external order. -/
theorem transport_lower_no_loss (n : ℕ)
    (b : LiftDomain period → Domain 4) (e : LiftDomain period → Vector3)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hbL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w b) 2 (liftMeasure
        period))
    (heL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w e) 2 (liftMeasure
        period)) :
    wordSobolevNorm period 5 n (transportField period 3 b e) ≤
      (5460 * lowerProductConstant period 3) * leibnizConvolution
        (fun l => wordSobolevNorm period 6 l b) (fun l => wordSobolevNorm period 6 l e) n := by
  apply (transport_wordH5Norm_bound period 3 n b e hb he hbL heL).trans
  have hconv : leibnizConvolution (fun l => wordSobolevNorm period 5 l b)
      (fun l => wordSobolevNorm period 5 (l+1) e) n ≤
      5460 * leibnizConvolution (fun l => wordSobolevNorm period 6 l b) (fun l => wordSobolevNorm
          period 6 l e) n := by
    unfold leibnizConvolution
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    have h := mul_le_mul
      (mul_le_mul_of_nonneg_left (wordSobolevNorm_mono period (by
          norm_num : 5 ≤ 6) l b) (Nat.cast_nonneg (n.choose l)))
      (lower_word_shift_le period (n-l) e he) (wordSobolevNorm_nonneg period 5 (n-l+1) e)
      (mul_nonneg (Nat.cast_nonneg (n.choose l)) (wordSobolevNorm_nonneg period 6 l b))
    exact h.trans_eq (by ring)
  exact (mul_le_mul_of_nonneg_left hconv (lowerProductConstant_nonneg period 3)).trans_eq (by ring)

end EulerH6Nonlinear
