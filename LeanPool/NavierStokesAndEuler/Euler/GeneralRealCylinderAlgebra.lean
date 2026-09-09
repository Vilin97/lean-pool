/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GeneralCylinderAlgebra
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

@[expose] public section

/-! Actual real and scalar-vector cylinder multiplication at every fixed Sobolev order q≥6. -/

noncomputable section

namespace EulerGeneralCylinderAlgebra

open MeasureTheory EulerSobolev EulerCylinderSobolev EulerLiftedGradientSpace EulerMetricTransport
  EulerRealCylinder EulerVectorCylinder
open scoped ENNReal NNReal ContDiff Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual real cylinder algebra estimate at every fixed order q≥6. -/
theorem real_cylinder_Hq_algebra {q : ℕ} (hq : 6 ≤ q) (f g : LiftDomain period → ℝ)
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
    (fun j hj w => by rw [complexField_word period w f hf]; exact complexField_memLp period _ (hfL2
      j hj w))
    (fun j hj w => by rw [complexField_word period w g hg]; exact complexField_memLp period _ (hgL2
      j hj w))
  have he : complexField period f * complexField period g = complexField period (f * g) := by
    ext x
    exact (Complex.ofReal_mul _ _).symm
  rw [he, complexField_sobolevNorm period q (f * g) (fun x => (hf x).mul (hg x)),
    complexField_sobolevNorm period q f hf, complexField_sobolevNorm period q g hg] at h
  exact h

/-- Every real product derivative through order q is genuinely square-integrable. -/
theorem real_product_word_memLp {q n : ℕ} (hq : 6 ≤ q) (hn : n ≤ q) (w : Fin n → Fin 4)
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
    (fun j hj v => by rw [complexField_word period v f hf]; exact complexField_memLp period _ (hfL2
      j hj v))
    (fun j hj v => by rw [complexField_word period v g hg]; exact complexField_memLp period _ (hgL2
      j hj v))
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
theorem scalar_vector_product_word_memLp {q n : ℕ} (hq : 6 ≤ q) (hn : n ≤ q) (d : ℕ)
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

/-- Multiplication of an actual vector field by a scalar field is bounded in every Hq, q≥6. -/
theorem cylinder_Hq_scalar_vector_product {q : ℕ} (hq : 6 ≤ q) (d : ℕ)
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

end EulerGeneralCylinderAlgebra
