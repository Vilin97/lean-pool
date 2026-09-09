/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderAlgebra
import LeanPool.NavierStokesAndEuler.Euler.Foundations.RealCylinder
import LeanPool.NavierStokesAndEuler.Euler.Foundations.SobolevDerivativeNorm

/-! Real Euclidean vector wrappers for the actual cylinder Sobolev estimates. -/

@[expose] public section

noncomputable section

namespace EulerVectorCylinder

open MeasureTheory EulerSobolev EulerSobolevDerivativeNorm EulerRealCylinder
open EulerCylinderSobolev EulerCylinderAlgebra EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives
open scoped ENNReal NNReal ContDiff

variable (period : ℝ) [Fact (0 < period)]

section Postcomposition
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [Fact (0 < period)] in
theorem postcomp_smooth (L : F →L[ℝ] G) (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (L ∘ f) x) := fun x => L.contDiff.comp (hf x)

theorem postcomp_word_memLp {s n : ℕ} (hn : n ≤ s) (L : F →L[ℝ] G)
    (f : LiftDomain period → F) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ s, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) (w : Fin n → Fin 4) :
    MemLp (iteratedFieldDerivative period w (L ∘ f)) 2 (liftMeasure period) := by
  rw [iteratedFieldDerivative_postcomp period L w f hf]
  exact L.comp_memLp' (hfL2 n hn w)

theorem postcomp_sobolevNorm_le (s : ℕ) (L : F →L[ℝ] G) (hL : ‖L‖ ≤ 1)
    (f : LiftDomain period → F) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ s, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) :
    liftSobolevNorm period s (L ∘ f) ≤ liftSobolevNorm period s f := by
  apply Finset.sum_le_sum
  intro n hn
  apply Finset.sum_le_sum
  intro w _
  rw [iteratedFieldDerivative_postcomp period L w f hf]
  apply ENNReal.toReal_mono (hfL2 n (by have := Finset.mem_range.1 hn; omega) w).eLpNorm_ne_top
  apply eLpNorm_mono
  intro x
  have h := L.le_opNorm (iteratedFieldDerivative period w f x)
  exact h.trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq (one_mul _))

end Postcomposition

/-- A coordinate projection on a real Euclidean target, of operator norm at most one. -/
noncomputable def coordinate (q : ℕ) (i : Fin q) : Domain q →L[ℝ] ℝ := EuclideanSpace.proj i

theorem coordinate_norm_le (q : ℕ) (i : Fin q) : ‖coordinate q i‖ ≤ 1 := by
  apply (coordinate q i).opNorm_le_bound (by norm_num)
  intro x
  change ‖x i‖ ≤ 1 * ‖x‖
  simpa only [one_mul] using PiLp.norm_apply_le x i

/-- H³ controls the pointwise norm of a genuine real Euclidean cylinder field. -/
theorem vector_cylinder_pointwise_le_H3 (q : ℕ) (f : LiftDomain period → Domain q)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ 3, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖f x‖ ≤ ((q : ℝ) * cylinderEmbeddingConstant period) * liftSobolevNorm period 3 f := by
  have hA := norm_le_sum_coordinates q (f x)
  have hB (i : Fin q) : ‖f x i‖ ≤ cylinderEmbeddingConstant period * liftSobolevNorm period 3 f :=
      by
    have h := real_cylinder_pointwise_le_H3 period (coordinate q i ∘ f)
      (postcomp_smooth period _ f hf) (fun j hj w => postcomp_word_memLp period hj _ f hf hfL2 w) x
    exact h.trans (mul_le_mul_of_nonneg_left
      (postcomp_sobolevNorm_le period 3 _ (coordinate_norm_le q i) f hf hfL2)
      (cylinderEmbeddingConstant_nonneg period))
  have hC := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => hB i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hC
  exact hA.trans (hC.trans_eq (mul_assoc _ _ _).symm)

omit [Fact (0 < period)] in
/-- The coordinate of a classical derivative is the derivative of the coordinate. -/
theorem coordinate_word {n : ℕ} (q : ℕ) (i : Fin q) (w : Fin n → Fin 4)
    (f : LiftDomain period → Domain q) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x :
        LiftDomain period) :
    iteratedFieldDerivative period w (coordinate q i ∘ f) x = iteratedFieldDerivative period w f x
        i := by
  rw [iteratedFieldDerivative_postcomp period _ w f hf]
  rfl

theorem vector_eLpNorm_le_sum_coordinates (q : ℕ) (f : LiftDomain period → Domain q)
    (hf : ∀ i : Fin q, MemLp (fun x => f x i) 2 (liftMeasure period)) :
    eLpNorm f 2 (liftMeasure period) ≤ ∑ i : Fin q, eLpNorm (fun x => f x i) 2 (liftMeasure period)
        := by
  have hA : eLpNorm f 2 (liftMeasure period) ≤
      eLpNorm (fun x => ∑ i : Fin q, ‖f x i‖) 2 (liftMeasure period) := by
    apply eLpNorm_mono
    intro x
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    exact norm_le_sum_coordinates q (f x)
  have he : (fun x => ∑ i : Fin q, ‖f x i‖) = ∑ i : Fin q, (fun x => ‖f x i‖) := by
    funext x
    simp
  rw [he] at hA
  have hB := eLpNorm_sum_le
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => (hf i).1.norm) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  simpa only [eLpNorm_norm] using hA.trans hB

theorem vector_word_L2_le_sum_coordinates {s n : ℕ} (hn : n ≤ s) (q : ℕ) (w : Fin n → Fin 4)
    (f : LiftDomain period → Domain q) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ i : Fin q, ∀ j ≤ s, ∀ v : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period v (coordinate q i ∘ f)) 2 (liftMeasure period)) :
    (eLpNorm (iteratedFieldDerivative period w f) 2 (liftMeasure period)).toReal ≤
      ∑ i : Fin q, (eLpNorm (iteratedFieldDerivative period w (coordinate q i ∘ f)) 2 (liftMeasure
          period)).toReal := by
  have hc (i : Fin q) : MemLp (fun x => iteratedFieldDerivative period w f x i) 2 (liftMeasure
      period) := by
    have h := hfL2 i n hn w
    rw [iteratedFieldDerivative_postcomp period _ w f hf] at h
    exact h
  have hA := vector_eLpNorm_le_sum_coordinates period q (iteratedFieldDerivative period w f) hc
  have hfin : (∑ i : Fin q, eLpNorm (fun x => iteratedFieldDerivative period w f x i) 2
      (liftMeasure period)) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 (fun i _ => (hc i).eLpNorm_ne_top)
  have hB := ENNReal.toReal_mono hfin hA
  rw [ENNReal.toReal_sum (fun i _ => (hc i).eLpNorm_ne_top)] at hB
  have he (i : Fin q) : (fun x => iteratedFieldDerivative period w f x i) =
      iteratedFieldDerivative period w (coordinate q i ∘ f) := by
    funext x
    exact (coordinate_word period q i w f hf x).symm
  simp_rw [he] at hB
  exact hB

/-- A vector Sobolev norm is controlled by the sum of its scalar coordinate norms. -/
theorem vector_sobolevNorm_le_sum_coordinates (q s : ℕ) (f : LiftDomain period → Domain q)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ i : Fin q, ∀ j ≤ s, ∀ v : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period v (coordinate q i ∘ f)) 2 (liftMeasure period)) :
    liftSobolevNorm period s f ≤ ∑ i : Fin q, liftSobolevNorm period s (coordinate q i ∘ f) := by
  have hA : liftSobolevNorm period s f ≤
      ∑ n ∈ Finset.range (s+1), ∑ w : Fin n → Fin 4, ∑ i : Fin q,
        (eLpNorm (iteratedFieldDerivative period w (coordinate q i ∘ f)) 2 (liftMeasure
            period)).toReal := by
    apply Finset.sum_le_sum
    intro n hn
    apply Finset.sum_le_sum
    intro w _
    exact vector_word_L2_le_sum_coordinates period (by
        have := Finset.mem_range.1 hn; omega) q w f hf hfL2
  apply hA.trans_eq
  calc
    _ = ∑ n ∈ Finset.range (s+1), ∑ i : Fin q, ∑ w : Fin n → Fin 4,
        (eLpNorm (iteratedFieldDerivative period w (coordinate q i ∘ f)) 2 (liftMeasure
            period)).toReal := by
      apply Finset.sum_congr rfl
      intro n _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

theorem real_product_word_memLp {n : ℕ} (hn : n ≤ 6) (w : Fin n → Fin 4)
    (f g : LiftDomain period → ℝ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ j ≤ 6, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure
        period))
    (hgL2 : ∀ j ≤ 6, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure
        period)) :
    MemLp (iteratedFieldDerivative period w (f*g)) 2 (liftMeasure period) := by
  have h := product_word_memLp period hn w (complexField period f) (complexField period g)
    (complexField_smooth period f hf) (complexField_smooth period g hg)
    (fun j hj v => by
        rw [complexField_word period v f hf]; exact complexField_memLp period _ (hfL2 j hj v))
    (fun j hj v => by
        rw [complexField_word period v g hg]; exact complexField_memLp period _ (hgL2 j hj v))
  have he : complexField period f * complexField period g = complexField period (f*g) := by
    ext x
    exact (Complex.ofReal_mul _ _).symm
  rw [he, complexField_word period w (f*g) (fun x => (hf x).mul (hg x))] at h
  apply h.of_le
    ((smoothField_continuous period _ (iteratedFieldDerivative_smooth period w (f*g)
      (fun x => (hf x).mul (hg x)))).aestronglyMeasurable)
  filter_upwards [] with x
  exact (Complex.norm_real _).ge

omit [Fact (0 < period)] in
theorem coordinate_smul (q : ℕ) (i : Fin q) (f : LiftDomain period → ℝ) (g : LiftDomain period →
    Domain q) :
    coordinate q i ∘ (fun x => f x • g x) = f * (coordinate q i ∘ g) := by
  funext x
  simp [Function.comp_def, map_smul, smul_eq_mul]

/-- Multiplication of an actual vector field by a scalar field is bounded in H⁶. -/
theorem cylinder_H6_scalar_vector_product (q : ℕ) (f : LiftDomain period → ℝ)
    (g : LiftDomain period → Domain q)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ j ≤ 6, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure
        period))
    (hgL2 : ∀ j ≤ 6, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure
        period)) :
    liftSobolevNorm period 6 (fun x => f x • g x) ≤
      ((q : ℝ) * (5461 * 128 * lowDerivativeConstant period)) *
        liftSobolevNorm period 6 f * liftSobolevNorm period 6 g := by
  have hs : ∀ x, ContDiff ℝ ∞ (localFieldLift period (fun x => f x • g x) x) :=
    fun x => (hf x).smul (hg x)
  have hcomp (i : Fin q) : ∀ j ≤ 6, ∀ v : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period v (coordinate q i ∘ g)) 2 (liftMeasure period) :=
    fun j hj v => postcomp_word_memLp period hj _ g hg hgL2 v
  have hA := vector_sobolevNorm_le_sum_coordinates period q 6 (fun x => f x • g x) hs
    (fun i j hj v => by
      rw [coordinate_smul]
      exact real_product_word_memLp period hj v f (coordinate q i ∘ g) hf
        (postcomp_smooth period _ g hg) hfL2 (hcomp i))
  have hB (i : Fin q) : liftSobolevNorm period 6 (coordinate q i ∘ (fun x => f x • g x)) ≤
      (5461 * 128 * lowDerivativeConstant period) * liftSobolevNorm period 6 f * liftSobolevNorm
          period 6 g := by
    rw [coordinate_smul]
    have h := real_cylinder_H6_algebra period f (coordinate q i ∘ g) hf (postcomp_smooth period _ g
        hg) hfL2 (hcomp i)
    exact h.trans (mul_le_mul_of_nonneg_left
      (postcomp_sobolevNorm_le period 6 _ (coordinate_norm_le q i) g hg hgL2)
      (mul_nonneg (mul_nonneg (by
          norm_num) (lowDerivativeConstant_nonneg period)) (liftSobolevNorm_nonneg period 6 f)))
  have hC := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => hB i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hC
  have he (q C A B : ℝ) : q*(C*A*B) = (q*C)*A*B := by ring
  exact hA.trans (hC.trans_eq (he _ _ _ _))

end EulerVectorCylinder
