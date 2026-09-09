/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.H5RealCylinderAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.ExternalTransportCommutator

@[expose] public section

/-! Actual lower-base Sobolev bounds for the transport pressure, without an external derivative
  loss. -/

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
      EulerH5CylinderAlgebra.cylinder_Hq_scalar_vector_product period (by norm_num : 5 ≤ 5) q f g
        hf hg (fun j _ w => hfL2 j w) (fun j _ w => hgL2 j w)
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

/-- Raising the external count by one while lowering the fixed base index consumes no higher Sobolev norm. -/
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
      (mul_le_mul_of_nonneg_left (wordSobolevNorm_mono period (by norm_num : 5 ≤ 6) l b)
        (Nat.cast_nonneg (n.choose l)))
      (lower_word_shift_le period (n-l) e he) (wordSobolevNorm_nonneg period 5 (n-l+1) e)
      (mul_nonneg (Nat.cast_nonneg (n.choose l)) (wordSobolevNorm_nonneg period 6 l b))
    exact h.trans_eq (by ring)
  exact (mul_le_mul_of_nonneg_left hconv (lowerProductConstant_nonneg period 3)).trans_eq (by ring)

end EulerH6Nonlinear
