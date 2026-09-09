/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.H5RealCylinderAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.H6NonlinearProduct

@[expose] public section

/-! Mixed derivative product estimates with only five total derivatives, for the base transport
  commutator. -/

noncomputable section

namespace EulerMixedH5Product

open MeasureTheory EulerSobolev EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives
  EulerCylinderSobolev EulerRealCylinder EulerVectorCylinder EulerGeneralCylinderAlgebra
    EulerH6Nonlinear
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- An explicit uniform constant for mixed scalar-vector derivative products through total order five. -/
def mixedConstant : ℝ := 3 * 85 * cylinderEmbeddingConstant period

theorem mixedConstant_nonneg : 0 ≤ mixedConstant period := by
  unfold mixedConstant
  exact mul_nonneg (by norm_num) (cylinderEmbeddingConstant_nonneg period)

/-- Low scalar derivatives are bounded by the original H⁵ norm. -/
theorem scalar_word_pointwise {k : ℕ} (hk : k ≤ 2) (w : Fin k → Fin 4)
    (f : LiftDomain period → ℝ) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL : ∀ j ≤ 5, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure
      period))
    (x : LiftDomain period) :
    ‖iteratedFieldDerivative period w f x‖ ≤ mixedConstant period * liftSobolevNorm period 5 f := by
  have h := real_cylinder_pointwise_le_H3 period (iteratedFieldDerivative period w f)
    (iteratedFieldDerivative_smooth period w f hf)
    (fun j hj v => word_memLp period (by omega : k+j ≤ 5) v w f hfL) x
  have h2 := mul_le_mul_of_nonneg_left (word_H3_le_Hq period (by omega : k+3 ≤ 5) w f)
    (cylinderEmbeddingConstant_nonneg period)
  apply h.trans (h2.trans _)
  unfold mixedConstant
  have hpos := mul_nonneg (cylinderEmbeddingConstant_nonneg period) (liftSobolevNorm_nonneg period
    5 f)
  nlinarith

/-- Low vector derivatives are bounded by the original H⁵ norm. -/
theorem vector_word_pointwise {k : ℕ} (hk : k ≤ 2) (w : Fin k → Fin 4)
    (f : LiftDomain period → Vector3) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL : ∀ j ≤ 5, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure
      period))
    (x : LiftDomain period) :
    ‖iteratedFieldDerivative period w f x‖ ≤ mixedConstant period * liftSobolevNorm period 5 f := by
  have h := vector_cylinder_pointwise_le_H3 period 3 (iteratedFieldDerivative period w f)
    (iteratedFieldDerivative_smooth period w f hf)
    (fun j hj v => word_memLp period (by omega : k+j ≤ 5) v w f hfL) x
  have h2 := mul_le_mul_of_nonneg_left (word_H3_le_Hq period (by omega : k+3 ≤ 5) w f)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (cylinderEmbeddingConstant_nonneg period))
  exact h.trans (h2.trans_eq (by unfold mixedConstant; ring))

/-- An actual pointwise L² domination gives both integrability and the corresponding norm estimate. -/
theorem memLp_norm_of_domination {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : LiftDomain period → E) (g : LiftDomain period → F) (c : ℝ) (hc : 0 ≤ c)
    (hf : AEStronglyMeasurable f (liftMeasure period)) (hg : MemLp g 2 (liftMeasure period))
    (h : ∀ᵐ x ∂liftMeasure period, ‖f x‖ ≤ c*‖g x‖) :
    MemLp f 2 (liftMeasure period) ∧
      (eLpNorm f 2 (liftMeasure period)).toReal ≤ c*(eLpNorm g 2 (liftMeasure period)).toReal := by
  have hm := hg.of_le_mul hf h
  refine ⟨hm, ?_⟩
  have hh := eLpNorm_le_mul_eLpNorm_of_ae_le_mul h (2 : ℝ≥0∞)
  have hfin : ENNReal.ofReal c * eLpNorm g 2 (liftMeasure period) ≠ ⊤ := by finiteness
  have hh' := ENNReal.toReal_mono hfin hh
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] using hh'

/-- The literal product of two derivative words with at most five total derivatives is in L² with a fixed H⁵ bound. -/
theorem mixed_product_bound {k l : ℕ} (hkl : k+l ≤ 5)
    (w : Fin k → Fin 4) (v : Fin l → Fin 4)
    (f : LiftDomain period → ℝ) (g : LiftDomain period → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL : ∀ j ≤ 5, ∀ u : Fin j → Fin 4, MemLp (iteratedFieldDerivative period u f) 2 (liftMeasure
      period))
    (hgL : ∀ j ≤ 5, ∀ u : Fin j → Fin 4, MemLp (iteratedFieldDerivative period u g) 2 (liftMeasure
      period)) :
    MemLp (fun x => iteratedFieldDerivative period w f x • iteratedFieldDerivative period v g x) 2
      (liftMeasure period) ∧
    (eLpNorm (fun x => iteratedFieldDerivative period w f x • iteratedFieldDerivative period v g x)
      2 (liftMeasure period)).toReal ≤ mixedConstant period * liftSobolevNorm period 5 f *
        liftSobolevNorm period 5 g := by
  have hmeas : AEStronglyMeasurable (fun x => iteratedFieldDerivative period w f x •
    iteratedFieldDerivative period v g x)
      (liftMeasure period) :=
    ((smoothField_continuous period _ (iteratedFieldDerivative_smooth period w f hf)).smul
      (smoothField_continuous period _ (iteratedFieldDerivative_smooth period v g
        hg))).aestronglyMeasurable
  by_cases hk : k ≤ 2
  · have h := memLp_norm_of_domination period _ (iteratedFieldDerivative period v g)
      (mixedConstant period * liftSobolevNorm period 5 f)
      (mul_nonneg (mixedConstant_nonneg period) (liftSobolevNorm_nonneg period 5 f)) hmeas (hgL l
        (by omega) v)
      (Filter.Eventually.of_forall (fun x => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (scalar_word_pointwise period hk w f hf hfL x)
          (norm_nonneg _)))
    exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_left (word_L2_le_liftSobolevNorm period (by omega :
      l ≤ 5) v g)
      (mul_nonneg (mixedConstant_nonneg period) (liftSobolevNorm_nonneg period 5 f)))⟩
  · have hl : l ≤ 2 := by omega
    have h := memLp_norm_of_domination period _ (iteratedFieldDerivative period w f)
      (mixedConstant period * liftSobolevNorm period 5 g)
      (mul_nonneg (mixedConstant_nonneg period) (liftSobolevNorm_nonneg period 5 g)) hmeas (hfL k
        (by omega) w)
      (Filter.Eventually.of_forall (fun x => by
        rw [norm_smul]
        exact (mul_le_mul_of_nonneg_left (vector_word_pointwise period hl v g hg hgL x)
          (norm_nonneg _)).trans_eq (mul_comm _ _)))
    refine ⟨h.1, h.2.trans ?_⟩
    exact (mul_le_mul_of_nonneg_left (word_L2_le_liftSobolevNorm period (by omega : k ≤ 5) w f)
      (mul_nonneg (mixedConstant_nonneg period) (liftSobolevNorm_nonneg period 5 g))).trans_eq (by
        ring)

/-- The real L² norm obeys the triangle inequality whenever both actual fields are square-integrable. -/
theorem fieldL2_add_le {E : Type*} [NormedAddCommGroup E]
    (f g : LiftDomain period → E) (hf : MemLp f 2 (liftMeasure period)) (hg : MemLp g 2
      (liftMeasure period)) :
    (eLpNorm (f+g) 2 (liftMeasure period)).toReal ≤
      (eLpNorm f 2 (liftMeasure period)).toReal+(eLpNorm g 2 (liftMeasure period)).toReal := by
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩)
    (eLpNorm_add_le hf.1 hg.1 (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  simpa only [ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top] using h

end EulerMixedH5Product
