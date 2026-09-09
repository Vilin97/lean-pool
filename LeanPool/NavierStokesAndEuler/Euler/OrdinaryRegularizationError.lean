/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryRegularizer
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryRegularizedFlow
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryH3Commutator

@[expose] public section

/-! The actual regularized Euler right-hand side converges to the
projected Euler right-hand side, uniformly on bounded H⁴ sets. -/

noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
  EulerSmoothSobolev Finset
open scoped ContDiff Topology

theorem regularizer_error_words (n : ℕ) (A : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) (q : ℕ) (M : ℝ) (hM : WordBound (q+1) M A) :
    WordBound q (regularizerError n*M) (fieldSub ((regularizer n).field A.toLp) A) := by
  intro k hk w
  simp only [fieldSub,wordField_add,wordField_neg,toLp_addField,toLp_fieldNeg,
    SmoothingOperator.field_word,← sub_eq_add_neg]
  have hp : solenoidalProjection (wordField A w).toLp=(wordField A w).toLp :=
    solenoidalSpace.starProjection_eq_self_iff.mpr (word_solenoidal A hA w)
  have h := regularizer_error_wordBound n (wordField A w) M
    (wordBound_wordField (wordBound_mono hM (by omega : k+1 ≤ q+1)) w)
  simpa only [hp] using h

theorem wordBound_gradient {A : SmoothL2Field Space} {M : ℝ} (hM : WordBound 3 M A)
    (x : Space) : ‖fderiv ℝ A.field x‖ ≤ (360*smoothEmbeddingConstant)*M := by
  have h := real_smooth_fderiv_le_H3 3 A.field A.smooth (fun j _ => A.integrable j) x
  rw [← tensorNorm_eq] at h
  exact (h.trans (mul_le_mul_of_nonneg_left (tensorNorm_three_le A M hM)
    (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg))).trans_eq (by ring)

theorem advection_low_words (A : SmoothL2Field Space) (M : ℝ) (hM : WordBound 4 M A) :
    WordBound 1 (6*h3ProductConstant*M^2) (advectionField A A) := by
  intro k hk w
  apply (source_advection_outer A A M M (wordBound_mono hM (by omega)) hM (by omega) w).trans
  have hcoef : 3*(2 : ℝ)^k ≤ 6 := by interval_cases k <;> norm_num
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef h3ProductConstant_nonneg) (wordBound_nonneg hM))
    (wordBound_nonneg hM)).trans_eq (by ring)

def regularizationCost (M : ℝ) : ℝ := (6*h3ProductConstant+399*smoothEmbeddingConstant)*M^2

theorem regularizationCost_nonneg (M : ℝ) : 0 ≤ regularizationCost M := by
  have := h3ProductConstant_nonneg
  have := smoothEmbeddingConstant_nonneg
  unfold regularizationCost
  positivity

theorem regularized_rhs_error (n : ℕ) (A : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) (M : ℝ) (hM : WordBound 4 M A) :
    ‖((regularizer n).rhs A.toLp).toLp-(projectedRhs A).toLp‖ ≤
      regularizerError n*regularizationCost M := by
  let S := regularizer n
  let B := S.field A.toLp
  have hB : WordBound 4 M B := S.field_wordBound A 4 M hM
  have he := regularizer_error_words n A hA 1 M (wordBound_mono hM (by omega))
  have he0 : ‖B.toLp-A.toLp‖ ≤ regularizerError n*M := by
    simpa only [toLp_fieldSub] using wordBound_toLp he
  have he1 : ‖B.jetLp 1-A.jetLp 1‖ ≤ 3*(regularizerError n*M) := by
    simpa only [jetLp_fieldSub,pow_one] using wordBound_jet_norm he (le_refl 1)
  have hadv : ‖(advectionField B B).toLp-(advectionField A A).toLp‖ ≤
      ((360*smoothEmbeddingConstant)*M)*(regularizerError n*M)+
      ((13*smoothEmbeddingConstant)*M)*(3*(regularizerError n*M)) := by
    apply (advection_sub_norm B A _ _ (wordBound_gradient (wordBound_mono hB (by omega)))
      (wordBound_pointwise (wordBound_mono hM (by omega)))).trans
    exact add_le_add (mul_le_mul_of_nonneg_left he0
      (mul_nonneg (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg) (wordBound_nonneg hM)))
      (mul_le_mul_of_nonneg_left he1
      (mul_nonneg (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg) (wordBound_nonneg hM)))
  have hp := regularizer_error_wordBound n (advectionField B B) _ (advection_low_words B M hB)
  have hq : ‖solenoidalProjection (advectionField B B).toLp-
      solenoidalProjection (advectionField A A).toLp‖ ≤
      ‖(advectionField B B).toLp-(advectionField A A).toLp‖ := by
    rw [← map_sub]
    exact solenoidalProjection_apply_norm_le _
  have heq : ((regularizer n).rhs A.toLp).toLp-(projectedRhs A).toLp=
      -(S.op (advectionField B B).toLp-solenoidalProjection (advectionField A A).toLp) := by
    simp only [SmoothingOperator.rhs_toLp,SmoothingOperator.quadratic_apply,projectedRhs_toLp,S,B]
    abel
  rw [heq,norm_neg]
  apply (norm_sub_le_norm_sub_add_norm_sub (S.op (advectionField B B).toLp)
    (solenoidalProjection (advectionField B B).toLp)
    (solenoidalProjection (advectionField A A).toLp)).trans
  exact (add_le_add hp (hq.trans hadv)).trans_eq (by unfold regularizationCost; ring)

end EulerOrdinarySobolev
