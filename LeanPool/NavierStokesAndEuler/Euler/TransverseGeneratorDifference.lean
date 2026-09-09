/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointBounds
public import LeanPool.NavierStokesAndEuler.Euler.TransverseForwardInverse
public import LeanPool.NavierStokesAndEuler.Euler.TransverseStrongEstimates

@[expose] public section

/-! Polynomial size and coefficient sensitivity of the actual source (10) generator. -/

noncomputable section


namespace EulerTransverseGeneratorDifference

open Set ContinuousLinearMap InnerProductSpace
  EulerTransverseGramInverse EulerTransverseGramPath EulerTransverseStrongEstimates
  EulerTransverseForwardInverse EulerCoerciveEndpointBounds EulerCoerciveProjection

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gram_sub_norm_le (A B : U →L[ℝ] E) (q : ℝ)
    (hA : ‖A‖ ≤ q) (hB : ‖B‖ ≤ q) :
    ‖gram A - gram B‖ ≤ 2 * q * ‖A-B‖ := by
  have hq := (norm_nonneg A).trans hA
  have had : ‖A.adjoint-B.adjoint‖ = ‖A-B‖ := by
    rw [← map_sub, LinearIsometryEquiv.norm_map]
  apply (norm_comp_sub_le A.adjoint B.adjoint A B).trans
  rw [had, LinearIsometryEquiv.norm_map]
  exact (add_le_add (mul_le_mul_of_nonneg_left hA (norm_nonneg _))
    (mul_le_mul_of_nonneg_right hB (norm_nonneg _))).trans_eq (by ring)

theorem gramInverse_sub_norm_le (A B : U →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hA : ∀ u, c * ‖u‖^2 ≤ ‖A u‖^2) (hB : ∀ u, c * ‖u‖^2 ≤ ‖B u‖^2)
    (q : ℝ) (hAn : ‖A‖ ≤ q) (hBn : ‖B‖ ≤ q) :
    ‖gramInverse A c hc hA - gramInverse B c hc hB‖ ≤
      2 * (c⁻¹)^2 * q * ‖A-B‖ := by
  have hh := coerciveInverse_norm_sub_le (gram A) (gram B) c c hc hc
    (gram_coercive A c hA) (gram_coercive B c hB)
  have hgram : ‖gram B-gram A‖ ≤ 2*q*‖A-B‖ :=
    (norm_sub_rev _ _).trans_le (gram_sub_norm_le A B q hAn hBn)
  exact hh.trans ((mul_le_mul_of_nonneg_left hgram (by positivity)).trans_eq (by ring))

variable (T : ℝ) (Q Q₁ P P₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c)
  (hQ : ∀ t u, c * ‖u‖^2 ≤ ‖Q t u‖^2)
  (hP : ∀ t u, c * ‖u‖^2 ≤ ‖P t u‖^2)

theorem generator_norm_le (q r : ℝ) (hQn : ‖Q‖ ≤ q) (hQ₁n : ‖Q₁‖ ≤ r) :
    ‖generator T Q Q₁ c hc hQ‖ ≤ 2 * c⁻¹ * q * r := by
  have hq := (norm_nonneg Q).trans hQn
  have hr := (norm_nonneg Q₁).trans hQ₁n
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro t
  change ‖(-2 : ℝ) • (gramInverse (Q t) c hc (hQ t)).comp ((Q t).adjoint.comp (Q₁ t))‖ ≤ _
  rw [norm_smul]
  norm_num only [Real.norm_eq_abs]
  have hprod : ‖(Q t).adjoint.comp (Q₁ t)‖ ≤ q*r := by
    apply (opNorm_comp_le _ _).trans
    rw [LinearIsometryEquiv.norm_map]
    exact mul_le_mul ((Q.norm_coe_le_norm t).trans hQn)
      ((Q₁.norm_coe_le_norm t).trans hQ₁n) (norm_nonneg _) hq
  apply (mul_le_mul_of_nonneg_left ((opNorm_comp_le _ _).trans
    (mul_le_mul (gramInverse_norm (Q t) c hc (hQ t)) hprod
      (norm_nonneg _) (inv_nonneg.mpr hc.le))) (by norm_num)).trans_eq
  ring

/-- Only frame differences occur in the genuine generator difference. -/
def generatorDifferenceCost (c q r δq δr : ℝ) : ℝ :=
  (4*(c⁻¹)^2*q^2*r + 2*c⁻¹*r)*δq + 2*c⁻¹*q*δr

theorem generator_sub_norm_le (q r : ℝ)
    (hQn : ‖Q‖ ≤ q) (hPn : ‖P‖ ≤ q) (hQ₁n : ‖Q₁‖ ≤ r) (_hP₁n : ‖P₁‖ ≤ r) :
    ‖generator T Q Q₁ c hc hQ - generator T P P₁ c hc hP‖ ≤
      generatorDifferenceCost c q r ‖Q-P‖ ‖Q₁-P₁‖ := by
  have hq := (norm_nonneg Q).trans hQn
  have hr := (norm_nonneg Q₁).trans hQ₁n
  have hcost : 0 ≤ generatorDifferenceCost c q r ‖Q-P‖ ‖Q₁-P₁‖ := by
    unfold generatorDifferenceCost
    positivity
  apply (ContinuousMap.norm_le _ hcost).2
  intro t
  have htQ : ‖Q t‖ ≤ q := (Q.norm_coe_le_norm t).trans hQn
  have htP : ‖P t‖ ≤ q := (P.norm_coe_le_norm t).trans hPn
  have htQ₁ : ‖Q₁ t‖ ≤ r := (Q₁.norm_coe_le_norm t).trans hQ₁n
  have hδQ : ‖Q t-P t‖ ≤ ‖Q-P‖ := (Q-P).norm_coe_le_norm t
  have hδQ₁ : ‖Q₁ t-P₁ t‖ ≤ ‖Q₁-P₁‖ := (Q₁-P₁).norm_coe_le_norm t
  have hI : ‖gramInverse (Q t) c hc (hQ t) - gramInverse (P t) c hc (hP t)‖ ≤
      2*(c⁻¹)^2*q*‖Q-P‖ :=
    (gramInverse_sub_norm_le (Q t) (P t) c hc (hQ t) (hP t) q htQ htP).trans
      (mul_le_mul_of_nonneg_left hδQ (by positivity))
  have hprod : ‖(Q t).adjoint.comp (Q₁ t)‖ ≤ q*r := by
    apply (opNorm_comp_le _ _).trans
    rw [LinearIsometryEquiv.norm_map]
    exact mul_le_mul htQ htQ₁ (norm_nonneg _) hq
  have hprodδ : ‖(Q t).adjoint.comp (Q₁ t) - (P t).adjoint.comp (P₁ t)‖ ≤
      ‖Q-P‖*r + q*‖Q₁-P₁‖ := by
    apply (norm_comp_sub_le _ _ _ _).trans
    have had : ‖(Q t).adjoint-(P t).adjoint‖ = ‖Q t-P t‖ := by
      rw [← map_sub, LinearIsometryEquiv.norm_map]
    rw [had, LinearIsometryEquiv.norm_map]
    exact add_le_add (mul_le_mul hδQ htQ₁ (by positivity) (by positivity))
      (mul_le_mul htP hδQ₁ (norm_nonneg _) hq)
  have htotal := (norm_comp_sub_le
    (gramInverse (Q t) c hc (hQ t)) (gramInverse (P t) c hc (hP t))
    ((Q t).adjoint.comp (Q₁ t)) ((P t).adjoint.comp (P₁ t))).trans
      (add_le_add (mul_le_mul hI hprod (norm_nonneg _) (by positivity))
        (mul_le_mul (gramInverse_norm (P t) c hc (hP t)) hprodδ
          (norm_nonneg _) (inv_nonneg.mpr hc.le)))
  change ‖(-2 : ℝ) • (gramInverse (Q t) c hc (hQ t)).comp ((Q t).adjoint.comp (Q₁ t)) -
    (-2 : ℝ) • (gramInverse (P t) c hc (hP t)).comp ((P t).adjoint.comp (P₁ t))‖ ≤ _
  rw [← smul_sub, norm_smul]
  norm_num only [Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left htotal (by norm_num)).trans_eq
    (by unfold generatorDifferenceCost; ring)

end EulerTransverseGeneratorDifference
