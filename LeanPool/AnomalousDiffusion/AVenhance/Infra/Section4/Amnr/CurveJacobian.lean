/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.JacobianJetScaling

/-! The actual linearized Volterra operator and its primitive jets. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

instance CurveJacobian.amnrCurveEndNorm {K E : Type} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (C(K, E) →L[ℝ] C(K, E)) := inferInstance

instance CurveJacobian.amnrCurveEndSpace {K E : Type} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (C(K, E) →L[ℝ] C(K, E)) := inferInstance

instance CurveJacobian.amnrOperatorCurveNorm {K E : Type} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup C(K, E →L[ℝ] E) := inferInstance

instance CurveJacobian.amnrOperatorCurveSpace {K E : Type} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ C(K, E →L[ℝ] E) := inferInstance

/-- The linearized Volterra coefficient at an actual continuous trajectory. -/
def amnrCurveJacobianCoefficient {K E : Type} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × E → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (η : C(K, ℝ))
    (V : C(K, E) →L[ℝ] C(K, E)) (u : C(K, E)) : C(K, E) →L[ℝ] C(K, E) :=
  V.comp (amnrCurveOperator (amnrCurveJointCompose (amnrStateDerivative f)
    (amnrStateDerivative_contDiff hf).continuous η u))

/-- Lifting an operator curve and composing with time integration is linear
with norm at most the integration norm. -/
theorem amnrCurveJacobian_lift_norm_le {K E : Type} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : C(K, E) →L[ℝ] C(K, E)) :
    ‖(ContinuousLinearMap.compL ℝ (C(K, E)) (C(K, E)) (C(K, E)) V).comp
      (amnrCurveOperatorMap (K := K) (E := E) (F := E))‖ ≤ ‖V‖ := by
  have hO : ‖amnrCurveOperatorMap (K := K) (E := E) (F := E)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro A
    change ‖amnrCurveOperator A‖ ≤ 1 * ‖A‖
    rw [one_mul]
    exact amnrCurveOperator_norm_le A
  have hL : ‖ContinuousLinearMap.compL ℝ (C(K, E)) (C(K, E)) (C(K, E)) V‖ ≤ ‖V‖ := by
    exact ((ContinuousLinearMap.compL ℝ (C(K, E)) (C(K, E)) (C(K, E))).le_opNorm V).trans
      ((mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_compL_le ℝ _ _ _) (norm_nonneg
          V)).trans_eq (one_mul _))
  exact ((ContinuousLinearMap.compL ℝ (C(K, E)) (C(K, E)) (C(K, E)) V).opNorm_comp_le _).trans
    ((mul_le_mul hL hO (norm_nonneg _) (norm_nonneg V)).trans_eq (mul_one _))

/-- Primitive joint derivative bounds prove smoothness of the linearized
coefficient, including when its state is an actual flow curve. -/
theorem amnrCurveJacobianCoefficient_contDiff {K E : Type}
    [TopologicalSpace K] [CompactSpace K] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × E → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hbound : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖iteratedFDeriv ℝ j f z‖ ≤ C)
    (η : C(K, ℝ)) (V : C(K, E) →L[ℝ] C(K, E)) :
    ContDiff ℝ (⊤ : ℕ∞) (amnrCurveJacobianCoefficient f hf η V) := by
  have hb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z,
      ‖iteratedFDeriv ℝ j (amnrStateDerivative f) z‖ ≤ C := by
    intro j
    obtain ⟨C, hC, hCb⟩ := hbound (j + 1)
    exact ⟨C, hC, amnrStateDerivative_iteratedFDeriv_norm_le hf j hCb⟩
  exact ((ContinuousLinearMap.compL ℝ (C(K, E)) (C(K, E)) (C(K, E)) V).comp
    (amnrCurveOperatorMap (K := K) (E := E) (F := E))).contDiff.comp
      (amnrCurveJointCompose_contDiff_infty (amnrStateDerivative_contDiff hf) hb η)

/-- Every coefficient jet has only the time-integration norm as additional
cost, beyond the actual primitive state-Jacobian jet. -/
theorem amnrCurveJacobianCoefficient_iteratedFDeriv_norm_le {K E : Type}
    [TopologicalSpace K] [CompactSpace K] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × E → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hbound : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖iteratedFDeriv ℝ j f z‖ ≤ C)
    (η : C(K, ℝ)) (V : C(K, E) →L[ℝ] C(K, E)) (n : ℕ) (u : C(K, E))
    {B : ℝ} (hB : 0 ≤ B)
    (hstate : ∀ t x, ‖iteratedFDeriv ℝ n (fun y => amnrStateDerivative f (η t, y)) x‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (amnrCurveJacobianCoefficient f hf η V) u‖ ≤ ‖V‖ * B := by
  have hb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z,
      ‖iteratedFDeriv ℝ j (amnrStateDerivative f) z‖ ≤ C := by
    intro j
    obtain ⟨C, hC, hCb⟩ := hbound (j + 1)
    exact ⟨C, hC, amnrStateDerivative_iteratedFDeriv_norm_le hf j hCb⟩
  let N := amnrCurveJointCompose (amnrStateDerivative f) (amnrStateDerivative_contDiff
      hf).continuous η
  let L := (ContinuousLinearMap.compL ℝ (C(K, E)) (C(K, E)) (C(K, E)) V).comp
    (amnrCurveOperatorMap (K := K) (E := E) (F := E))
  have hh := L.norm_iteratedFDeriv_comp_left
    ((amnrCurveJointCompose_contDiff_infty (amnrStateDerivative_contDiff hf) hb η).contDiffAt (x
        := u))
    (n := n) (by simp)
  change ‖iteratedFDeriv ℝ n (amnrCurveJacobianCoefficient f hf η V) u‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ
      n N u‖ at hh
  exact hh.trans (mul_le_mul (amnrCurveJacobian_lift_norm_le V)
    (amnrCurveJointCompose_iteratedFDeriv_norm_le (amnrStateDerivative_contDiff hf) hb η n u hB
        hstate)
    (norm_nonneg _) (norm_nonneg V))

/-- Differentiating the actual Volterra equation yields the Jacobian fixed
 equation. Its highest derivative is derived, never imposed as a premise. -/
theorem amnrCurveResidual_solution_jacobian_equation {K E : Type}
    [TopologicalSpace K] [CompactSpace K] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × E → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ z, ‖iteratedFDeriv ℝ 2 f z‖ ≤ C)
    (η : C(K, ℝ)) (V : C(K, E) →L[ℝ] C(K, E))
    {Q : E → C(K, E)} (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (heq : ∀ y, amnrCurveResidual f hf.continuous η V (Q y) = ContinuousMap.const K y)
    (x : E) :
    fderiv ℝ Q x = ContinuousLinearMap.const ℝ K +
      (amnrCurveJacobianCoefficient f hf η V (Q x)).comp (fderiv ℝ Q x) := by
  have hh := (amnrCurveResidual_hasFDerivAt hf hC hbound η V (Q x)).comp x
    (hQ.differentiable (by simp) x).hasFDerivAt
  have he : amnrCurveResidual f hf.continuous η V ∘ Q = ContinuousLinearMap.const ℝ K := funext heq
  rw [he] at hh
  have hd := hh.unique ((ContinuousLinearMap.const ℝ K).hasFDerivAt (x := x))
  change ((1 : C(K, E) →L[ℝ] C(K, E)) - amnrCurveJacobianCoefficient f hf η V (Q x)).comp
    (fderiv ℝ Q x) = _ at hd
  rw [ContinuousLinearMap.sub_comp] at hd
  change fderiv ℝ Q x - (amnrCurveJacobianCoefficient f hf η V (Q x)).comp
    (fderiv ℝ Q x) = ContinuousLinearMap.const ℝ K at hd
  exact sub_eq_iff_eq_add.mp hd

end AVenhance.Infra.Section4
