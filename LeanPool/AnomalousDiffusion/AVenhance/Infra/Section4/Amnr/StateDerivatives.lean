/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FieldTaylor

/-! Spatial restriction of joint derivatives, preserving all primitive bounds. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Restrict a joint time-state operator to state directions. -/
def amnrRestrictState : ((ℝ × E) →L[ℝ] F) →L[ℝ] (E →L[ℝ] F) :=
  LinearMap.mkContinuous
    { toFun := fun A : (ℝ × E) →L[ℝ] F => A.comp (ContinuousLinearMap.inr ℝ ℝ E)
      map_add' := by intro A B; ext h; simp
      map_smul' := by intro c A; ext h; simp }
    1 (fun A => by
      change ‖A.comp (ContinuousLinearMap.inr ℝ ℝ E)‖ ≤ 1 * ‖A‖
      rw [one_mul]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
      intro h
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
        Prod.norm_def, norm_zero, max_eq_right (norm_nonneg h)] using A.le_opNorm (0, h))

/-- Restricting to state directions has unit operator cost. -/
theorem amnrRestrictState_norm_le : ‖amnrRestrictState (E := E) (F := F)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro A
  change ‖A.comp (ContinuousLinearMap.inr ℝ ℝ E)‖ ≤ 1 * ‖A‖
  rw [one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro h
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    Prod.norm_def, norm_zero, max_eq_right (norm_nonneg h)] using A.le_opNorm (0, h)

/-- The actual state derivative of a joint primitive field. -/
def amnrStateDerivative (f : ℝ × E → F) (z : ℝ × E) : E →L[ℝ] F :=
  amnrRestrictState (fderiv ℝ f z)

/-- The actual state derivative retains all joint smoothness. -/
theorem amnrStateDerivative_contDiff {f : ℝ × E → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (amnrStateDerivative f) :=
  (amnrRestrictState (E := E) (F := F)).contDiff.comp
    (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp))

/-- Every next derivative of the primitive field supplies the corresponding
operator bound for its actual state derivative. -/
theorem amnrStateDerivative_iteratedFDeriv_norm_le {f : ℝ × E → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) {C : ℝ}
    (hbound : ∀ z, ‖iteratedFDeriv ℝ (n + 1) f z‖ ≤ C) (z : ℝ × E) :
    ‖iteratedFDeriv ℝ n (amnrStateDerivative f) z‖ ≤ C := by
  have hd := hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hh := amnrRestrictState.norm_iteratedFDeriv_comp_left (hd.contDiffAt (x := z)) (n := n) (by
      simp)
  change ‖iteratedFDeriv ℝ n (amnrStateDerivative f) z‖ ≤ _ at hh
  rw [norm_iteratedFDeriv_fderiv] at hh
  exact hh.trans ((mul_le_mul amnrRestrictState_norm_le (hbound z)
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul C))

end AVenhance.Infra.Section4
