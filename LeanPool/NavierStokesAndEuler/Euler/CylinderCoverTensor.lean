/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderCoveringDerivative

@[expose] public section

/-! Exact coordinate words and tensor norm bounds for the real periodic
cover of a smooth cylinder field. -/

noncomputable section


namespace EulerCylinderSmoothOrbit

open EulerLiftedGradientSpace EulerMetricTransport EulerCylinderCoordinates
  EulerCylinderSobolev EulerSobolevDerivativeNorm
open scoped ContDiff

variable (P : ℝ) {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
theorem coverField_eq_euclidean (f : LiftDomain P → V) :
    (fun x : LiftTangent => f (coveringMap P x)) =
      euclideanLift P f 0 ∘ coordinateEquiv.symm.toContinuousLinearMap := by
  funext x
  simp only [Function.comp_apply, euclideanLift, localFieldLift,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
    Prod.fst_zero, Prod.snd_zero, zero_add]
  rfl

theorem coverField_word {n : ℕ} (w : Fin n → Fin 4) (f : LiftDomain P → V)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift P f x)) (x : LiftTangent) :
    iteratedFieldDerivative P w f (coveringMap P x) =
      iteratedFDeriv ℝ n (fun y => f (coveringMap P y)) x
        (fun i => standardDirection (w i)) := by
  have he := euclideanLift_iteratedFieldDerivative P w f hf 0 (coordinateEquiv.symm x)
  have hs := coverField_contDiff P f hf
  have hd := coordinateEquiv.toContinuousLinearMap.iteratedFDeriv_comp_right
    hs (coordinateEquiv.symm x) (show (n : ℕ∞) ≤ ∞ by simp)
  have hfun : ((fun z : LiftTangent => f (z.1, (z.2 : AddCircle P))) ∘
      coordinateEquiv.toContinuousLinearMap) = euclideanLift P f 0 := by
    rw [coverField_eq_local]
    rfl
  rw [hfun] at hd
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at hd
  rw [hd] at he
  simpa only [euclideanLift, Function.comp_apply, localFieldLift,
    ContinuousLinearEquiv.apply_symm_apply, Prod.fst_zero, Prod.snd_zero, zero_add,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe, standardDirection, coveringMap] using he

theorem coverField_tensor_norm_le (n : ℕ) (f : LiftDomain P → V)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift P f x)) (x : LiftTangent) :
    ‖iteratedFDeriv ℝ n (fun y => f (coveringMap P y)) x‖ ≤
      ‖coordinateEquiv.symm.toContinuousLinearMap‖^n *
        ∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative P w f (coveringMap P x)‖ := by
  have ht := euclideanLift_tensor_norm_le P n f hf 0 (coordinateEquiv.symm x)
  have he (w : Fin n → Fin 4) :
      euclideanLift P (iteratedFieldDerivative P w f) 0 (coordinateEquiv.symm x) =
        iteratedFieldDerivative P w f (coveringMap P x) := by
    simp only [euclideanLift, Function.comp_apply, localFieldLift,
      ContinuousLinearEquiv.apply_symm_apply, Prod.fst_zero, Prod.snd_zero, zero_add]
    rfl
  simp_rw [he] at ht
  rw [coverField_eq_euclidean,
    coordinateEquiv.symm.toContinuousLinearMap.iteratedFDeriv_comp_right
      (euclideanLift_smooth P f hf 0) x (by simp)]
  have hc := (iteratedFDeriv ℝ n (euclideanLift P f 0) (coordinateEquiv.symm
    x)).norm_compContinuousLinearMap_le
    (fun _ : Fin n => coordinateEquiv.symm.toContinuousLinearMap)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hc
  exact hc.trans ((mul_le_mul_of_nonneg_right ht (pow_nonneg (norm_nonneg _) n)).trans_eq
    (mul_comm _ _))

end EulerCylinderSmoothOrbit
