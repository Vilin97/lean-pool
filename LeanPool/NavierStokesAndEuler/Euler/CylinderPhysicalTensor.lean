/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderGraphRealization
public import LeanPool.NavierStokesAndEuler.Euler.GraphPressurePotential

@[expose] public section

/-! The actual physical graph field is smooth. Its ordinary spatial
derivative tensors are bounded by cylinder derivative words, with an
explicit polynomial frequency loss. -/

noncomputable section

namespace EulerCylinderPhysicalTensor

open Set MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport
  EulerCylinderCoordinates EulerCylinderSobolev EulerGraphPullback
  EulerGraphPressurePotential EulerSobolev
open scoped ContDiff

def graphCoordinates (k : ℝ) (m : Vector3) : Vector3 →L[ℝ] Domain 4 :=
  coordinateEquiv.symm.toContinuousLinearMap.comp (graphMap k m)

@[simp] theorem coordinateEquiv_graphCoordinates (k : ℝ) (m x : Vector3) :
    coordinateEquiv (graphCoordinates k m x) = graphMap k m x :=
  coordinateEquiv.apply_symm_apply _

def frequencyFactor (k : ℝ) (m : Vector3) : ℝ :=
  ‖coordinateEquiv.symm.toContinuousLinearMap‖*(1+|k| * ‖m‖)

theorem frequencyFactor_nonneg (k : ℝ) (m : Vector3) : 0 ≤ frequencyFactor k m := by
  unfold frequencyFactor
  positivity

theorem graphMap_norm_le (k : ℝ) (m : Vector3) : ‖graphMap k m‖ ≤ 1+|k| * ‖m‖ := by
  apply (graphMap k m).opNorm_le_bound (by positivity)
  intro x
  rw [graphMap_apply,Prod.norm_def]
  apply max_le
  · nlinarith [norm_nonneg x,mul_nonneg (abs_nonneg k) (norm_nonneg m)]
  · have hi := norm_inner_le_norm (𝕜 := ℝ) m x
    rw [norm_mul,Real.norm_eq_abs]
    calc
      |k| * ‖inner ℝ m x‖ ≤ |k| * (‖m‖*‖x‖) := mul_le_mul_of_nonneg_left hi (abs_nonneg k)
      _ ≤ (1+|k| * ‖m‖)*‖x‖ := by nlinarith [norm_nonneg x]

theorem graphCoordinates_norm_le (k : ℝ) (m : Vector3) :
    ‖graphCoordinates k m‖ ≤ frequencyFactor k m :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (graphMap_norm_le k m) (norm_nonneg _))

variable (P : ℝ) [Fact (0 < P)]

def physicalField (k : ℝ) (m : Vector3) (f : LiftDomain P → Vector3) : Vector3 → Vector3 :=
  fun x => f (cylinderGraph P k m x)

omit [Fact (0 < P)] in
theorem physicalField_eq_euclidean (k : ℝ) (m : Vector3) (f : LiftDomain P → Vector3) :
    physicalField P k m f = euclideanLift P f 0 ∘ graphCoordinates k m := by
  funext x
  simp only [Function.comp_apply,euclideanLift,coordinateEquiv_graphCoordinates,
    localFieldLift,Prod.fst_zero,Prod.snd_zero,zero_add,graphMap_apply,physicalField,cylinderGraph]

omit [Fact (0 < P)] in
theorem physicalField_contDiff (k : ℝ) (m : Vector3) (f : LiftDomain P → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift P f x)) :
    ContDiff ℝ ∞ (physicalField P k m f) := by
  rw [physicalField_eq_euclidean]
  exact (euclideanLift_smooth P f hf 0).comp (graphCoordinates k m).contDiff

omit [Fact (0 < P)] in
theorem physicalTensor_norm_le (k : ℝ) (m : Vector3) (f : LiftDomain P → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift P f x)) (n : ℕ) (x : Vector3) :
    ‖iteratedFDeriv ℝ n (physicalField P k m f) x‖ ≤
      frequencyFactor k m ^ n *
        ∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative P w f (cylinderGraph P k m x)‖ := by
  have ht := euclideanLift_tensor_norm_le P n f hf 0 (graphCoordinates k m x)
  have he (w : Fin n → Fin 4) :
      euclideanLift P (iteratedFieldDerivative P w f) 0 (graphCoordinates k m x) =
        iteratedFieldDerivative P w f (cylinderGraph P k m x) :=
    (congrFun (physicalField_eq_euclidean P k m (iteratedFieldDerivative P w f)) x).symm
  simp_rw [he] at ht
  rw [physicalField_eq_euclidean,
    (graphCoordinates k m).iteratedFDeriv_comp_right (euclideanLift_smooth P f hf 0) x (by simp)]
  have hc := (iteratedFDeriv ℝ n (euclideanLift P f 0) (graphCoordinates k m
    x)).norm_compContinuousLinearMap_le
    (fun _ : Fin n => graphCoordinates k m)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hc
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (euclideanLift P f 0) (graphCoordinates k m x)‖*
        ‖graphCoordinates k m‖^n := hc
    _ ≤ (∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative P w f (cylinderGraph P k m x)‖)*
        frequencyFactor k m^n :=
      mul_le_mul ht (pow_le_pow_left₀ (norm_nonneg _) (graphCoordinates_norm_le k m) n)
        (by positivity) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    _ = _ := mul_comm _ _

end EulerCylinderPhysicalTensor
