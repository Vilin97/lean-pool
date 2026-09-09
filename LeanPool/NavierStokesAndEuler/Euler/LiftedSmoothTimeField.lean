/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldLinear
public import LeanPool.NavierStokesAndEuler.Euler.LiftedTransportTrace
public import LeanPool.NavierStokesAndEuler.Euler.PacketNormalDriftBounds

@[expose] public section

/-! The actual lifted velocity retains the small normal component in its
coefficient estimates. No division by the packet amplitude is used. -/

noncomputable section


namespace EulerLiftedSmoothTimeField

open InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMetricTransport EulerLiftedTransportTrace EulerPacketCylinderField
    EulerCylinderScalarPrimitive
open scoped ContDiff BoundedContinuousFunction

def angularInjection : Space →L[ℝ] LiftTangent :=
  (ContinuousLinearMap.inr ℝ Space ℝ).comp scalarProject

theorem angularInjection_norm : ‖angularInjection‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro v
  change ‖((0 : Space), scalarProject v)‖ ≤ 1 * ‖v‖
  simpa only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _), one_mul,
    scalarProject_norm] using scalarProject.le_opNorm v

theorem spatialInjection_norm : ‖ContinuousLinearMap.inl ℝ Space ℝ‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro v
  simp

theorem transportLinear_split (κ : ℝ) (m : Space) :
    transportLinear κ m = κ • ContinuousLinearMap.inl ℝ Space ℝ +
      angularInjection.comp (normalComponentMap m) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · simp [transportLinear, angularInjection]
  · simp [transportLinear, angularInjection]

theorem transport_tensor_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : ℝ) (m : Space) {n : ℕ} (A : E [×n]→L[ℝ] Space) :
    ‖(transportLinear κ m).compContinuousMultilinearMap A‖ ≤
      |κ| * ‖A‖ + ‖(normalComponentMap m).compContinuousMultilinearMap A‖ := by
  have he : (transportLinear κ m).compContinuousMultilinearMap A =
      κ • (ContinuousLinearMap.inl ℝ Space ℝ).compContinuousMultilinearMap A +
        angularInjection.compContinuousMultilinearMap
          ((normalComponentMap m).compContinuousMultilinearMap A) := by
    apply ContinuousMultilinearMap.ext
    intro v
    exact congrArg (fun L : Space →L[ℝ] LiftTangent => L (A v)) (transportLinear_split κ m)
  rw [he]
  calc
    _ ≤ ‖κ • (ContinuousLinearMap.inl ℝ Space ℝ).compContinuousMultilinearMap A‖ +
        ‖angularInjection.compContinuousMultilinearMap
          ((normalComponentMap m).compContinuousMultilinearMap A)‖ := norm_add_le _ _
    _ ≤ |κ| * (1 * ‖A‖) +
        1 * ‖(normalComponentMap m).compContinuousMultilinearMap A‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (((ContinuousLinearMap.inl ℝ Space ℝ).norm_compContinuousMultilinearMap_le A).trans
            (mul_le_mul_of_nonneg_right spatialInjection_norm (norm_nonneg A))) (abs_nonneg κ)
      · exact (angularInjection.norm_compContinuousMultilinearMap_le _).trans
          (mul_le_mul_of_nonneg_right angularInjection_norm (norm_nonneg _))
    _ = _ := by rw [one_mul, one_mul]

variable {K E : Type} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private local instance (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] Space) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] Space) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] LiftTangent) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] LiftTangent) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] Space)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] Space)) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] LiftTangent)) :=
  inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] LiftTangent)) := inferInstance

def lift (A : SmoothTimeField K E Space) (κ : ℝ) (m : Space) : SmoothTimeField K E LiftTangent :=
  A.map (transportLinear κ m)

@[simp] theorem lift_apply (A : SmoothTimeField K E Space) (κ : ℝ) (m : Space) (t : K) (x : E) :
    (lift A κ m).field t x = (κ • A.field t x, inner ℝ m (A.field t x)) := rfl

theorem lift_jet_norm_le (A : SmoothTimeField K E Space) (κ : ℝ) (m : Space) (n : ℕ) :
    ‖(lift A κ m).jet n‖ ≤ |κ| * ‖A.jet n‖ + ‖(A.map (normalComponentMap m)).jet n‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro t
  apply (BoundedContinuousFunction.norm_le (by positivity)).2
  intro x
  change ‖(transportLinear κ m).compContinuousMultilinearMap (A.jet n t x)‖ ≤ _
  exact (transport_tensor_norm κ m _).trans
    (add_le_add
      (mul_le_mul_of_nonneg_left
        (((A.jet n t).norm_coe_le_norm x).trans ((A.jet n).norm_coe_le_norm t)) (abs_nonneg κ))
      ((((A.map (normalComponentMap m)).jet n t).norm_coe_le_norm x).trans
        (((A.map (normalComponentMap m)).jet n).norm_coe_le_norm t)))

theorem lift_jet_norm_le_full (A : SmoothTimeField K E Space) (κ : ℝ) (m : Space) (n : ℕ) :
    ‖(lift A κ m).jet n‖ ≤ (|κ| + ‖m‖) * ‖A.jet n‖ := by
  apply (lift_jet_norm_le A κ m n).trans
  have hm := ((A.map_jet_norm_le (normalComponentMap m) n).trans
    (mul_le_mul_of_nonneg_right (normalComponentMap_norm_le m) (norm_nonneg (A.jet n))))
  simpa only [add_mul] using add_le_add (le_refl (|κ| * ‖A.jet n‖)) hm

end EulerLiftedSmoothTimeField
