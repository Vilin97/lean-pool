/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowThirdPrimitive
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! Curve-space operators for higher flow dependence on the initial point. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped NNReal
namespace AVenhance.Infra.Section4

variable {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pointwise application of a continuous operator curve to a state curve. -/
def amnrCurveApply (A : C(K, E →L[ℝ] F)) (u : C(K, E)) : C(K, F) :=
  ⟨fun t => A t (u t), A.continuous.clm_apply u.continuous⟩

/-- Uniform application costs the product of the two actual curve norms. -/
theorem amnrCurveApply_norm_le (A : C(K, E →L[ℝ] F)) (u : C(K, E)) :
    ‖amnrCurveApply A u‖ ≤ ‖A‖ * ‖u‖ := by
  apply (ContinuousMap.norm_le (amnrCurveApply A u) (mul_nonneg (norm_nonneg A) (norm_nonneg
      u))).mpr
  intro t
  exact ((A t).le_opNorm (u t)).trans
    (mul_le_mul (A.norm_coe_le_norm t) (u.norm_coe_le_norm t) (norm_nonneg _) (norm_nonneg _))

/-- The actual operator curve acts as a bounded linear operator on curves. -/
def amnrCurveOperator (A : C(K, E →L[ℝ] F)) : C(K, E) →L[ℝ] C(K, F) :=
  LinearMap.mkContinuous
    { toFun := amnrCurveApply A
      map_add' := by intro u v; ext t; simp [amnrCurveApply]
      map_smul' := by intro c u; ext t; simp [amnrCurveApply] }
    ‖A‖ (amnrCurveApply_norm_le A)

@[simp]
theorem amnrCurveOperator_apply (A : C(K, E →L[ℝ] F)) (u : C(K, E)) (t : K) :
    amnrCurveOperator A u t = A t (u t) := rfl

/-- No compact-domain cardinality enters the operator bound. -/
theorem amnrCurveOperator_norm_le (A : C(K, E →L[ℝ] F)) :
    ‖amnrCurveOperator A‖ ≤ ‖A‖ := by
  apply (amnrCurveOperator A).opNorm_le_bound (norm_nonneg A)
  exact amnrCurveApply_norm_le A

/-- Taking an operator curve to its curve-space action is itself bounded
linear. This will preserve every finite differentiability order. -/
def amnrCurveOperatorMap : C(K, E →L[ℝ] F) →L[ℝ] (C(K, E) →L[ℝ] C(K, F)) :=
  LinearMap.mkContinuous
    { toFun := fun (A : C(K, E →L[ℝ] F)) => amnrCurveOperator A
      map_add' := by intro A B; ext u t; simp
      map_smul' := by intro c A; ext u t; simp }
    1 (fun A => by
      change ‖amnrCurveOperator A‖ ≤ 1 * ‖A‖
      rw [one_mul]
      exact amnrCurveOperator_norm_le A)

/-- Composition of a time-dependent field with an actual continuous curve. -/
def amnrCurveCompose (f : K → E → F) (hf : Continuous (fun z : K × E => f z.1 z.2))
    (u : C(K, E)) : C(K, F) :=
  ⟨fun t => f t (u t), hf.comp (continuous_id.prodMk u.continuous)⟩

end AVenhance.Infra.Section4
