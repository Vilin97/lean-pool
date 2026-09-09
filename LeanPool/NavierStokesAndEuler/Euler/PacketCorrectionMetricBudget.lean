/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionSourceData
public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionMetricTime

@[expose] public section

/-! A genuine inverse-metric budget for the source correction data.
Its time derivative, symmetry, coercivity and inverse identity are proved
from the prescribed deformation; the bounds are finite norms of actual
coefficient paths and their actual first translation derivative. -/

noncomputable section

namespace EulerPacketCorrectionCoefficients

open Set EulerSmoothLimit EulerPacketCylinderField EulerAllOrderCorrectionData
  EulerCorrectionEnergyData EulerRegularizedMetricPaths EulerVolterraConvolution
  EulerLpCylinderRectangular EulerMeanCoefficients EulerLiftedGradientSpace
  EulerPacketProfileRecursion
open scoped BoundedContinuousFunction

private local instance : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) := inferInstance

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) (P : ℝ) [Fact (0 < P)]

theorem inverseMetric_operatorPath_eq :
    metricOperatorPath P D.T (inverseMetricTower D P).coefficient
      (inverseMetricTower_continuous D P) = fullPathMap P (inverseMetricCoefficient D).path := by
  apply ContinuousMap.ext
  intro t
  exact MatrixCoefficient.toCoefficientTower_operator P (inverseMetricCoefficient D) t

theorem inverseMetric_operator_hasDerivAt (t : ℝ) (ht : t ∈ Ioo 0 D.T) :
    HasDerivAt (extendPath D.T D.T_pos.le
      (metricOperatorPath P D.T (inverseMetricTower D P).coefficient
        (inverseMetricTower_continuous D P)))
      (extendPath D.T D.T_pos.le (inverseMetricDerivativePath D P) t) t := by
  rw [inverseMetric_operatorPath_eq]
  have h := (inverseMetric_operator_hasDerivWithinAt D P
    ⟨t,⟨ht.1.le,ht.2.le⟩⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  simpa only [extendPath,projIcc_of_mem D.T_pos.le ⟨ht.1.le,ht.2.le⟩] using h

def inverseMetricBound : ℝ := ‖(inverseMetricCoefficient D).path‖

def inverseMetricFirstBound : ℝ :=
  ‖iteratedFDeriv ℝ 1 (translateCoefficientPath (inverseMetricCoefficient D).path) 0‖

def inverseMetricTimeBound : ℝ := ‖(inverseMetricTimeCoefficient D).path‖

theorem inverseMetricBound_le : inverseMetricBound D ≤ ‖D.F.field‖^2 := by
  apply (ContinuousMap.norm_le _ (sq_nonneg ‖D.F.field‖)).2
  intro t
  apply (BoundedContinuousFunction.norm_le (sq_nonneg ‖D.F.field‖)).2
  intro x
  rw [inverseMetricCoefficient_apply]
  have hF : ‖D.F.field t x‖ ≤ ‖D.F.field‖ :=
    ((D.F.field t).norm_coe_le_norm x).trans (D.F.field.norm_coe_le_norm t)
  calc
    _ ≤ ‖(D.F.field t x).adjoint‖*‖D.F.field t x‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖D.F.field t x‖*‖D.F.field t x‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ ‖D.F.field‖*‖D.F.field‖ := mul_le_mul hF hF (norm_nonneg _) (norm_nonneg _)
    _ = _ := (pow_two _).symm

theorem inverseMetricTimeBound_le :
    inverseMetricTimeBound D ≤ 2*‖D.F.field‖*‖D.F₁.field‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro t
  apply (BoundedContinuousFunction.norm_le (by positivity)).2
  intro x
  rw [inverseMetricTimeCoefficient_apply]
  have hF : ‖D.F.field t x‖ ≤ ‖D.F.field‖ :=
    ((D.F.field t).norm_coe_le_norm x).trans (D.F.field.norm_coe_le_norm t)
  have hF₁ : ‖D.F₁.field t x‖ ≤ ‖D.F₁.field‖ :=
    ((D.F₁.field t).norm_coe_le_norm x).trans (D.F₁.field.norm_coe_le_norm t)
  calc
    _ ≤ ‖(D.F₁.field t x).adjoint.comp (D.F.field t x)‖ +
        ‖(D.F.field t x).adjoint.comp (D.F₁.field t x)‖ := norm_add_le _ _
    _ ≤ ‖(D.F₁.field t x).adjoint‖*‖D.F.field t x‖ +
        ‖(D.F.field t x).adjoint‖*‖D.F₁.field t x‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ = ‖D.F₁.field t x‖*‖D.F.field t x‖ + ‖D.F.field t x‖*‖D.F₁.field t x‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map,ContinuousLinearMap.adjoint.norm_map]
    _ ≤ ‖D.F₁.field‖*‖D.F.field‖ + ‖D.F.field‖*‖D.F₁.field‖ :=
      add_le_add (mul_le_mul hF₁ hF (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul hF hF₁ (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

/-- The actual source inverse metric supplies every field of the metric
budget at every finite Sobolev order. -/
def sourceMetricBudget (κ : ℝ) (hκ : |κ| ≤ 1)
    (Z G : FieldTower P D.T) (q : ℕ) :
    MetricBudget P D.T D.T_pos.le ((correctionData D P κ hκ Z G).atOrder P (q+1)) where
  metric := (inverseMetricTower D P).coefficient
  continuous := inverseMetricTower_continuous D P
  derivative := inverseMetricDerivativePath D P
  hasDeriv := inverseMetric_operator_hasDerivAt D P
  c := D.inverseBound⁻¹
  c_pos := inv_pos.mpr D.inverseBound_pos
  symmetric t x v w := inverseMetric_symmetric D t x.1 v w
  coercive t x v := inverseMetric_coercive D t x.1 v
  inverse t x v := inverseMetricTower_inverse D P t x v
  bound := inverseMetricBound D
  first := inverseMetricFirstBound D
  time := inverseMetricTimeBound D
  bound_nonneg := norm_nonneg _
  first_nonneg := norm_nonneg _
  time_nonneg := norm_nonneg _
  bound_le t := (inverseMetricCoefficient D).path.norm_coe_le_norm t
  first_le _ := le_rfl
  time_le t := inverseMetricDerivativePath_norm D P t

def sourceMetricBudgetOfFields (κ : ℝ) (hκ : |κ| ≤ 1)
    {z r : VectorField} (Z : Field P D.T z) (G : Field P D.T r) (q : ℕ) :
    MetricBudget P D.T D.T_pos.le
      ((correctionDataOfFields D P κ hκ Z G).atOrder P (q+1)) :=
  sourceMetricBudget D P κ hκ Z.toFieldTower G.toFieldTower q

@[simp] theorem sourceMetricBudget_metric (κ : ℝ) (hκ : |κ| ≤ 1)
    (Z G : FieldTower P D.T) (q : ℕ) :
    (sourceMetricBudget D P κ hκ Z G q).metric = (inverseMetricTower D P).coefficient := rfl

@[simp] theorem sourceMetricBudget_derivative (κ : ℝ) (hκ : |κ| ≤ 1)
    (Z G : FieldTower P D.T) (q : ℕ) :
    (sourceMetricBudget D P κ hκ Z G q).derivative = inverseMetricDerivativePath D P := rfl

@[simp] theorem sourceMetricBudget_c (κ : ℝ) (hκ : |κ| ≤ 1)
    (Z G : FieldTower P D.T) (q : ℕ) :
    (sourceMetricBudget D P κ hκ Z G q).c = D.inverseBound⁻¹ := rfl

theorem sourceMetricBudget_bound_le (κ : ℝ) (hκ : |κ| ≤ 1)
    (Z G : FieldTower P D.T) (q : ℕ) :
    (sourceMetricBudget D P κ hκ Z G q).bound ≤ ‖D.F.field‖^2 :=
  inverseMetricBound_le D

theorem sourceMetricBudget_time_le (κ : ℝ) (hκ : |κ| ≤ 1)
    (Z G : FieldTower P D.T) (q : ℕ) :
    (sourceMetricBudget D P κ hκ Z G q).time ≤ 2*‖D.F.field‖*‖D.F₁.field‖ :=
  inverseMetricTimeBound_le D

end EulerPacketCorrectionCoefficients
