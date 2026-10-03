/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionSourceData
import Mathlib.Algebra.Order.Star.Real
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceCorrectionCoefficients
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderFullTime

/-! A genuine inverse-metric budget for the source correction data.
Its time derivative, symmetry, coercivity and inverse identity are proved
from the prescribed deformation; the bounds are finite norms of actual
coefficient paths and their actual first translation derivative. -/

section

/-! The time derivative of the actual inverse pressure metric, first as
a bounded matrix field and then as its cylinder L² multiplier. -/

@[expose] public section

noncomputable section

namespace EulerPacketCorrectionCoefficients

open Set ContinuousLinearMap EulerSmoothLimit EulerPacketPointJets
  EulerPacketCylinderField EulerLpCylinderRectangular EulerLiftedGradientSpace
  EulerVolterraConvolution EulerTransverseGramPath EulerMeanCoefficients
open scoped BoundedContinuousFunction

/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketCorrectionMetricTime1 : NormedAddCommGroup (Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketCorrectionMetricTime2 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instPacketCorrectionMetricTime3 : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instPacketCorrectionMetricTime4 : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U)

/-- Raw inverse metric time, given by `(rawFrameTime D z).adjoint.comp (rawFrame D z) +
(rawFrame D z).adjoint.comp (rawFrameTime D z)`. -/
def rawInverseMetricTime (z : Domain) : Space →L[ℝ] Space :=
  (adjoint (𝕜 := ℝ) (E := Space) (F := Space) (rawFrameTime D z)).comp (rawFrame D z) +
    (adjoint (𝕜 := ℝ) (E := Space) (F := Space) (rawFrame D z)).comp (rawFrameTime D z)

/-- Inverse metric time coefficient, given by `((frameTimeCoefficient D).adjoint.comp
(frameCoefficient D)).add ((frameCoefficient D).adjoint.comp (frameTimeCoefficient D))`. -/
def inverseMetricTimeCoefficient : MatrixCoefficient D.T (rawInverseMetricTime D) :=
  ((frameTimeCoefficient D).adjoint.comp (frameCoefficient D)).add
    ((frameCoefficient D).adjoint.comp (frameTimeCoefficient D))

@[simp] theorem inverseMetricTimeCoefficient_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    (inverseMetricTimeCoefficient D).path t x =
      (adjoint (𝕜 := ℝ) (E := Space) (F := Space) (D.F₁.field t x)).comp (D.F.field t x) +
        (adjoint (𝕜 := ℝ) (E := Space) (F := Space) (D.F.field t x)).comp (D.F₁.field t x) := rfl

theorem inverseMetric_field_hasDerivWithinAt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D.T)
    (x : Space) :
    HasDerivWithinAt (fun s => extendPath D.T D.T_pos.le (inverseMetricCoefficient D).path s x)
      (extendPath D.T D.T_pos.le (inverseMetricTimeCoefficient D).path t x)
      (Icc (0 : ℝ) D.T) t := by
  have h := hasDerivWithinAt_gram
    (fun s => extendPath D.T D.T_pos.le D.F.field s x)
    (extendPath D.T D.T_pos.le D.F₁.field t x)
    (Icc (0 : ℝ) D.T) t (D.frame_time t ht x)
  apply h

variable (P : ℝ) [Fact (0 < P)]

/-- Inverse metric derivative path, given by `fullPathMap P (inverseMetricTimeCoefficient
D).path`. -/
def inverseMetricDerivativePath : C(Icc (0 : ℝ) D.T,LiftL2 P →L[ℝ] LiftL2 P) :=
  fullPathMap (K := Icc (0 : ℝ) D.T) (E := Vector3) (F := Vector3) P
    (inverseMetricTimeCoefficient D).path

theorem inverseMetric_operator_hasDerivWithinAt (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (extendPath D.T D.T_pos.le
      (fullPathMap (K := Icc (0 : ℝ) D.T) (E := Space) (F := Space) P
        (inverseMetricCoefficient D).path))
      (inverseMetricDerivativePath D P t) (Icc (0 : ℝ) D.T) t :=
  fullPath_hasDerivWithinAt P D.T D.T_pos.le (inverseMetricCoefficient D).path
    (inverseMetricTimeCoefficient D).path (inverseMetric_field_hasDerivWithinAt D) t

theorem inverseMetricDerivativePath_norm (t : Icc (0 : ℝ) D.T) :
    ‖inverseMetricDerivativePath D P t‖ ≤ ‖(inverseMetricTimeCoefficient D).path‖ := by
  exact ((fullOperatorMap (E := Space) (F := Space) P).le_opNorm ((inverseMetricTimeCoefficient
      D).path t)).trans
    ((mul_le_mul_of_nonneg_right (fullOperatorMap_norm (E := Space) (F := Space) P)
      (norm_nonneg ((inverseMetricTimeCoefficient D).path t))).trans
        (by simpa only [one_mul] using (inverseMetricTimeCoefficient D).path.norm_coe_le_norm t))

end EulerPacketCorrectionCoefficients

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketCorrectionCoefficients

open Set EulerSmoothLimit EulerPacketCylinderField EulerAllOrderCorrectionData
  EulerCorrectionEnergyData EulerRegularizedMetricPaths EulerVolterraConvolution
  EulerLpCylinderRectangular EulerMeanCoefficients EulerLiftedGradientSpace
  EulerPacketProfileRecursion
open scoped BoundedContinuousFunction

/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketCorrectionMetricBudget1 : NormedAddCommGroup (Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketCorrectionMetricBudget2 : NormedSpace ℝ (Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instPacketCorrectionMetricBudget3 : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space)
    := inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instPacketCorrectionMetricBudget4 : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) (P : ℝ) [Fact (0 < P)]

theorem inverseMetric_operatorPath_eq :
    metricOperatorPath P D.T (inverseMetricTower D P).coefficient
      (inverseMetricTower_continuous D P) =
      fullPathMap (K := Icc (0 : ℝ) D.T) (E := Space) (F := Space) P
        (inverseMetricCoefficient D).path := by
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

/-- Inverse metric bound, given by `‖(inverseMetricCoefficient D).path‖`. -/
def inverseMetricBound : ℝ := ‖(inverseMetricCoefficient D).path‖

/-- Inverse metric first bound, given by `‖iteratedFDeriv ℝ 1 (translateCoefficientPath
(inverseMetricCoefficient D).path) 0‖`. -/
def inverseMetricFirstBound : ℝ :=
  ‖iteratedFDeriv ℝ 1 (translateCoefficientPath (inverseMetricCoefficient D).path) 0‖

/-- Inverse metric time bound, given by `‖(inverseMetricTimeCoefficient D).path‖`. -/
def inverseMetricTimeBound : ℝ := ‖(inverseMetricTimeCoefficient D).path‖

theorem adjoint_comp_norm_le (A B : Space →L[ℝ] Space) :
    ‖(ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Space) (F := Space) A).comp B‖ ≤ ‖A‖ * ‖B‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq
    (congrArg (· * ‖B‖) (ContinuousLinearMap.adjoint.norm_map A))

theorem inverseMetricBound_le : inverseMetricBound D ≤ ‖D.F.field‖^2 := by
  apply (ContinuousMap.norm_le _ (sq_nonneg ‖D.F.field‖)).2
  intro t
  apply (BoundedContinuousFunction.norm_le (sq_nonneg ‖D.F.field‖)).2
  intro x
  rw [inverseMetricCoefficient_apply]
  have hF : ‖D.F.field t x‖ ≤ ‖D.F.field‖ :=
    ((D.F.field t).norm_coe_le_norm x).trans (D.F.field.norm_coe_le_norm t)
  calc
    _ ≤ ‖D.F.field t x‖*‖D.F.field t x‖ := adjoint_comp_norm_le _ _
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
    _ ≤ ‖D.F₁.field t x‖*‖D.F.field t x‖ + ‖D.F.field t x‖*‖D.F₁.field t x‖ :=
      (norm_add_le _ _).trans (add_le_add (adjoint_comp_norm_le _ _) (adjoint_comp_norm_le _ _))
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

/-- Source metric budget of fields, given by `sourceMetricBudget D P κ hκ Z.toFieldTower
G.toFieldTower q`. -/
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
