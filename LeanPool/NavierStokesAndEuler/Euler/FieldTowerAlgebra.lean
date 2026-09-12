/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerRepresentative

/-! Actual algebra of coherent all-order fields, including multiplication
by the genuine coefficient towers of the source deformation. -/

@[expose] public section


noncomputable section

namespace EulerAllOrderCorrectionData.FieldTower

open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerSobolevCoefficientPressure EulerMetricTransport

variable {P T : ℝ} [Fact (0 < P)] (A B : EulerAllOrderCorrectionData.FieldTower P T)

/-- Add, bundling `field`, `realization`, `value_eq`. -/
def add : EulerAllOrderCorrectionData.FieldTower P T where
  field := A.field+B.field
  realization q := A.realization q+B.realization q
  value_eq q t := by
    change value P (A.realization q t)+value P (B.realization q t)=_
    rw [A.value_eq,B.value_eq]
    rfl

/-- Smul, bundling `field`, `realization`, `value_eq`. -/
def smul (c : ℝ) : EulerAllOrderCorrectionData.FieldTower P T where
  field := c • A.field
  realization q := c • A.realization q
  value_eq q t := by
    change c • value P (A.realization q t)=_
    rw [A.value_eq]
    rfl

theorem add_pointField (t : Icc (0 : ℝ) T) :
    (A.add B).pointField t = fun x => A.pointField t x+B.pointField t x := by
  apply (A.add B).pointField_unique t _
    ((Continuous.uncurry_left t A.pointField_joint_continuous).add
      (Continuous.uncurry_left t B.pointField_joint_continuous))
  filter_upwards [Lp.coeFn_add (A.field t) (B.field t),A.pointField_ae t,B.pointField_ae t]
    with x hs ha hb
  exact hs.trans (congrArg₂ (·+·) ha hb)

theorem smul_pointField (c : ℝ) (t : Icc (0 : ℝ) T) :
    (A.smul c).pointField t = fun x => c • A.pointField t x := by
  apply (A.smul c).pointField_unique t _
    ((Continuous.uncurry_left t A.pointField_joint_continuous).const_smul c)
  filter_upwards [Lp.coeFn_smul c (A.field t),A.pointField_ae t] with x hs ha
  exact hs.trans (congrArg (c • ·) ha)

/-- Multiply, bundling `field`, `realization`, `value_eq`. -/
def multiply (C : CoefficientTower P T) : EulerAllOrderCorrectionData.FieldTower P T where
  field := (valueOperator P 0).compLeftContinuous ℝ (Icc (0 : ℝ) T)
    ⟨fun t => coefficientSobolevOperator P (C.jet 0 t) (A.realization 0 t),
      (C.continuous 0).clm_apply (A.realization 0).continuous⟩
  realization q := ⟨fun t => coefficientSobolevOperator P (C.jet q t) (A.realization q t),
    (C.continuous q).clm_apply (A.realization q).continuous⟩
  value_eq q t := by
    change value P (coefficientSobolevOperator P (C.jet q t) (A.realization q t)) =
      value P (coefficientSobolevOperator P (C.jet 0 t) (A.realization 0 t))
    rw [coefficientSobolevOperator_value,coefficientSobolevOperator_value,A.value_eq,A.value_eq]

theorem multiply_field (C : CoefficientTower P T) (t : Icc (0 : ℝ) T) :
    (A.multiply C).field t = (C.coefficient t).operator (A.field t) := by
  change value P (coefficientSobolevOperator P (C.jet 0 t) (A.realization 0 t))=_
  rw [coefficientSobolevOperator_value,A.value_eq]

theorem multiply_pointField (C : CoefficientTower P T) (t : Icc (0 : ℝ) T) :
    (A.multiply C).pointField t =
      fun x => (C.coefficient t).coefficient x (A.pointField t x) := by
  apply (A.multiply C).pointField_unique t _
    ((smoothField_continuous P _ (C.coefficient t).smooth).clm_apply
      (Continuous.uncurry_left t A.pointField_joint_continuous))
  rw [A.multiply_field C t]
  filter_upwards [(C.coefficient t).operator_ae (A.field t),A.pointField_ae t] with x hc ha
  exact hc.trans (congrArg ((C.coefficient t).coefficient x) ha)

end EulerAllOrderCorrectionData.FieldTower
