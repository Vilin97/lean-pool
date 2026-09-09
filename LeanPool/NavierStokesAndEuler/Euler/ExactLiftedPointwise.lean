/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedExactLifted
public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerRepresentative
public import LeanPool.NavierStokesAndEuler.Euler.SobolevPointMultiplication
public import LeanPool.NavierStokesAndEuler.Euler.LiftedTransportComponents

@[expose] public section

/-! The exact Sobolev equation is the literal pointwise normalized equation
for the canonical smooth representatives. No pointwise PDE is assumed. -/

noncomputable section

namespace EulerAllOrderDriftCorrection

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerLiftedGradientSpace
  EulerAllOrderCorrectionData EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSobolevPointEvaluation EulerSobolevPointMultiplication EulerSobolevCoefficientPressure
  EulerCorrectionOperators EulerCorrectionResidualCancellation EulerSobolevTransport
  EulerMetricTransport EulerTransportDerivatives EulerLiftedWeakDerivative
  EulerSpatialSobolevInverse EulerVectorCylinder EulerVolterraConvolution
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] {T : ℝ}

private theorem coefficient_value_ae (C : SmoothCoefficient P)
    {q : ℕ} (K : CoefficientJet P standardDirection q C)
    (u : SobolevSpace P q) (f : LiftDomain P → Vector3)
    (hu : (value P u : LiftDomain P → Vector3) =ᵐ[liftMeasure P] f) :
    (value P (coefficientSobolevOperator P K u) : LiftDomain P → Vector3) =ᵐ[liftMeasure P]
      fun x => C.coefficient x (f x) := by
  rw [coefficientSobolevOperator_value]
  filter_upwards [C.operator_ae (value P u),hu] with x hc hf
  exact hc.trans (congrArg (C.coefficient x) hf)

def pointNonlinearity (A : Data P T) (Z : FieldTower P T)
    (t : Icc (0 : ℝ) T) (x : LiftDomain P) : Vector3 :=
  (A.linear.coefficient t).coefficient x (Z.pointField t x) +
    fieldFDeriv P (Z.pointField t) x (transportDirection A.κ A.direction (Z.pointField t x)) +
    ∑ i : Fin 3, (Z.pointField t x) i •
      ((A.quadratic i).coefficient t).coefficient x (Z.pointField t x)

theorem pointNonlinearity_continuous (A : Data P T) (Z : FieldTower P T)
    (t : Icc (0 : ℝ) T) : Continuous (pointNonlinearity P A Z t) := by
  have hZ := smoothField_continuous P _ (Z.pointField_smooth t)
  have hDZ := smoothField_continuous P _ (fieldFDeriv_smooth P _ (Z.pointField_smooth t))
  have hdir : Continuous (fun x => transportDirection A.κ A.direction (Z.pointField t x)) :=
    (hZ.const_smul A.κ).prodMk (continuous_const.inner hZ)
  have hC := smoothField_continuous P _ (A.linear.coefficient t).smooth
  have hsum : Continuous (fun x => ∑ i : Fin 3, (Z.pointField t x) i •
      ((A.quadratic i).coefficient t).coefficient x (Z.pointField t x)) := by
    apply continuous_finsetSum
    intro i _
    exact ((coordinate 3 i).continuous.comp hZ).smul
      ((smoothField_continuous P _ ((A.quadratic i).coefficient t).smooth).clm_apply hZ)
  exact ((hC.clm_apply hZ).add (hDZ.clm_apply hdir)).add hsum

theorem nonlinearity_value_ae (A : Data P T) (Z : FieldTower P T)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    (value P (nonlinearity P (A.atOrder P q) hq t (Z.realization (q+1) t)) :
      LiftDomain P → Vector3) =ᵐ[liftMeasure P] pointNonlinearity P A Z t := by
  let u := Z.realization (q+1) t
  let a := coefficientSobolevOperator P (A.linear.jet q t) (truncateOperator P q u)
  let b := transportBilinear P hq (velocityComponents A.κ A.direction)
    (velocityComponents_norm A.κ A.direction A.scale_bound A.direction_bound) u u
  let c := algebraicBilinear P hq
    (fun i => coefficientSobolevOperator P ((A.quadratic i).jet q t)) u u
  have hu : (value P u : LiftDomain P → Vector3) =ᵐ[liftMeasure P] Z.pointField t := by
    rw [Z.value_eq]
    exact Z.pointField_ae t
  have ha := coefficient_value_ae P (A.linear.coefficient t) (A.linear.jet q t)
    (truncateOperator P q u) (Z.pointField t) (by simpa only [value_truncateOperator] using hu)
  have hb := transportBilinear_ae P hq (velocityComponents A.κ A.direction)
    (velocityComponents_norm A.κ A.direction A.scale_bound A.direction_bound)
    u u (Z.pointField t) (Z.pointField t) hu hu (Z.pointField_smooth t)
  have hc := algebraicBilinear_ae P hq (fun i => (A.quadratic i).coefficient t)
    (fun i => (A.quadratic i).jet q t) u u (Z.pointField t) (Z.pointField t) hu hu
  change ((valueOperator P q) (a+(b+c)) : LiftDomain P → Vector3) =ᵐ[liftMeasure P] _
  rw [map_add,map_add]
  filter_upwards [Lp.coeFn_add (value P a) (value P b+value P c),
    Lp.coeFn_add (value P b) (value P c),ha,hb,hc] with x hx hy ha hb hc
  change (value P a+(value P b+value P c)) x = _
  simp only [Pi.add_apply] at hx hy
  change (value P a) x = _ at ha
  change (value P b) x = _ at hb
  change (value P c) x = _ at hc
  rw [hx,hy,ha,hb,hc]
  have hd : (∑ i : Fin 4, velocityComponents A.κ A.direction i (Z.pointField t x) •
      fieldDerivative P (standardDirection i) (Z.pointField t) x) =
      fieldFDeriv P (Z.pointField t) x (transportDirection A.κ A.direction (Z.pointField t x)) := by
    rw [← velocityComponents_direction A.κ A.direction, map_sum]
    simp only [map_smul]
    rfl
  rw [hd]
  exact (add_assoc _ _ _).symm

theorem pointEvaluation_nonlinearity (A : Data P T) (Z : FieldTower P T)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) (x : LiftDomain P) :
    pointEvaluation P x (restrictOperator P (by omega : 3 ≤ q)
      (nonlinearity P (A.atOrder P q) hq t (Z.realization (q+1) t))) =
      pointNonlinearity P A Z t x := by
  apply pointEvaluation_eq P x _ _ (pointNonlinearity_continuous P A Z t)
  simpa only [value_restrictOperator] using nonlinearity_value_ae P A Z q hq t

namespace ExactLiftedPacket

variable {P} {hT : 0 < T} {A : Data P T} {B : Budget P hT A}
  (S : ExactLiftedPacket P hT A B)

def pointTimeDerivative (t : Icc (0 : ℝ) T) (x : LiftDomain P) : Vector3 :=
  -pointNonlinearity P A S.velocity t x -
    (A.metric.coefficient t).coefficient x (S.pressure.pointField t x)

/-- Bounded Sobolev evaluation differentiates the actual solved path. -/
theorem pointField_hasDerivAt (x : LiftDomain P) (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => S.velocity.pointField (projIcc 0 T hT.le r) x)
      (S.pointTimeDerivative ⟨t,ht.1.le,ht.2.le⟩ x) t := by
  have h := ((pointEvaluation P x).comp (restrictOperator P (by omega : 3 ≤
    6))).hasFDerivAt.comp_hasDerivAt t
    (S.equation 6 le_rfl t ht)
  have hfun : (fun r => (pointEvaluation P x).comp (restrictOperator P (by omega : 3 ≤ 6))
      (extendPath T hT.le (S.velocity.realization 6) r)) =
      fun r => S.velocity.pointField (projIcc 0 T hT.le r) x := by
    funext r
    exact (S.velocity.pointField_eq_high 6 (by omega) _ x).symm
  change HasDerivAt (fun r => (pointEvaluation P x).comp (restrictOperator P (by omega : 3 ≤ 6))
    (extendPath T hT.le (S.velocity.realization 6) r)) _ t at h
  rw [hfun] at h
  simp only [comp_apply,map_sub,map_neg] at h
  rw [pointEvaluation_nonlinearity P A S.velocity 6 le_rfl,
    pointEvaluation_coefficient P (by omega : 3 ≤ 6),
    ← S.pressure.pointField_eq_high 6 (by omega)] at h
  exact h

/-- The canonical fields satisfy the literal normalized pointwise equation. -/
theorem pointwise_equation (t : Icc (0 : ℝ) T) (x : LiftDomain P) :
    S.pointTimeDerivative t x +
      (A.linear.coefficient t).coefficient x (S.velocity.pointField t x) +
      fieldFDeriv P (S.velocity.pointField t) x
        (transportDirection A.κ A.direction (S.velocity.pointField t x)) +
      (∑ i : Fin 3, (S.velocity.pointField t x) i •
        ((A.quadratic i).coefficient t).coefficient x (S.velocity.pointField t x)) +
      (A.metric.coefficient t).coefficient x (S.pressure.pointField t x) = 0 := by
  unfold pointTimeDerivative pointNonlinearity
  abel

end ExactLiftedPacket
end EulerAllOrderDriftCorrection
