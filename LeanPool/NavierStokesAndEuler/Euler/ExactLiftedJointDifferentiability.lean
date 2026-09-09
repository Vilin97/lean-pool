/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ExactLiftedPointwise
public import LeanPool.NavierStokesAndEuler.Euler.BoundedEvaluationDifferentiation
public import LeanPool.NavierStokesAndEuler.Euler.CylinderCoveringDerivative

@[expose] public section

/-! The actual exact lifted field is jointly differentiable in time and
covering-space coordinates. Uniform bounded Sobolev evaluation supplies the
time remainder estimate, so joint differentiability is a conclusion. -/

noncomputable section

namespace EulerAllOrderCorrectionData.FieldTower

open Set ContinuousLinearMap EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerSobolevPointEvaluation EulerSobolevJointEvaluation EulerMetricTransport
  EulerLiftedWeakDerivative EulerCylinderSmoothOrbit EulerVolterraConvolution
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)] (A : FieldTower P T)

def rawField (hT : 0 ≤ T) (q : ℝ × LiftTangent) : Vector3 :=
  A.pointField (projIcc 0 T hT q.1) (coveringMap P q.2)

theorem rawField_hasFDerivAt (hT : 0 ≤ T) (t : ℝ) (ht : t ∈ Icc 0 T)
    (u' : SobolevSpace P 3)
    (hd : HasDerivAt (extendPath T hT (A.realization 3)) u' t) (z : LiftTangent) :
    HasFDerivAt (A.rawField hT)
      (((toSpanSingleton ℝ (pointEvaluation P (coveringMap P z) u')).comp (fst ℝ ℝ LiftTangent)) +
        (fieldFDeriv P (A.pointField ⟨t,ht⟩) (coveringMap P z)).comp (snd ℝ ℝ LiftTangent)) (t,z)
          := by
  let E := fun y : LiftTangent => pointEvaluation P (coveringMap P y)
  let u := extendPath T hT (A.realization 3)
  have hs : HasFDerivAt (fun y => E y (u t))
      (fieldFDeriv P (A.pointField ⟨t,ht⟩) (coveringMap P z)) z := by
    have h := ((coverField_contDiff P (A.pointField ⟨t,ht⟩)
      (A.pointField_smooth ⟨t,ht⟩)).differentiable (by simp) z).hasFDerivAt
    rw [coverField_fderiv] at h
    simpa only [E,u,extendPath,projIcc_of_mem hT ht,pointField,coveringMap] using h
  have hc : ContinuousAt (fun y => E y u') z :=
    ((representative_continuous P u').comp (coveringMap_isOpenQuotient P).continuous).continuousAt
  exact EulerBoundedEvaluation.hasFDerivAt E (sobolevEmbeddingConstant P 3)
    (fun y => pointEvaluation_norm_le P (coveringMap P y)) u u' t z hd _ hs hc

end EulerAllOrderCorrectionData.FieldTower

namespace EulerAllOrderDriftCorrection.ExactLiftedPacket

open Set ContinuousLinearMap EulerLiftedGradientSpace EulerAllOrderCorrectionData
  EulerCylinderSobolevSpace EulerCylinderSobolev EulerSobolevPointEvaluation
  EulerSobolevCoefficientPressure EulerCorrectionResidualCancellation EulerMetricTransport
  EulerLiftedWeakDerivative EulerVolterraConvolution

variable {P T : ℝ} [Fact (0 < P)] {hT : 0 < T} {A : Data P T} {B : Budget P hT A}
  (S : ExactLiftedPacket P hT A B)

def rawVelocity : ℝ × LiftTangent → Vector3 := S.velocity.rawField hT.le
def rawPressure : ℝ × LiftTangent → Vector3 := S.pressure.rawField hT.le

theorem rawVelocity_hasFDerivAt (t : ℝ) (ht : t ∈ Ioo 0 T) (z : LiftTangent) :
    HasFDerivAt S.rawVelocity
      (((toSpanSingleton ℝ (S.pointTimeDerivative ⟨t,ht.1.le,ht.2.le⟩ (coveringMap P z))).comp
          (fst ℝ ℝ LiftTangent)) +
        (fieldFDeriv P (S.velocity.pointField ⟨t,ht.1.le,ht.2.le⟩) (coveringMap P z)).comp
          (snd ℝ ℝ LiftTangent)) (t,z) := by
  let u' := restrictOperator P (by omega : 3 ≤ 6)
    (-nonlinearity P (A.atOrder P 6) le_rfl ⟨t,ht.1.le,ht.2.le⟩
      (S.velocity.realization 7 ⟨t,ht.1.le,ht.2.le⟩) -
      coefficientSobolevOperator P (A.metric.jet 6 ⟨t,ht.1.le,ht.2.le⟩)
        (S.pressure.realization 6 ⟨t,ht.1.le,ht.2.le⟩))
  have hd : HasDerivAt (extendPath T hT.le (S.velocity.realization 3)) u' t := by
    have h := (restrictOperator P (by omega : 3 ≤ 6)).hasFDerivAt.comp_hasDerivAt t
      (S.equation 6 le_rfl t ht)
    have he : (fun r => restrictOperator P (by omega : 3 ≤ 6)
        (extendPath T hT.le (S.velocity.realization 6) r)) =
        extendPath T hT.le (S.velocity.realization 3) := by
      funext r
      exact S.velocity.restrict_realization (by omega : 3 ≤ 6) _
    change HasDerivAt (fun r => restrictOperator P (by omega : 3 ≤ 6)
      (extendPath T hT.le (S.velocity.realization 6) r)) u' t at h
    rwa [he] at h
  have hv : pointEvaluation P (coveringMap P z) u' =
      S.pointTimeDerivative ⟨t,ht.1.le,ht.2.le⟩ (coveringMap P z) := by
    have h := (pointEvaluation P (coveringMap P z)).hasFDerivAt.comp_hasDerivAt t hd
    change HasDerivAt (fun r => S.velocity.pointField (projIcc 0 T hT.le r) (coveringMap P z)) _ t
      at h
    exact h.unique (S.pointField_hasDerivAt (coveringMap P z) t ht)
  have h := S.velocity.rawField_hasFDerivAt hT.le t ⟨ht.1.le,ht.2.le⟩ u' hd z
  rw [hv] at h
  exact h

/-- The normalized equation now uses the genuine full Fréchet derivative of
the actual covering-space field, as required by physical coordinate change. -/
theorem raw_normalized_equation (t : ℝ) (ht : t ∈ Ioo 0 T) (z : LiftTangent) :
    fderiv ℝ S.rawVelocity (t,z) (1,0) +
      (A.linear.coefficient ⟨t,ht.1.le,ht.2.le⟩).coefficient (coveringMap P z) (S.rawVelocity
        (t,z)) +
      fderiv ℝ S.rawVelocity (t,z) (0,transportDirection A.κ A.direction (S.rawVelocity (t,z))) +
      (∑ i : Fin 3, (S.rawVelocity (t,z)) i •
        ((A.quadratic i).coefficient ⟨t,ht.1.le,ht.2.le⟩).coefficient (coveringMap P z)
          (S.rawVelocity (t,z))) +
      (A.metric.coefficient ⟨t,ht.1.le,ht.2.le⟩).coefficient (coveringMap P z)
        (S.rawPressure (t,z)) = 0 := by
  rw [(S.rawVelocity_hasFDerivAt t ht z).fderiv]
  simpa only [rawVelocity,rawPressure,FieldTower.rawField,projIcc_of_mem hT.le ⟨ht.1.le,ht.2.le⟩,
    add_apply,comp_apply,toSpanSingleton_apply,coe_fst',coe_snd',one_smul,zero_smul,map_zero,
    zero_add,add_zero] using S.pointwise_equation ⟨t,ht.1.le,ht.2.le⟩ (coveringMap P z)

end EulerAllOrderDriftCorrection.ExactLiftedPacket
