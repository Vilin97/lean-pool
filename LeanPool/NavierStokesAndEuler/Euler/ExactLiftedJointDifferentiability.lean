/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.ExactLiftedPointwise
import LeanPool.NavierStokesAndEuler.Euler.CylinderCoveringDerivative
import LeanPool.NavierStokesAndEuler.Euler.SobolevJointEvaluation
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Asymptotics.Lemmas

/-! The actual exact lifted field is jointly differentiable in time and
covering-space coordinates. Uniform bounded Sobolev evaluation supplies the
time remainder estimate, so joint differentiability is a conclusion. -/

section

/-! Joint differentiation through uniformly bounded evaluation operators.
Strong continuity on the derivative vector suffices; operator-norm continuity
or differentiability of the whole family of evaluation maps is unnecessary. -/

@[expose] public section

noncomputable section

namespace EulerBoundedEvaluation

open Filter Asymptotics ContinuousLinearMap
open scoped Topology

variable {X H V : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem hasFDerivAt (E : X → H →L[ℝ] V) (C : ℝ) (hE : ∀ x, ‖E x‖ ≤ C)
    (u : ℝ → H) (u' : H) (t : ℝ) (x : X)
    (hu : HasDerivAt u u' t) (D : X →L[ℝ] V)
    (hx : HasFDerivAt (fun y => E y (u t)) D x)
    (hc : ContinuousAt (fun y => E y u') x) :
    HasFDerivAt (fun q : ℝ × X => E q.2 (u q.1))
      (((toSpanSingleton ℝ (E x u')).comp (fst ℝ ℝ X)) + D.comp (snd ℝ ℝ X)) (t,x) := by
  let l : Filter (ℝ × X) := 𝓝 (t,x)
  have htend : Tendsto (Prod.fst : ℝ × X → ℝ) l (𝓝 t) := continuous_fst.tendsto (t,x)
  have hxend : Tendsto (Prod.snd : ℝ × X → X) l (𝓝 x) := continuous_snd.tendsto (t,x)
  have hfst : (fun q : ℝ × X => q.1-t) =O[l] fun q => q-(t,x) := by
    apply IsBigO.of_bound 1
    exact Filter.Eventually.of_forall (fun q => by
      change ‖(q-(t,x)).1‖ ≤ 1*‖q-(t,x)‖
      rw [one_mul]
      exact norm_fst_le (q-(t,x)))
  have hsnd : (fun q : ℝ × X => q.2-x) =O[l] fun q => q-(t,x) := by
    apply IsBigO.of_bound 1
    exact Filter.Eventually.of_forall (fun q => by
      change ‖(q-(t,x)).2‖ ≤ 1*‖q-(t,x)‖
      rw [one_mul]
      exact norm_snd_le (q-(t,x)))
  have hr : (fun q : ℝ × X => u q.1-u t-(q.1-t) • u') =o[l] fun q => q-(t,x) :=
    (hu.isLittleO.comp_tendsto htend).trans_isBigO hfst
  have hbound : (fun q : ℝ × X => E q.2 (u q.1-u t-(q.1-t) • u')) =O[l]
      fun q => u q.1-u t-(q.1-t) • u' := by
    apply IsBigO.of_bound C
    exact Filter.Eventually.of_forall (fun q =>
      ((E q.2).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hE q.2) (norm_nonneg _)))
  have hfirst := hbound.trans_isLittleO hr
  have hcont : Tendsto (fun q : ℝ × X => E q.2 u'-E x u') l (𝓝 0) := by
    simpa only [sub_self,Function.comp_def] using
      (hc.tendsto.comp hxend).sub_const (E x u')
  have hsmall : (fun q : ℝ × X => E q.2 u'-E x u') =o[l] fun _ => (1 : ℝ) :=
    (isLittleO_one_iff ℝ).mpr hcont
  have hsecond : (fun q : ℝ × X => (q.1-t) • (E q.2 u'-E x u')) =o[l]
      fun q => q-(t,x) := by
    have h := (isBigO_refl (fun q : ℝ × X => q.1-t) l).smul_isLittleO hsmall
    simp only [smul_eq_mul,mul_one] at h
    exact h.trans_isBigO hfst
  have hthird : (fun q : ℝ × X => E q.2 (u t)-E x (u t)-D (q.2-x)) =o[l]
      fun q => q-(t,x) :=
    (hx.isLittleO.comp_tendsto hxend).trans_isBigO hsnd
  apply hasFDerivAt_iff_isLittleO.mpr
  apply ((hfirst.add hsecond).add hthird).congr_left
  intro q
  simp only [map_sub,map_smul,add_apply,comp_apply,toSpanSingleton_apply,coe_fst',coe_snd',smul_sub]
  module

end EulerBoundedEvaluation

end
end

end

@[expose] public section

noncomputable section

namespace EulerAllOrderCorrectionData.FieldTower

open Set ContinuousLinearMap EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerSobolevPointEvaluation EulerSobolevJointEvaluation EulerMetricTransport
  EulerLiftedWeakDerivative EulerCylinderSmoothOrbit EulerVolterraConvolution
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)] (A : FieldTower P T)

/-- Raw field, given by `A.pointField (projIcc 0 T hT q.1) (coveringMap P q.2)`. -/
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

/-- Raw velocity, given by `S.velocity.rawField hT.le`. -/
def rawVelocity : ℝ × LiftTangent → Vector3 := S.velocity.rawField hT.le
/-- Raw pressure, given by `S.pressure.rawField hT.le`. -/
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
