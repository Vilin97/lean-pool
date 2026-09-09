/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryField
public import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarAverage
public import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarParity
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderPressureLocality
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJets

@[expose] public section

/-! The primary pressure is the actual mean-zero angular primitive of the
normal residual.  Its field satisfies the homogeneous packet equation. -/

noncomputable section

namespace EulerTransversePacketPrimary

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerMeanCoefficients
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
    EulerLpCylinderRectangular
  EulerCylinderSmoothOrbit EulerCylinderAngleAverage EulerMetricTransport EulerCylinderLocalSupport
  EulerSourceNormalResidualBounds EulerSourceNormalCoefficient EulerPacketProfileRecursion
  EulerCylinderScalarPrimitive EulerTransversePacketProvider EulerPacketCylinderField
  EulerPacketPointJets EulerCylinderFieldReflection
open scoped ContDiff BoundedContinuousFunction

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) (Y : InitialData P D)

def normalResidual (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) : ℝ :=
  -(2*⟪D.normal.field t x.1,D.M.field t x.1
    (pointField P (velocityPath τ hτ hτT B Y) (velocityPath_orbit τ hτ hτT B Y) t x)⟫_ℝ)/
      ‖D.normal.field t x.1‖^2

def residualPath : C(Icc (0 : ℝ) D.T,CylinderL2 P ℝ) :=
  sourceResidual P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    0 (velocityPath τ hτ hτT B Y)

theorem residualPath_orbit : ContDiff ℝ ∞ (fun a => pathTranslate P a (residualPath τ hτ hτT B Y))
  :=
  sourceResidual_contDiff P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    0 (velocityPath τ hτ hτT B Y) (by simpa only [map_zero] using (contDiff_const :
      ContDiff ℝ ∞ (fun _ : LiftTangent => (0 : C(Icc (0 : ℝ) D.T,LiftL2 P)))))
    (velocityPath_orbit τ hτ hτT B Y)

theorem residualPath_slice_smooth (t : Icc (0 : ℝ) D.T) :
    ContDiff ℝ ∞ (fun a => translate P a (residualPath τ hτ hτT B Y t)) :=
  (ContinuousMap.evalCLM ℝ t : C(Icc (0 : ℝ) D.T,CylinderL2 P ℝ) →L[ℝ]
    CylinderL2 P ℝ).contDiff.comp (residualPath_orbit τ hτ hτT B Y)

theorem residualPath_average_zero (t : Icc (0 : ℝ) D.T) :
    average P (residualPath τ hτ hτT B Y t) = 0 := by
  change average P (fullOperatorMap P
    (normalFunctional D.normal D.normalLower D.normalLower_pos D.normal_lower t)
    (0-(2 : ℝ) • fullOperatorMap P (D.M.field t) (velocityPath τ hτ hτT B Y t))) = 0
  simp only [average_fullOperator,map_sub,map_smul,map_zero,
    velocityPath_mean_zero τ hτ hτT B Y t,smul_zero,sub_self]

theorem normalResidual_continuous (t : Icc (0 : ℝ) D.T) :
    Continuous (normalResidual τ hτ hτT B Y t) := by
  have hA := smoothField_continuous P _
    (pointField_smooth P (velocityPath τ hτ hτT B Y) (velocityPath_orbit τ hτ hτT B Y) t)
  have hM : Continuous (fun x : LiftDomain P => D.M.field t x.1) :=
    (D.M.field t).continuous.comp continuous_fst
  have hm : Continuous (fun x : LiftDomain P => D.normal.field t x.1) :=
    (D.normal.field t).continuous.comp continuous_fst
  exact (continuous_const.mul (hm.inner (hM.clm_apply hA))).neg.div (hm.norm.pow 2)
    (fun x => ne_of_gt (D.normalLower_pos.trans_le (D.normal_lower t x.1)))

theorem normalResidual_smooth (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    ContDiff ℝ ∞ (localFieldLift P (normalResidual τ hτ hτT B Y t) x) := by
  have hp : ContDiff ℝ ∞ (fun h : LiftTangent => x.1+h.1) := contDiff_const.add contDiff_fst
  have hm := (D.normal.smooth t).comp hp
  have hM := (D.M.smooth t).comp hp
  have hA := pointField_smooth P (velocityPath τ hτ hτT B Y) (velocityPath_orbit τ hτ hτT B Y) t x
  have hd : ∀ h : LiftTangent, ⟪D.normal.field t (x.1+h.1),D.normal.field t (x.1+h.1)⟫_ℝ ≠ 0 := by
    intro h
    rw [real_inner_self_eq_norm_sq]
    exact ne_of_gt (D.normalLower_pos.trans_le (D.normal_lower t (x.1+h.1)))
  have h := ((contDiff_const (c := (2 : ℝ))).mul (hm.inner ℝ (hM.clm_apply hA))).neg.div
    (hm.inner ℝ hm) hd
  convert! h using 1
  first
    | rfl
    | (funext z; simp only [localFieldLift,normalResidual,Function.comp_apply,
        real_inner_self_eq_norm_sq,Pi.div_apply])

theorem residualPath_ae (t : Icc (0 : ℝ) D.T) :
    residualPath τ hτ hτT B Y t =ᵐ[liftMeasure P] normalResidual τ hτ hτT B Y t := by
  let v := velocityPath τ hτ hτT B Y t
  let w := fullOperatorMap P (D.M.field t) v
  let N := normalFunctional D.normal D.normalLower D.normalLower_pos D.normal_lower t
  have he : residualPath τ hτ hτT B Y t = (-2 : ℝ) • fullOperatorMap P N w := by
    change fullOperatorMap P N (0-(2 : ℝ) • w) = _
    simp only [zero_sub,map_neg,map_smul,neg_smul]
  rw [he]
  filter_upwards [Lp.coeFn_smul (-2 : ℝ) (fullOperatorMap P N w),
    EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P N) w,
    EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (D.M.field t)) v,
    pointField_ae P (velocityPath τ hτ hτT B Y) (velocityPath_orbit τ hτ hτT B Y) t]
    with x hs hn hm hv
  rw [hs]
  change (fullOperatorMap P N w) x = N x.1 (w x) at hn
  change w x = D.M.field t x.1 (v x) at hm
  change (-2 : ℝ)*((fullOperatorMap P N w) x) = _
  rw [hn]
  change (-2 : ℝ)*(normalFunctional D.normal D.normalLower D.normalLower_pos D.normal_lower
    t x.1 (w x)) = _
  rw [normalFunctional_apply,hm]
  change (-2 : ℝ)*(⟪D.normal.field t x.1,D.M.field t x.1
    (velocityPath τ hτ hτT B Y t x)⟫_ℝ/‖D.normal.field t x.1‖^2) = _
  rw [hv]
  unfold normalResidual
  ring

theorem normalResidual_mean_zero (t : Icc (0 : ℝ) D.T) (y : Space) :
    (∫ θ in (0 : ℝ)..P, normalResidual τ hτ hτT B Y t (y,(θ : AddCircle P))) = 0 :=
  scalar_mean_zero P (residualPath τ hτ hτT B Y t) (residualPath_slice_smooth τ hτ hτT B Y t)
    (normalResidual τ hτ hτT B Y t) (normalResidual_continuous τ hτ hτT B Y t)
    (residualPath_ae τ hτ hτT B Y t) (residualPath_average_zero τ hτ hτT B Y t) y

def pressureField (t : Icc (0 : ℝ) D.T) : LiftDomain P → ℝ :=
  classicalPrimitive P (normalResidual τ hτ hτT B Y t) (normalResidual_continuous τ hτ hτT B Y t)
    (normalResidual_mean_zero τ hτ hτT B Y t)

theorem pressureField_ae (t : Icc (0 : ℝ) D.T) :
    pressurePath τ hτ hτT B Y t =ᵐ[liftMeasure P] pressureField τ hτ hτT B Y t :=
  primitive_ae_constructed P (residualPath τ hτ hτT B Y t) (residualPath_slice_smooth τ hτ hτT B Y
    t)
    (normalResidual τ hτ hτT B Y t) (normalResidual_continuous τ hτ hτT B Y t)
    (residualPath_ae τ hτ hτT B Y t) (normalResidual_mean_zero τ hτ hτT B Y t)

theorem pressureField_smooth (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    ContDiff ℝ ∞ (localFieldLift P (pressureField τ hτ hτT B Y t) x) :=
  classicalPrimitive_smooth P _ _ _ (normalResidual_smooth τ hτ hτT B Y t) x

theorem pressureField_eq_scalarPointField (t : Icc (0 : ℝ) D.T) :
    pressureField τ hτ hτT B Y t =
      scalarPointField P (pressurePath τ hτ hτT B Y) (pressurePath_orbit τ hτ hτT B Y) t :=
  (scalarPointField_eq P (pressurePath τ hτ hτT B Y) (pressurePath_orbit τ hτ hτT B Y) t
    (pressureField τ hτ hτT B Y t) (smoothField_continuous P _ (pressureField_smooth τ hτ hτT B Y
      t))
    (pressureField_ae τ hτ hτT B Y t)).symm

theorem scalar_eq_pressureField (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    scalar τ hτ hτT B Y (t,(x,θ)) = pressureField τ hτ hτT B Y t (x,(θ : AddCircle P)) := by
  rw [scalar_eq_pointField,pressureField_eq_scalarPointField]

theorem pressureField_angle (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    HasDerivAt (fun s : ℝ => pressureField τ hτ hτT B Y t (x,(s : AddCircle P)))
      (normalResidual τ hτ hτT B Y t (x,(θ : AddCircle P))) θ :=
  classicalPrimitive_angle P _ _ _ x θ

theorem scalar_normalized (t : Icc (0 : ℝ) D.T) (x : Space) :
    (∫ θ in (0 : ℝ)..P, scalar τ hτ hτT B Y (t,(x,θ))) = 0 := by
  simp_rw [scalar_eq_pressureField]
  exact classicalPrimitive_mean_zero P _ _ _ x

theorem normalResidual_zero_outside (t : Icc (0 : ℝ) D.T) (y : Space) (hy : y ∉ D.support)
    (θ : AddCircle P) : normalResidual τ hτ hτT B Y t (y,θ) = 0 := by
  have hv := pointField_zero_outside P D.support D.support_measurable
    (velocityPath τ hτ hτT B Y) (velocityPath_orbit τ hτ hτT B Y) D.support_compact.isClosed
    (velocityPath_supported τ hτ hτT B Y) t (y,θ) hy
  simp only [normalResidual,hv,map_zero,inner_zero_right,mul_zero,neg_zero,zero_div]

theorem scalar_zero_outside (t : ℝ) (x : Space) (hx : x ∉ D.support) (θ : ℝ) :
    scalar τ hτ hτT B Y (t,(x,θ)) = 0 := by
  change scalarPointField P (pressurePath τ hτ hτT B Y) (pressurePath_orbit τ hτ hτT B Y)
    (D.clamp t) (x,(θ : AddCircle P)) = 0
  rw [← pressureField_eq_scalarPointField]
  exact classicalPrimitive_zero P _ _ _ x (normalResidual_zero_outside τ hτ hτT B Y (D.clamp t) x
    hx) _

theorem scalarGradient_zero_outside (t : ℝ) (x : Space) (hx : x ∉ D.support) (θ : ℝ) :
    pressureGradient (scalar τ hτ hτT B Y) (t,(x,θ)) = 0 :=
  pressureGradient_zero_outside (scalar τ hτ hτT B Y) t D.support D.support_compact.isClosed
    (scalar_zero_outside τ hτ hτT B Y t) x hx θ

theorem field_balance (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    pointField P (derivativePath τ hτ hτT B Y) (derivativePath_orbit τ hτ hτT B Y) t x+
      D.M.field t x.1 (pointField P (velocityPath τ hτ hτT B Y) (velocityPath_orbit τ hτ hτT B Y) t
        x)+
      normalResidual τ hτ hτT B Y t x • D.normal.field t x.1 = 0 := by
  have hae : (fun y : LiftDomain P =>
      pointField P (derivativePath τ hτ hτT B Y) (derivativePath_orbit τ hτ hτT B Y) t y+
      D.M.field t y.1 (pointField P (velocityPath τ hτ hτT B Y) (velocityPath_orbit τ hτ hτT B Y) t
        y)+
      normalResidual τ hτ hτT B Y t y • D.normal.field t y.1) =ᵐ[liftMeasure P] (fun _ => 0) := by
    filter_upwards [balance_ae τ hτ hτT B Y t,
      pointField_ae P (velocityPath τ hτ hτT B Y) (velocityPath_orbit τ hτ hτT B Y) t,
      pointField_ae P (derivativePath τ hτ hτT B Y) (derivativePath_orbit τ hτ hτT B Y) t]
      with y he hv hd
    rw [hv,hd] at he
    exact he
  have hA := smoothField_continuous P _
    (pointField_smooth P (velocityPath τ hτ hτT B Y) (velocityPath_orbit τ hτ hτT B Y) t)
  have hD := smoothField_continuous P _
    (pointField_smooth P (derivativePath τ hτ hτT B Y) (derivativePath_orbit τ hτ hτT B Y) t)
  have hM : Continuous (fun y : LiftDomain P => D.M.field t y.1) :=
    (D.M.field t).continuous.comp continuous_fst
  have hm : Continuous (fun y : LiftDomain P => D.normal.field t y.1) :=
    (D.normal.field t).continuous.comp continuous_fst
  exact congrFun (Measure.eq_of_ae_eq hae ((hD.add (hM.clm_apply hA)).add
    ((normalResidual_continuous τ hτ hτT B Y t).smul hm)) continuous_const) x

theorem equation (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    vectorDerivative τ hτ hτT B Y (t,(x,θ))+
      D.strain (t,(x,θ)) (vector τ hτ hτT B Y (t,(x,θ)))+
      deriv (fun s => scalar τ hτ hτT B Y (t,(x,s))) θ • D.normalField (t,(x,θ)) = 0 := by
  have hp : (fun s => scalar τ hτ hτT B Y (t,(x,s))) =
      fun s : ℝ => pressureField τ hτ hτT B Y t (x,(s : AddCircle P)) :=
    funext (scalar_eq_pressureField τ hτ hτT B Y t x)
  rw [hp,(pressureField_angle τ hτ hτT B Y t x θ).deriv]
  simpa only [vectorDerivative,vector,Data.strain,Data.normalField,Data.clamp_coe] using
    field_balance τ hτ hτT B Y t (x,(θ : AddCircle P))

theorem jet_equation (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    linearPart (D.strain (t,(x,θ)))
        (slicedJet (Icc (0 : ℝ) D.T) (vector τ hτ hτT B Y) (t,(x,θ)))+
      fastPressure (D.normalField (t,(x,θ))) (pressureJet (scalar τ hτ hτT B Y) (t,(x,θ))) = 0 := by
  change (slicedJet (Icc (0 : ℝ) D.T) (vector τ hτ hτT B Y) (t,(x,θ))).2 timeDirection+
    D.strain (t,(x,θ)) (vector τ hτ hτT B Y (t,(x,θ)))+_ = _
  rw [(vectorField τ hτ hτT B Y).slicedJet_temporal D.T_pos (vectorDerivativeField τ hτ hτT B Y)
    (vectorField_time τ hτ hτT B Y),fastPressure_pressureJet _ (scalar τ hτ hτT B Y) t x θ
      ((scalar_smooth τ hτ hτT B Y t).differentiable (by simp) (x,θ))]
  exact equation τ hτ hτT B Y t x θ

variable (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
  (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
  (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
  (hH : ∀ t x, B.H.field t (-x) = B.H.field t x)
  (hY : reflection P (Y.value : CylinderL2 P U) = -(Y.value : CylinderL2 P U))

include hSym hF hM hH hY

theorem normalResidual_odd (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    normalResidual τ hτ hτT B Y t (-x,((-θ : ℝ) : AddCircle P)) =
      -normalResidual τ hτ hτT B Y t (x,(θ : AddCircle P)) := by
  have hv := vector_odd τ hτ hτT B Y hSym hF hM hH hY t x θ
  simp only [vector,Data.clamp_coe] at hv
  simp only [normalResidual,D.normal_even hF,hM,hv,map_neg,inner_neg_right]
  ring

theorem scalar_even (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    scalar τ hτ hτT B Y (t,(-x,-θ)) = scalar τ hτ hτT B Y (t,(x,θ)) := by
  rw [scalar_eq_pressureField,scalar_eq_pressureField]
  exact classicalPrimitive_joint_even P _ _ _
    (normalResidual_odd τ hτ hτT B Y hSym hF hM hH hY t) x θ

theorem scalarGradient_odd (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    pressureGradient (scalar τ hτ hτT B Y) (t,(-x,-θ)) =
      -pressureGradient (scalar τ hτ hτT B Y) (t,(x,θ)) :=
  pressureGradient_odd (scalar τ hτ hτT B Y) t (scalar_smooth τ hτ hτT B Y t)
    (scalar_even τ hτ hτT B Y hSym hF hM hH hY t) x θ

end EulerTransversePacketPrimary
