/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistory
public import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarAverage
public import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarTime

@[expose] public section

/-!
# The actual normalized scalar pressure for the transverse history

The pressure is the literal mean-zero angular integral of the normal
residual of the constructed history. Its L² realization, zero mean, spatial
smoothness, support, and pointwise equation (11) are proved here.
-/

noncomputable section

namespace EulerTransversePacketProvider.HistoryData

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerMeanCoefficients
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
    EulerLpCylinderRectangular
  EulerCylinderSmoothOrbit EulerCylinderAngleAverage EulerVolterraConvolution EulerMetricTransport
  EulerSourceNormalResidualBounds EulerSourceNormalCoefficient EulerPacketProfileRecursion
  EulerCylinderScalarPrimitive
open scoped ContDiff BoundedContinuousFunction

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (B : HistoryData D) {raw : VectorField} (G : Forcing P D raw)

abbrev forceField (t : Icc (0 : ℝ) D.T) := pointField P (forcingPath G) G.path_orbit t

def normalResidual (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) : ℝ :=
  (⟪D.normal.field t x.1,forceField G t x⟫_ℝ-
    2*⟪D.normal.field t x.1,D.M.field t x.1 (B.field G t x)⟫_ℝ)/‖D.normal.field t x.1‖^2

def residualPath : C(Icc (0 : ℝ) D.T,CylinderL2 P ℝ) :=
  sourceResidual P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    (forcingPath G) (B.velocityPath G)

theorem residualPath_orbit : ContDiff ℝ ∞ (fun a => pathTranslate P a (B.residualPath G)) :=
  sourceResidual_contDiff P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    (forcingPath G) (B.velocityPath G) G.path_orbit (B.velocityPath_orbit G)

theorem residualPath_slice_smooth (t : Icc (0 : ℝ) D.T) :
    ContDiff ℝ ∞ (fun a => translate P a (B.residualPath G t)) :=
  (ContinuousMap.evalCLM ℝ t : C(Icc (0 : ℝ) D.T,CylinderL2 P ℝ) →L[ℝ]
    CylinderL2 P ℝ).contDiff.comp (B.residualPath_orbit G)

theorem residualPath_average_zero (t : Icc (0 : ℝ) D.T) : average P (B.residualPath G t) = 0 := by
  have hf : average P (forcingPath G t) = 0 := G.mean_zero t
  change average P (fullOperatorMap P
    (normalFunctional D.normal D.normalLower D.normalLower_pos D.normal_lower t)
    (forcingPath G t-(2 : ℝ) • fullOperatorMap P (D.M.field t) (B.velocityPath G t))) = 0
  rw [average_fullOperator,map_sub,map_smul,average_fullOperator,
    B.velocityPath_mean_zero G t,hf,map_zero,smul_zero,sub_self,map_zero]

theorem normalResidual_continuous (t : Icc (0 : ℝ) D.T) : Continuous (B.normalResidual G t) := by
  have hA := smoothField_continuous P _ (B.field_smooth G t)
  have hF := smoothField_continuous P _ (pointField_smooth P (forcingPath G) G.path_orbit t)
  have hM : Continuous (fun x : LiftDomain P => D.M.field t x.1) :=
    (D.M.field t).continuous.comp continuous_fst
  have hm : Continuous (fun x : LiftDomain P => D.normal.field t x.1) :=
    (D.normal.field t).continuous.comp continuous_fst
  exact ((hm.inner hF).sub (continuous_const.mul (hm.inner (hM.clm_apply hA)))).div
    (hm.norm.pow 2) (fun x => pow_ne_zero 2 (norm_ne_zero_iff.mpr (normal_ne_zero t x.1)))

theorem normalResidual_smooth (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    ContDiff ℝ ∞ (localFieldLift P (B.normalResidual G t) x) := by
  have hp : ContDiff ℝ ∞ (fun h : LiftTangent => x.1+h.1) := contDiff_const.add contDiff_fst
  have hm := (D.normal.smooth t).comp hp
  have hM := (D.M.smooth t).comp hp
  have hA := B.field_smooth G t x
  have hF := pointField_smooth P (forcingPath G) G.path_orbit t x
  have hd : ∀ h : LiftTangent, ⟪D.normal.field t (x.1+h.1),D.normal.field t (x.1+h.1)⟫_ℝ ≠ 0 := by
    intro h
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (normal_ne_zero t (x.1+h.1)))
  have h := ((hm.inner ℝ hF).sub ((contDiff_const (c := (2 : ℝ))).mul
    (hm.inner ℝ (hM.clm_apply hA)))).div (hm.inner ℝ hm) hd
  convert h using 1 <;> first
    | rfl
    | (funext z; simp only [localFieldLift,normalResidual,forceField,Function.comp_apply,
        real_inner_self_eq_norm_sq,Pi.div_apply])

/-- The actual scalar L² source equals the literal normal quotient. -/
theorem residualPath_ae (t : Icc (0 : ℝ) D.T) :
    B.residualPath G t =ᵐ[liftMeasure P] B.normalResidual G t := by
  let v := B.velocityPath G t
  let w := fullOperatorMap P (D.M.field t) v
  let r := forcingPath G t-(2 : ℝ) • w
  let N := normalFunctional D.normal D.normalLower D.normalLower_pos D.normal_lower t
  filter_upwards [EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P N) r,
    EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (D.M.field t)) v,
    Lp.coeFn_sub (forcingPath G t) ((2 : ℝ) • w),Lp.coeFn_smul (2 : ℝ) w,
    B.field_ae G t,pointField_ae P (forcingPath G) G.path_orbit t] with x hn hM hr hs hv hf
  change (EulerLpOperatorField.full (liftMeasure P) (fieldLift P N) r) x = _
  rw [hn]
  change normalFunctional D.normal D.normalLower D.normalLower_pos D.normal_lower t x.1 (r x) = _
  rw [normalFunctional_apply]
  change ⟪D.normal.field t x.1,(forcingPath G t-(2 : ℝ) • w) x⟫_ℝ/_ = _
  rw [hr]
  simp only [Pi.sub_apply]
  rw [hs]
  simp only [Pi.smul_apply]
  change ⟪D.normal.field t x.1,forcingPath G t x-(2 : ℝ) •
    (EulerLpOperatorField.full (liftMeasure P) (fieldLift P (D.M.field t)) v) x⟫_ℝ/_ = _
  rw [hM,inner_sub_right,inner_smul_right]
  change (⟪D.normal.field t x.1,forcingPath G t x⟫_ℝ-
    2*⟪D.normal.field t x.1,D.M.field t x.1 (B.velocityPath G t x)⟫_ℝ)/_ = _
  rw [hv,hf]
  rfl

theorem normalResidual_mean_zero (t : Icc (0 : ℝ) D.T) (y : Space) :
    (∫ θ in (0 : ℝ)..P, B.normalResidual G t (y,(θ : AddCircle P))) = 0 :=
  scalar_mean_zero P (B.residualPath G t) (B.residualPath_slice_smooth G t)
    (B.normalResidual G t) (B.normalResidual_continuous G t) (B.residualPath_ae G t)
    (B.residualPath_average_zero G t) y

/-- The actual mean-zero periodic angular integral. -/
def pressureField (t : Icc (0 : ℝ) D.T) : LiftDomain P → ℝ :=
  classicalPrimitive P (B.normalResidual G t) (B.normalResidual_continuous G t)
    (B.normalResidual_mean_zero G t)

theorem pressureField_ae (t : Icc (0 : ℝ) D.T) :
    B.pressurePath G t =ᵐ[liftMeasure P] B.pressureField G t :=
  primitive_ae_constructed P (B.residualPath G t) (B.residualPath_slice_smooth G t)
    (B.normalResidual G t) (B.normalResidual_continuous G t) (B.residualPath_ae G t)
    (B.normalResidual_mean_zero G t)

theorem pressureField_angle (t : Icc (0 : ℝ) D.T) (y : Space) (θ : ℝ) :
    HasDerivAt (fun s : ℝ => B.pressureField G t (y,(s : AddCircle P)))
      (B.normalResidual G t (y,(θ : AddCircle P))) θ :=
  classicalPrimitive_angle P _ _ _ y θ

theorem pressureField_mean_zero (t : Icc (0 : ℝ) D.T) (y : Space) :
    (∫ θ in (0 : ℝ)..P, B.pressureField G t (y,(θ : AddCircle P))) = 0 :=
  classicalPrimitive_mean_zero P _ _ _ y

theorem pressureField_smooth (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    ContDiff ℝ ∞ (localFieldLift P (B.pressureField G t) x) :=
  classicalPrimitive_smooth P _ _ _ (B.normalResidual_smooth G t) x

theorem pressureField_eq_scalarPointField (t : Icc (0 : ℝ) D.T) :
    B.pressureField G t = scalarPointField P (B.pressurePath G) (B.pressurePath_orbit G) t :=
  (scalarPointField_eq P (B.pressurePath G) (B.pressurePath_orbit G) t
    (B.pressureField G t) (smoothField_continuous P _ (B.pressureField_smooth G t))
    (B.pressureField_ae G t)).symm

theorem normalResidual_zero_outside (t : Icc (0 : ℝ) D.T) (y : Space) (hy : y ∉ D.support)
    (θ : AddCircle P) : B.normalResidual G t (y,θ) = 0 := by
  have hf : forceField G t (y,θ) = 0 := by
    change pointField P (forcingPath G) G.path_orbit t (y,θ) = 0
    rw [pointField_eq_representative]
    exact representative_zero_outside P D.support D.support_measurable D.support_compact.isClosed
      _ _ (G.path t).property (y,θ) hy
  simp only [normalResidual,hf,B.field_zero_outside G t (y,θ) hy,
    map_zero,inner_zero_right,mul_zero,sub_self,zero_div]

theorem pressureField_zero_outside (t : Icc (0 : ℝ) D.T) (y : Space) (hy : y ∉ D.support)
    (θ : AddCircle P) : B.pressureField G t (y,θ) = 0 :=
  classicalPrimitive_zero P _ _ _ y (B.normalResidual_zero_outside G t y hy) θ

/-- Equation (11) before taking the angular integral, valid at every point. -/
theorem field_balance (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    B.derivativeField G t x+D.M.field t x.1 (B.field G t x)+
      B.normalResidual G t x • D.normal.field t x.1 = forceField G t x := by
  have hae : (fun y : LiftDomain P => B.derivativeField G t y+D.M.field t y.1 (B.field G t y)+
      B.normalResidual G t y • D.normal.field t y.1) =ᵐ[liftMeasure P] forceField G t := by
    filter_upwards [B.balance_ae G t,B.field_ae G t,B.derivativeField_ae G t,
      pointField_ae P (forcingPath G) G.path_orbit t] with y he ha hd hf
    rw [ha,hd,hf] at he
    exact he
  have hA := smoothField_continuous P _ (B.field_smooth G t)
  have hD := smoothField_continuous P _ (B.derivativeField_smooth G t)
  have hF := smoothField_continuous P _ (pointField_smooth P (forcingPath G) G.path_orbit t)
  have hM : Continuous (fun y : LiftDomain P => D.M.field t y.1) :=
    (D.M.field t).continuous.comp continuous_fst
  have hm : Continuous (fun y : LiftDomain P => D.normal.field t y.1) :=
    (D.normal.field t).continuous.comp continuous_fst
  exact congrFun (Measure.eq_of_ae_eq hae ((hD.add (hM.clm_apply hA)).add
    ((B.normalResidual_continuous G t).smul hm)) hF) x

/-- The constructed history and its literal normalized pressure solve (11). -/
theorem field_pressure_equation (t : Icc (0 : ℝ) D.T) (y : Space) (θ : ℝ) :
    B.derivativeField G t (y,(θ : AddCircle P))+
      D.M.field t y (B.field G t (y,(θ : AddCircle P)))+
      deriv (fun s : ℝ => B.pressureField G t (y,(s : AddCircle P))) θ • D.normal.field t y =
        raw (t,(y,θ)) := by
  rw [(B.pressureField_angle G t y θ).deriv,G.raw_eq t y θ]
  exact B.field_balance G t (y,(θ : AddCircle P))

end EulerTransversePacketProvider.HistoryData
