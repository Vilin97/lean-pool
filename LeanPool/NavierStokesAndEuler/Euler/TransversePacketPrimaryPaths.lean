/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.SourceNormalResidualBounds
public import LeanPool.NavierStokesAndEuler.Euler.ElapsedTimePathGluing
import LeanPool.NavierStokesAndEuler.Euler.ElapsedTimePathNaturality
import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderMeanZero
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedSupport
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketEndpoint
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketIntervalData
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCylinderFields
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketInitial
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketTraceMatching

/-!
The actual primary field on the full history-plus-forward interval.
Only the history interval uses the coercive endpoint solve. The forward
interval uses its true coordinate trace, and gluing preserves the actual
time derivative and the mixed translation orbit.
-/

section

/-!
The primary history has prescribed terminal displacement. Its actual
coordinate velocity at τ is the initial value of the homogeneous forward
solve. Both the physical velocity and its true derivative match at τ.
-/

@[expose] public section

noncomputable section

namespace EulerTransversePacketPrimary

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
      EulerLpCylinderRectangular
  EulerCylinderSmoothOrbit EulerPacketProfileRecursion EulerTransversePacketProvider
  EulerVolterraConvolution
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

/-- Zero forcing, bundling `path`, `path_orbit`, `raw_eq`, `mean_zero`. -/
def zeroForcing (D : Data U) : Forcing P D (0 : VectorField) where
  path := 0
  path_orbit := by
    simpa only [map_zero] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : LiftTangent => (0 : C(Icc (0 : ℝ) D.T,LiftL2 P))))
  raw_eq t x θ := (pointField_zero_of_value_zero P _ _ t (by simp) (x,(θ : AddCircle P))).symm
  mean_zero _ := map_zero _

variable {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) (Y : InitialData P D)

/-- Endpoint data, bundling `value`, `orbit`, `mean_zero`. -/
def endpointData : InitialData P (D.initial τ hτ hτT.le) where
  value := Y.value
  orbit := Y.orbit
  mean_zero := Y.mean_zero

/-- Forward initial, bundling `value`, `orbit`, `mean_zero`. -/
def forwardInitial : InitialData P (D.tail τ hτ.le hτT) where
  value := (EulerTransversePacketEndpoint.terminalInitial B (endpointData τ hτ hτT Y)).value
  orbit := (EulerTransversePacketEndpoint.terminalInitial B (endpointData τ hτ hτT Y)).orbit
  mean_zero := (EulerTransversePacketEndpoint.terminalInitial B (endpointData τ hτ hτT Y)).mean_zero

/-- Past velocity, given by `EulerTransversePacketEndpoint.velocityPath B (endpointData τ hτ hτT
Y)`. -/
def pastVelocity : C(Icc (0 : ℝ) τ,LiftL2 P) :=
  EulerTransversePacketEndpoint.velocityPath B (endpointData τ hτ hτT Y)

/-- Past derivative, given by `EulerTransversePacketEndpoint.derivativePath B (endpointData τ hτ
hτT Y)`. -/
def pastDerivative : C(Icc (0 : ℝ) τ,LiftL2 P) :=
  EulerTransversePacketEndpoint.derivativePath B (endpointData τ hτ hτT Y)

/-- Future velocity, given by `includePath P D.support D.support_measurable ((zeroForcing
(D.tail τ hτ.le hτT)).velocityPath (forwardInitial τ hτ hτT B Y))`. -/
def futureVelocity : C(Icc (0 : ℝ) (D.T-τ),LiftL2 P) :=
  includePath P D.support D.support_measurable
    ((zeroForcing (D.tail τ hτ.le hτT)).velocityPath (forwardInitial τ hτ hτT B Y))

/-- Future derivative, given by `includePath P D.support D.support_measurable ((zeroForcing
(D.tail τ hτ.le hτT)).derivativePath (forwardInitial τ hτ hτT B Y))`. -/
def futureDerivative : C(Icc (0 : ℝ) (D.T-τ),LiftL2 P) :=
  includePath P D.support D.support_measurable
    ((zeroForcing (D.tail τ hτ.le hτT)).derivativePath (forwardInitial τ hτ hτT B Y))

theorem pastVelocity_orbit : ContDiff ℝ ∞ (fun a => pathTranslate P a (pastVelocity τ hτ hτT B Y))
    :=
  EulerTransversePacketEndpoint.velocityPath_orbit B (endpointData τ hτ hτT Y)

theorem pastDerivative_orbit : ContDiff ℝ ∞ (fun a => pathTranslate P a (pastDerivative τ hτ hτT B
    Y)) :=
  EulerTransversePacketEndpoint.derivativePath_orbit B (endpointData τ hτ hτT Y)

theorem futureVelocity_orbit : ContDiff ℝ ∞ (fun a => pathTranslate P a (futureVelocity τ hτ hτT B
    Y)) :=
  (zeroForcing (D.tail τ hτ.le hτT)).velocityPath_orbit (forwardInitial τ hτ hτT B Y)

theorem futureDerivative_orbit : ContDiff ℝ ∞ (fun a => pathTranslate P a (futureDerivative τ hτ
    hτT B Y)) :=
  (zeroForcing (D.tail τ hτ.le hτT)).derivativePath_orbit (forwardInitial τ hτ hτT B Y)

theorem velocity_match : pastVelocity τ hτ hτT B Y ⟨τ,hτ.le,le_rfl⟩ =
    futureVelocity τ hτ hτT B Y ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ := by
  let th : Icc (0 : ℝ) τ := ⟨τ,hτ.le,le_rfl⟩
  let tf : Icc (0 : ℝ) (D.T-τ) := ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩
  have hQ : (D.initial τ hτ hτT.le).frame.field th = (D.tail τ hτ.le hτT).frame.field tf := by
    apply BoundedContinuousFunction.ext
    intro x
    apply ContinuousLinearMap.ext
    intro v
    change D.F.field ⟨τ,hτ.le,hτT.le⟩ x (D.R v : Space) =
      D.F.field ⟨τ+0,by linarith,by linarith⟩ x (D.R v : Space)
    simp only [add_zero]
  change fullOperatorMap P ((D.initial τ hτ hτT.le).frame.field th)
    (EulerTransversePacketEndpoint.coordinatePath B (endpointData τ hτ hτT Y) th) =
      fullOperatorMap P ((D.tail τ hτ.le hτT).frame.field tf)
        (((zeroForcing (D.tail τ hτ.le hτT)).coordinatePath (forwardInitial τ hτ hτT B Y) tf) :
          CylinderL2 P U)
  dsimp only [tf]
  erw [Forcing.coordinatePath_initial,hQ]
  rfl

theorem past_balance_ae (t : Icc (0 : ℝ) τ) :
    ∀ᵐ x ∂liftMeasure P,
      pastDerivative τ hτ hτT B Y t x +
        (D.initial τ hτ hτT.le).M.field t x.1 (pastVelocity τ hτ hτT B Y t x) +
        (-(2*⟪(D.initial τ hτ hτT.le).normal.field t x.1,
          (D.initial τ hτ hτT.le).M.field t x.1 (pastVelocity τ hτ hτT B Y t x)⟫_ℝ)/
          ‖(D.initial τ hτ hτT.le).normal.field t x.1‖^2) •
            (D.initial τ hτ hτT.le).normal.field t x.1 = 0 :=
  EulerTransversePacketEndpoint.balance_ae B (endpointData τ hτ hτT Y) t

theorem future_balance_ae (t : Icc (0 : ℝ) (D.T - τ)) :
    ∀ᵐ x ∂liftMeasure P,
      futureDerivative τ hτ hτT B Y t x +
        (D.tail τ hτ.le hτT).M.field t x.1 (futureVelocity τ hτ hτT B Y t x) +
        (-(2*⟪(D.tail τ hτ.le hτT).normal.field t x.1,
          (D.tail τ hτ.le hτT).M.field t x.1 (futureVelocity τ hτ hτT B Y t x)⟫_ℝ)/
          ‖(D.tail τ hτ.le hτT).normal.field t x.1‖^2) •
            (D.tail τ hτ.le hτT).normal.field t x.1 = 0 := by
  let Df := D.tail τ hτ.le hτT
  have hh := EulerSourceCylinderEquation.velocity_balance_ae P D.support D.support_measurable
    Df.T Df.T_pos.le Df.frame Df.frameDerivative Df.frameLower Df.frameLower_pos Df.frame_lower
    (zeroForcing Df).path (forwardInitial τ hτ hτT B Y).value
    (fun t x => Df.M.field t x) (fun t x => Df.normal.field t x)
    (HistoryData.normal_ne_zero (D := Df)) Df.frame_tangent Df.frame_range Df.frame_strain t
  filter_upwards [hh,Lp.coeFn_zero Space 2 (liftMeasure P)] with x hx hz
  change futureDerivative τ hτ hτT B Y t x+Df.M.field t x.1 (futureVelocity τ hτ hτT B Y t x) +
    ((⟪Df.normal.field t x.1,(0 : LiftL2 P) x⟫_ℝ -
      2*⟪Df.normal.field t x.1,Df.M.field t x.1 (futureVelocity τ hτ hτT B Y t x)⟫_ℝ)/
      ‖Df.normal.field t x.1‖^2) • Df.normal.field t x.1 = (0 : LiftL2 P) x at hx
  simpa only [hz,Pi.zero_apply,inner_zero_right,zero_sub] using hx

theorem derivative_match : pastDerivative τ hτ hτT B Y ⟨τ,hτ.le,le_rfl⟩ =
    futureDerivative τ hτ hτT B Y ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ := by
  let th : Icc (0 : ℝ) τ := ⟨τ,hτ.le,le_rfl⟩
  let tf : Icc (0 : ℝ) (D.T-τ) := ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩
  have hM : (D.initial τ hτ hτT.le).M.field th = (D.tail τ hτ.le hτT).M.field tf :=
    EulerTransversePacketJoin.source_coefficient_match τ hτ hτT D.M
  have hm : (D.initial τ hτ hτT.le).normal.field th = (D.tail τ hτ.le hτT).normal.field tf :=
    EulerTransversePacketJoin.normal_match τ hτ hτT
  have hh := past_balance_ae τ hτ hτT B Y th
  rw [hM,hm,velocity_match τ hτ hτT B Y] at hh
  apply Lp.ext
  filter_upwards [hh,future_balance_ae τ hτ hτT B Y tf] with x hx hy
  exact add_right_cancel (add_right_cancel (hx.trans hy.symm))

theorem pastVelocity_time (t : Icc (0 : ℝ) τ) :
    HasDerivWithinAt (extendPath τ hτ.le (pastVelocity τ hτ hτT B Y))
      (pastDerivative τ hτ hτT B Y t) (Icc (0 : ℝ) τ) t :=
  EulerTransversePacketEndpoint.velocityPath_time B (endpointData τ hτ hτT Y) t

theorem futureVelocity_time (t : Icc (0 : ℝ) (D.T - τ)) :
    HasDerivWithinAt (extendPath (D.T-τ) (sub_pos.mpr hτT).le (futureVelocity τ hτ hτT B Y))
      (futureDerivative τ hτ hτT B Y t) (Icc (0 : ℝ) (D.T-τ)) t :=
  (zeroForcing (D.tail τ hτ.le hτT)).vectorField_time (forwardInitial τ hτ hτT B Y) t

end EulerTransversePacketPrimary

end
end

end

@[expose] public section

noncomputable section

namespace EulerTransversePacketPrimary

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerElapsedTimePathGluing
  EulerVolterraConvolution EulerTransversePacketProvider EulerCylinderAngleAverage
  EulerSourceNormalResidualBounds
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) (Y : InitialData P D)

/-- Velocity path, given by `join D.T τ hτ.le hτT.le (pastVelocity τ hτ hτT B Y) (futureVelocity
τ hτ hτT B Y) (velocity_match τ hτ hτT B Y)`. -/
def velocityPath : C(Icc (0 : ℝ) D.T,LiftL2 P) :=
  join D.T τ hτ.le hτT.le (pastVelocity τ hτ hτT B Y) (futureVelocity τ hτ hτT B Y)
    (velocity_match τ hτ hτT B Y)

/-- Derivative path, given by `join D.T τ hτ.le hτT.le (pastDerivative τ hτ hτT B Y)
(futureDerivative τ hτ hτT B Y) (derivative_match τ hτ hτT B Y)`. -/
def derivativePath : C(Icc (0 : ℝ) D.T,LiftL2 P) :=
  join D.T τ hτ.le hτT.le (pastDerivative τ hτ hτT B Y) (futureDerivative τ hτ hτT B Y)
    (derivative_match τ hτ hτT B Y)

/-- Pressure path, given by `sourcePressure P D.M D.normal D.normalLower D.normalLower_pos
D.normal_lower 0 (velocityPath τ hτ hτT B Y)`. -/
def pressurePath : C(Icc (0 : ℝ) D.T,CylinderL2 P ℝ) :=
  sourcePressure P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    0 (velocityPath τ hτ hτT B Y)

theorem velocityPath_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (velocityPath τ hτ hτT B Y)) :=
  join_orbit_contDiff P D.T τ hτ.le hτT.le _ _ (velocity_match τ hτ hτT B Y)
    (pastVelocity_orbit τ hτ hτT B Y) (futureVelocity_orbit τ hτ hτT B Y)

theorem derivativePath_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (derivativePath τ hτ hτT B Y)) :=
  join_orbit_contDiff P D.T τ hτ.le hτT.le _ _ (derivative_match τ hτ hτT B Y)
    (pastDerivative_orbit τ hτ hτT B Y) (futureDerivative_orbit τ hτ hτT B Y)

theorem pressurePath_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (pressurePath τ hτ hτT B Y)) :=
  sourcePressure_contDiff P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    0 (velocityPath τ hτ hτT B Y) (by simpa only [map_zero] using (contDiff_const :
      ContDiff ℝ ∞ (fun _ : LiftTangent => (0 : C(Icc (0 : ℝ) D.T,LiftL2 P)))))
    (velocityPath_orbit τ hτ hτT B Y)

theorem velocityPath_left (t : Icc (0 : ℝ) τ) :
    velocityPath τ hτ hτT B Y ⟨t,t.property.1,t.property.2.trans hτT.le⟩ =
      pastVelocity τ hτ hτT B Y t :=
  join_left D.T τ hτ.le hτT.le _ _ (velocity_match τ hτ hτT B Y) t

theorem derivativePath_left (t : Icc (0 : ℝ) τ) :
    derivativePath τ hτ hτT B Y ⟨t,t.property.1,t.property.2.trans hτT.le⟩ =
      pastDerivative τ hτ hτT B Y t :=
  join_left D.T τ hτ.le hτT.le _ _ (derivative_match τ hτ hτT B Y) t

theorem velocityPath_right (t : Icc τ D.T) :
    velocityPath τ hτ hτT B Y ⟨t,hτ.le.trans t.property.1,t.property.2⟩ =
      futureVelocity τ hτ hτT B Y
        ⟨(t : ℝ)-τ,sub_nonneg.mpr t.property.1,sub_le_sub_right t.property.2 τ⟩ :=
  join_right D.T τ hτ.le hτT.le _ _ (velocity_match τ hτ hτT B Y) t

theorem derivativePath_right (t : Icc τ D.T) :
    derivativePath τ hτ hτT B Y ⟨t,hτ.le.trans t.property.1,t.property.2⟩ =
      futureDerivative τ hτ hτT B Y
        ⟨(t : ℝ)-τ,sub_nonneg.mpr t.property.1,sub_le_sub_right t.property.2 τ⟩ :=
  join_right D.T τ hτ.le hτT.le _ _ (derivative_match τ hτ hτT B Y) t

theorem velocityPath_time (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (extendPath D.T D.T_pos.le (velocityPath τ hτ hτT B Y))
      (derivativePath τ hτ hτT B Y t) (Icc (0 : ℝ) D.T) t :=
  join_hasDerivWithinAt D.T τ hτ.le hτT.le
    (pastVelocity τ hτ hτT B Y) (futureVelocity τ hτ hτT B Y) (velocity_match τ hτ hτT B Y)
    (pastDerivative τ hτ hτT B Y) (futureDerivative τ hτ hτT B Y) (derivative_match τ hτ hτT B Y)
    (pastVelocity_time τ hτ hτT B Y) (futureVelocity_time τ hτ hτT B Y) t

theorem velocityPath_supported (t : Icc (0 : ℝ) D.T) :
    velocityPath τ hτ hτT B Y t ∈ Supported P Space D.support D.support_measurable :=
  join_mem D.T τ hτ.le hτT.le _ _ (velocity_match τ hτ hτT B Y) _
    (EulerTransversePacketEndpoint.velocityPath_supported B (endpointData τ hτ hτT Y))
    (fun s => ((zeroForcing (D.tail τ hτ.le hτT)).velocityPath (forwardInitial τ hτ hτT B Y)
        s).property) t

theorem derivativePath_supported (t : Icc (0 : ℝ) D.T) :
    derivativePath τ hτ hτT B Y t ∈ Supported P Space D.support D.support_measurable :=
  join_mem D.T τ hτ.le hτT.le _ _ (derivative_match τ hτ hτT B Y) _
    (EulerTransversePacketEndpoint.derivativePath_supported B (endpointData τ hτ hτT Y))
    (fun s => ((zeroForcing (D.tail τ hτ.le hτT)).derivativePath (forwardInitial τ hτ hτT B Y)
        s).property) t

theorem velocityPath_mean_zero (t : Icc (0 : ℝ) D.T) :
    average P (velocityPath τ hτ hτT B Y t) = 0 := by
  apply join_mem D.T τ hτ.le hτT.le _ _ (velocity_match τ hτ hτT B Y)
    {u | average P u = 0} _ _ t
  · exact EulerTransversePacketEndpoint.velocityPath_mean_zero B (endpointData τ hτ hτT Y)
  · intro s
    exact EulerSourceCylinderEquation.velocity_average_zero P D.support D.support_measurable
      (D.T-τ) (sub_pos.mpr hτT).le (D.tail τ hτ.le hτT).frame (D.tail τ hτ.le hτT).frameDerivative
      (D.tail τ hτ.le hτT).frameLower (D.tail τ hτ.le hτT).frameLower_pos (D.tail τ hτ.le
          hτT).frame_lower
      (zeroForcing (D.tail τ hτ.le hτT)).path (forwardInitial τ hτ hτT B Y).value
      (zeroForcing (D.tail τ hτ.le hτT)).mean_zero (forwardInitial τ hτ hτT B Y).mean_zero s

theorem derivativePath_mean_zero (t : Icc (0 : ℝ) D.T) :
    average P (derivativePath τ hτ hτT B Y t) = 0 := by
  apply join_mem D.T τ hτ.le hτT.le _ _ (derivative_match τ hτ hτT B Y)
    {u | average P u = 0} _ _ t
  · exact EulerTransversePacketEndpoint.derivativePath_mean_zero B (endpointData τ hτ hτT Y)
  · intro s
    exact EulerSourceCylinderEquation.velocityDerivative_average_zero P D.support
        D.support_measurable
      (D.T-τ) (sub_pos.mpr hτT).le (D.tail τ hτ.le hτT).frame (D.tail τ hτ.le hτT).frameDerivative
      (D.tail τ hτ.le hτT).frameLower (D.tail τ hτ.le hτT).frameLower_pos (D.tail τ hτ.le
          hτT).frame_lower
      (zeroForcing (D.tail τ hτ.le hτT)).path (forwardInitial τ hτ hτT B Y).value
      (zeroForcing (D.tail τ hτ.le hτT)).mean_zero (forwardInitial τ hτ hτT B Y).mean_zero s

end EulerTransversePacketPrimary
