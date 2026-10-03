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
  includePath (K := Icc (0 : ℝ) (D.T-τ)) (V := Vector3) P D.support D.support_measurable
    ((zeroForcing (D.tail τ hτ.le hτT)).velocityPath (forwardInitial τ hτ hτT B Y))

/-- Future derivative, given by `includePath P D.support D.support_measurable ((zeroForcing
(D.tail τ hτ.le hτT)).derivativePath (forwardInitial τ hτ hτT B Y))`. -/
def futureDerivative : C(Icc (0 : ℝ) (D.T-τ),LiftL2 P) :=
  includePath (K := Icc (0 : ℝ) (D.T-τ)) (V := Vector3) P D.support D.support_measurable
    ((zeroForcing (D.tail τ hτ.le hτT)).derivativePath (forwardInitial τ hτ hτT B Y))

theorem pastVelocity_orbit : ContDiff ℝ ∞ (fun a =>
    pathTranslate (K := Icc (0 : ℝ) τ) (V := Vector3) P a (pastVelocity τ hτ hτT B Y)) :=
  EulerTransversePacketEndpoint.velocityPath_orbit B (endpointData τ hτ hτT Y)

theorem pastDerivative_orbit : ContDiff ℝ ∞ (fun a =>
    pathTranslate (K := Icc (0 : ℝ) τ) (V := Vector3) P a (pastDerivative τ hτ hτT B Y)) :=
  EulerTransversePacketEndpoint.derivativePath_orbit B (endpointData τ hτ hτT Y)

theorem futureVelocity_orbit : ContDiff ℝ ∞ (fun a =>
    pathTranslate (K := Icc (0 : ℝ) (D.T-τ)) (V := Vector3) P a
      (futureVelocity τ hτ hτT B Y)) :=
  (zeroForcing (D.tail τ hτ.le hτT)).velocityPath_orbit (forwardInitial τ hτ hτT B Y)

theorem futureDerivative_orbit : ContDiff ℝ ∞ (fun a =>
    pathTranslate (K := Icc (0 : ℝ) (D.T-τ)) (V := Vector3) P a
      (futureDerivative τ hτ hτT B Y)) :=
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
  change fullOperatorMap (E := U) (F := Space) P ((D.initial τ hτ hτT.le).frame.field th)
    (EulerTransversePacketEndpoint.coordinatePath B (endpointData τ hτ hτT Y) th) =
      fullOperatorMap (E := U) (F := Space) P ((D.tail τ hτ.le hτT).frame.field tf)
        (((zeroForcing (D.tail τ hτ.le hτT)).coordinatePath (forwardInitial τ hτ hτT B Y) tf) :
          CylinderL2 P U)
  dsimp only [tf]
  erw [Forcing.coordinatePath_initial,hQ]
  rfl

theorem pastVelocity_eq : pastVelocity τ hτ hτT B Y =
    EulerTransversePacketEndpoint.velocityPath B (endpointData τ hτ hτT Y) := rfl

theorem pastDerivative_eq : pastDerivative τ hτ hτT B Y =
    EulerTransversePacketEndpoint.derivativePath B (endpointData τ hτ hτT Y) := rfl

theorem past_balance_ae (t : Icc (0 : ℝ) τ) :
    ∀ᵐ x ∂liftMeasure P,
      pastDerivative τ hτ hτT B Y t x +
        (D.initial τ hτ hτT.le).M.field t x.1 (pastVelocity τ hτ hτT B Y t x) +
        (-(2*⟪(D.initial τ hτ hτT.le).normal.field t x.1,
          (D.initial τ hτ hτT.le).M.field t x.1 (pastVelocity τ hτ hτT B Y t x)⟫_ℝ)/
          ‖(D.initial τ hτ hτT.le).normal.field t x.1‖^2) •
            (D.initial τ hτ hτT.le).normal.field t x.1 = 0 := by
  have h := EulerTransversePacketEndpoint.balance_ae B (endpointData τ hτ hτT Y) t
  rw [← pastDerivative_eq, ← pastVelocity_eq] at h
  exact h

theorem zeroForcing_balance_ae (D : Data U) (I : InitialData P D) (t : Icc (0 : ℝ) D.T) :
    ∀ᵐ x ∂liftMeasure P,
      ((zeroForcing D).derivativePath I t : LiftL2 P) x +
        D.M.field t x.1 (((zeroForcing D).velocityPath I t : LiftL2 P) x) +
        (-(2*⟪D.normal.field t x.1,
          D.M.field t x.1 (((zeroForcing D).velocityPath I t : LiftL2 P) x)⟫_ℝ)/
          ‖D.normal.field t x.1‖^2) • D.normal.field t x.1 = 0 := by
  have hh := EulerSourceCylinderEquation.velocity_balance_ae P D.support D.support_measurable
    D.T D.T_pos.le D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower
    (zeroForcing D).path I.value
    (fun t x => D.M.field t x) (fun t x => D.normal.field t x)
    (HistoryData.normal_ne_zero (D := D)) D.frame_tangent D.frame_range D.frame_strain t
  have h0 : ((zeroForcing (P := P) D).path t : LiftL2 P) = 0 := rfl
  filter_upwards [hh,Lp.coeFn_zero Space 2 (liftMeasure P)] with x hx hz
  simp only [h0,hz,Pi.zero_apply,inner_zero_right,zero_sub] at hx
  apply hx

theorem futureVelocity_apply (t : Icc (0 : ℝ) (D.T - τ)) :
    futureVelocity τ hτ hτT B Y t =
      ((zeroForcing (D.tail τ hτ.le hτT)).velocityPath (forwardInitial τ hτ hτT B Y) t :
        LiftL2 P) :=
  includePath_apply P D.support D.support_measurable _ t

theorem futureDerivative_apply (t : Icc (0 : ℝ) (D.T - τ)) :
    futureDerivative τ hτ hτT B Y t =
      ((zeroForcing (D.tail τ hτ.le hτT)).derivativePath (forwardInitial τ hτ hτT B Y) t :
        LiftL2 P) :=
  includePath_apply P D.support D.support_measurable _ t

theorem future_balance_ae (t : Icc (0 : ℝ) (D.T - τ)) :
    ∀ᵐ x ∂liftMeasure P,
      futureDerivative τ hτ hτT B Y t x +
        (D.tail τ hτ.le hτT).M.field t x.1 (futureVelocity τ hτ hτT B Y t x) +
        (-(2*⟪(D.tail τ hτ.le hτT).normal.field t x.1,
          (D.tail τ hτ.le hτT).M.field t x.1 (futureVelocity τ hτ hτT B Y t x)⟫_ℝ)/
          ‖(D.tail τ hτ.le hτT).normal.field t x.1‖^2) •
            (D.tail τ hτ.le hτT).normal.field t x.1 = 0 := by
  rw [futureDerivative_apply, futureVelocity_apply]
  exact zeroForcing_balance_ae (D.tail τ hτ.le hτT) _ t

theorem derivative_match : pastDerivative τ hτ hτT B Y ⟨τ,hτ.le,le_rfl⟩ =
    futureDerivative τ hτ hτT B Y ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ := by
  have hM : (D.initial τ hτ hτT.le).M.field (⟨τ,hτ.le,le_rfl⟩ : Icc (0 : ℝ) τ) =
      (D.tail τ hτ.le hτT).M.field (⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ : Icc (0 : ℝ) (D.T-τ)) :=
    EulerTransversePacketJoin.source_coefficient_match τ hτ hτT D.M
  have hm : (D.initial τ hτ hτT.le).normal.field (⟨τ,hτ.le,le_rfl⟩ : Icc (0 : ℝ) τ) =
      (D.tail τ hτ.le hτT).normal.field (⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ : Icc (0 : ℝ) (D.T-τ)) :=
    EulerTransversePacketJoin.normal_match τ hτ hτT
  have hh := past_balance_ae τ hτ hτT B Y ⟨τ,hτ.le,le_rfl⟩
  rw [hM,hm,velocity_match τ hτ hτT B Y] at hh
  apply Lp.ext
  filter_upwards [hh,future_balance_ae τ hτ hτT B Y ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩] with x hx hy
  exact add_right_cancel (add_right_cancel (hx.trans hy.symm))

theorem pastVelocity_time (t : Icc (0 : ℝ) τ) :
    HasDerivWithinAt (extendPath τ hτ.le (pastVelocity τ hτ hτT B Y))
      (pastDerivative τ hτ hτT B Y t) (Icc (0 : ℝ) τ) t := by
  have h := EulerTransversePacketEndpoint.velocityPath_time B (endpointData τ hτ hτT Y) t
  rw [← pastDerivative_eq, ← pastVelocity_eq] at h
  exact h

theorem futureVelocity_time (t : Icc (0 : ℝ) (D.T - τ)) :
    HasDerivWithinAt (extendPath (D.T-τ) (sub_pos.mpr hτT).le (futureVelocity τ hτ hτT B Y))
      (futureDerivative τ hτ hτT B Y t) (Icc (0 : ℝ) (D.T-τ)) t := by
  have hv : futureVelocity τ hτ hτT B Y =
      (zeroForcing (D.tail τ hτ.le hτT)).fullVelocityPath (forwardInitial τ hτ hτT B Y) := rfl
  have hd : futureDerivative τ hτ hτT B Y =
      (zeroForcing (D.tail τ hτ.le hτT)).fullDerivativePath (forwardInitial τ hτ hτT B Y) := rfl
  have h := (zeroForcing (D.tail τ hτ.le hτT)).fullVelocityPath_time
    (forwardInitial τ hτ hτT B Y) t
  rw [← hv, ← hd] at h
  exact h

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

omit [Fact (0 < P)] [CompleteSpace U] in
theorem match_sub_nonneg {E : Type*} [TopologicalSpace E] {S σ : ℝ} (hσS : σ < S) {x : E}
    {v : C(Icc (0 : ℝ) (S - σ), E)} (h : x = v ⟨0, le_rfl, (sub_pos.mpr hσS).le⟩) :
    x = v ⟨0, le_rfl, sub_nonneg.mpr hσS.le⟩ := h

theorem velocity_match' : pastVelocity τ hτ hτT B Y ⟨τ,hτ.le,le_rfl⟩ =
    futureVelocity τ hτ hτT B Y ⟨0,le_rfl,sub_nonneg.mpr hτT.le⟩ :=
  match_sub_nonneg hτT (velocity_match τ hτ hτT B Y)

theorem derivative_match' : pastDerivative τ hτ hτT B Y ⟨τ,hτ.le,le_rfl⟩ =
    futureDerivative τ hτ hτT B Y ⟨0,le_rfl,sub_nonneg.mpr hτT.le⟩ :=
  match_sub_nonneg hτT (derivative_match τ hτ hτT B Y)

theorem velocityPath_eq_join : velocityPath τ hτ hτT B Y =
    join D.T τ hτ.le hτT.le _ _ (velocity_match' τ hτ hτT B Y) := rfl

theorem derivativePath_eq_join : derivativePath τ hτ hτT B Y =
    join D.T τ hτ.le hτT.le _ _ (derivative_match' τ hτ hτT B Y) := rfl

theorem velocityPath_orbit :
    ContDiff ℝ ∞ (fun a =>
      pathTranslate (K := Icc (0 : ℝ) D.T) (V := Vector3) P a (velocityPath τ hτ hτT B Y)) := by
  have h := join_orbit_contDiff P D.T τ hτ.le hτT.le _ _ (velocity_match' τ hτ hτT B Y)
    (pastVelocity_orbit τ hτ hτT B Y) (futureVelocity_orbit τ hτ hτT B Y)
  rw [velocityPath_eq_join]
  exact h

theorem derivativePath_orbit :
    ContDiff ℝ ∞ (fun a =>
      pathTranslate (K := Icc (0 : ℝ) D.T) (V := Vector3) P a
        (derivativePath τ hτ hτT B Y)) := by
  have h := join_orbit_contDiff P D.T τ hτ.le hτT.le _ _ (derivative_match' τ hτ hτT B Y)
    (pastDerivative_orbit τ hτ hτT B Y) (futureDerivative_orbit τ hτ hτT B Y)
  rw [derivativePath_eq_join]
  exact h

theorem pressurePath_orbit :
    ContDiff ℝ ∞ (fun a =>
      pathTranslate (K := Icc (0 : ℝ) D.T) (V := ℝ) P a (pressurePath τ hτ hτT B Y)) :=
  sourcePressure_contDiff P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    0 (velocityPath τ hτ hτT B Y) (by simpa only [map_zero] using (contDiff_const :
      ContDiff ℝ ∞ (fun _ : LiftTangent => (0 : C(Icc (0 : ℝ) D.T,LiftL2 P)))))
    (velocityPath_orbit τ hτ hτT B Y)

theorem velocityPath_left (t : Icc (0 : ℝ) τ) :
    velocityPath τ hτ hτT B Y ⟨t,t.property.1,t.property.2.trans hτT.le⟩ =
      pastVelocity τ hτ hτT B Y t := by
  have h := join_left D.T τ hτ.le hτT.le _ _ (velocity_match' τ hτ hτT B Y) t
  rw [velocityPath_eq_join]
  exact h

theorem derivativePath_left (t : Icc (0 : ℝ) τ) :
    derivativePath τ hτ hτT B Y ⟨t,t.property.1,t.property.2.trans hτT.le⟩ =
      pastDerivative τ hτ hτT B Y t := by
  have h := join_left D.T τ hτ.le hτT.le _ _ (derivative_match' τ hτ hτT B Y) t
  rw [derivativePath_eq_join]
  exact h

theorem velocityPath_right (t : Icc τ D.T) :
    velocityPath τ hτ hτT B Y ⟨t,hτ.le.trans t.property.1,t.property.2⟩ =
      futureVelocity τ hτ hτT B Y
        ⟨(t : ℝ)-τ,sub_nonneg.mpr t.property.1,sub_le_sub_right t.property.2 τ⟩ := by
  have h := join_right D.T τ hτ.le hτT.le _ _ (velocity_match' τ hτ hτT B Y) t
  rw [velocityPath_eq_join]
  exact h

theorem derivativePath_right (t : Icc τ D.T) :
    derivativePath τ hτ hτT B Y ⟨t,hτ.le.trans t.property.1,t.property.2⟩ =
      futureDerivative τ hτ hτT B Y
        ⟨(t : ℝ)-τ,sub_nonneg.mpr t.property.1,sub_le_sub_right t.property.2 τ⟩ := by
  have h := join_right D.T τ hτ.le hτT.le _ _ (derivative_match' τ hτ hτT B Y) t
  rw [derivativePath_eq_join]
  exact h

theorem velocityPath_time (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (extendPath D.T D.T_pos.le (velocityPath τ hτ hτT B Y))
      (derivativePath τ hτ hτT B Y t) (Icc (0 : ℝ) D.T) t := by
  have h := join_hasDerivWithinAt D.T τ hτ.le hτT.le _ _ (velocity_match' τ hτ hτT B Y)
    _ _ (derivative_match' τ hτ hτT B Y)
    (pastVelocity_time τ hτ hτT B Y) (futureVelocity_time τ hτ hτT B Y) t
  rw [velocityPath_eq_join, derivativePath_eq_join]
  exact h

theorem pastVelocity_supported (s : Icc (0 : ℝ) τ) :
    pastVelocity τ hτ hτT B Y s ∈ Supported P Space D.support D.support_measurable := by
  have h := EulerTransversePacketEndpoint.velocityPath_supported B (endpointData τ hτ hτT Y) s
  rw [← pastVelocity_eq] at h
  exact h

theorem pastDerivative_supported (s : Icc (0 : ℝ) τ) :
    pastDerivative τ hτ hτT B Y s ∈ Supported P Space D.support D.support_measurable := by
  have h := EulerTransversePacketEndpoint.derivativePath_supported B (endpointData τ hτ hτT Y) s
  rw [← pastDerivative_eq] at h
  exact h

theorem futureVelocity_supported (s : Icc (0 : ℝ) (D.T - τ)) :
    futureVelocity τ hτ hτT B Y s ∈ Supported P Space D.support D.support_measurable := by
  rw [futureVelocity_apply]
  exact ((zeroForcing (D.tail τ hτ.le hτT)).velocityPath (forwardInitial τ hτ hτT B Y)
    s).property

theorem futureDerivative_supported (s : Icc (0 : ℝ) (D.T - τ)) :
    futureDerivative τ hτ hτT B Y s ∈ Supported P Space D.support D.support_measurable := by
  rw [futureDerivative_apply]
  exact ((zeroForcing (D.tail τ hτ.le hτT)).derivativePath (forwardInitial τ hτ hτT B Y)
    s).property

theorem velocityPath_supported (t : Icc (0 : ℝ) D.T) :
    velocityPath τ hτ hτT B Y t ∈ Supported P Space D.support D.support_measurable := by
  have key := join_mem D.T τ hτ.le hτT.le _ _ (velocity_match' τ hτ hτT B Y)
    (Supported P Space D.support D.support_measurable : Set (LiftL2 P))
    (pastVelocity_supported τ hτ hτT B Y) (futureVelocity_supported τ hτ hτT B Y) t
  rw [velocityPath_eq_join]
  exact key

theorem derivativePath_supported (t : Icc (0 : ℝ) D.T) :
    derivativePath τ hτ hτT B Y t ∈ Supported P Space D.support D.support_measurable := by
  have key := join_mem D.T τ hτ.le hτT.le _ _ (derivative_match' τ hτ hτT B Y)
    (Supported P Space D.support D.support_measurable : Set (LiftL2 P))
    (pastDerivative_supported τ hτ hτT B Y) (futureDerivative_supported τ hτ hτT B Y) t
  rw [derivativePath_eq_join]
  exact key

theorem pastVelocity_mean_zero (s : Icc (0 : ℝ) τ) :
    average P (pastVelocity τ hτ hτT B Y s) = 0 := by
  have h := EulerTransversePacketEndpoint.velocityPath_mean_zero B (endpointData τ hτ hτT Y) s
  rw [← pastVelocity_eq] at h
  exact h

theorem pastDerivative_mean_zero (s : Icc (0 : ℝ) τ) :
    average P (pastDerivative τ hτ hτT B Y s) = 0 := by
  have h := EulerTransversePacketEndpoint.derivativePath_mean_zero B (endpointData τ hτ hτT Y) s
  rw [← pastDerivative_eq] at h
  exact h

theorem futureVelocity_mean_zero (s : Icc (0 : ℝ) (D.T - τ)) :
    average P (futureVelocity τ hτ hτT B Y s) = 0 := by
  rw [futureVelocity_apply]
  exact EulerSourceCylinderEquation.velocity_average_zero P _ _ _ _ _ _ _ _ _ _ _
    (zeroForcing (D.tail τ hτ.le hτT)).mean_zero (forwardInitial τ hτ hτT B Y).mean_zero s

theorem futureDerivative_mean_zero (s : Icc (0 : ℝ) (D.T - τ)) :
    average P (futureDerivative τ hτ hτT B Y s) = 0 := by
  rw [futureDerivative_apply]
  exact EulerSourceCylinderEquation.velocityDerivative_average_zero P _ _ _ _ _ _ _ _ _ _ _
    (zeroForcing (D.tail τ hτ.le hτT)).mean_zero (forwardInitial τ hτ hτT B Y).mean_zero s

theorem velocityPath_mean_zero (t : Icc (0 : ℝ) D.T) :
    average P (velocityPath τ hτ hτT B Y t) = 0 := by
  have key := join_mem D.T τ hτ.le hτT.le _ _ (velocity_match' τ hτ hτT B Y)
    {u | average P u = 0} (pastVelocity_mean_zero τ hτ hτT B Y)
    (futureVelocity_mean_zero τ hτ hτT B Y) t
  rw [velocityPath_eq_join]
  exact key

theorem derivativePath_mean_zero (t : Icc (0 : ℝ) D.T) :
    average P (derivativePath τ hτ hτT B Y t) = 0 := by
  have key := join_mem D.T τ hτ.le hτT.le _ _ (derivative_match' τ hτ hτT B Y)
    {u | average P u = 0} (pastDerivative_mean_zero τ hτ hτT B Y)
    (futureDerivative_mean_zero τ hτ hτT B Y) t
  rw [derivativePath_eq_join]
  exact key

end EulerTransversePacketPrimary
