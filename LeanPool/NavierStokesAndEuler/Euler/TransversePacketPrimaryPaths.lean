/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryMatching
public import LeanPool.NavierStokesAndEuler.Euler.SourceNormalResidualBounds
public import LeanPool.NavierStokesAndEuler.Euler.ElapsedTimePathGluing
import LeanPool.NavierStokesAndEuler.Euler.ElapsedTimePathNaturality
import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderMeanZero
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedSupport

/-!
The actual primary field on the full history-plus-forward interval.
Only the history interval uses the coercive endpoint solve. The forward
interval uses its true coordinate trace, and gluing preserves the actual
time derivative and the mixed translation orbit.
-/

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
