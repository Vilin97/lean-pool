/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketLocalHistory
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistoryPressure
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketProvider

@[expose] public section

/-!
# The history trace matches the actual forward transverse solve

The forward datum is the constructed history coordinate velocity. Both
physical velocities therefore agree at the source time τ, with the same
deformation frame on the two intervals.
-/

noncomputable section

namespace EulerTransversePacketJoin

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerTimeIntervalRestriction
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
    EulerLpCylinderRectangular
  EulerCylinderSmoothOrbit EulerPacketProfileRecursion EulerCylinderAngleAverage
  EulerTransversePacketProvider
open scoped ContDiff BoundedContinuousFunction

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) {raw : VectorField} (G : Forcing P D raw)

def pastVelocity : C(Icc (0 : ℝ) τ,LiftL2 P) :=
  B.velocityPath (G.initial τ hτ hτT.le)

def futureVelocity : C(Icc (0 : ℝ) (D.T-τ),LiftL2 P) :=
  includePath P D.support D.support_measurable
    ((G.tail τ hτ.le hτT).velocityPath (forwardInitial τ hτ hτT B G))

def pastDerivative : C(Icc (0 : ℝ) τ,LiftL2 P) :=
  B.derivativePath (G.initial τ hτ hτT.le)

def futureDerivative : C(Icc (0 : ℝ) (D.T-τ),LiftL2 P) :=
  includePath P D.support D.support_measurable
    ((G.tail τ hτ.le hτT).derivativePath (forwardInitial τ hτ hτT B G))

def pastPressure : C(Icc (0 : ℝ) τ,CylinderL2 P ℝ) :=
  B.pressurePath (G.initial τ hτ hτT.le)

def futurePressure : C(Icc (0 : ℝ) (D.T-τ),CylinderL2 P ℝ) :=
  (G.tail τ hτ.le hτT).pressurePath (forwardInitial τ hτ hτT B G)

theorem pastVelocity_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (pastVelocity τ hτ hτT B G)) :=
  B.velocityPath_orbit (G.initial τ hτ hτT.le)

theorem futureVelocity_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (futureVelocity τ hτ hτT B G)) :=
  (G.tail τ hτ.le hτT).velocityPath_orbit (forwardInitial τ hτ hτT B G)

theorem pastDerivative_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (pastDerivative τ hτ hτT B G)) :=
  B.derivativePath_orbit (G.initial τ hτ hτT.le)

theorem futureDerivative_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (futureDerivative τ hτ hτT B G)) :=
  (G.tail τ hτ.le hτT).derivativePath_orbit (forwardInitial τ hτ hτT B G)

theorem pastPressure_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (pastPressure τ hτ hτT B G)) :=
  B.pressurePath_orbit (G.initial τ hτ hτT.le)

theorem futurePressure_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (futurePressure τ hτ hτT B G)) :=
  (G.tail τ hτ.le hτT).pressurePath_orbit (forwardInitial τ hτ hτT B G)

/-- The actual forward velocity starts from the actual history velocity. -/
theorem velocity_match : pastVelocity τ hτ hτT B G ⟨τ,hτ.le,le_rfl⟩ =
    futureVelocity τ hτ hτT B G ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ := by
  let th : Icc (0 : ℝ) (D.initial τ hτ hτT.le).T := ⟨τ,hτ.le,le_rfl⟩
  let tf : Icc (0 : ℝ) (D.tail τ hτ.le hτT).T := ⟨0,le_rfl,(D.tail τ hτ.le hτT).T_pos.le⟩
  have hQ : (D.initial τ hτ hτT.le).frame.field th = (D.tail τ hτ.le hτT).frame.field tf := by
    apply BoundedContinuousFunction.ext
    intro x
    apply ContinuousLinearMap.ext
    intro v
    change D.F.field ⟨τ,hτ.le,hτT.le⟩ x (D.R v : Space) =
      D.F.field ⟨τ+0,by linarith,by linarith⟩ x (D.R v : Space)
    simp only [add_zero]
  change fullOperatorMap P ((D.initial τ hτ hτT.le).frame.field th)
    (B.coordinatePath (G.initial τ hτ hτT.le) th) =
      fullOperatorMap P ((D.tail τ hτ.le hτT).frame.field tf)
        ((EulerSourceCylinderEquation.coordinates P D.support D.support_measurable
          (D.tail τ hτ.le hτT).T (D.tail τ hτ.le hτT).T_pos.le (D.tail τ hτ.le hτT).frame
          (D.tail τ hτ.le hτT).frameDerivative (D.tail τ hτ.le hτT).frameLower
          (D.tail τ hτ.le hτT).frameLower_pos (D.tail τ hτ.le hτT).frame_lower
          (G.tail τ hτ.le hτT).path (forwardInitial τ hτ hτT B G).value tf :
            Supported P U D.support D.support_measurable) : CylinderL2 P U)
  dsimp only [tf]
  erw [EulerSourceCylinderEquation.coordinates_initial,hQ]
  rfl

end EulerTransversePacketJoin
