/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketOrbitForcing
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSpatialMeanPath
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSpatialMeanRepresentative
public import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeRegularity
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketNonlinearForcing
import LeanPool.NavierStokesAndEuler.Euler.CylinderSpatialMeanTime

/-!
# Literal angular averages are admissible mean forcing

The cylinder-to-space mean is the actual normalized angular integral. Its
proved ordinary translation regularity is converted into literal spatial L²
jets, so the mean packet provider receives an actual admissible input.
-/

@[expose] public section


noncomputable section

namespace EulerMeanPacketProvider

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerCylinderSpatialMean
  EulerMeanSmoothRepresentative EulerMeanTimeContinuousTranslation
  EulerPacketPointJets EulerPacketProfileRecursion
open scoped ContDiff

variable (D : Data) (P : ℝ) [Fact (0 < P)]
  (p : C(Icc (0 : ℝ) D.T, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))

/-- The literal normalized integral of the actual cylinder representative. -/
def angularMeanRaw : VectorField := fun z =>
  rawMean P (pointField P p hp (D.clamp z.1)) z.2.1

include hp in
theorem angularMean_orbit :
    ContDiff ℝ ∞ (fun a : Space => pathTranslation D.T a (pathMean P p)) := by
  simpa only [pathTranslation, spatialPathTranslation, EulerLpTranslation.translation,
    EulerMeanSolenoidal.translation] using pathMean_orbit_contDiff P p hp

/-- A genuine forcing witness for the normalized angular mean. -/
def angularMeanForcing : Forcing D (angularMeanRaw D P p hp) :=
  Forcing.ofOrbitPath (pathMean P p) (angularMean_orbit D P p hp) (fun t x θ => by
    simp only [angularMeanRaw, Data.clamp_coe]
    exact congrFun (mean_pointField_eq P p hp t).symm x)

/-- A raw cylinder field identified with that representative has the same admissible mean. -/
def angularMeanForcingOfRaw (raw : VectorField)
    (hraw : ∀ (t : Icc (0 : ℝ) D.T) x θ,
      raw (t, (x, θ)) = pointField P p hp t (x, (θ : AddCircle P))) :
    Forcing D (fun z => P⁻¹ • (∫ θ in (0 : ℝ)..P, raw (z.1,(z.2.1,θ)))) := by
  apply (angularMeanForcing D P p hp).congr
  intro t x θ
  simp only [angularMeanRaw, Data.clamp_coe, rawMean]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  exact hraw t x s

end EulerMeanPacketProvider
