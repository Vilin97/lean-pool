/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketAngularForcing
public import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleAverageTime

@[expose] public section

/-! Literal angular averaging preserves actual raw cylinder-path admissibility. -/

noncomputable section

namespace EulerPacketCylinderField.Field

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerMetricTransport
  EulerCylinderSobolevSpace EulerCylinderAngleAverage EulerCylinderSpatialMean
  EulerPacketProfileRecursion
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField}

/-- Its path is the genuine average operator, and its raw field is exactly the angular integral. -/
def angleMean (G : Field P T raw) : Field P T (EulerPacketProfileRecursion.angleMean P raw) :=
  ofLifted (pathAverage P G.path) (pathAverage_orbit_contDiff P G.path G.orbit)
    (fun t x => rawMean P (pointField P G.path G.orbit t) x.1)
    (fun t => (rawMean_continuous P (sobolevPath P 3 G.path G.orbit t)
      (pointField P G.path G.orbit t) (smoothField_continuous P _ (pointField_smooth P G.path
        G.orbit t))
      (by simpa only [sobolevPath_value] using pointField_ae P G.path G.orbit t)).comp
        continuous_fst)
    (fun t => by
      have h := average_ae_rawMean P (sobolevPath P 3 G.path G.orbit t)
        (pointField P G.path G.orbit t) (smoothField_continuous P _ (pointField_smooth P G.path
          G.orbit t))
        (by simpa only [sobolevPath_value] using pointField_ae P G.path G.orbit t)
      simpa only [sobolevPath_value,pathAverage_apply] using h)
    (fun t x θ => by
      change P⁻¹ • (∫ s in (0 : ℝ)..P, raw (t,(x,s))) =
        P⁻¹ • (∫ s in (0 : ℝ)..P, pointField P G.path G.orbit t (x,(s : AddCircle P)))
      congr 1
      apply intervalIntegral.integral_congr
      intro s _
      exact G.raw_eq t x s)

/-- Subtracting the literal mean is an operation on the actual cylinder L² path. -/
def highPart (G : Field P T raw) : Field P T (raw-EulerPacketProfileRecursion.angleMean P raw) :=
  G.sub G.angleMean

@[simp] theorem angleMean_path (G : Field P T raw) :
    G.angleMean.path = pathAverage P G.path := rfl

/-- The same actual angular integral is admissible for the constructed ordinary-space mean solver. -/
def meanForcing (D : EulerMeanPacketProvider.Data) {raw : VectorField}
    (G : Field P D.T raw) :
    EulerMeanPacketProvider.Forcing D (EulerPacketProfileRecursion.angleMean P raw) :=
  EulerMeanPacketProvider.angularMeanForcing_of_raw D P G.path G.orbit raw G.raw_eq

end EulerPacketCylinderField.Field
