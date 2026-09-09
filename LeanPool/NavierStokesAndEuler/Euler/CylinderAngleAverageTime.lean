/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeRegularity
public import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleAverage
import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleAverageRepresentative

/-! Actual angular means of the reconstructed continuous-time cylinder fields. -/

@[expose] public section


noncomputable section

namespace EulerCylinderAngleAverage

open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerMetricTransport
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]
  {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- The actual L² kernel condition and the literal classical mean agree at every time. -/
theorem pointField_mean_zero_iff (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) (t : K) :
    average P (p t) = 0 ↔
      ∀ y, (∫ s in (0 : ℝ)..P, pointField P p hp t (y,(s : AddCircle P))) = 0 := by
  have h := average_eq_zero_iff P (sobolevPath P 3 p hp t) (pointField P p hp t)
    (smoothField_continuous P _ (pointField_smooth P p hp t))
    (by simpa only [sobolevPath_value] using pointField_ae P p hp t)
  simpa only [sobolevPath_value] using h

theorem pathAverage_eq_zero_iff (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) :
    pathAverage P p = 0 ↔
      ∀ t y, (∫ s in (0 : ℝ)..P, pointField P p hp t (y,(s : AddCircle P))) = 0 := by
  constructor
  · intro h t
    apply (pointField_mean_zero_iff P p hp t).mp
    exact congrArg (fun q : C(K,LiftL2 P) => q t) h
  · intro h
    apply ContinuousMap.ext
    intro t
    exact (pointField_mean_zero_iff P p hp t).mpr (h t)

theorem pathAverage_orbit_contDiff (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (pathAverage P p)) := by
  simpa only [Function.comp_def, pathAverage_translation] using
    (pathAverage (K := K) (V := Vector3) P).contDiff.comp hp

end EulerCylinderAngleAverage
