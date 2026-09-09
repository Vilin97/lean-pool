/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSpatialMeanPath
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSpatialMeanRepresentative
public import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeRegularity
public import LeanPool.NavierStokesAndEuler.Euler.MeanSmoothRepresentative

/-! The literal angular mean of a solved cylinder path is an actual smooth spatial L² path. -/

@[expose] public section


noncomputable section

namespace EulerCylinderSpatialMean

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSobolevSpace EulerCylinderSmoothOrbit EulerLpCylinderTranslation
  EulerCylinderSpatialEmbedding EulerMetricTransport
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]
  {K : Type*} [TopologicalSpace K] [CompactSpace K]
  (p : C(K, LiftL2 P)) (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))

include hp

/-- The ordinary L² time path represents the actual angular integral at every time. -/
theorem pathMean_pointField_ae (t : K) :
    (pathMean P p t : Space → Space) =ᵐ[volume] rawMean P (pointField P p hp t) := by
  have h := mean_ae_rawMean P (sobolevPath P 3 p hp t) (pointField P p hp t)
    (smoothField_continuous P _ (pointField_smooth P p hp t))
    (by simpa only [sobolevPath_value] using pointField_ae P p hp t)
  simpa only [pathMean_apply, sobolevPath_value] using h

theorem mean_slice_orbit (t : K) :
    EulerMeanSmoothRepresentative.SmoothOrbit (pathMean P p t) := by
  have h := (ContinuousMap.evalCLM ℝ t).contDiff.comp (pathMean_orbit_contDiff P p hp)
  exact h

/-- Uniqueness identifies the mean solver's ordinary representative with the literal integral. -/
theorem mean_pointField_eq (t : K) :
    EulerMeanSmoothRepresentative.representative (pathMean P p t) (mean_slice_orbit P p hp t) =
      rawMean P (pointField P p hp t) := by
  apply EulerMeanSmoothRepresentative.representative_unique
  · exact rawMean_continuous P (sobolevPath P 3 p hp t) (pointField P p hp t)
      (smoothField_continuous P _ (pointField_smooth P p hp t))
      (by simpa only [sobolevPath_value] using pointField_ae P p hp t)
  · exact pathMean_pointField_ae P p hp t

theorem rawMean_pointField_contDiff (t : K) :
    ContDiff ℝ ∞ (rawMean P (pointField P p hp t)) := by
  rw [← mean_pointField_eq P p hp t]
  exact EulerMeanSmoothRepresentative.representative_smooth _ _

end EulerCylinderSpatialMean
