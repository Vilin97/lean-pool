/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointForcing
public import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletRegularity
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangularRegularity

@[expose] public section

/-!
Genuine mixed spatial/angular regularity of the nonzero-terminal cylinder
inverse. The terminal datum's actual translation orbit is the only field
regularity assumption; output regularity follows from the forced inverse.
-/

noncomputable section

namespace EulerLpCylinderTranslation

open ContinuousLinearMap EulerLiftedGradientSpace
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]
  {K V : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem constantPath_orbit_contDiff (Y : CylinderL2 P V)
    (hY : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a Y)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (ContinuousMap.const K Y)) := by
  convert (ContinuousLinearMap.const ℝ K).contDiff.comp hY using 1
  funext a
  apply ContinuousMap.ext
  intro t
  rfl

end EulerLpCylinderTranslation

namespace EulerCylinderDirichlet.Coefficients

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderRectangular
  EulerTimeLp EulerVolterraConvolution EulerMeanCoefficients
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E)

variable (hQ : ContDiff ℝ ∞ (translateCoefficientPath D.Q))
  (hQ₁ : ContDiff ℝ ∞ (translateCoefficientPath D.Q₁))
  (hH : ContDiff ℝ ∞ (translateCoefficientPath D.H))
  (Y : CylinderL2 P U) (hY : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a Y))

omit [CompleteSpace U] [CompleteSpace E] in
include hY in
theorem endpointConstant_orbit_contDiff :
    ContDiff ℝ ∞ (fun a : LiftTangent =>
      pathTranslate P a (ContinuousMap.const (Icc (0 : ℝ) T) (T⁻¹ • Y))) := by
  apply constantPath_orbit_contDiff
  simpa only [map_smul] using hY.const_smul T⁻¹

omit [CompleteSpace U] [CompleteSpace E] in
include hQ₁ hY in
theorem endpointForcing_orbit_contDiff :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (D.endpointForcing P Y)) := by
  have hp := product_orbit_contDiff P D.Q₁ hQ₁
    (ContinuousMap.const (Icc (0 : ℝ) T) (T⁻¹ • Y))
    (endpointConstant_orbit_contDiff P Y hY)
  have he : D.endpointForcing P Y = (2 : ℝ) • fullMultiplierMap P D.Q₁
      (ContinuousMap.const (Icc (0 : ℝ) T) (T⁻¹ • Y)) := rfl
  simpa only [he,map_smul] using hp.const_smul (2 : ℝ)

include hQ hQ₁ hH hY

theorem endpointCoordinate_orbit_contDiff :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (D.endpointCoordinate P Y)) := by
  rw [D.endpointCoordinate_eq_forced P Y]
  simp only [map_sub]
  exact (endpointConstant_orbit_contDiff P Y hY).sub
    (D.velocityPath_orbit_contDiff P hQ hQ₁ hH (D.endpointForcing P Y)
      (D.endpointForcing_orbit_contDiff P hQ₁ Y hY))

theorem endpointAcceleration_orbit_contDiff :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (D.endpointAcceleration P Y)) := by
  rw [D.endpointAcceleration_eq_forced P Y]
  simp only [map_neg]
  exact (D.accelerationPath_orbit_contDiff P hQ hQ₁ hH (D.endpointForcing P Y)
    (D.endpointForcing_orbit_contDiff P hQ₁ Y hY)).neg

theorem endpointVelocity_orbit_contDiff :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (D.endpointVelocity P Y)) := by
  change ContDiff ℝ ∞ (fun a : LiftTangent =>
    pathTranslate P a (fullMultiplierMap P D.Q (D.endpointCoordinate P Y)))
  exact product_orbit_contDiff P D.Q hQ _ (D.endpointCoordinate_orbit_contDiff P hQ hQ₁ hH Y hY)

theorem endpointDerivative_orbit_contDiff :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (D.endpointDerivative P Y)) := by
  have hv := product_orbit_contDiff P D.Q₁ hQ₁ _
    (D.endpointCoordinate_orbit_contDiff P hQ hQ₁ hH Y hY)
  have ha := product_orbit_contDiff P D.Q hQ _
    (D.endpointAcceleration_orbit_contDiff P hQ hQ₁ hH Y hY)
  have he : D.endpointDerivative P Y =
      fullMultiplierMap P D.Q₁ (D.endpointCoordinate P Y)+
        fullMultiplierMap P D.Q (D.endpointAcceleration P Y) := rfl
  simpa only [he,map_add] using hv.add ha

end EulerCylinderDirichlet.Coefficients
