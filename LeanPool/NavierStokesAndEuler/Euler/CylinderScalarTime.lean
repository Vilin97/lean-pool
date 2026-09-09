/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarPrimitive
public import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeRegularity
import LeanPool.NavierStokesAndEuler.Euler.ClassicalPressureCurl

/-! Jointly continuous scalar representatives of actual smooth cylinder L² paths. -/

@[expose] public section


noncomputable section

namespace EulerCylinderScalarPrimitive

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerCylinderConstantMap EulerCylinderSmoothOrbit EulerMetricTransport
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]
  {K : Type*} [TopologicalSpace K] [CompactSpace K]
  (p : C(K, CylinderL2 P ℝ))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))

/-- A fixed norm-one embedding lets the existing bounded H3 evaluation recover
the genuine scalar field without making a new representative choice. -/
def scalarPointField (t : K) (x : LiftDomain P) : ℝ :=
  scalarProject (pointField P (pathMap P scalarEmbed p)
    (pathMap_orbit_contDiff P scalarEmbed p hp) t x)

theorem scalarPointField_joint_continuous :
    Continuous (fun z : K × LiftDomain P => scalarPointField P p hp z.1 z.2) :=
  scalarProject.continuous.comp
    (pointField_joint_continuous P (pathMap P scalarEmbed p)
      (pathMap_orbit_contDiff P scalarEmbed p hp))

theorem scalarPointField_smooth (t : K) (x : LiftDomain P) :
    ContDiff ℝ ∞ (localFieldLift P (scalarPointField P p hp t) x) :=
  scalarProject.contDiff.comp
    (pointField_smooth P (pathMap P scalarEmbed p)
      (pathMap_orbit_contDiff P scalarEmbed p hp) t x)

theorem scalarPointField_continuous (t : K) :
    Continuous (scalarPointField P p hp t) :=
  smoothField_continuous P _ (scalarPointField_smooth P p hp t)

theorem scalarPointField_ae (t : K) :
    (p t : LiftDomain P → ℝ) =ᵐ[liftMeasure P] scalarPointField P p hp t := by
  filter_upwards [map_ae P scalarEmbed (p t),
    pointField_ae P (pathMap P scalarEmbed p)
      (pathMap_orbit_contDiff P scalarEmbed p hp) t] with x he hr
  change (map P scalarEmbed (p t)) x = _ at hr
  have h := congrArg scalarProject (he.symm.trans hr)
  simpa only [project_embed, scalarPointField] using h

/-- Any continuous scalar representative is this same jointly continuous field. -/
theorem scalarPointField_eq (t : K) (f : LiftDomain P → ℝ) (hf : Continuous f)
    (hrep : (p t : LiftDomain P → ℝ) =ᵐ[liftMeasure P] f) :
    scalarPointField P p hp t = f :=
  Measure.eq_of_ae_eq ((scalarPointField_ae P p hp t).symm.trans hrep)
    (scalarPointField_continuous P p hp t) hf

end EulerCylinderScalarPrimitive
