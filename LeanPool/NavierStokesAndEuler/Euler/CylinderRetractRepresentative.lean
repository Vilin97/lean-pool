/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderConstantMap
public import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeRegularity
import LeanPool.NavierStokesAndEuler.Euler.ClassicalPressureCurl

/-!
Actual pointwise representatives for coordinate spaces embedded in Space.
A fixed bounded embedding and left inverse transfer the proved H³ point
evaluation. This will apply to the two-dimensional reference plane, without
identifying an L² normal with a pointwise normal vector.
-/

@[expose] public section


noncomputable section

namespace EulerCylinderRetractRepresentative

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerCylinderConstantMap EulerVolterraConvolution EulerMetricTransport
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] {U : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  (J : U →L[ℝ] Space) (L : Space →L[ℝ] U)
  {K : Type*} [TopologicalSpace K] [CompactSpace K]
  (p : C(K, CylinderL2 P U))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))

/-- Point field, given by `L (EulerCylinderSmoothOrbit.pointField P (pathMap P J p)
(pathMap_orbit_contDiff P J p hp) t x)`. -/
def pointField (t : K) (x : LiftDomain P) : U :=
  L (EulerCylinderSmoothOrbit.pointField P (pathMap P J p) (pathMap_orbit_contDiff P J p hp) t x)

theorem pointField_joint_continuous :
    Continuous (fun z : K × LiftDomain P => pointField P J L p hp z.1 z.2) :=
  L.continuous.comp (EulerCylinderSmoothOrbit.pointField_joint_continuous P
    (pathMap P J p) (pathMap_orbit_contDiff P J p hp))

theorem pointField_smooth (t : K) (x : LiftDomain P) :
    ContDiff ℝ ∞ (localFieldLift P (pointField P J L p hp t) x) :=
  L.contDiff.comp (EulerCylinderSmoothOrbit.pointField_smooth P
    (pathMap P J p) (pathMap_orbit_contDiff P J p hp) t x)

theorem pointField_continuous (t : K) : Continuous (pointField P J L p hp t) :=
  smoothField_continuous P _ (pointField_smooth P J L p hp t)

/-- Point path as an element of `C(K,U)`. -/
def pointPath (x : LiftDomain P) : C(K,U) :=
  ⟨fun t => pointField P J L p hp t x,
    L.continuous.comp ((EulerSobolevPointEvaluation.pointEvaluation P x).continuous.comp
      (EulerCylinderSmoothOrbit.sobolevPath P 3 (pathMap P J p)
        (pathMap_orbit_contDiff P J p hp)).continuous)⟩

theorem pointField_ae (hL : ∀ v : U, L (J v) = v) (t : K) :
    p t =ᵐ[liftMeasure P] pointField P J L p hp t := by
  filter_upwards [map_ae P J (p t),EulerCylinderSmoothOrbit.pointField_ae P
    (pathMap P J p) (pathMap_orbit_contDiff P J p hp) t] with x hm he
  change (map P J (p t)) x = _ at he
  change p t x = L _
  rw [← he,hm,hL]

theorem pointField_eq (hL : ∀ v : U, L (J v) = v) (t : K)
    (f : LiftDomain P → U) (hf : Continuous f) (hrep : p t =ᵐ[liftMeasure P] f) :
    pointField P J L p hp t = f :=
  Measure.eq_of_ae_eq ((pointField_ae P J L p hp hL t).symm.trans hrep)
    (pointField_continuous P J L p hp t) hf

section Time

variable (T : ℝ) (hT : 0 ≤ T)
  (p q : C(Icc (0 : ℝ) T, CylinderL2 P U))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hq : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a q))
  (hd : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT p) (q t) (Icc (0 : ℝ) T) t)

include hd in
theorem pointPath_hasDerivWithinAt (x : LiftDomain P) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (pointPath P J L p hp x))
      (pointPath P J L q hq x t) (Icc (0 : ℝ) T) t := by
  have hdJ (s : Icc (0 : ℝ) T) :
      HasDerivWithinAt (extendPath T hT (pathMap P J p)) (pathMap P J q s)
        (Icc (0 : ℝ) T) s :=
    (map P J).hasFDerivAt.comp_hasDerivWithinAt (s : ℝ) (hd s)
  exact L.hasFDerivAt.comp_hasDerivWithinAt (t : ℝ)
    (EulerCylinderSmoothOrbit.pointField_hasDerivWithinAt P T hT
      (pathMap P J p) (pathMap P J q) (pathMap_orbit_contDiff P J p hp)
      (pathMap_orbit_contDiff P J q hq) hdJ t x)

end Time
end EulerCylinderRetractRepresentative
