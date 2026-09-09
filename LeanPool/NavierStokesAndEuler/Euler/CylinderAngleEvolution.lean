/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleRepresentative
public import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleWordBounds
public import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeRegularity

@[expose] public section

/-! Time differentiation of the actual normalized angular integral on the cylinder. -/

noncomputable section

namespace EulerCylinderAnglePrimitive

open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerMetricTransport
  EulerVolterraConvolution
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]
  {K : Type*} [TopologicalSpace K] [CompactSpace K]

omit [CompactSpace K] in
theorem pathPrimitive_translation (p : C(K,LiftL2 P)) (a : LiftTangent) :
    pathPrimitive P (pathTranslate P a p) = pathTranslate P a (pathPrimitive P p) := by
  apply ContinuousMap.ext
  intro t
  exact primitive_mixed_translation P a (p t)

theorem pathPrimitive_orbit_contDiff (p : C(K,LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (pathPrimitive P p)) := by
  simpa only [Function.comp_def, pathPrimitive_translation] using
    (pathPrimitive (K := K) P).contDiff.comp hp

theorem primitive_sobolevPath (p : C(K,LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) (q : ℕ) (t : K) :
    sobolevPath P q (pathPrimitive P p) (pathPrimitive_orbit_contDiff P p hp) t =
      sobolevPrimitive P q (sobolevPath P q p hp t) := by
  apply value_injective P
  change value P (sobolevPath P q (pathPrimitive P p) _ t) =
    primitive P (value P (sobolevPath P q p hp t))
  rw [sobolevPath_value, sobolevPath_value]
  rfl

/-- The representative of the time-dependent L² primitive is the same explicit angular integral. -/
theorem pointField_primitive_formula (p : C(K,LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
    (hmean : ∀ t y, (∫ s in (0 : ℝ)..P, pointField P p hp t (y,(s : AddCircle P)))=0)
    (t : K) (y : Vector3) (θ : ℝ) :
    pointField P (pathPrimitive P p) (pathPrimitive_orbit_contDiff P p hp) t (y,(θ : AddCircle P)) =
      EulerAngleMeanZeroPrimitive.primitive P
        (fun s => pointField P p hp t (y,(s : AddCircle P))) θ := by
  unfold pointField
  rw [primitive_sobolevPath P p hp 3 t]
  apply pointEvaluation_primitive_classical P (sobolevPath P 3 p hp t)
    (pointField P p hp t)
    (smoothField_continuous P _ (pointField_smooth P p hp t))
  · simpa only [sobolevPath_value] using pointField_ae P p hp t
  · exact hmean t

section Time

variable (T : ℝ) (hT : 0 ≤ T) (p f : C(Icc (0 : ℝ) T,LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a f))
  (hd : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT p) (f t) (Icc (0 : ℝ) T) t)

include hd in
theorem pathPrimitive_time_derivative (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (pathPrimitive P p)) (pathPrimitive P f t)
      (Icc (0 : ℝ) T) t :=
  primitive_hasDerivWithinAt P _ t (extendPath T hT p) (f t) (hd t)

include hd in
/-- The literal primitive differentiates within the closed time interval at every angle. -/
theorem classicalPrimitive_time_derivative
    (hpm : ∀ t y, (∫ s in (0 : ℝ)..P, pointField P p hp t (y,(s : AddCircle P)))=0)
    (hfm : ∀ t y, (∫ s in (0 : ℝ)..P, pointField P f hf t (y,(s : AddCircle P)))=0)
    (t : Icc (0 : ℝ) T) (y : Vector3) (θ : ℝ) :
    HasDerivWithinAt (fun r => EulerAngleMeanZeroPrimitive.primitive P
        (fun s => pointField P p hp (projIcc 0 T hT r) (y,(s : AddCircle P))) θ)
      (EulerAngleMeanZeroPrimitive.primitive P
        (fun s => pointField P f hf t (y,(s : AddCircle P))) θ) (Icc (0 : ℝ) T) t := by
  have h := pointField_hasDerivWithinAt P T hT (pathPrimitive P p) (pathPrimitive P f)
    (pathPrimitive_orbit_contDiff P p hp) (pathPrimitive_orbit_contDiff P f hf)
    (pathPrimitive_time_derivative P T hT p f hd) t (y,(θ : AddCircle P))
  rw [pointField_primitive_formula P f hf hfm t y θ] at h
  apply h.congr_of_mem _ t.property
  intro r _
  exact (pointField_primitive_formula P p hp hpm (projIcc 0 T hT r) y θ).symm

end Time
end EulerCylinderAnglePrimitive
