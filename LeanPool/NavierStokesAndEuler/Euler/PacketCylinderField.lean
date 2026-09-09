/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileRecursion
public import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeRegularity
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.LiftedWeakDerivative
import LeanPool.NavierStokesAndEuler.Euler.CylinderCoveringDerivative

/-!
# Actual cylinder-path witnesses for raw packet fields

These records contain a genuine continuous L² path, its true smooth mixed
translation orbit, and equality with the raw field on the time interval.
Time derivatives are an actual L² evolution identity, stated separately.
-/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerMetricTransport
  EulerLiftedWeakDerivative EulerPacketPointJets EulerPacketProfileRecursion
      EulerVolterraConvolution
open scoped ContDiff

/-- Field data, collecting `path`, `orbit`, `raw_eq`. -/
structure Field (P T : ℝ) [Fact (0 < P)] (raw : VectorField) where
  /-- Time-dependent path of `Field`, of type `C(Icc (0 : ℝ) T,LiftL2 P)`. -/
  path : C(Icc (0 : ℝ) T,LiftL2 P)
  orbit : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a path)
  raw_eq : ∀ (t : Icc (0 : ℝ) T) x θ,
    raw (t,(x,θ)) = pointField P path orbit t (x,(θ : AddCircle P))

variable {P T : ℝ} [Fact (0 < P)] {raw raw_t : VectorField}

/-- The derivative witness is an actual within-interval derivative in the Hilbert L² space. -/
def TimeDerivative (hT : 0 ≤ T) (G : Field P T raw) (H : Field P T raw_t) : Prop :=
  ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT G.path)
    (H.path t) (Icc (0 : ℝ) T) t

namespace Field

variable (G : Field P T raw)

include G in
theorem raw_smooth (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun y : Space × ℝ => raw (t,y)) := by
  have he : (fun y : Space × ℝ => raw (t,y)) =
      fun y : LiftTangent => pointField P G.path G.orbit t (y.1,(y.2 : AddCircle P)) :=
    funext (fun y => G.raw_eq t y.1 y.2)
  rw [he]
  exact coverField_contDiff P _ (pointField_smooth P G.path G.orbit t)

theorem raw_fderiv (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) :
    fderiv ℝ (fun y : Space × ℝ => raw (t,y)) (x,θ) =
      fieldFDeriv P (pointField P G.path G.orbit t) (x,(θ : AddCircle P)) := by
  have he : (fun y : Space × ℝ => raw (t,y)) =
      fun y : LiftTangent => pointField P G.path G.orbit t (y.1,(y.2 : AddCircle P)) :=
    funext (fun y => G.raw_eq t y.1 y.2)
  rw [he,coverField_fderiv]

theorem slicedJet_spatial (s : Set ℝ) (t : Icc (0 : ℝ) T) (x v : Space) (θ : ℝ) :
    (slicedJet s raw (t,(x,θ))).2 (spatialInjection v) =
      fieldFDeriv P (pointField P G.path G.orbit t) (x,(θ : AddCircle P)) (v,0) := by
  rw [slicedJet_space,G.raw_fderiv]

theorem slicedJet_angular (s : Set ℝ) (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) :
    (slicedJet s raw (t,(x,θ))).2 angleDirection =
      fieldFDeriv P (pointField P G.path G.orbit t) (x,(θ : AddCircle P)) (0,1) := by
  rw [slicedJet_angle,G.raw_fderiv]

theorem raw_hasDerivWithinAt (hT : 0 ≤ T) (H : Field P T raw_t)
    (h : TimeDerivative hT G H) (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) :
    HasDerivWithinAt (fun r => raw (r,(x,θ))) (raw_t (t,(x,θ))) (Icc (0 : ℝ) T) t := by
  have hd := pointField_hasDerivWithinAt P T hT G.path H.path G.orbit H.orbit h t
    (x,(θ : AddCircle P))
  rw [← H.raw_eq t x θ] at hd
  apply hd.congr_of_mem _ t.property
  intro r hr
  simpa only [projIcc_of_mem hT hr] using G.raw_eq ⟨r,hr⟩ x θ

theorem slicedJet_temporal (hT : 0 < T) (H : Field P T raw_t)
    (h : TimeDerivative hT.le G H) (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) :
    (slicedJet (Icc (0 : ℝ) T) raw (t,(x,θ))).2 timeDirection = raw_t (t,(x,θ)) :=
  slicedJet_time_eq _ _ _ _ ((uniqueDiffOn_Icc hT) _ t.property)
    (G.raw_hasDerivWithinAt hT.le H h t x θ)

end Field
end EulerPacketCylinderField
