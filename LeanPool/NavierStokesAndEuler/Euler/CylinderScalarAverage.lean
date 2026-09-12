/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleAverage
import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleAverageRepresentative
import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarRepresentative

/-! The actual scalar average-zero condition gives literal pointwise zero angular mean. -/

@[expose] public section


noncomputable section

namespace EulerCylinderScalarPrimitive

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerCylinderConstantMap EulerCylinderSmoothOrbit
      EulerCylinderSobolevSpace
  EulerCylinderAngleAverage
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]

/-- No pointwise mean-zero condition is assumed for the representative: it
follows from the zero average of the actual scalar L² class. -/
theorem scalar_mean_zero (u : CylinderL2 P ℝ)
    (hu : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a u))
    (f : LiftDomain P → ℝ) (hf : Continuous f)
    (hrep : (u : LiftDomain P → ℝ) =ᵐ[liftMeasure P] f)
    (hz : average P u = 0) (y : Space) :
    (∫ s in (0 : ℝ)..P, f (y,(s : AddCircle P))) = 0 := by
  let J := EulerCylinderSmoothOrbit.sobolev P 3 (embed P u) (embed_smooth P u hu)
  have hval : value P J = embed P u :=
    EulerCylinderSmoothOrbit.sobolev_value P 3 (embed P u) (embed_smooth P u hu)
  have hrepE : (value P J : LiftDomain P → Space) =ᵐ[liftMeasure P] fun x => scalarEmbed (f x) := by
    rw [hval]
    filter_upwards [map_ae P scalarEmbed u,hrep] with x he hx
    exact he.trans (congrArg scalarEmbed hx)
  have havg : average P (value P J) = 0 := by
    rw [hval,average_intertwines P (embed P)
      (fun s v => map_translation P scalarEmbed (0,s) v),hz,map_zero]
  have hmean := (average_eq_zero_iff P J (fun x => scalarEmbed (f x))
    (scalarEmbed.continuous.comp hf) hrepE).1 havg y
  have hcont : Continuous (fun s : ℝ => f (y,(s : AddCircle P))) :=
    hf.comp (continuous_const.prodMk (AddCircle.continuous_mk' P))
  rw [scalarEmbed.intervalIntegral_comp_comm (hcont.intervalIntegrable 0 P)] at hmean
  have h := congrArg scalarProject hmean
  simpa only [project_embed,map_zero] using h

end EulerCylinderScalarPrimitive
