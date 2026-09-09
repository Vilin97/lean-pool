/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarPrimitive
public import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarClassical
public import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleRepresentative
public import LeanPool.NavierStokesAndEuler.Euler.AnglePrimitiveMap

@[expose] public section

/-!
# The actual scalar L² primitive represents the classical pressure integral

The fixed scalar embedding has a norm-one left inverse. Applying the already
proved vector H3 evaluation theorem to this embedding identifies the actual
scalar L² primitive with the literal normalized periodic integral.
-/

noncomputable section

namespace EulerCylinderScalarPrimitive

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerCylinderConstantMap EulerCylinderSmoothOrbit
    EulerCylinderSobolevSpace
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]

theorem embed_smooth (u : CylinderL2 P ℝ)
    (hu : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a u)) : SmoothOrbit P (embed P u) := by
  have he : (fun a : LiftTangent => translate P a (embed P u)) =
      (fun a => embed P (translate P a u)) :=
    funext (fun a => (map_translation P scalarEmbed a u).symm)
  change ContDiff ℝ ∞ _
  rw [he]
  exact (embed P).contDiff.comp hu

/-- The vector H3 reconstruction theorem transfers to the actual scalar primitive. -/
theorem primitive_ae_classical (u : CylinderL2 P ℝ)
    (hu : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a u))
    (f q : LiftDomain P → ℝ) (hf : Continuous f)
    (hrep : (u : LiftDomain P → ℝ) =ᵐ[liftMeasure P] f)
    (hmean : ∀ y, (∫ s in (0 : ℝ)..P, f (y,(s : AddCircle P))) = 0)
    (hq : ∀ (y : Space) (θ : ℝ), q (y,(θ : AddCircle P)) =
      EulerAngleMeanZeroPrimitive.primitive P (fun s => f (y,(s : AddCircle P))) θ) :
    (primitive P u : LiftDomain P → ℝ) =ᵐ[liftMeasure P] q := by
  let J := EulerCylinderSmoothOrbit.sobolev P 3 (embed P u) (embed_smooth P u hu)
  have hval : value P J = embed P u :=
    EulerCylinderSmoothOrbit.sobolev_value P 3 (embed P u) (embed_smooth P u hu)
  have hrepE : (value P J : LiftDomain P → Space) =ᵐ[liftMeasure P] fun x => scalarEmbed (f x) := by
    rw [hval]
    filter_upwards [map_ae P scalarEmbed u,hrep] with x he hx
    exact he.trans (congrArg scalarEmbed hx)
  have hmeanE (y : Space) : (∫ s in (0 : ℝ)..P, scalarEmbed (f (y,(s : AddCircle P)))) = 0 := by
    have hcont : Continuous (fun s : ℝ => f (y,(s : AddCircle P))) :=
      hf.comp (continuous_const.prodMk (AddCircle.continuous_mk' P))
    rw [scalarEmbed.intervalIntegral_comp_comm (hcont.intervalIntegrable 0 P),hmean,map_zero]
  have hqE (y : Space) (θ : ℝ) : scalarEmbed (q (y,(θ : AddCircle P))) =
      EulerAngleMeanZeroPrimitive.primitive P (fun s => scalarEmbed (f (y,(s : AddCircle P)))) θ :=
        by
    rw [hq]
    exact EulerAngleMeanZeroPrimitive.primitive_map scalarEmbed P _
      (hf.comp (continuous_const.prodMk (AddCircle.continuous_mk' P))) θ
  have hr := EulerCylinderAnglePrimitive.primitive_ae_classical P J
    (fun x => scalarEmbed (f x)) (fun x => scalarEmbed (q x)) (scalarEmbed.continuous.comp hf)
    hrepE hmeanE hqE
  rw [hval] at hr
  filter_upwards [hr,map_ae P scalarProject (EulerCylinderAnglePrimitive.primitive P (embed P u))]
    with x hq' hp
  exact hp.trans ((congrArg scalarProject hq').trans (project_embed (q x)))

/-- The actual scalar primitive is exactly the descended normalized integral. -/
theorem primitive_ae_constructed (u : CylinderL2 P ℝ)
    (hu : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a u))
    (f : LiftDomain P → ℝ) (hf : Continuous f)
    (hrep : (u : LiftDomain P → ℝ) =ᵐ[liftMeasure P] f)
    (hmean : ∀ y, (∫ s in (0 : ℝ)..P, f (y,(s : AddCircle P))) = 0) :
    (primitive P u : LiftDomain P → ℝ) =ᵐ[liftMeasure P] classicalPrimitive P f hf hmean :=
  primitive_ae_classical P u hu f (classicalPrimitive P f hf hmean) hf hrep hmean
    (classicalPrimitive_cover P f hf hmean)

end EulerCylinderScalarPrimitive
