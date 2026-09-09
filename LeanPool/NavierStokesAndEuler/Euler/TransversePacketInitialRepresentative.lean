/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketInitial
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCylinderFields

@[expose] public section

/-! The raw forward field attains the actual continuous representative of
its prescribed supported initial coordinates. -/

noncomputable section

namespace EulerTransversePacketProvider.Forcing

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderRectangular
  EulerCylinderSmoothOrbit EulerMetricTransport EulerPacketProfileRecursion

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)

theorem vector_initial_of_representative (f : LiftDomain P → U) (hf : Continuous f)
    (hrep : (I.value : CylinderL2 P U) =ᵐ[liftMeasure P] f) (y : Space) (θ : ℝ) :
    G.vector I (0,(y,θ)) = D.frame.field ⟨0,le_rfl,D.T_pos.le⟩ y (f (y,(θ : AddCircle P))) := by
  let t0 : Icc (0 : ℝ) D.T := ⟨0,le_rfl,D.T_pos.le⟩
  have he : G.fullVelocityPath I t0 =
      fullOperatorMap P (D.frame.field t0) (I.value : CylinderL2 P U) :=
    congrArg Subtype.val (G.velocityPath_initial I)
  have hp := pointField_ae P (G.fullVelocityPath I) (G.velocityPath_orbit I) t0
  rw [he] at hp
  have hae : pointField P (G.fullVelocityPath I) (G.velocityPath_orbit I) t0 =ᵐ[liftMeasure P]
      fun x => D.frame.field t0 x.1 (f x) := by
    filter_upwards [hp,EulerLpOperatorField.full_ae (liftMeasure P)
      (fieldLift P (D.frame.field t0)) (I.value : CylinderL2 P U),hrep] with x hx hm hf
    exact hx.symm.trans (hm.trans (congrArg (D.frame.field t0 x.1) hf))
  have hpoint : pointField P (G.fullVelocityPath I) (G.velocityPath_orbit I) t0 =
      fun x => D.frame.field t0 x.1 (f x) :=
    Measure.eq_of_ae_eq hae
      (smoothField_continuous P _ (pointField_smooth P _ _ t0))
      (((D.frame.field t0).continuous.comp continuous_fst).clm_apply hf)
  calc
    _ = pointField P (G.fullVelocityPath I) (G.velocityPath_orbit I) t0 (y,(θ : AddCircle P)) :=
      (G.vectorField I).raw_eq t0 y θ
    _ = _ := congrFun hpoint (y,(θ : AddCircle P))

end EulerTransversePacketProvider.Forcing
