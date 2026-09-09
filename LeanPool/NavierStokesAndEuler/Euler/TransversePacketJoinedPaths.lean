/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketTraceMatching
public import LeanPool.NavierStokesAndEuler.Euler.ElapsedTimePathNaturality
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCylinderFields

@[expose] public section

/-!
# The actual complete forced transverse path

The constructed history and forward paths are joined using their proved
matching traces. The result has a true continuous time derivative across
the junction, and its mixed translation orbit is smooth in the uniform
time-path topology.
-/

noncomputable section

namespace EulerTransversePacketJoin

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerPacketProfileRecursion EulerTransversePacketProvider EulerElapsedTimePathGluing
  EulerVolterraConvolution EulerParameterWordGevrey
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) {raw : VectorField} (G : Forcing P D raw)

def velocityPath : C(Icc (0 : ℝ) D.T,LiftL2 P) :=
  join D.T τ hτ.le hτT.le (pastVelocity τ hτ hτT B G) (futureVelocity τ hτ hτT B G)
    (velocity_match τ hτ hτT B G)

def derivativePath : C(Icc (0 : ℝ) D.T,LiftL2 P) :=
  join D.T τ hτ.le hτT.le (pastDerivative τ hτ hτT B G) (futureDerivative τ hτ hτT B G)
    (derivative_match τ hτ hτT B G)

def pressurePath : C(Icc (0 : ℝ) D.T,CylinderL2 P ℝ) :=
  join D.T τ hτ.le hτT.le (pastPressure τ hτ hτT B G) (futurePressure τ hτ hτT B G)
    (pressure_match τ hτ hτT B G)

theorem velocityPath_orbit : ContDiff ℝ ∞ (fun a => pathTranslate P a (velocityPath τ hτ hτT B G))
  :=
  join_orbit_contDiff P D.T τ hτ.le hτT.le _ _ (velocity_match τ hτ hτT B G)
    (pastVelocity_orbit τ hτ hτT B G) (futureVelocity_orbit τ hτ hτT B G)

theorem derivativePath_orbit : ContDiff ℝ ∞ (fun a => pathTranslate P a (derivativePath τ hτ hτT B
  G)) :=
  join_orbit_contDiff P D.T τ hτ.le hτT.le _ _ (derivative_match τ hτ hτT B G)
    (pastDerivative_orbit τ hτ hτT B G) (futureDerivative_orbit τ hτ hτT B G)

theorem pressurePath_orbit : ContDiff ℝ ∞ (fun a => pathTranslate P a (pressurePath τ hτ hτT B G))
  :=
  join_orbit_contDiff P D.T τ hτ.le hτT.le _ _ (pressure_match τ hτ hτT B G)
    (pastPressure_orbit τ hτ hτT B G) (futurePressure_orbit τ hτ hτT B G)

theorem velocityPath_left (t : Icc (0 : ℝ) τ) :
    velocityPath τ hτ hτT B G ⟨t,t.property.1,t.property.2.trans hτT.le⟩ =
      pastVelocity τ hτ hτT B G t :=
  join_left D.T τ hτ.le hτT.le _ _ (velocity_match τ hτ hτT B G) t

theorem derivativePath_left (t : Icc (0 : ℝ) τ) :
    derivativePath τ hτ hτT B G ⟨t,t.property.1,t.property.2.trans hτT.le⟩ =
      pastDerivative τ hτ hτT B G t :=
  join_left D.T τ hτ.le hτT.le _ _ (derivative_match τ hτ hτT B G) t

theorem pressurePath_left (t : Icc (0 : ℝ) τ) :
    pressurePath τ hτ hτT B G ⟨t,t.property.1,t.property.2.trans hτT.le⟩ =
      pastPressure τ hτ hτT B G t :=
  join_left D.T τ hτ.le hτT.le _ _ (pressure_match τ hτ hτT B G) t

theorem velocityPath_right (t : Icc τ D.T) :
    velocityPath τ hτ hτT B G ⟨t,hτ.le.trans t.property.1,t.property.2⟩ =
      futureVelocity τ hτ hτT B G ⟨(t : ℝ)-τ,sub_nonneg.mpr t.property.1,sub_le_sub_right
        t.property.2 τ⟩ :=
  join_right D.T τ hτ.le hτT.le _ _ (velocity_match τ hτ hτT B G) t

theorem derivativePath_right (t : Icc τ D.T) :
    derivativePath τ hτ hτT B G ⟨t,hτ.le.trans t.property.1,t.property.2⟩ =
      futureDerivative τ hτ hτT B G ⟨(t : ℝ)-τ,sub_nonneg.mpr t.property.1,sub_le_sub_right
        t.property.2 τ⟩ :=
  join_right D.T τ hτ.le hτT.le _ _ (derivative_match τ hτ hτT B G) t

theorem pressurePath_right (t : Icc τ D.T) :
    pressurePath τ hτ hτT B G ⟨t,hτ.le.trans t.property.1,t.property.2⟩ =
      futurePressure τ hτ hτT B G ⟨(t : ℝ)-τ,sub_nonneg.mpr t.property.1,sub_le_sub_right
        t.property.2 τ⟩ :=
  join_right D.T τ hτ.le hτT.le _ _ (pressure_match τ hτ hτT B G) t

/-- The physical time derivative exists through τ, on the closed whole interval. -/
theorem velocityPath_time (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (extendPath D.T D.T_pos.le (velocityPath τ hτ hτT B G))
      (derivativePath τ hτ hτT B G t) (Icc (0 : ℝ) D.T) t := by
  apply join_hasDerivWithinAt D.T τ hτ.le hτT.le
    (pastVelocity τ hτ hτT B G) (futureVelocity τ hτ hτT B G)
    (velocity_match τ hτ hτT B G) (pastDerivative τ hτ hτT B G) (futureDerivative τ hτ hτT B G)
    (derivative_match τ hτ hτT B G) _ _ t
  · exact B.velocityPath_time (G.initial τ hτ hτT.le)
  · exact (G.tail τ hτ.le hτT).vectorField_time (forwardInitial τ hτ hτT B G)

/-- The gluing step itself has no external radius cost. -/
theorem velocityPath_block_le {ι : Type*} [Fintype ι] (directions : ι → LiftTangent) (q n : ℕ) (a :
  LiftTangent) :
    block directions q (fun b => pathTranslate P b (velocityPath τ hτ hτT B G)) n a ≤
      block directions q (fun b => pathTranslate P b (pastVelocity τ hτ hτT B G)) n a+
        block directions q (fun b => pathTranslate P b (futureVelocity τ hτ hτT B G)) n a :=
  join_orbit_block P D.T τ hτ.le hτT.le _ _ (velocity_match τ hτ hτT B G)
    (pastVelocity_orbit τ hτ hτT B G) (futureVelocity_orbit τ hτ hτT B G) directions q n a

theorem derivativePath_block_le {ι : Type*} [Fintype ι] (directions : ι → LiftTangent) (q n : ℕ) (a
  : LiftTangent) :
    block directions q (fun b => pathTranslate P b (derivativePath τ hτ hτT B G)) n a ≤
      block directions q (fun b => pathTranslate P b (pastDerivative τ hτ hτT B G)) n a+
        block directions q (fun b => pathTranslate P b (futureDerivative τ hτ hτT B G)) n a :=
  join_orbit_block P D.T τ hτ.le hτT.le _ _ (derivative_match τ hτ hτT B G)
    (pastDerivative_orbit τ hτ hτT B G) (futureDerivative_orbit τ hτ hτT B G) directions q n a

theorem pressurePath_block_le {ι : Type*} [Fintype ι] (directions : ι → LiftTangent) (q n : ℕ) (a :
  LiftTangent) :
    block directions q (fun b => pathTranslate P b (pressurePath τ hτ hτT B G)) n a ≤
      block directions q (fun b => pathTranslate P b (pastPressure τ hτ hτT B G)) n a+
        block directions q (fun b => pathTranslate P b (futurePressure τ hτ hτT B G)) n a :=
  join_orbit_block P D.T τ hτ.le hτT.le _ _ (pressure_match τ hτ hτT B G)
    (pastPressure_orbit τ hτ hτT B G) (futurePressure_orbit τ hτ hτT B G) directions q n a

end EulerTransversePacketJoin
