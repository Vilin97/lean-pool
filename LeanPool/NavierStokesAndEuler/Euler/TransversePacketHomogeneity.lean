/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedPaths
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldAlgebra
import LeanPool.NavierStokesAndEuler.Euler.TransverseSolutionHomogeneity

/-!
Exact homogeneity of admissible forcing and the actual joined inverse.
This permits one fixed unit-amplitude radius budget for every recursive
forcing amplitude, including zero.
-/

@[expose] public section


noncomputable section

namespace EulerTransversePacketProvider.Forcing

open Set ContinuousLinearMap EulerSmoothLimit EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerPacketProfileRecursion EulerPacketCylinderField EulerCylinderAngleAverage

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw raw' : VectorField}

/-- Scalar multiplication of the literal forcing, with its genuine path witness. -/
def smul (G : Forcing P D raw) (a : ℝ) : Forcing P D (a • raw) where
  path := a • G.path
  path_orbit := by simpa only [map_smul] using G.path_orbit.const_smul a
  raw_eq := (Field.smul (⟨includePath P D.support D.support_measurable G.path,
    G.path_orbit,G.raw_eq⟩ : Field P D.T raw) a).raw_eq
  mean_zero t := by
    change average P (a • (G.path t : CylinderL2 P Space)) = 0
    rw [map_smul,G.mean_zero t,smul_zero]

theorem velocityPath_eq_smul (G : Forcing P D raw) (H : Forcing P D raw')
    (I J : InitialData P D) (a : ℝ) (h : H.path = a • G.path) (hi : J.value = a • I.value) :
    H.velocityPath J = a • G.velocityPath I := by
  change EulerSourceCylinderEquation.velocity P D.support D.support_measurable D.T D.T_pos.le
      D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower H.path J.value = _
  rw [h,hi]
  exact EulerSourceCylinderEquation.velocity_smul P D.support D.support_measurable D.T D.T_pos.le
    D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower a G.path I.value

theorem derivativePath_eq_smul (G : Forcing P D raw) (H : Forcing P D raw')
    (I J : InitialData P D) (a : ℝ) (h : H.path = a • G.path) (hi : J.value = a • I.value) :
    H.derivativePath J = a • G.derivativePath I := by
  change EulerSourceCylinderEquation.velocityDerivative P D.support D.support_measurable D.T
      D.T_pos.le
      D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower H.path J.value = _
  rw [h,hi]
  exact EulerSourceCylinderEquation.velocityDerivative_smul P D.support D.support_measurable D.T
      D.T_pos.le
    D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower a G.path I.value

end EulerTransversePacketProvider.Forcing

namespace EulerTransversePacketProvider.HistoryData

open Set ContinuousLinearMap EulerSmoothLimit EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerPacketProfileRecursion EulerTimeLp

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (B : HistoryData D) {raw raw' : VectorField}
  (G : Forcing P D raw) (H : Forcing P D raw') (a : ℝ) (h : H.path = a • G.path)

include h

theorem coordinatePath_eq_smul : B.coordinatePath H = a • B.coordinatePath G := by
  have hf : forcingPath H = a • forcingPath G := by unfold forcingPath; rw [h,map_smul]
  change B.coefficients.velocityPath P (pathLp D.T D.T_pos.le (forcingPath H)) = _
  rw [hf,pathLp_smul,map_smul]
  rfl

theorem velocityPath_eq_smul : B.velocityPath H = a • B.velocityPath G := by
  have hf : forcingPath H = a • forcingPath G := by unfold forcingPath; rw [h,map_smul]
  change B.coefficients.physicalVelocity P (forcingPath H) = _
  rw [hf,B.coefficients.physicalVelocity_smul P a (forcingPath G)]
  rfl

theorem derivativePath_eq_smul : B.derivativePath H = a • B.derivativePath G := by
  have hf : forcingPath H = a • forcingPath G := by unfold forcingPath; rw [h,map_smul]
  change B.coefficients.physicalDerivative P (forcingPath H) = _
  rw [hf,B.coefficients.physicalDerivative_smul P a (forcingPath G)]
  rfl

end EulerTransversePacketProvider.HistoryData

namespace EulerElapsedTimePathGluing

open Set EulerPacketTimePathGluing

theorem join_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S τ : ℝ) (hτ : 0 ≤ τ) (hτS : τ ≤ S)
    (u : C(Icc (0 : ℝ) τ, E)) (v : C(Icc (0 : ℝ) (S - τ), E))
    (hm : u ⟨τ, hτ, le_rfl⟩ = v ⟨0, le_rfl, sub_nonneg.mpr hτS⟩) (a : ℝ) :
    join S τ hτ hτS (a • u) (a • v) (congrArg (a • ·) hm) =
      a • join S τ hτ hτS u v hm := by
  apply ContinuousMap.ext
  intro t
  change (if (t : ℝ) ≤ τ then a • u (projIcc 0 τ hτ t)
    else a • v (elapsedTime S τ (projIcc τ S hτS t))) =
      a • (if (t : ℝ) ≤ τ then u (projIcc 0 τ hτ t)
        else v (elapsedTime S τ (projIcc τ S hτS t)))
  split <;> rfl

end EulerElapsedTimePathGluing

namespace EulerTransversePacketJoin

open Set ContinuousLinearMap EulerSmoothLimit EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerPacketProfileRecursion EulerTransversePacketProvider EulerElapsedTimePathGluing
  EulerTimeIntervalRestriction

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) {raw raw' : VectorField}
  (G : Forcing P D raw) (H : Forcing P D raw') (a : ℝ) (h : H.path = a • G.path)

include h

omit [CompleteSpace U] in
theorem initial_forcing_eq_smul : (H.initial τ hτ hτT.le).path = a • (G.initial τ hτ hτT.le).path
    := by
  change initialPath D.T τ hτT.le H.path = a • initialPath D.T τ hτT.le G.path
  rw [h,map_smul]

omit [CompleteSpace U] in
theorem tail_forcing_eq_smul : (H.tail τ hτ.le hτT).path = a • (G.tail τ hτ.le hτT).path := by
  change tailPath D.T τ hτ.le H.path = a • tailPath D.T τ hτ.le G.path
  rw [h,map_smul]

theorem forwardInitial_eq_smul : (forwardInitial τ hτ hτT B H).value =
    a • (forwardInitial τ hτ hτT B G).value := by
  apply Subtype.ext
  change B.coordinatePath (H.initial τ hτ hτT.le) ⟨τ,hτ.le,le_rfl⟩ =
    a • B.coordinatePath (G.initial τ hτ hτT.le) ⟨τ,hτ.le,le_rfl⟩
  rw [B.coordinatePath_eq_smul (G.initial τ hτ hτT.le) (H.initial τ hτ hτT.le) a
    (initial_forcing_eq_smul τ hτ hτT G H a h),ContinuousMap.smul_apply]

theorem pastVelocity_eq_smul : pastVelocity τ hτ hτT B H = a • pastVelocity τ hτ hτT B G :=
  B.velocityPath_eq_smul (G.initial τ hτ hτT.le) (H.initial τ hτ hτT.le) a
    (initial_forcing_eq_smul τ hτ hτT G H a h)

theorem pastDerivative_eq_smul : pastDerivative τ hτ hτT B H = a • pastDerivative τ hτ hτT B G :=
  B.derivativePath_eq_smul (G.initial τ hτ hτT.le) (H.initial τ hτ hτT.le) a
    (initial_forcing_eq_smul τ hτ hτT G H a h)

theorem futureVelocity_eq_smul : futureVelocity τ hτ hτT B H = a • futureVelocity τ hτ hτT B G := by
  unfold futureVelocity
  rw [(G.tail τ hτ.le hτT).velocityPath_eq_smul (H.tail τ hτ.le hτT)
    (forwardInitial τ hτ hτT B G) (forwardInitial τ hτ hτT B H) a
    (tail_forcing_eq_smul τ hτ hτT G H a h) (forwardInitial_eq_smul τ hτ hτT B G H a h)]
  exact (includePath P D.support D.support_measurable).map_smul a _

theorem futureDerivative_eq_smul : futureDerivative τ hτ hτT B H = a • futureDerivative τ hτ hτT B
    G := by
  unfold futureDerivative
  rw [(G.tail τ hτ.le hτT).derivativePath_eq_smul (H.tail τ hτ.le hτT)
    (forwardInitial τ hτ hτT B G) (forwardInitial τ hτ hτT B H) a
    (tail_forcing_eq_smul τ hτ hτT G H a h) (forwardInitial_eq_smul τ hτ hτT B G H a h)]
  exact (includePath P D.support D.support_measurable).map_smul a _

theorem velocityPath_eq_smul : velocityPath τ hτ hτT B H = a • velocityPath τ hτ hτT B G := by
  apply ContinuousMap.ext
  intro t
  rw [ContinuousMap.smul_apply]
  by_cases ht : (t : ℝ) ≤ τ
  · let th : Icc (0 : ℝ) τ := ⟨t,t.property.1,ht⟩
    rw [velocityPath_left τ hτ hτT B H th,velocityPath_left τ hτ hτT B G th,
      pastVelocity_eq_smul τ hτ hτT B G H a h,ContinuousMap.smul_apply]
  · let tr : Icc τ D.T := ⟨t,(not_le.mp ht).le,t.property.2⟩
    rw [velocityPath_right τ hτ hτT B H tr,velocityPath_right τ hτ hτT B G tr,
      futureVelocity_eq_smul τ hτ hτT B G H a h,ContinuousMap.smul_apply]

theorem derivativePath_eq_smul : derivativePath τ hτ hτT B H = a • derivativePath τ hτ hτT B G := by
  apply ContinuousMap.ext
  intro t
  rw [ContinuousMap.smul_apply]
  by_cases ht : (t : ℝ) ≤ τ
  · let th : Icc (0 : ℝ) τ := ⟨t,t.property.1,ht⟩
    rw [derivativePath_left τ hτ hτT B H th,derivativePath_left τ hτ hτT B G th,
      pastDerivative_eq_smul τ hτ hτT B G H a h,ContinuousMap.smul_apply]
  · let tr : Icc τ D.T := ⟨t,(not_le.mp ht).le,t.property.2⟩
    rw [derivativePath_right τ hτ hτT B H tr,derivativePath_right τ hτ hτT B G tr,
      futureDerivative_eq_smul τ hτ hτT B G H a h,ContinuousMap.smul_apply]

end EulerTransversePacketJoin
