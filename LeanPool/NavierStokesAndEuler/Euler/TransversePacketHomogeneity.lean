/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedPaths
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletData
public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderEquation

/-!
Exact homogeneity of admissible forcing and the actual joined inverse.
This permits one fixed unit-amplitude radius budget for every recursive
forcing amplitude, including zero.
-/

section

/-! Exact scalar homogeneity of the constructed history and forward paths. -/

@[expose] public section

noncomputable section

namespace EulerCylinderDirichlet.Coefficients

open Set ContinuousLinearMap EulerSmoothLimit EulerTimeLp EulerLpCylinderTranslation
  EulerLpCylinderRectangular EulerTransverseGramInverse

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E) (a : ℝ) (f : C(Icc (0 : ℝ) T, CylinderL2 P E))

theorem continuousVelocity_smul :
    D.velocityPath P (pathLp T D.time_pos.le (a • f)) =
      a • D.velocityPath P (pathLp T D.time_pos.le f) := by
  rw [pathLp_smul,map_smul]

theorem accelerationPath_smul : D.accelerationPath P (a • f) = a • D.accelerationPath P f := by
  apply ContinuousMap.ext
  intro t
  change gramInverse (D.frame P t) D.lower D.lower_pos (D.frame_lower P t)
    ((D.frame P t).adjoint ((a • f) t-(2 : ℝ) • D.frameDerivative P t
      (D.velocityPath P (pathLp T D.time_pos.le (a • f)) t))) =
    a • gramInverse (D.frame P t) D.lower D.lower_pos (D.frame_lower P t)
      ((D.frame P t).adjoint (f t-(2 : ℝ) • D.frameDerivative P t
        (D.velocityPath P (pathLp T D.time_pos.le f) t)))
  rw [D.continuousVelocity_smul P a f]
  simp only [ContinuousMap.smul_apply,map_smul]
  rw [smul_comm (2 : ℝ) a,← smul_sub,map_smul,map_smul]

theorem physicalVelocity_smul : D.physicalVelocity P (a • f) = a • D.physicalVelocity P f := by
  apply ContinuousMap.ext
  intro t
  change D.frame P t (D.velocityPath P (pathLp T D.time_pos.le (a • f)) t) =
    a • D.frame P t (D.velocityPath P (pathLp T D.time_pos.le f) t)
  rw [D.continuousVelocity_smul P a f,ContinuousMap.smul_apply,map_smul]

theorem physicalDerivative_smul : D.physicalDerivative P (a • f) = a • D.physicalDerivative P f :=
    by
  apply ContinuousMap.ext
  intro t
  change D.frameDerivative P t (D.velocityPath P (pathLp T D.time_pos.le (a • f)) t) +
    D.frame P t (D.accelerationPath P (a • f) t) =
    a • (D.frameDerivative P t (D.velocityPath P (pathLp T D.time_pos.le f) t) +
      D.frame P t (D.accelerationPath P f t))
  rw [D.continuousVelocity_smul P a f,D.accelerationPath_smul P a f]
  simp only [ContinuousMap.smul_apply,map_smul,smul_add]

end EulerCylinderDirichlet.Coefficients

namespace EulerSourceCylinderEquation

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerLpCylinderTranslation
  EulerLpCylinderPaths EulerLpCylinderRectangular EulerSourceCylinderForward
  EulerSourceCylinderForcing EulerLinearDuhamel
open scoped BoundedContinuousFunction

private theorem solution_smul {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] {T : ℝ} {hT : 0 ≤ T} {B : C(Icc (0 : ℝ) T, X →L[ℝ] X)}
    (W : Evolution T hT B) (a : ℝ) (f : C(Icc (0 : ℝ) T, X)) (a₀ : X) :
    W.solution (a • f) (a • a₀) = a • W.solution f a₀ := by
  simp only [Evolution.solution_eq_operators, map_smul, smul_add]

variable (P : ℝ) [Fact (0 < P)] {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (S : Set Space) (hS : MeasurableSet S) (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q.field t x v‖ ^ 2)
  (a : ℝ) (f : C(Icc (0 : ℝ) T, Supported P E S hS)) (a₀ : Supported P U S hS)

theorem coordinates_smul :
    coordinates P S hS T hT Q Q₁ c hc hQ (a • f) (a • a₀) =
      a • coordinates P S hS T hT Q Q₁ c hc hQ f a₀ := by
  unfold coordinates projectedForcing
  rw [map_smul]
  exact solution_smul (X := Supported P U S hS) _ a _ a₀

theorem velocity_smul :
    velocity P S hS T hT Q Q₁ c hc hQ (a • f) (a • a₀) =
      a • velocity P S hS T hT Q Q₁ c hc hQ f a₀ := by
  unfold velocity physicalVelocity
  rw [coordinates_smul,map_smul]

theorem velocityDerivative_smul :
    velocityDerivative P S hS T hT Q Q₁ c hc hQ (a • f) (a • a₀) =
      a • velocityDerivative P S hS T hT Q Q₁ c hc hQ f a₀ := by
  unfold velocityDerivative coordinateDerivative projectedForcing
  rw [coordinates_smul]
  simp only [map_smul,smul_add,map_add]

end EulerSourceCylinderEquation

end
end

end

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
  let L := initialPath (V := Supported P Space D.support D.support_measurable) D.T τ hτT.le
  exact (congrArg L h).trans (L.map_smul a G.path)

omit [CompleteSpace U] in
theorem tail_forcing_eq_smul : (H.tail τ hτ.le hτT).path = a • (G.tail τ hτ.le hτT).path := by
  let L := tailPath (V := Supported P Space D.support D.support_measurable) D.T τ hτ.le
  exact (congrArg L h).trans (L.map_smul a G.path)

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
  exact (includePath (V := Space) (K := Icc (0 : ℝ) (D.T - τ))
    P D.support D.support_measurable).map_smul a _

theorem futureDerivative_eq_smul : futureDerivative τ hτ hτT B H = a • futureDerivative τ hτ hτT B
    G := by
  unfold futureDerivative
  rw [(G.tail τ hτ.le hτT).derivativePath_eq_smul (H.tail τ hτ.le hτT)
    (forwardInitial τ hτ hτT B G) (forwardInitial τ hτ hτT B H) a
    (tail_forcing_eq_smul τ hτ hτT G H a h) (forwardInitial_eq_smul τ hτ hτT B G H a h)]
  exact (includePath (V := Space) (K := Icc (0 : ℝ) (D.T - τ))
    P D.support D.support_measurable).map_smul a _

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
