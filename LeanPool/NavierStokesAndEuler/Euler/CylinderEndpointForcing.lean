/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointData
public import LeanPool.NavierStokesAndEuler.Euler.FixedEndpointForcing

@[expose] public section

/-!
The actual cylinder endpoint inverse is affine data minus the genuine
zero-endpoint inverse of its explicit forcing. These identities transfer
the already proved support, translation and same-radius estimates to the
nonzero-terminal construction.
-/

noncomputable section

namespace EulerCylinderDirichlet.Coefficients

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerTimeLp
  EulerVolterraConvolution EulerTimeH1FrameTransport EulerTerminalTimePrimitive
  EulerInitialTimePrimitive EulerTransverseFixedEndpoint
  EulerTransverseEndpointParameter EulerTransverseEndpointCoordinates
  EulerFixedEndpointForcing EulerContinuousTimeIntegral

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (P : ℝ) [Fact (0 < P)] {T : ℝ} (D : Coefficients T U E)

/-- The exact forcing of the affine endpoint correction. -/
def endpointForcing : CylinderL2 P U →L[ℝ] C(Icc (0 : ℝ) T,CylinderL2 P E) :=
  affineForcing T (D.frameDerivative P)

omit [CompleteSpace U] [CompleteSpace E] in
theorem endpointForcing_apply (Y : CylinderL2 P U) (t : Icc (0 : ℝ) T) :
    D.endpointForcing P Y t = (2 : ℝ) • D.frameDerivative P t (T⁻¹ • Y) := rfl

/-- Equality of the genuinely constructed corrections, not a new solution assumption. -/
theorem endpointCorrection_eq_forced (Y : CylinderL2 P U) :
    D.endpointCorrection P Y = D.coordinateSolver P (pathLp T D.time_pos.le (D.endpointForcing P
      Y)) :=
  correction_eq_forced T D.time_pos.le (D.frame P) (D.frameDerivative P) (D.frameSecond P)
    (D.hessian P) (D.frame_derivative P) (D.frame_second_derivative P) (D.frame_equation P)
    D.lower D.lower_pos (D.frame_lower P) D.potential D.potential_nonneg
    (D.hessian_upper P) D.small Y

theorem endpointSlope_eq_const_sub (Y : CylinderL2 P U) :
    D.endpointSlope P Y = constantFieldOperator T D.time_pos.le (T⁻¹ • Y)-
      D.velocityLp P (pathLp T D.time_pos.le (D.endpointForcing P Y)) := by
  change constantFieldOperator T D.time_pos.le (T⁻¹ • Y)-
    (D.endpointCorrection P Y : TimeLp T (CylinderL2 P U)) = _
  rw [D.endpointCorrection_eq_forced P Y]
  rfl

theorem endpointDisplacement_eq_affine_sub (Y : CylinderL2 P U) (t : Icc (0 : ℝ) T) :
    D.endpointDisplacement P Y t = (t : ℝ) • (T⁻¹ • Y)-
      D.displacementPath P (pathLp T D.time_pos.le (D.endpointForcing P Y)) t := by
  have hz : initialTrace T D.time_pos.le
      (D.velocityLp P (pathLp T D.time_pos.le (D.endpointForcing P Y))) = 0 :=
    (D.coordinateSolver P (pathLp T D.time_pos.le (D.endpointForcing P Y))).property
  change initialPrimitive T D.time_pos.le (D.endpointSlope P Y) t = _
  rw [D.endpointSlope_eq_const_sub P Y,map_sub,ContinuousMap.sub_apply,
    initialPrimitive_constantFieldOperator,initialPrimitive_eq_terminal_sub,
    hz,sub_zero]
  rfl

/-- Equality in continuous time follows from the true displacement
derivative, including the endpoint derivatives. -/
theorem endpointCoordinate_eq_const_sub (Y : CylinderL2 P U) (t : Icc (0 : ℝ) T) :
    D.endpointCoordinate P Y t = T⁻¹ • Y-
      D.velocityPath P (pathLp T D.time_pos.le (D.endpointForcing P Y)) t := by
  have hc : HasDerivWithinAt (fun s : ℝ => s • (T⁻¹ • Y)) (T⁻¹ • Y)
      (Icc (0 : ℝ) T) t := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id (t : ℝ)).smul_const (T⁻¹ •
      Y)).hasDerivWithinAt
  have hh := hc.sub (D.displacement_hasDerivWithinAt P (D.endpointForcing P Y) t)
  have he : HasDerivWithinAt (extendPath T D.time_pos.le (D.endpointDisplacement P Y))
      (T⁻¹ • Y-D.velocityPath P (pathLp T D.time_pos.le (D.endpointForcing P Y)) t)
      (Icc (0 : ℝ) T) t := by
    apply hh.congr_of_mem _ t.property
    intro s hs
    simpa only [Pi.sub_apply,extendPath,projIcc_of_mem D.time_pos.le hs] using
      D.endpointDisplacement_eq_affine_sub P Y ⟨s,hs⟩
  exact ((D.endpointDisplacement_hasDerivWithinAt P Y t).derivWithin
    ((uniqueDiffOn_Icc D.time_pos) _ t.property)).symm.trans
      (he.derivWithin ((uniqueDiffOn_Icc D.time_pos) _ t.property))

theorem endpointCoordinate_eq_forced (Y : CylinderL2 P U) :
    D.endpointCoordinate P Y = ContinuousMap.const (Icc (0 : ℝ) T) (T⁻¹ • Y)-
      D.velocityPath P (pathLp T D.time_pos.le (D.endpointForcing P Y)) := by
  apply ContinuousMap.ext
  intro t
  exact D.endpointCoordinate_eq_const_sub P Y t

theorem endpointAcceleration_eq_forced (Y : CylinderL2 P U) :
    D.endpointAcceleration P Y = -D.accelerationPath P (D.endpointForcing P Y) := by
  apply ContinuousMap.ext
  intro t
  have hh := (hasDerivWithinAt_const (t : ℝ) (Icc (0 : ℝ) T) (T⁻¹ • Y)).sub
    (D.velocity_hasDerivWithinAt P (D.endpointForcing P Y) t)
  have he : HasDerivWithinAt (extendPath T D.time_pos.le (D.endpointCoordinate P Y))
      (-D.accelerationPath P (D.endpointForcing P Y) t) (Icc (0 : ℝ) T) t := by
    apply (hh.congr_deriv (zero_sub _)).congr_of_mem _ t.property
    intro s hs
    simpa only [Pi.sub_apply,extendPath,projIcc_of_mem D.time_pos.le hs] using
      D.endpointCoordinate_eq_const_sub P Y ⟨s,hs⟩
  exact ((D.endpointCoordinate_hasDerivWithinAt P Y t).derivWithin
    ((uniqueDiffOn_Icc D.time_pos) _ t.property)).symm.trans
      (he.derivWithin ((uniqueDiffOn_Icc D.time_pos) _ t.property))

theorem endpointVelocity_eq_forced (Y : CylinderL2 P U) :
    D.endpointVelocity P Y =
      multiplier (D.frame P) (ContinuousMap.const (Icc (0 : ℝ) T) (T⁻¹ • Y))-
        D.physicalVelocity P (D.endpointForcing P Y) := by
  apply ContinuousMap.ext
  intro t
  change D.frame P t (D.endpointCoordinate P Y t) =
    D.frame P t (T⁻¹ • Y)-D.frame P t
      (D.velocityPath P (pathLp T D.time_pos.le (D.endpointForcing P Y)) t)
  rw [D.endpointCoordinate_eq_const_sub P Y t,map_sub]

theorem endpointDerivative_eq_forced (Y : CylinderL2 P U) :
    D.endpointDerivative P Y =
      multiplier (D.frameDerivative P) (ContinuousMap.const (Icc (0 : ℝ) T) (T⁻¹ • Y))-
        D.physicalDerivative P (D.endpointForcing P Y) := by
  apply ContinuousMap.ext
  intro t
  change D.frameDerivative P t (D.endpointCoordinate P Y t)+D.frame P t (D.endpointAcceleration P Y
    t) =
    D.frameDerivative P t (T⁻¹ • Y)-(D.frameDerivative P t
      (D.velocityPath P (pathLp T D.time_pos.le (D.endpointForcing P Y)) t)+
        D.frame P t (D.accelerationPath P (D.endpointForcing P Y) t))
  rw [D.endpointCoordinate_eq_const_sub P Y t,D.endpointAcceleration_eq_forced P Y,
    ContinuousMap.neg_apply,map_sub,map_neg]
  abel

end EulerCylinderDirichlet.Coefficients
