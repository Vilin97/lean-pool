/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketOrbitForcing
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketReflection

@[expose] public section

/-!
# Homogeneity of the genuine mean packet solution

The selected strong representatives inherit the linearity of the actual
coercive inverse. Consequently scalar forcing envelopes remain outside the
velocity, time-derivative, and physical-pressure estimates.
-/

noncomputable section

namespace EulerMeanPacketProvider.Forcing

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanVariationalInverse EulerMeanScalarPressure EulerTimeLp EulerVolterraConvolution
  EulerMeanTimeContinuousTranslation EulerPacketPointJets EulerPacketProfileRecursion
open scoped ContDiff

variable {D : Data} {raw raw' : VectorField}

theorem path_ae_raw (G : Forcing D raw) (t : Icc (0 : ℝ) D.T) (θ : ℝ) :
    (G.path t : Space → Space) =ᵐ[volume] fun x => raw (t,(x,θ)) := by
  rw [G.path_eq]
  exact (G.slices t).toLp_ae.trans (Filter.Eventually.of_forall fun x => (G.raw_eq t x θ).symm)

section Scaling

variable (G : Forcing D raw) (H : Forcing D raw') (a : ℝ)
  (hraw : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw' (t,(x,θ)) = a • raw (t,(x,θ)))

include hraw

theorem path_smul : H.path = a • G.path := by
  apply ContinuousMap.ext
  intro t
  apply Lp.ext
  filter_upwards [G.path_ae_raw t 0, H.path_ae_raw t 0, Lp.coeFn_smul a (G.path t)] with x hG hH ha
  change H.path t x = (a • G.path t) x
  rw [hH, ha, Pi.smul_apply, hG, hraw t x 0]

theorem lp_smul : H.lp = a • G.lp := by
  exact (congrArg (pathLp (E := L2) D.T D.T_pos.le) (path_smul G H a hraw)).trans
    (pathLp_smul D.T D.T_pos.le a G.path)

theorem velocityLp_smul : H.solution.velocityLp = a • G.solution.velocityLp := by
  exact H.velocityLp_eq_coordinateSolver.trans
    ((congrArg D.coordinateSolver (lp_smul G H a hraw)).trans
      ((D.coordinateSolver.map_smul a G.lp).trans
        (congrArg (fun v : TimeLp D.T solenoidalSpace => a • v)
          G.velocityLp_eq_coordinateSolver).symm))

/-- Linearity of the L² solve fixes the continuous coordinate representative at every time. -/
theorem coordinate_velocity_smul (t : Icc (0 : ℝ) D.T) :
    H.solution.velocity t = a • G.solution.velocity t := by
  have hae : (fun r => H.solution.velocity r) =ᵐ[timeMeasure D.T]
      fun r => a • G.solution.velocity r := by
    filter_upwards [H.solution.velocity_ae, G.solution.velocity_ae,
      Lp.coeFn_smul a G.solution.velocityLp] with r hH hG ha
    have he := congrArg (fun z : TimeLp D.T solenoidalSpace => z r) (velocityLp_smul G H a hraw)
    exact hH.symm.trans (he.trans (ha.trans (congrArg (fun v : solenoidalSpace => a • v) hG)))
  have hcG : ContinuousOn G.solution.velocity (Icc (0 : ℝ) D.T) := by
    simpa only [uIcc_of_le D.T_pos.le] using G.solution.velocity_ac.continuousOn
  have hcH : ContinuousOn H.solution.velocity (Icc (0 : ℝ) D.T) := by
    simpa only [uIcc_of_le D.T_pos.le] using H.solution.velocity_ac.continuousOn
  exact Measure.eqOn_Icc_of_ae_eq volume D.T_pos.ne hae hcH (hcG.const_smul a) t.property

theorem coordinateVelocityPath_smul :
    H.solution.coordinateVelocityPath = a • G.solution.coordinateVelocityPath := by
  apply ContinuousMap.ext
  intro t
  exact coordinate_velocity_smul G H a hraw t

theorem velocityPath_smul : H.velocityPath = a • G.velocityPath := by
  let J := EulerContinuousTimeIntegral.multiplier (solenoidalFrame D.T D.opF)
  exact (H.solution.continuousVelocity_eq_frame D.T_pos D.opF_time).trans
    ((congrArg J (coordinateVelocityPath_smul G H a hraw)).trans
      ((J.map_smul a G.solution.coordinateVelocityPath).trans
        (congrArg (fun p : C(Icc (0 : ℝ) D.T,L2) => a • p)
          (G.solution.continuousVelocity_eq_frame D.T_pos D.opF_time)).symm))

/-- The true within-time derivatives scale by uniqueness of the derivative. -/
theorem derivativePath_smul : H.derivativePath = a • G.derivativePath := by
  apply ContinuousMap.ext
  intro t
  have h₁ := H.velocityPath_time t
  have h₂ := (G.velocityPath_time t).const_smul a
  have he : extendPath D.T D.T_pos.le H.velocityPath =
      fun r => a • extendPath D.T D.T_pos.le G.velocityPath r := by
    funext r
    exact congrArg (fun p : C(Icc (0 : ℝ) D.T,L2) => p (projIcc 0 D.T D.T_pos.le r))
      (velocityPath_smul G H a hraw)
  rw [he] at h₁
  exact (h₁.derivWithin ((uniqueDiffOn_Icc D.T_pos) t t.property)).symm.trans
    (h₂.derivWithin ((uniqueDiffOn_Icc D.T_pos) t t.property))

/-- The actual physical pressure residual scales, including at the time endpoints. -/
theorem pressureForcePath_smul : H.pressureForcePath = a • G.pressureForcePath := by
  apply ContinuousMap.ext
  intro t
  have hG := G.solution.pressurePath_equation D.frameLower D.frameLower_pos D.frame_lower
    G.path D.T_pos D.opF_time D.opM D.opStrain_eq t
  have hH := H.solution.pressurePath_equation D.frameLower D.frameLower_pos D.frame_lower
    H.path D.T_pos D.opF_time D.opM D.opStrain_eq t
  have hv : H.velocityPath t = a • G.velocityPath t :=
    congrArg (fun p : C(Icc (0 : ℝ) D.T,L2) => p t) (velocityPath_smul G H a hraw)
  have hd : H.derivativePath t = a • G.derivativePath t :=
    congrArg (fun p : C(Icc (0 : ℝ) D.T,L2) => p t) (derivativePath_smul G H a hraw)
  have hf : H.path t = a • G.path t :=
    congrArg (fun p : C(Icc (0 : ℝ) D.T,L2) => p t) (path_smul G H a hraw)
  change H.derivativePath t+D.opM t (H.velocityPath t)+H.pressureForcePath t=H.path t at hH
  change G.derivativePath t+D.opM t (G.velocityPath t)+G.pressureForcePath t=G.path t at hG
  rw [hd, hv, hf, map_smul] at hH
  have he := congrArg (fun z : L2 => a • z) hG
  simp only [smul_add] at he
  exact add_left_cancel (hH.trans he.symm)

end Scaling

end EulerMeanPacketProvider.Forcing
