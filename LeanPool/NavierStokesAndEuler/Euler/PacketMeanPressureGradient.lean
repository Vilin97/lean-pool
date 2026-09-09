/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPressureWitness
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketPressureForcing
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketCylinderFields
public import LeanPool.NavierStokesAndEuler.Euler.CylinderGradientEmbedding
import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientFrame
import LeanPool.NavierStokesAndEuler.Euler.MeanPacketJets

/-! The actual mean pressure enters the lifted gradient closure.
Only its genuine L² gradient is embedded; its scalar potential need not be L². -/

@[expose] public section


noncomputable section

namespace EulerMeanPacketProvider.Forcing

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerMeanSolenoidal EulerMeanCoefficients EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketCylinderField EulerPacketPressure EulerCylinderSpatialEmbedding
open scoped ContDiff

variable {D : Data} {raw : VectorField} (G : Forcing D raw)

theorem path_ae_raw_zeroAngle (t : Icc (0 : ℝ) D.T) :
    (G.path t : Space → Space) =ᵐ[volume] fun x => raw (t,(x,0)) := by
  rw [G.path_eq]
  filter_upwards [(G.slices t).toLp_ae] with x hx
  exact hx.trans (G.raw_eq t x 0).symm

/-- The classical gradient constructed from the radial potential is the same
ordinary L² element as the projected pressure residual. -/
theorem scalarGradient_path_eq (t : Icc (0 : ℝ) D.T) :
    G.scalarGradientForcing.path t = (D.opF t).adjoint (G.pressureForcePath t) := by
  change G.scalarGradientForcing.path t =
    (EulerMeanCoefficients.multiplier (D.F.field t)).adjoint (G.pressureForcePath t)
  rw [← multiplier_adjointField]
  apply Lp.ext
  filter_upwards [G.scalarGradientForcing.path_ae_raw_zeroAngle t,
    G.pressureForceForcing.path_ae_raw_zeroAngle t,
    multiplier_ae (adjointField (D.F.field t)) (G.pressureForcePath t)] with x hg hp hm
  change G.scalarGradientForcing.path t x =
    (EulerMeanCoefficients.multiplier (adjointField (D.F.field t)) (G.pressureForcePath t)) x
  rw [hg,hm,adjointField_apply]
  change G.scalarGradient (t,(x,0)) = (D.F.field t x).adjoint (G.pressureForceForcing.path t x)
  rw [hp,G.scalarGradient_eq]

theorem scalarGradient_path_mem (t : Icc (0 : ℝ) D.T) :
    G.scalarGradientForcing.path t ∈ EulerMeanSolenoidal.gradientSpace := by
  rw [G.scalarGradient_path_eq]
  exact G.solution.pressurePath_gradient D.frameLower D.frameLower_pos D.frame_lower G.path t

theorem pressureGradient_eq_scalarGradient (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    pressureGradient G.scalar (t,(x,θ)) = G.scalarGradient (t,(x,θ)) := by
  change (toDual ℝ Space).symm ((pressureJet G.scalar (t,(x,θ))).2.comp spatialInjection) = _
  rw [pressureJet_spatial_derivative G.scalar t x θ
    ((G.scalar_spatial_smooth t).differentiable (by simp) (x,θ))]
  rfl

/-- This witness uses the actual projected mean equation to prove membership,
without any compact-support or integrability premise on the scalar potential. -/
def pressureGradientWitness (P κ : ℝ) [Fact (0 < P)] (m : Space) :
    GradientWitness P D.T κ m G.scalar where
  smooth t := G.scalar_spatial_smooth t
  field := ((G.scalarGradientForcing.toCylinderField P).smul κ).congr (fun t x θ => by
    rw [rawGradient,G.scalar_angle_jet,zero_smul,add_zero,
      G.pressureGradient_eq_scalarGradient]
    rfl)
  gradient_mem t :=
    smul_embedding_gradient_mem P κ m (G.scalarGradientForcing.path t) (G.scalarGradient_path_mem t)

end EulerMeanPacketProvider.Forcing
