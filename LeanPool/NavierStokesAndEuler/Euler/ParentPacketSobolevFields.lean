/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketScaledBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParentParticleInverse
public import LeanPool.NavierStokesAndEuler.Euler.PacketEulerianRegularity
import LeanPool.NavierStokesAndEuler.Euler.SmoothL2ScalingContinuity

/-! Actual physical L² fields of a packet over a parent. The genuine
inverse and the proved parent label bound supply all reconstruction
regularity, and the physical spatial scale is retained exactly. -/

@[expose] public section


noncomputable section

namespace EulerParentPacketFrames

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerPacketPhysicalField EulerAllOrderCorrectionData EulerPacketParentLabelBounds
  EulerTransverseFrameCoordinates EulerGraphPressurePotential

namespace ParticleInverse

variable {A : Parent} (I : ParticleInverse A)

theorem normalized_scaled (t : Icc (0 : ℝ) A.T) (x : Space) :
    I.normalized t (A.ell⁻¹ • x)=A.ell⁻¹ • I.field t x := by
  simp only [normalized,Parent.packetInverse,projIcc_of_mem A.T_pos.le t.property,
    smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul]

end ParticleInverse

namespace LabelData

variable {A : Parent} (L : LabelData A) (I : ParticleInverse A)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  (P : ℝ) [Fact (0 < P)] (κ : ℝ) (Z : FieldTower P A.T) (k : ℝ)

/-- Packet velocity field, constructed using `scaleField`. -/
def packetVelocityField (t : Icc (0 : ℝ) A.T) : SmoothL2Field Space :=
  scaleField A.ell A.ell_pos
    (eulerianSmoothField (A.transverseData m hm J support hSupport) P κ Z k
      (fun s x => A.packetPosition (s,x)) I.normalized A.packetPosition_spatial
      I.normalized_left I.normalized_right I.normalized_continuous
      L.scaledRadius (frameAmplitude L.K) L.scaledRadius_nonneg (frameAmplitude_nonneg L.K)
      A.frame_det L.frame_scaled_bound t)

/-- Packet force field, constructed using `scaleField`. -/
def packetForceField (t : Icc (0 : ℝ) A.T) : SmoothL2Field Space :=
  scaleField A.ell A.ell_pos
    (pressureForceSmoothField (A.transverseData m hm J support hSupport) P κ Z k
      (fun s x => A.packetPosition (s,x)) I.normalized A.packetPosition_spatial
      I.normalized_left I.normalized_right I.normalized_continuous
      L.scaledRadius (frameAmplitude L.K) L.scaledRadius_nonneg (frameAmplitude_nonneg L.K)
      A.frame_det L.frame_scaled_bound t)

theorem packetVelocityField_apply (t : Icc (0 : ℝ) A.T) (x : Space) :
    (L.packetVelocityField I m hm J support hSupport P κ Z k t).field x =
      A.ell • (κ • A.frame.field t (A.ell⁻¹ • I.field t x)
        (Z.pointField t (cylinderGraph P k m (A.ell⁻¹ • I.field t x)))) := by
  rw [packetVelocityField,scaleField_apply]
  erw [eulerianSmoothField_apply,I.normalized_scaled]
  rfl

theorem packetForceField_apply (t : Icc (0 : ℝ) A.T) (x : Space) :
    (L.packetForceField I m hm J support hSupport P κ Z k t).field x =
      A.ell • (κ • (A.inverse.field t (A.ell⁻¹ • I.field t x)).adjoint
        (Z.pointField t (cylinderGraph P k m (A.ell⁻¹ • I.field t x)))) := by
  rw [packetForceField,scaleField_apply]
  erw [pressureForceSmoothField_apply,I.normalized_scaled]
  rfl

theorem packetVelocityField_continuous (n : ℕ) :
    Continuous (fun t => (L.packetVelocityField I m hm J support hSupport P κ Z k t).jetLp n) :=
  continuous_jetLp_scaleField A.ell A.ell_pos A.ell_le_one _
    (eulerianSmoothField_jetLp_continuous (A.transverseData m hm J support hSupport) P κ Z k
      (fun s x => A.packetPosition (s,x)) I.normalized A.packetPosition_spatial
      I.normalized_left I.normalized_right I.normalized_continuous
      L.scaledRadius (frameAmplitude L.K) L.scaledRadius_nonneg (frameAmplitude_nonneg L.K)
      A.frame_det L.frame_scaled_bound) n

theorem packetForceField_continuous (n : ℕ) :
    Continuous (fun t => (L.packetForceField I m hm J support hSupport P κ Z k t).jetLp n) :=
  continuous_jetLp_scaleField A.ell A.ell_pos A.ell_le_one _
    (pressureForceSmoothField_jetLp_continuous (A.transverseData m hm J support hSupport) P κ Z k
      (fun s x => A.packetPosition (s,x)) I.normalized A.packetPosition_spatial
      I.normalized_left I.normalized_right I.normalized_continuous
      L.scaledRadius (frameAmplitude L.K) L.scaledRadius_nonneg (frameAmplitude_nonneg L.K)
      A.frame_det L.frame_scaled_bound) n

end LabelData
end EulerParentPacketFrames
