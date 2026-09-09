/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentStateGeometry
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketGeometryGuards
public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryAssembly

@[expose] public section

/-! Quantitative parameters at a genuine geometric target. The matching
certificate below is proved for the actual state renewal constructors in
`ParentTargetRenewal`; it records equality of the physical matrix and the
two physical vectors, rather than postulating their scalar estimates. -/

noncomputable section

namespace EulerPacketMovingFrame.PhysicalGeometryData

open Set InnerProductSpace EulerSmoothLimit

variable {ι : Type*} (G : PhysicalGeometryData ι)

def couplingError : ℝ := G.y^4+G.σ^2*G.y^2+8*G.σ*G.y^3+
  30000000*neighborStabilityConstant*G.error*G.Θ^40

def tiltError : ℝ := 1500*G.σ+30000000*neighborStabilityConstant*G.error*G.Θ^40

/-- A lower bound for the magnitude of the leading compressive term. -/
def compressionScale : ℝ := G.a/(20*G.ε*G.target)

theorem start_lt_targetTime : G.t₀ < G.targetTime := by
  change G.t₀ < G.t₀+(G.ε/G.a)*G.target
  exact lt_add_of_pos_right _ (mul_pos (div_pos G.epsilon_pos G.a_pos) G.target_pos)

theorem targetTime_pos (hstart : 0 ≤ G.t₀) : 0 < G.targetTime :=
  hstart.trans_lt G.start_lt_targetTime

theorem nextCoupling_pos : 0 < G.nextCoupling := by
  obtain ⟨F,F1,Z,Z1,J⟩ := G.exists_geometry
  have hp := J.positive_pressure G.center G.target ⟨G.target_one,G.target_le_horizon⟩
  change 0 < normalizedCoupling _ _ _
  rw [normalizedCoupling_eq]
  exact div_pos hp J.target_positive

theorem nextCoupling_error : |G.nextCoupling/G.a-1| ≤ G.couplingError := by
  obtain ⟨F,F1,Z,Z1,J⟩ := G.exists_geometry
  exact J.next_frame.1

theorem nextTilt_error : |(G.y⁻¹)^2*G.nextTilt-1| ≤ G.tiltError := by
  obtain ⟨F,F1,Z,Z1,J⟩ := G.exists_geometry
  exact J.next_frame.2

theorem nextTilt_pos (herror : G.tiltError ≤ 1/2) : 0 < G.nextTilt := by
  have h := (abs_le.mp G.nextTilt_error).1
  have hn : 0 < (G.y⁻¹)^2 := sq_pos_of_pos (inv_pos.mpr G.y_pos)
  by_contra hneg
  have hzero := mul_nonpos_of_nonneg_of_nonpos hn.le (le_of_not_gt hneg)
  linarith only [h,herror,hzero]

theorem compressionScale_pos : 0 < G.compressionScale := by
  unfold compressionScale
  positivity [G.a_pos,G.epsilon_pos,G.target_pos]

/-- The existing geometric smallness guard leaves enough compression
margin for any subsequent center remainder of size at most one. -/
theorem compression_margin {e : ℝ} (he : e ≤ 1) :
    3*(G.G+G.d)+e < G.compressionScale := by
  have hbound := G.error_le_one
  have hn : 0 ≤ G.ε*G.Θ*G.G^2 := by positivity [G.epsilon_pos,G.Theta_pos]
  have hd : G.d ≤ 1/16 := by
    unfold error at hbound
    nlinarith only [hbound,hn]
  have hsmall : G.ε*G.Θ*G.G^2 ≤ 1/256 := by
    unfold error at hbound
    nlinarith only [hbound,G.d_nonneg]
  have hg : 3*(G.G+G.d)+1 ≤ 5*G.G^2 := by
    nlinarith only [hd,G.G_lower,sq_nonneg (G.G-1)]
  have hprod := mul_le_mul_of_nonneg_right hg
    (mul_nonneg G.epsilon_pos.le G.Theta_pos.le)
  have htime := mul_le_mul_of_nonneg_left G.target_le_Theta G.epsilon_pos.le
  have hnorm : 0 ≤ 3*(G.G+G.d)+1 := by positivity [G.G_lower,G.d_nonneg]
  have htarget := mul_le_mul_of_nonneg_left htime hnorm
  have hstrong : 3*(G.G+G.d)+1 < G.compressionScale := by
    unfold compressionScale
    apply (lt_div_iff₀ (show 0 < 20*G.ε*G.target by positivity [G.epsilon_pos,G.target_pos])).mpr
    nlinarith only [hprod,htarget,hsmall,G.a_lower]
  linarith only [he,hstrong]

theorem nextCompression_le : G.nextCompression ≤ -G.compressionScale+3*(G.G+G.d) := by
  obtain ⟨F,F1,Z,Z1,J⟩ := G.exists_geometry
  have hm := mul_le_mul_of_nonneg_right G.target_shear_lower G.epsilon_pos.le
  have hd := div_le_div_of_nonneg_right hm
    (show 0 ≤ 10*G.target by positivity [G.target_pos])
  have he : (G.a/(2*G.ε^2)*G.ε)/(10*G.target)=G.compressionScale := by
    unfold compressionScale
    field_simp [G.epsilon_pos.ne',G.target_pos.ne']
    ring
  rw [he] at hd
  have hb := J.compression_bound
  rw [neg_div] at hb
  linarith only [hb,hd]

theorem target_shear_normalization (hδ : 0 < G.δ) :
    (G.amplitude/G.δ)*G.targetSize=G.hchild := by
  obtain ⟨F,F1,Z,Z1,J⟩ := G.exists_geometry
  calc
    _ = (G.amplitude*G.targetSize)/G.δ := by ring
    _ = (G.δ*G.hchild)/G.δ := by rw [J.amplitude_normalization]
    _ = G.hchild := by field_simp

end EulerPacketMovingFrame.PhysicalGeometryData

namespace EulerParentPacketFrames

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerPacketMovingFrame EulerPacketNormalizedPrimary EulerPacketSourceGeometry
  EulerTransversePacketProvider

variable {ι : Type*} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {D : Data V} (G : PhysicalGeometryData ι) (P : ParentFrame D G.targetTime)

/-- Exact target matching, supplied by the actual forward or joined
`SmoothState` renewal. In particular the primary is not renormalized. -/
structure RenewalAtTarget : Prop where
  matrix_eq : P.B G.targetTime=G.M G.center G.targetTime
  ray_eq : P.m G.targetTime=G.r G.center G.targetTime
  velocity_eq : P.v G.targetTime=G.w G.center G.targetTime
  coefficient_eq : P.c=G.amplitude/G.δ

namespace RenewalAtTarget

variable {G P} (J : RenewalAtTarget G P)

include J

theorem a_eq : P.a=G.nextCoupling := by
  simp only [ParentFrame.a,PhysicalGeometryData.nextCoupling,
    J.matrix_eq,J.ray_eq,J.velocity_eq]

theorem sigma_eq : P.sigma=Real.sqrt G.nextTilt := by
  simp only [ParentFrame.sigma,PhysicalGeometryData.nextTilt,
    J.matrix_eq,J.ray_eq,J.velocity_eq]

theorem shear_eq (hδ : 0 < G.δ) : P.shear=G.hchild := by
  change P.c*(‖P.m G.targetTime‖*‖P.v G.targetTime‖)=G.hchild
  rw [J.coefficient_eq,J.ray_eq,J.velocity_eq]
  exact G.target_shear_normalization hδ

theorem epsilon_eq (hδ : 0 < G.δ) : P.epsilon=Real.sqrt (P.a/G.hchild) := by
  rw [ParentFrame.epsilon,J.shear_eq hδ]

theorem normalized_ray_eq : unit (P.m G.targetTime)=unit (G.r G.center G.targetTime) :=
  congrArg unit J.ray_eq

theorem normalized_velocity_eq : unit (P.v G.targetTime)=unit (G.w G.center G.targetTime) :=
  congrArg unit J.velocity_eq

/-- The actual next source matrix has the prescribed target shear and
the original packet's center error. -/
theorem target_remainder (hδ : 0 < G.δ) (hT : G.targetTime ≤ D.T) :
    ‖D.M.field (D.clamp G.targetTime) 0-G.M G.center G.targetTime-
      G.hchild • rankOne ℝ (unit (G.w G.center G.targetTime))
        (unit (G.r G.center G.targetTime))‖ ≤ P.error := by
  have h := P.remainder_bound G.targetTime ⟨le_rfl,hT⟩
  change ‖D.M.field (D.clamp G.targetTime) 0-P.B G.targetTime-
    P.shear • rankOne ℝ (unit (P.v G.targetTime)) (unit (P.m G.targetTime))‖ ≤ P.error at h
  rw [J.matrix_eq,J.ray_eq,J.velocity_eq,J.shear_eq hδ] at h
  exact h

theorem coupling_pos : 0 < P.a := by rw [J.a_eq]; exact G.nextCoupling_pos

theorem coupling_error : |P.a/G.a-1| ≤ G.couplingError := by
  rw [J.a_eq]
  exact G.nextCoupling_error

theorem coupling_interval :
    (1-G.couplingError)*G.a ≤ P.a ∧ P.a ≤ (1+G.couplingError)*G.a := by
  have h := abs_le.mp J.coupling_error
  constructor
  · have hh : 1-G.couplingError ≤ P.a/G.a := by linarith only [h.1]
    exact (le_div_iff₀ G.a_pos).mp hh
  · have hh : P.a/G.a ≤ 1+G.couplingError := by linarith only [h.2]
    exact (div_le_iff₀ G.a_pos).mp hh

theorem coupling_absolute_error : |P.a-G.a| ≤ G.a*G.couplingError := by
  rw [abs_le]
  constructor <;> nlinarith only [J.coupling_interval.1,J.coupling_interval.2]

theorem sigma_sq (herror : G.tiltError ≤ 1/2) : P.sigma^2=G.nextTilt := by
  rw [J.sigma_eq,Real.sq_sqrt (G.nextTilt_pos herror).le]

theorem sigma_pos (herror : G.tiltError ≤ 1/2) : 0 < P.sigma := by
  rw [J.sigma_eq]
  exact Real.sqrt_pos.mpr (G.nextTilt_pos herror)

theorem tilt_error (herror : G.tiltError ≤ 1/2) :
    |(G.y⁻¹)^2*P.sigma^2-1| ≤ G.tiltError := by
  rw [J.sigma_sq herror]
  exact G.nextTilt_error

theorem tilt_interval (herror : G.tiltError ≤ 1/2) :
    1/2 ≤ (G.y⁻¹)^2*P.sigma^2 ∧ (G.y⁻¹)^2*P.sigma^2 ≤ 3/2 := by
  have h := abs_le.mp (J.tilt_error herror)
  constructor <;> linarith only [h.1,h.2,herror]

theorem sigma_small (herror : G.tiltError ≤ 1/2) (hy : G.y ≤ 1/8) : P.sigma ≤ 1/4 := by
  have hi : 8 ≤ G.y⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ G.y_pos).mpr
    linarith only [hy]
  have hin : 64 ≤ (G.y⁻¹)^2 := by nlinarith only [hi]
  have hm := mul_le_mul_of_nonneg_right hin (sq_nonneg P.sigma)
  have hu := (J.tilt_interval herror).2
  nlinarith only [hm,hu,sq_nonneg (P.sigma-1/4)]

theorem background_compression_eq :
    ⟪P.B G.targetTime (unit (P.m G.targetTime)),unit (P.m G.targetTime)⟫_ℝ=
      G.nextCompression := by
  rw [J.matrix_eq,J.ray_eq]
  exact real_inner_comm _ _

/-- The new packet error is retained in the compression margin. -/
theorem activation_normal_le (ht : 0 < G.targetTime) (hT : G.targetTime < D.T) :
    ⟪D.M.field ⟨G.targetTime,ht.le,hT.le⟩ 0 (unit (P.m G.targetTime)),
      unit (P.m G.targetTime)⟫_ℝ ≤ -G.compressionScale+3*(G.G+G.d)+P.error := by
  have h := P.activation_normal_le ht hT
  rw [J.background_compression_eq] at h
  exact h.trans (add_le_add G.nextCompression_le le_rfl)

theorem activation_compression (ht : 0 < G.targetTime) (hT : G.targetTime < D.T)
    (hmargin : 3*(G.G+G.d)+P.error < G.compressionScale) :
    ⟪D.M.field ⟨G.targetTime,ht.le,hT.le⟩ 0 (unit (P.m G.targetTime)),
      unit (P.m G.targetTime)⟫_ℝ < 0 := by
  have h := J.activation_normal_le ht hT
  linarith only [h,hmargin]

theorem activation_compression_of_error_le_one
    (ht : 0 < G.targetTime) (hT : G.targetTime < D.T) (he : P.error ≤ 1) :
    ⟪D.M.field ⟨G.targetTime,ht.le,hT.le⟩ 0 (unit (P.m G.targetTime)),
      unit (P.m G.targetTime)⟫_ℝ < 0 :=
  J.activation_compression ht hT (G.compression_margin he)

end RenewalAtTarget
end EulerParentPacketFrames
