/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardGeometryAssembly
public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryLowBounds

/-! The actual forward primary has the same universal good-time size
and pressure sign as the joined primary. At time zero and on the early
interval its size has the exponential target-ratio gain. -/

@[expose] public section


noncomputable section

namespace EulerPacketSourceGeometry.ForwardGuards

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerSpatialCutoffs
  EulerPacketMovingFrame EulerTransversePacketProvider EulerPacketGeometryLowBounds
  EulerPacketForwardFactorization

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {P : ParentFrame D 0} (G : ForwardGuards P)
  (hball : (1 / 2 : ℝ) ≤ G.radius)

/-- Low geometry, given by `G.geometryData {x | ‖x‖ ≤ (1/2 : ℝ)} (by norm_num) (fun _ hx =>
hx.trans hball)`. -/
def lowGeometry : PhysicalGeometryData {x : Space // ‖x‖ ≤ (1/2 : ℝ)} :=
  G.geometryData {x | ‖x‖ ≤ (1/2 : ℝ)} (by norm_num) (fun _ hx => hx.trans hball)

/-- Primary amplitude, given by `(G.lowGeometry hball).amplitude`. -/
def primaryAmplitude : ℝ := (G.lowGeometry hball).amplitude

theorem primaryAmplitude_nonneg : 0 ≤ G.primaryAmplitude hball :=
  EulerPacketGeometryLowBounds.amplitude_nonneg (G.lowGeometry hball)

/-- Early ratio, given by `cutoffBound*(8232*Real.exp 9*P.horizon^5*Real.exp
(-(1/(4*P.sigma))))`. -/
def earlyRatio (_G : ForwardGuards P) : ℝ :=
  cutoffBound*(8232*Real.exp 9*P.horizon^5*Real.exp (-(1/(4*P.sigma))))

omit [CompleteSpace U] in
theorem earlyRatio_nonneg : 0 ≤ G.earlyRatio := by
  unfold earlyRatio
  positivity [cutoffBound_pos,G.horizon_lower]

include G in
omit [CompleteSpace U] in
theorem scaledTime_mem (t : Icc (0 : ℝ) D.T) :
    scaledTime 0 P.a P.epsilon t ∈ Icc 0 P.horizon := by
  have ha := G.a_pos
  have he := G.epsilon_pos
  constructor
  · unfold scaledTime
    exact mul_nonneg (div_nonneg ha.le he.le) (by simpa using t.property.1)
  · have hh := mul_le_mul_of_nonneg_left t.property.2 (div_nonneg ha.le he.le)
    calc
      _ = (P.a/P.epsilon)*(t : ℝ) := by unfold scaledTime; ring
      _ ≤ (P.a/P.epsilon)*D.T := hh
      _ = _ := by unfold ParentFrame.horizon; ring

theorem lowGeometry_size (t : Icc (0 : ℝ) D.T) (x : Space) (hx : ‖x‖ ≤ (1 / 2 : ℝ)) :
    (G.lowGeometry hball).size ⟨x,hx⟩ (scaledTime 0 P.a P.epsilon t) =
      ‖D.normal.field t x‖*‖uncutVelocity D G.initialCoordinate t x‖ := by
  change ‖D.normal.field (D.clamp (physicalTime 0 P.a P.epsilon (scaledTime 0 P.a P.epsilon t))) x‖*
    ‖uncutVelocity D G.initialCoordinate (physicalTime 0 P.a P.epsilon (scaledTime 0 P.a P.epsilon
        t)) x‖ = _
  rw [physicalTime_scaledTime G.a_pos.ne' G.epsilon_pos.ne',Data.clamp_coe]

theorem cutoff_amplitude_size (t : Icc (0 : ℝ) D.T) (x : Space) :
    G.primaryAmplitude hball*(‖D.normal.field t x‖*‖canonicalVelocity D G.initialCoordinate t x‖) =
      innerCutoff x*(G.primaryAmplitude hball*(‖D.normal.field t x‖*‖uncutVelocity D
          G.initialCoordinate t x‖)) := by
  rw [canonicalVelocity,norm_smul,Real.norm_of_nonneg (innerCutoff_nonneg x)]
  ring

theorem good_primary_size (t : Icc (0 : ℝ) D.T)
    (ht : 1 ≤ scaledTime 0 P.a P.epsilon t) (x : Space) :
    G.primaryAmplitude hball*(‖D.normal.field t x‖*‖canonicalVelocity D G.initialCoordinate t x‖) ≤
      G.δ*G.hchild*goodRatio := by
  rw [G.cutoff_amplitude_size hball t x]
  by_cases hcut : innerCutoff x=0
  · rw [hcut,zero_mul]
    positivity [G.delta_nonneg,G.child_nonneg,goodRatio_pos]
  have hx : ‖x‖ ≤ (1/2 : ℝ) := by
    have hm := innerCutoff_support (subset_tsupport _ (Function.mem_support.mpr hcut))
    exact le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using hm)
  have hg := good_amplitude_size (G.lowGeometry hball) ⟨x,hx⟩ (scaledTime 0 P.a P.epsilon t)
    ⟨ht,(G.scaledTime_mem t).2⟩
  rw [G.lowGeometry_size hball t x hx] at hg
  change G.primaryAmplitude hball*(‖D.normal.field t x‖*‖uncutVelocity D G.initialCoordinate t x‖) ≤
    G.δ*G.hchild*(64*Real.exp 6) at hg
  calc
    _ ≤ innerCutoff x*(G.δ*G.hchild*(64*Real.exp 6)) :=
      mul_le_mul_of_nonneg_left hg (innerCutoff_nonneg x)
    _ ≤ cutoffBound*(G.δ*G.hchild*(64*Real.exp 6)) :=
      mul_le_mul_of_nonneg_right (cutoff_le x) (by positivity [G.delta_nonneg,G.child_nonneg])
    _ = _ := by unfold goodRatio; ring

include hball in
theorem good_primary_flux (t : Icc (0 : ℝ) D.T)
    (ht : 1 ≤ scaledTime 0 P.a P.epsilon t) (x : Space) :
    0 ≤ ⟪D.normal.field t x,D.M.field t x (canonicalVelocity D G.initialCoordinate t x)⟫_ℝ := by
  rw [canonicalVelocity,map_smul,real_inner_smul_right]
  by_cases hcut : innerCutoff x=0
  · simp only [hcut,zero_mul,le_refl]
  have hx : ‖x‖ ≤ (1/2 : ℝ) := by
    have hm := innerCutoff_support (subset_tsupport _ (Function.mem_support.mpr hcut))
    exact le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using hm)
  have hg := good_flux (G.lowGeometry hball) ⟨x,hx⟩ (scaledTime 0 P.a P.epsilon t)
    ⟨ht,(G.scaledTime_mem t).2⟩
  change 0 < ⟪D.normal.field (D.clamp (physicalTime 0 P.a P.epsilon (scaledTime 0 P.a P.epsilon
      t))) x,
    D.M.field (D.clamp (physicalTime 0 P.a P.epsilon (scaledTime 0 P.a P.epsilon t))) x
      (uncutVelocity D G.initialCoordinate (physicalTime 0 P.a P.epsilon (scaledTime 0 P.a
          P.epsilon t)) x)⟫_ℝ at hg
  rw [physicalTime_scaledTime G.a_pos.ne' G.epsilon_pos.ne',Data.clamp_coe] at hg
  exact mul_nonneg (innerCutoff_nonneg x) hg.le

theorem early_primary_size (t : Icc (0 : ℝ) D.T)
    (ht : scaledTime 0 P.a P.epsilon t ≤ 1) (x : Space) :
    G.primaryAmplitude hball*(‖D.normal.field t x‖*‖canonicalVelocity D G.initialCoordinate t x‖) ≤
      G.δ*G.hchild*G.earlyRatio := by
  rw [G.cutoff_amplitude_size hball t x]
  by_cases hcut : innerCutoff x=0
  · rw [hcut,zero_mul]
    positivity [G.delta_nonneg,G.child_nonneg,G.earlyRatio_nonneg]
  have hx : ‖x‖ ≤ (1/2 : ℝ) := by
    have hm := innerCutoff_support (subset_tsupport _ (Function.mem_support.mpr hcut))
    exact le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using hm)
  have hg := early_amplitude_size (G.lowGeometry hball) ⟨x,hx⟩ (scaledTime 0 P.a P.epsilon t)
    ⟨(G.scaledTime_mem t).1,ht⟩
  rw [G.lowGeometry_size hball t x hx] at hg
  change G.primaryAmplitude hball*(‖D.normal.field t x‖*‖uncutVelocity D G.initialCoordinate t x‖) ≤
    G.δ*G.hchild*(8232*Real.exp 9*P.horizon^5*Real.exp (-(1/(4*P.sigma)))) at hg
  calc
    _ ≤ innerCutoff x*(G.δ*G.hchild*(8232*Real.exp 9*P.horizon^5*Real.exp (-(1/(4*P.sigma))))) :=
      mul_le_mul_of_nonneg_left hg (innerCutoff_nonneg x)
    _ ≤ cutoffBound*(G.δ*G.hchild*(8232*Real.exp 9*P.horizon^5*Real.exp (-(1/(4*P.sigma))))) :=
      mul_le_mul_of_nonneg_right (cutoff_le x) (by
          positivity [G.delta_nonneg,G.child_nonneg,G.horizon_lower])
    _ = _ := by unfold earlyRatio; ring

end EulerPacketSourceGeometry.ForwardGuards
