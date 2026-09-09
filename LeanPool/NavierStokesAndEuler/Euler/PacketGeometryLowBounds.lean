/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPropagationTime
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceGeometryAssembly
import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryAssembly
import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryGuards
import LeanPool.NavierStokesAndEuler.Euler.PacketTargetAmplification

/-! Actual primary size and sign estimates on the good, early, and
stationary-history portions of the packet horizon. The amplitude is the
one selected by its genuine center target size. -/

@[expose] public section


noncomputable section

namespace EulerPacketGeometryLowBounds

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerSpatialCutoffs
  EulerGevreyCutoff EulerGevrey EulerPacketMovingFrame

/-- Cutoff bound, given by `1+(9/rawBump 0)^3`. -/
def cutoffBound : ℝ := 1+(9/rawBump 0)^3

theorem cutoffBound_pos : 0 < cutoffBound := by
  unfold cutoffBound
  positivity [rawBump_pos_zero]

theorem cutoff_le (x : Space) : innerCutoff x ≤ cutoffBound := by
  have h := innerCutoff_gevrey 0 x
  simp only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
    Nat.cast_one,pow_zero,one_pow,mul_one] at h
  have he := (le_abs_self (innerCutoff x)).trans (by simpa only [Real.norm_eq_abs] using h)
  exact he.trans (by unfold cutoffBound; linarith)

/-- Good ratio, given by `cutoffBound*(64*Real.exp 6)`. -/
def goodRatio : ℝ := cutoffBound*(64*Real.exp 6)

theorem goodRatio_pos : 0 < goodRatio := by unfold goodRatio; positivity [cutoffBound_pos]

variable {ι : Type*} (G : PhysicalGeometryData ι)

theorem amplitude_size_of_ratio (value R : ℝ) (h : value / G.targetSize ≤ R) :
    G.amplitude*value ≤ G.δ*G.hchild*R := by
  have hh := mul_le_mul_of_nonneg_left h (mul_nonneg G.delta_nonneg G.child_nonneg)
  calc
    _ = (G.δ*G.hchild)*(value/G.targetSize) := by
      unfold PhysicalGeometryData.amplitude primaryAmplitude PhysicalGeometryData.targetSize
        PhysicalGeometryData.size PhysicalGeometryData.targetTime
      ring
    _ ≤ _ := hh

theorem good_amplitude_size (x : ι) (s : ℝ) (hs : s ∈ Icc 1 G.H) :
    G.amplitude*G.size x s ≤ G.δ*G.hchild*(64*Real.exp 6) := by
  obtain ⟨F,F1,Z,Z1,J⟩ := G.exists_geometry
  have hh := mul_le_mul_of_nonneg_left (J.horizon_size x s hs) J.amplitude_nonneg
  calc
    _ ≤ G.amplitude*(64*Real.exp 6*G.targetSize) := hh
    _ = (64*Real.exp 6)*(G.amplitude*G.targetSize) := by ring
    _ = _ := by rw [J.amplitude_normalization]; ring

theorem early_amplitude_size (x : ι) (s : ℝ) (hs : s ∈ Icc 0 1) :
    G.amplitude*G.size x s ≤ G.δ*G.hchild *
      (8232*Real.exp 9*G.Θ^5*Real.exp (-(1/(4*G.σ)))) := by
  obtain ⟨F,F1,Z,Z1,J⟩ := G.exists_geometry
  exact amplitude_size_of_ratio G _ _ (J.early_size x s hs)

theorem amplitude_nonneg : 0 ≤ G.amplitude := by
  obtain ⟨F,F1,Z,Z1,J⟩ := G.exists_geometry
  exact J.amplitude_nonneg

theorem good_flux (x : ι) (s : ℝ) (hs : s ∈ Icc 1 G.H) :
    0 < ⟪G.r x (G.time s),G.M x (G.time s) (G.w x (G.time s))⟫_ℝ := by
  obtain ⟨F,F1,Z,Z1,J⟩ := G.exists_geometry
  exact J.positive_pressure x s hs

end EulerPacketGeometryLowBounds

namespace EulerPacketSourceGeometry.Guards

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerSpatialCutoffs
  EulerPacketMovingFrame EulerPacketPrimaryFactorization EulerPacketActivationHistory
  EulerTransversePacketProvider EulerPacketGeometryLowBounds

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T} {P : ParentFrame D τ}
  {H : HistoryData (D.initial τ hτ hτT.le)} (A : Guards hτ hτT P H)
  (hball : (1 / 2 : ℝ) ≤ A.radius)

/-- Low geometry, given by `A.geometryData {x | ‖x‖ ≤ (1/2 : ℝ)} (by norm_num) (fun _ hx =>
hx.trans hball)`. -/
def lowGeometry : PhysicalGeometryData {x : Space // ‖x‖ ≤ (1/2 : ℝ)} :=
  A.geometryData {x | ‖x‖ ≤ (1/2 : ℝ)} (by norm_num) (fun _ hx => hx.trans hball)

/-- Primary amplitude, given by `(A.lowGeometry hball).amplitude`. -/
def primaryAmplitude : ℝ := (A.lowGeometry hball).amplitude

theorem primaryAmplitude_nonneg : 0 ≤ A.primaryAmplitude hball :=
  EulerPacketGeometryLowBounds.amplitude_nonneg (A.lowGeometry hball)

/-- Early ratio, given by `cutoffBound*(8232*Real.exp 9*P.horizon^5*Real.exp
(-(1/(4*P.sigma))))`. -/
def earlyRatio (_A : Guards hτ hτT P H) : ℝ :=
  cutoffBound*(8232*Real.exp 9*P.horizon^5*Real.exp (-(1/(4*P.sigma))))

omit [CompleteSpace U] in
theorem earlyRatio_nonneg : 0 ≤ A.earlyRatio := by
  unfold earlyRatio
  positivity [cutoffBound_pos,A.horizon_lower]

include A in
omit [CompleteSpace U] in
theorem scaledTime_upper (t : Icc (0 : ℝ) D.T) :
    scaledTime τ P.a P.epsilon t ≤ P.horizon := by
  have ha := A.a_pos
  have he := A.epsilon_pos
  have hh := mul_le_mul_of_nonneg_left (sub_le_sub_right t.property.2 τ) (div_nonneg ha.le he.le)
  calc
    _ ≤ (P.a/P.epsilon)*(D.T-τ) := hh
    _ = _ := by unfold ParentFrame.horizon; ring

theorem lowGeometry_size (t : Icc (0 : ℝ) D.T) (x : Space) (hx : ‖x‖ ≤ (1 / 2 : ℝ)) :
    (A.lowGeometry hball).size ⟨x,hx⟩ (scaledTime τ P.a P.epsilon t) =
      ‖D.normal.field t x‖*‖uncutVelocity τ hτ hτT H A.terminal t x‖ := by
  change ‖D.normal.field (D.clamp (physicalTime τ P.a P.epsilon (scaledTime τ P.a P.epsilon t))) x‖*
    ‖uncutVelocity τ hτ hτT H A.terminal (physicalTime τ P.a P.epsilon (scaledTime τ P.a P.epsilon
        t)) x‖ = _
  rw [physicalTime_scaledTime A.a_pos.ne' A.epsilon_pos.ne',Data.clamp_coe]

theorem cutoff_amplitude_size (t : Icc (0 : ℝ) D.T) (x : Space)
    (hs : tsupport innerCutoff ⊆ D.support) :
    A.primaryAmplitude hball*(‖D.normal.field t x‖*‖canonicalVelocity τ hτ hτT H A.terminal hs t
        x‖) =
      innerCutoff x*(A.primaryAmplitude hball*(‖D.normal.field t x‖*‖uncutVelocity τ hτ hτT H
          A.terminal t x‖)) := by
  rw [canonicalVelocity_eq_cutoff_uncut,norm_smul,Real.norm_of_nonneg (innerCutoff_nonneg x)]
  ring

theorem good_primary_size (t : Icc (0 : ℝ) D.T)
    (ht : 1 ≤ scaledTime τ P.a P.epsilon t) (x : Space)
    (hs : tsupport innerCutoff ⊆ D.support) :
    A.primaryAmplitude hball*(‖D.normal.field t x‖*‖canonicalVelocity τ hτ hτT H A.terminal hs t
        x‖) ≤
      A.δ*A.hchild*goodRatio := by
  rw [A.cutoff_amplitude_size hball t x hs]
  by_cases hcut : innerCutoff x=0
  · rw [hcut,zero_mul]
    positivity [A.delta_nonneg,A.child_nonneg,goodRatio_pos]
  have hx : ‖x‖ ≤ (1/2 : ℝ) := by
    have hm := innerCutoff_support (subset_tsupport _ (Function.mem_support.mpr hcut))
    exact le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using hm)
  have hg := good_amplitude_size (A.lowGeometry hball) ⟨x,hx⟩ (scaledTime τ P.a P.epsilon t)
    ⟨ht,A.scaledTime_upper t⟩
  rw [A.lowGeometry_size hball t x hx] at hg
  change A.primaryAmplitude hball*(‖D.normal.field t x‖*‖uncutVelocity τ hτ hτT H A.terminal t x‖) ≤
    A.δ*A.hchild*(64*Real.exp 6) at hg
  calc
    _ ≤ innerCutoff x*(A.δ*A.hchild*(64*Real.exp 6)) :=
      mul_le_mul_of_nonneg_left hg (innerCutoff_nonneg x)
    _ ≤ cutoffBound*(A.δ*A.hchild*(64*Real.exp 6)) :=
      mul_le_mul_of_nonneg_right (cutoff_le x) (by positivity [A.delta_nonneg,A.child_nonneg])
    _ = _ := by unfold goodRatio; ring

include hball in
theorem good_primary_flux (t : Icc (0 : ℝ) D.T)
    (ht : 1 ≤ scaledTime τ P.a P.epsilon t) (x : Space)
    (hs : tsupport innerCutoff ⊆ D.support) :
    0 ≤ ⟪D.normal.field t x,D.M.field t x (canonicalVelocity τ hτ hτT H A.terminal hs t x)⟫_ℝ := by
  rw [canonicalVelocity_eq_cutoff_uncut,map_smul,real_inner_smul_right]
  by_cases hcut : innerCutoff x=0
  · simp only [hcut,zero_mul,le_refl]
  have hx : ‖x‖ ≤ (1/2 : ℝ) := by
    have hm := innerCutoff_support (subset_tsupport _ (Function.mem_support.mpr hcut))
    exact le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using hm)
  have hg := good_flux (A.lowGeometry hball) ⟨x,hx⟩ (scaledTime τ P.a P.epsilon t)
    ⟨ht,A.scaledTime_upper t⟩
  change 0 < ⟪D.normal.field (D.clamp (physicalTime τ P.a P.epsilon (scaledTime τ P.a P.epsilon
      t))) x,
    D.M.field (D.clamp (physicalTime τ P.a P.epsilon (scaledTime τ P.a P.epsilon t))) x
      (uncutVelocity τ hτ hτT H A.terminal (physicalTime τ P.a P.epsilon (scaledTime τ P.a
          P.epsilon t)) x)⟫_ℝ at hg
  rw [physicalTime_scaledTime A.a_pos.ne' A.epsilon_pos.ne',Data.clamp_coe] at hg
  exact mul_nonneg (innerCutoff_nonneg x) hg.le

theorem early_primary_size (t : Icc (0 : ℝ) D.T)
    (ht : scaledTime τ P.a P.epsilon t ∈ Icc 0 1) (x : Space)
    (hs : tsupport innerCutoff ⊆ D.support) :
    A.primaryAmplitude hball*(‖D.normal.field t x‖*‖canonicalVelocity τ hτ hτT H A.terminal hs t
        x‖) ≤
      A.δ*A.hchild*A.earlyRatio := by
  rw [A.cutoff_amplitude_size hball t x hs]
  by_cases hcut : innerCutoff x=0
  · rw [hcut,zero_mul]
    positivity [A.delta_nonneg,A.child_nonneg,A.earlyRatio_nonneg]
  have hx : ‖x‖ ≤ (1/2 : ℝ) := by
    have hm := innerCutoff_support (subset_tsupport _ (Function.mem_support.mpr hcut))
    exact le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using hm)
  have hg := early_amplitude_size (A.lowGeometry hball) ⟨x,hx⟩ (scaledTime τ P.a P.epsilon t) ht
  rw [A.lowGeometry_size hball t x hx] at hg
  change A.primaryAmplitude hball*(‖D.normal.field t x‖*‖uncutVelocity τ hτ hτT H A.terminal t x‖) ≤
    A.δ*A.hchild*(8232*Real.exp 9*P.horizon^5*Real.exp (-(1/(4*P.sigma)))) at hg
  calc
    _ ≤ innerCutoff x*(A.δ*A.hchild*(8232*Real.exp 9*P.horizon^5*Real.exp (-(1/(4*P.sigma))))) :=
      mul_le_mul_of_nonneg_left hg (innerCutoff_nonneg x)
    _ ≤ cutoffBound*(A.δ*A.hchild*(8232*Real.exp 9*P.horizon^5*Real.exp (-(1/(4*P.sigma))))) :=
      mul_le_mul_of_nonneg_right (cutoff_le x) (by
          positivity [A.delta_nonneg,A.child_nonneg,A.horizon_lower])
    _ = _ := by unfold earlyRatio; ring

/-- This cost is computed from the actual stationary endpoint operator.
It is used only on the history interval; the good interval keeps its
sharp universal target-size ratio. -/
def historySizeCost : ℝ :=
  D.inverseBound*historyLabelSizeCost H*P.terminalBound A.CM A.CH

theorem historySizeCost_nonneg : 0 ≤ A.historySizeCost := by
  have hh : 0 ≤ historyLabelSizeCost H :=
    (norm_nonneg (H.coefficients.labelVelocity 0)).trans (labelVelocity_norm H 0)
  unfold historySizeCost
  positivity [D.inverseBound_pos,A.terminalBound_nonneg]

/-- History ratio, given by `cutoffBound*(4*P.horizon*A.historySizeCost/(P.rayScale hτ hτT)) *
Real.exp (-(1/(4*P.sigma)))`. -/
def historyRatio : ℝ :=
  cutoffBound*(4*P.horizon*A.historySizeCost/(P.rayScale hτ hτT)) *
    Real.exp (-(1/(4*P.sigma)))

theorem historyRatio_nonneg : 0 ≤ A.historyRatio := by
  unfold historyRatio
  positivity [cutoffBound_pos,A.horizon_lower,A.historySizeCost_nonneg,rayScale_pos hτ hτT P]

/-- Bad ratio, given by `A.earlyRatio+A.historyRatio`. -/
def badRatio : ℝ := A.earlyRatio+A.historyRatio

theorem badRatio_nonneg : 0 ≤ A.badRatio := add_nonneg A.earlyRatio_nonneg A.historyRatio_nonneg

omit [CompleteSpace U] in
theorem badRatio_formula : A.badRatio = cutoffBound *
    (8232*Real.exp 9*P.horizon^5+4*P.horizon*A.historySizeCost/(P.rayScale hτ hτT)) *
      Real.exp (-(1/(4*P.sigma))) := by
  unfold badRatio earlyRatio historyRatio
  ring

theorem history_uncut_size (t : Icc (0 : ℝ) D.T) (ht : (t : ℝ) ≤ τ) (x : Space) :
    ‖D.normal.field t x‖*‖uncutVelocity τ hτ hτT H A.terminal t x‖ ≤ A.historySizeCost := by
  have hn : ‖D.normal.field t x‖ ≤ D.inverseBound := by
    change ‖(D.FInv.field t x).adjoint D.m₀‖ ≤ _
    calc
      _ ≤ ‖(D.FInv.field t x).adjoint‖*‖D.m₀‖ := (D.FInv.field t x).adjoint.le_opNorm _
      _ = ‖D.FInv.field t x‖ := by rw [ContinuousLinearMap.adjoint.norm_map,D.m₀_unit,mul_one]
      _ ≤ _ := D.inverse_norm t x
  have hv : ‖uncutVelocity τ hτ hτT H A.terminal t x‖ ≤
      historyLabelSizeCost H*P.terminalBound A.CM A.CH := by
    rw [uncutVelocity_history τ hτ hτT H A.terminal ⟨t,t.property.1,ht⟩ x]
    calc
      _ ≤ ‖H.coefficients.labelVelocity x A.terminal‖ :=
        (H.coefficients.labelVelocity x A.terminal).norm_coe_le_norm _
      _ ≤ ‖H.coefficients.labelVelocity x‖*‖A.terminal‖ :=
        (H.coefficients.labelVelocity x).le_opNorm _
      _ ≤ historyLabelSizeCost H*P.terminalBound A.CM A.CH :=
        mul_le_mul (labelVelocity_norm H x) A.terminal_properties.2.2.2.1
          (norm_nonneg _) ((norm_nonneg (H.coefficients.labelVelocity x)).trans (labelVelocity_norm
              H x))
  calc
    _ ≤ D.inverseBound*(historyLabelSizeCost H*P.terminalBound A.CM A.CH) :=
      mul_le_mul hn hv (norm_nonneg _) D.inverseBound_pos.le
    _ = _ := by unfold historySizeCost; ring

theorem history_primary_size (t : Icc (0 : ℝ) D.T) (ht : (t : ℝ) ≤ τ) (x : Space)
    (hs : tsupport innerCutoff ⊆ D.support) :
    A.primaryAmplitude hball*(‖D.normal.field t x‖*‖canonicalVelocity τ hτ hτT H A.terminal hs t
        x‖) ≤
      A.δ*A.hchild*A.historyRatio := by
  let G := A.lowGeometry hball
  obtain ⟨F,F1,Z,Z1,J⟩ := G.exists_geometry
  have hr := (ratio_bound_from_target_growth G.ray_scale_pos G.Theta_pos
    A.historySizeCost_nonneg (A.history_uncut_size t ht x) J.target_growth).2
  have ha := amplitude_size_of_ratio G _ _ hr
  change A.primaryAmplitude hball*(‖D.normal.field t x‖*‖uncutVelocity τ hτ hτT H A.terminal t x‖) ≤
    A.δ*A.hchild*((4*P.horizon*A.historySizeCost/(P.rayScale hτ hτT))*Real.exp (-(1/(4*P.sigma))))
        at ha
  rw [A.cutoff_amplitude_size hball t x hs]
  calc
    _ ≤ innerCutoff x*(A.δ*A.hchild*((4*P.horizon*A.historySizeCost/(P.rayScale hτ hτT))*Real.exp
        (-(1/(4*P.sigma))))) :=
      mul_le_mul_of_nonneg_left ha (innerCutoff_nonneg x)
    _ ≤ cutoffBound*(A.δ*A.hchild*((4*P.horizon*A.historySizeCost/(P.rayScale hτ hτT))*Real.exp
        (-(1/(4*P.sigma))))) :=
      mul_le_mul_of_nonneg_right (cutoff_le x)
        (by
            positivity [A.delta_nonneg, A.child_nonneg, A.horizon_lower, A.historySizeCost_nonneg,
                rayScale_pos hτ hτT P])
    _ = _ := by unfold historyRatio; ring

/-- One exponential target-ratio bound covers every time before scaled
time one, including the stationary history. -/
theorem bad_primary_size (t : Icc (0 : ℝ) D.T)
    (ht : scaledTime τ P.a P.epsilon t ≤ 1) (x : Space)
    (hs : tsupport innerCutoff ⊆ D.support) :
    A.primaryAmplitude hball*(‖D.normal.field t x‖*‖canonicalVelocity τ hτ hτT H A.terminal hs t
        x‖) ≤
      A.δ*A.hchild*A.badRatio := by
  by_cases hh : (t : ℝ) ≤ τ
  · exact (A.history_primary_size hball t hh x hs).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left A.earlyRatio_nonneg)
        (mul_nonneg A.delta_nonneg A.child_nonneg))
  · have htime : 0 ≤ scaledTime τ P.a P.epsilon t := by
      unfold scaledTime
      exact mul_nonneg (div_nonneg A.a_pos.le A.epsilon_pos.le) (sub_nonneg.mpr (le_of_not_ge hh))
    exact (A.early_primary_size hball t ⟨htime,ht⟩ x hs).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right A.historyRatio_nonneg)
        (mul_nonneg A.delta_nonneg A.child_nonneg))

end EulerPacketSourceGeometry.Guards
