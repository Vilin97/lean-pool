/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInductionStage

@[expose] public section

/-! The actual physical gradient at a stage's activation diverges with
the stage index. This uses the invariant's true frame decomposition. -/

noncomputable section

namespace EulerPacketInductionScales

open Real EulerPacketLowConstants EulerTransverseActivationSelection

theorem activationMargin_le_half : activationMargin ≤ 1/2 := by
  have hH := hessian_nonneg
  have hA : 0 ≤ activationConstant gradientConstant hessianConstant := by
    unfold activationConstant
    positivity
  unfold activationMargin
  apply (div_le_iff₀ (show 0 < 32*(activationConstant gradientConstant hessianConstant+1) by
    positivity)).mpr
  linarith only [hA]

namespace Scales

open EulerPacketSourceScaleSequence

theorem previousShear_ge_index {c B : ℝ} (S : Scales c B) (n : ℕ) :
    (n : ℝ)+1 ≤ previousShear S.J S.X n := by
  induction n with
  | zero => simpa only [Nat.cast_zero,zero_add] using S.previousShear_one 0
  | succ n ih =>
    have h := S.shear_separation n
    have hp := S.previousShear_one n
    change ((n+1 : ℕ) : ℝ)+1 ≤ shear S.J S.X n
    push_cast
    nlinarith only [ih,h,hp,sq_nonneg (previousShear S.J S.X n-1)]

end Scales
end EulerPacketInductionScales

namespace EulerPacketInduction.Stage

open Set Real Filter InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerPacketInductionScales EulerPacketSourceGeometry EulerPacketNormalizedPrimary
  EulerPacketSourceScaleSequence EulerPacketSourceScaleActual EulerPacketLowConstants
  EulerTransversePacketProvider
open scoped Topology

variable {c B : ℝ} {S : Scales c B} {n : ℕ} (P : Stage S n)

def activationGradient : ℝ :=
  ‖fderiv ℝ (fun x => P.state.evolution.velocity (P.time,x)) 0‖

theorem gradient_lower (hn : n ≠ 0) : previousShear S.J S.X n/2 ≤ P.activationGradient := by
  let t : Icc (0 : ℝ) P.parent.T := ⟨P.time,P.time_nonneg,P.time_lt.le⟩
  let M := P.parent.strain.field t 0
  let Q := P.frame.shear • rankOne ℝ (unit (P.frame.v P.time)) (unit (P.frame.m P.time))
  have hs := (S.previousShear_one n)
  have hnorm : ‖Q‖=previousShear S.J S.X n := by
    simp only [Q,norm_smul,Real.norm_eq_abs,P.frame_shear,
      abs_of_nonneg (zero_le_one.trans hs),norm_rankOne,
      unit_norm (P.frame.velocity_nonzero P.time ⟨le_rfl,P.time_lt.le⟩),
      unit_norm (P.frame.ray_nonzero P.time ⟨le_rfl,P.time_lt.le⟩),mul_one]
  have hr : ‖M-P.frame.B P.time-Q‖ ≤ P.frame.error := by
    have h := P.frame.remainder_bound P.time ⟨le_rfl,P.time_lt.le⟩
    rw [Data.clamp_coe (frameData P.parent) t] at h
    exact h
  have hB := P.frame.B_bound P.time ⟨le_rfl,P.time_lt.le⟩
  have hM : previousShear S.J S.X n ≤ ‖M‖+P.frame.G+P.frame.error := by
    calc
      _ = ‖Q‖ := hnorm.symm
      _ = ‖(M-P.frame.B P.time)-(M-P.frame.B P.time-Q)‖ := by congr 1; module
      _ ≤ ‖M-P.frame.B P.time‖+‖M-P.frame.B P.time-Q‖ := norm_sub_le _ _
      _ ≤ (‖M‖+‖P.frame.B P.time‖)+P.frame.error := add_le_add (norm_sub_le _ _) hr
      _ ≤ _ := add_le_add (add_le_add le_rfl hB) le_rfl
  have he : P.frame.G+P.frame.error ≤ previousShear S.J S.X n/2 := by
    have hc := (add_le_add P.frame_bound P.frame_error).trans (S.activation_small hn)
    have hh := mul_le_mul_of_nonneg_right activationMargin_le_half (zero_le_one.trans hs)
    nlinarith only [hc,hh]
  have heq : ‖M‖=P.activationGradient := by
    exact congrArg norm (P.state.evolution.strain_origin P.state.odd t)
  rw [heq] at hM
  linarith only [hM,he]

theorem gradient_atTop (P : ∀ n, Stage S n) :
    Tendsto (fun n => (P n).activationGradient) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  obtain ⟨N,hN⟩ := exists_nat_gt (2*b)
  filter_upwards [eventually_ge_atTop (N+1)] with n hn
  have hn0 : n ≠ 0 := by omega
  have hi : (N : ℝ)+1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hs := S.previousShear_ge_index n
  have hg := (P n).gradient_lower hn0
  linarith only [hN,hi,hs,hg]

end EulerPacketInduction.Stage
