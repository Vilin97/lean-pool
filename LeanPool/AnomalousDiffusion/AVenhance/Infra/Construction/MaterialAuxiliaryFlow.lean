/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowSpatialSourceRates

/-! Auxiliary spatial flow orders for the finite material word budget. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Flow

/-- The stream-regularity estimates and the actual source cutoff length control all actual spatial
    flow
operators by one constant independent of the scale and the starting time. -/
theorem amnr_aux_previous_flow_iteratedFDeriv_norm_le_of_A3 {β C : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) (hreg : AVenhance.StreamRegularityBounds C I Φ)
    {m : ℕ} (hm : 1 ≤ m) (s t : ℝ)
    (ht : |t - s| ≤ AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m)
    {N : ℕ} (n : ℕ) (hbudget : n ≤ N) (x : Vec 2) :
    ‖iteratedFDeriv ℝ (n + 1)
      (fun y => AVenhance.flow (AVenhance.streamVel (Φ (m - 1)))
        (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz t y s) x‖ ≤
      amnrFlowSpatialSourceConstant (N) *
        (AVenhance.epsilon β I.Λ (m - 1))⁻¹ ^ n := by
  let A := AVenhance.a β I.Λ (m - 1)
  let ε := AVenhance.epsilon β I.Λ (m - 1)
  let M := (2 : ℝ) ^ 20 * A
  let P := (2 : ℝ) ^ (N + 1) * amnrSpatialVelocityConstant N
  let B := P * A
  let D := (2 : ℝ) ^ (-25 : ℤ) * P
  have hA : 0 < A := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hε : 0 < ε := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hCN : 0 < amnrSpatialVelocityConstant N := amnrSpatialVelocityConstant_pos N
  have hP : 0 ≤ P := by
    dsimp [P]
    exact mul_nonneg (by positivity) (amnrSpatialVelocityConstant_pos N).le
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hB : 0 ≤ B := mul_nonneg hP hA.le
  have htime : |t - s| ≤ (2 : ℝ) ^ (-25 : ℤ) * A⁻¹ :=
    ht.trans (amnr_cutoff_window_fits_flow I hm)
  have hAd : A * |t - s| ≤ (2 : ℝ) ^ (-25 : ℤ) := by
    have hh := mul_le_mul_of_nonneg_left htime hA.le
    have heq : A * ((2 : ℝ) ^ (-25 : ℤ) * A⁻¹) = (2 : ℝ) ^ (-25 : ℤ) := by field_simp
    rwa [heq] at hh
  have hsmall : (max s t - min s t) * M ≤ 1 / 2 := by
    rw [max_sub_min_eq_abs]
    have hh := mul_le_mul_of_nonneg_left hAd (show (0 : ℝ) ≤ 2 ^ 20 by positivity)
    have heq : (2 : ℝ) ^ 20 * (2 : ℝ) ^ (-25 : ℤ) = 1 / 32 := by norm_num
    rw [heq] at hh
    have hmid : |t - s| * M ≤ 1 / 32 := by convert hh using 1; dsimp [M]; ring
    exact hmid.trans (by norm_num)
  have hscale : (max s t - min s t) * B ≤ D := by
    rw [max_sub_min_eq_abs]
    have hh := mul_le_mul_of_nonneg_left hAd hP
    convert hh using 1 <;> dsimp [B, D] <;> ring
  have hp : ∀ i, i ≤ N → ∀ u y,
      ‖iteratedFDeriv ℝ i (fun z => jointSpatialFDeriv (AVenhance.streamVel (Φ (m - 1))) u z) y‖ ≤
        B * ε⁻¹ ^ i := by
    intro i hi u y
    have hh := amnr_previous_velocityJacobian_iteratedFDeriv_norm_le_of_A3_auxiliary_budget
      I hΦ hreg hm i N hi u y
    refine hh.trans ?_
    change (2 : ℝ) ^ (i + 1) * (amnrSpatialVelocityConstant N * A * ε⁻¹ ^ i) ≤
      ((2 : ℝ) ^ (N + 1) * amnrSpatialVelocityConstant N * A) * ε⁻¹ ^ i
    calc
      _ ≤ (2 : ℝ) ^ (N + 1) * (amnrSpatialVelocityConstant N * A * ε⁻¹ ^ i) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
      _ = _ := by ring
  have hh := amnr_flow_iteratedFDeriv_norm_le_of_primitive_jets
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m))
    (AVenhance.flow_isFlow (AVenhance.streamVel (Φ (m - 1)))
      (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz)
    hM hB hε (amnr_previous_velocityJacobian_norm_le_of_A3 I hΦ hreg hm)
    (min_le_max) ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩
    hsmall hscale hp n hbudget x
  have hc : amnrJacobianJetConstant D N = amnrFlowSpatialSourceConstant N := by
    unfold amnrFlowSpatialSourceConstant
    congr 1
    dsimp [D, P]
    ring
  refine hh.trans ?_
  change amnrJacobianJetConstant D n * ε⁻¹ ^ n ≤ amnrFlowSpatialSourceConstant N * ε⁻¹ ^ n
  rw [← hc]
  exact mul_le_mul_of_nonneg_right (amnrJacobianJetConstant_mono D hbudget) (by positivity)

/-- The inverse flow has the same auxiliary-order spatial rate after exchanging its actual initial
    and target times. -/
theorem amnr_aux_xFlowInv_iteratedFDeriv_norm_le_of_A3 {β C : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) (hreg : AVenhance.StreamRegularityBounds C I Φ)
    {m : ℕ} (hm : 1 ≤ m) (l : ℤ) (t : ℝ)
    (ht : |t - (l : ℝ) * AVenhance.tauPP β I.Λ m| ≤
      AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m)
    {N : ℕ} (n : ℕ) (hbudget : n ≤ N) (x : Vec 2) :
    ‖iteratedFDeriv ℝ (n + 1) (I.xFlowInv hΦ m l t) x‖ ≤
      amnrFlowSpatialSourceConstant N *
        (AVenhance.epsilon β I.Λ (m - 1))⁻¹ ^ n :=
  amnr_aux_previous_flow_iteratedFDeriv_norm_le_of_A3 I hΦ hreg hm t _
    (by simpa only [abs_sub_comm] using ht) (N := N) n hbudget x

end AVenhance.Infra.Section4

end
