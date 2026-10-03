/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.HigherStepConstants

/-! Actual higher material velocity bounds by source scale summation. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- The actual source scale steps telescope with coefficient one on the
coarse term. No estimate on the current material velocity level is assumed. -/
theorem amnr_velocity_higher_material_abs_le_of_source_lower_levels {β C Kprev : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) (hreg : AVenhance.StreamRegularityBounds C I Φ)
    {n : ℕ} (hn : 1 ≤ n) (hlevels : AmnrSourceJetLevels I Φ Kprev (n - 1))
    (hKprev : 1 ≤ Kprev) (m : ℕ) (α : List (Fin 2))
    (hbudget : α.length + 2 * n + 1 ≤ AVenhance.Nstar β) (i : Fin 2) (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ m) y.1 y.2) (amnrMixedWord α n)
      (fun y => AVenhance.streamVel (Φ m) y.1 y.2 i) z| ≤
      (2 * amnrHigherVelocityStepConstant I Kprev n α.length) *
        AVenhance.epsilon β I.Λ m ^ (β - 1) * (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length *
          AVenhance.a β I.Λ m ^ n := by
  let b := fun j => fun y : AmnrSpace => AVenhance.streamVel (Φ j) y.1 y.2
  let F := fun j => amnrWord (b j) (List.replicate n none) (fun y => b j y i)
  let q := β - 1 + (β - 2) * (n : ℝ) - (α.length : ℝ)
  let v := fun j => amnrWord (fun _ => (0 : Vec 2)) (α.map some) (F j) z
  let u := fun j => AVenhance.epsilon β I.Λ j ^ q
  let K := amnrHigherVelocityStepConstant I Kprev n α.length
  have hK : 0 ≤ K := amnrHigherVelocityStepConstant_nonneg I (by linarith) n α.length
  have hF (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (F j) := by
    have hb := (AVenhance.Infra.Construction.smoothPeriodic_streamVel
        (AVenhance.streamSeq_isAdmissible hΦ j)).smooth
    exact contDiffOn_univ.mp (amnrWord_contDiffOn_infty isOpen_univ hb.contDiffOn
      ((contDiff_apply ℝ ℝ i).comp hb).contDiffOn (List.replicate n none))
  have hzero : v 0 = 0 := by
    have hFb : F 0 = 0 := amnr_streamVelocity_zero_word I hΦ _ i
    simp [v, hFb, amnrWord_zero]
  have hstep (j : ℕ) : |v (j + 1) - v j| ≤ K * u (j + 1) := by
    have hh := amnr_velocity_higher_source_step I hΦ hreg hn (m := j + 1) (by omega)
      hlevels hKprev α hbudget i z
    have hs := amnrWord_sub_global
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : AmnrSpace => (0 : Vec 2)))
      (hF (j + 1)) (hF j) (α.map some)
    have hscale := amnr_higher_material_spatial_scale
      (β := β) (AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
        (m := j + 1)) α.length n
    rw [amnrWord_spatial_independent _ (fun _ => (0 : Vec 2))] at hh
    change |amnrWord (fun _ => (0 : Vec 2)) (α.map some) (F (j + 1) - F j) z| ≤ _ at hh
    rw [hs] at hh
    refine hh.trans_eq ?_
    change K * AVenhance.epsilon β I.Λ (j + 1) ^ (β - 1) *
      (AVenhance.epsilon β I.Λ (j + 1))⁻¹ ^ α.length * AVenhance.a β I.Λ (j + 1) ^ n = K * u (j + 1)
    calc
      _ = K * (AVenhance.epsilon β I.Λ (j + 1) ^ (β - 1) *
          AVenhance.a β I.Λ (j + 1) ^ n * (AVenhance.epsilon β I.Λ (j + 1))⁻¹ ^ α.length) := by ring
      _ = _ := congrArg (fun x => K * x) hscale
  have hh := amnr_abs_recursion_sum v u hK
    (fun j => Real.rpow_nonneg (AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le (m := j)).le _) hzero hstep m
  have hq : q ≤ -(1 / 7 : ℝ) := amnr_higher_material_exponent_le I.beta_lt α.length n hn
  have hsum := amnr_negative_power_sum I hq m
  have hb := hh.trans (mul_le_mul_of_nonneg_left hsum hK)
  rw [amnrMixedWord, amnrWord_append,
    amnrWord_spatial_independent _ (fun _ => (0 : Vec 2))]
  refine hb.trans_eq ?_
  have hscale := amnr_higher_material_spatial_scale (β := β)
    (AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m))
        α.length n
  change K * (2 * AVenhance.epsilon β I.Λ m ^ q) = _
  rw [← hscale]
  dsimp [K, AVenhance.a]
  ring

end AVenhance.Infra.Section4
