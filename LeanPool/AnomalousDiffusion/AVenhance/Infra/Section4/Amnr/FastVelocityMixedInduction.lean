/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.StreamMixedCurrentRates

/-! Actual higher fast-velocity jets from strictly lower coarse gradient levels. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- The actual fast velocity has every mixed jet from lower material levels
of the coarse gradient. The input remains explicit in this conditional induction
step; its transported scalar and every commutator are proved. -/
theorem amnr_fastVelocity_mixed_abs_le_of_lower_gradient_bounds {β C Cb : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) (hreg : AVenhance.StreamRegularityBounds C I Φ)
    {m : ℕ} (hm : 1 ≤ m) (hCb : 0 ≤ Cb) (α : List (Fin 2)) (n : ℕ)
    (hbudget : α.length + 1 + 2 * n ≤ AVenhance.Nstar β) (i : Fin 2) (z : AmnrSpace)
    (hBb : ∀ p q η r, r < n → η.length + 2 * r + 2 ≤ AVenhance.Nstar β →
      |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) (amnrMixedWord η r)
        (amnrVelocityGradient (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) p q) z| ≤
        Cb * AVenhance.a β I.Λ m * (AVenhance.epsilon β I.Λ m)⁻¹ ^ η.length *
          AVenhance.a β I.Λ m ^ r) :
    |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) (amnrMixedWord α n)
      (fun y => AVenhance.streamVel (Φ m) y.1 y.2 i -
        AVenhance.streamVel (Φ (m - 1)) y.1 y.2 i) z| ≤
      ((1 + (2 : ℝ) ^ (AVenhance.Nstar β + 1) * Cb) ^ n * amnrStreamMixedCurrentConstant I) *
        AVenhance.epsilon β I.Λ m ^ (β - 1) * (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length *
        AVenhance.a β I.Λ m ^ n := by
  let b := fun y : AmnrSpace => AVenhance.streamVel (Φ (m - 1)) y.1 y.2
  let f := fun y : AmnrSpace => Φ m y.1 y.2 - Φ (m - 1) y.1 y.2
  let q : Fin 2 := if i = 0 then 1 else 0
  let S := (AVenhance.epsilon β I.Λ m)⁻¹
  let H := AVenhance.a β I.Λ m
  let F := amnrStreamMixedCurrentConstant I * H * AVenhance.epsilon β I.Λ m ^ 2
  have hb : ContDiff ℝ (⊤ : ℕ∞) b :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)).smooth
  have hf := amnr_streamIncrement_contDiff I hΦ m
  have hE := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hH := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hK := amnrStreamMixedCurrentConstant_pos I
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hh := amnr_material_gradient_mixed_abs_le_of_lower_gradient_bounds hb hf
    (N := AVenhance.Nstar β) (cut := n) (inv_nonneg.mpr hE.le) hH.le hF hCb z
    (fun η r hbudget => amnr_streamIncrement_mixed_current_abs_le_of_A3 I hΦ hreg hm η r hbudget z)
    hBb n le_rfl α 0 (by omega) q
  simp only [Nat.add_zero] at hh
  rw [amnr_fastVelocity_component I hΦ m i, amnrWord_const_smul]
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
  rw [show |if i = 0 then (-1 : ℝ) else 1| = 1 by split_ifs <;> norm_num, one_mul]
  change |amnrWord b (amnrMixedWord α n) (amnrOp b (some q) f) z| ≤ _
  have heq : amnrWord b (List.replicate 0 none) f = f := rfl
  rw [heq] at hh
  refine hh.trans_eq ?_
  have hc := amnr_stream_amplitude_spatial_cancel (A := H) (β := β) hE
    (amnr_amplitude_gradient_scale (β := β) hE) α.length
  change (1 + (2 : ℝ) ^ (AVenhance.Nstar β + 1) * Cb) ^ n * F * S ^ (α.length + 1) * H ^ n = _
  dsimp [F]
  calc
    _ = ((1 + (2 : ℝ) ^ (AVenhance.Nstar β + 1) * Cb) ^ n * amnrStreamMixedCurrentConstant I) *
        (H * AVenhance.epsilon β I.Λ m ^ 2 * S ^ (α.length + 1)) * H ^ n := by ring
    _ = _ := by rw [hc]; ring

end AVenhance.Infra.Section4
