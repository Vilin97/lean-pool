/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.VelocitySecondRates

/-! The first spatial primitive flow rate, from actual stream-regularity derivative bounds. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Flow

/-- The actual previous velocity has the source Lipschitz rate also at the
zero-stream base scale. -/
theorem amnr_previous_velocity_lipschitz_of_A3 {β C : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) {m : ℕ} (hm : 1 ≤ m)
    (t : ℝ) (x y : Vec 2) :
    ‖AVenhance.streamVel (Φ (m - 1)) t x - AVenhance.streamVel (Φ (m - 1)) t y‖ ≤
      ((2 : ℝ) ^ 20 * AVenhance.a β I.Λ (m - 1)) * ‖x - y‖ := by
  let L := (2 : ℝ) ^ 20 * AVenhance.a β I.Λ (m - 1)
  have ha := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m - 1)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hb := AVenhance.Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)
  have hs : ContDiff ℝ (⊤ : ℕ∞) (AVenhance.streamVel (Φ (m - 1)) t) :=
    hb.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hlip : LipschitzWith L.toNNReal (AVenhance.streamVel (Φ (m - 1)) t) := by
    apply lipschitzWith_of_nnnorm_fderiv_le (hs.differentiable (by simp))
    intro x
    apply NNReal.coe_le_coe.mp
    rw [coe_nnnorm, Real.coe_toNNReal L hL, ← jointSpatialFDeriv_eq_slice hb]
    exact amnr_previous_velocityJacobian_norm_le_of_A3 I hΦ hreg hm t x
  simpa only [dist_eq_norm, Real.coe_toNNReal L hL] using hlip.dist_le_mul x y

/-- The inverse flow has a uniform spatial derivative norm on each actual
cutoff window, from Grönwall and the preceding source velocity rate. -/
theorem amnr_xFlowInv_fderiv_norm_le_two_of_A3 {β C : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) {m : ℕ} (hm : 1 ≤ m)
    (l : ℤ) (t : ℝ) (x : Vec 2)
    (ht : |t - (l : ℝ) * AVenhance.tauPP β I.Λ m| ≤
      AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m) :
    ‖fderiv ℝ (I.xFlowInv hΦ m l t) x‖ ≤ 2 := by
  let b := AVenhance.streamVel (Φ (m - 1))
  let X := AVenhance.flow b (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz
  let s := (l : ℝ) * AVenhance.tauPP β I.Λ m
  let A := AVenhance.a β I.Λ (m - 1)
  let L := (2 : ℝ) ^ 20 * A
  have ha : 0 < A := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hX : AVenhance.IsFlow b X := AVenhance.flow_isFlow b _ _
  have hd : ‖fderiv ℝ (I.xFlowInv hΦ m l t) x‖ ≤ Real.exp (L * |t - s|) := by
    apply norm_fderiv_le_of_lip' ℝ (Real.exp_pos _).le
    apply Filter.Eventually.of_forall
    intro y
    have hh := flow_spatial_gronwall b (amnr_previous_velocity_lipschitz_of_A3 I hΦ hreg hm)
      hX y x t s
    simpa only [AVenhance.Ingredients.xFlowInv, AVenhance.flowInv, abs_sub_comm s t] using hh
  refine hd.trans ?_
  have htime : |t - s| ≤ (2 : ℝ) ^ (-25 : ℤ) * A⁻¹ :=
    ht.trans (amnr_cutoff_window_fits_flow I hm)
  have hh := mul_le_mul_of_nonneg_left htime (show 0 ≤ L by dsimp [L]; positivity)
  have heq : L * ((2 : ℝ) ^ (-25 : ℤ) * A⁻¹) = 1 / 32 := by
    dsimp [L]
    field_simp
    norm_num
  rw [heq] at hh
  have he := Real.exp_le_two_add_div_two_sub (x := (1 : ℝ) / 32) (by norm_num) (by norm_num)
  exact (Real.exp_le_exp.mpr hh).trans (he.trans (by norm_num))

end AVenhance.Infra.Section4
