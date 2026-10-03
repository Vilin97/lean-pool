/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureCalculus

/-! Primitive zero-order bounds for the actual pulled-back flow gradient. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Filter
namespace AVenhance.Infra.Section4

/-- Grönwall controls every coordinate of the actual flow gradient. The
pullback evaluation needs no additional estimate on the inverse flow. -/
theorem amnr_flowGrad_abs_le_of_lipschitz {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ) (m : ℕ)
    {L : ℝ} (hL : ∀ t x y,
      ‖AVenhance.streamVel (Φ (m - 1)) t x - AVenhance.streamVel (Φ (m - 1)) t y‖ ≤
        L * ‖x - y‖) (l : ℤ) (t : ℝ) (x : Vec 2) (k p : Fin 2) :
    |I.flowGrad hΦ m l t x k p| ≤
      Real.exp (L * |t - (l : ℝ) * AVenhance.tauPP β I.Λ m|) := by
  let b := AVenhance.streamVel (Φ (m - 1))
  let X := AVenhance.flow b (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz
  let s := (l : ℝ) * AVenhance.tauPP β I.Λ m
  let y := I.xFlowInv hΦ m l t x
  have hX : AVenhance.IsFlow b X := AVenhance.flow_isFlow b _ _
  have hd : ‖fderiv ℝ (fun v => X t v s p) y‖ ≤ Real.exp (L * |t - s|) := by
    apply norm_fderiv_le_of_lip' ℝ (Real.exp_pos _).le
    apply Filter.Eventually.of_forall
    intro v
    calc
      ‖X t v s p - X t y s p‖ ≤ ‖X t v s - X t y s‖ :=
        norm_le_pi_norm (X t v s - X t y s) p
      _ ≤ _ := AVenhance.Infra.Flow.flow_spatial_gronwall b hL hX v y s t
  change |fderiv ℝ (fun v => X t v s p) y (basisVec k)| ≤ _
  rw [← Real.norm_eq_abs]
  calc
    _ ≤ ‖fderiv ℝ (fun v => X t v s p) y‖ * ‖basisVec k‖ :=
      (fderiv ℝ (fun v => X t v s p) y).le_opNorm _
    _ = ‖fderiv ℝ (fun v => X t v s p) y‖ := by simp [basisVec, Pi.norm_single]
    _ ≤ _ := hd

/-- On every closed cutoff window, the source-scale Lipschitz estimate gives
a uniform primitive flow-gradient bound, independent of m and l. -/
theorem amnr_flowGrad_abs_le_on_cutoff_window {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ t x y,
      ‖AVenhance.streamVel (Φ (m - 1)) t x - AVenhance.streamVel (Φ (m - 1)) t y‖ ≤
        (C * AVenhance.a β I.Λ (m - 1)) * ‖x - y‖)
    (l : ℤ) (t : ℝ) (x : Vec 2)
    (ht : |t - (l : ℝ) * AVenhance.tauPP β I.Λ m| ≤
      AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m) (k p : Fin 2) :
    |I.flowGrad hΦ m l t x k p| ≤ Real.exp (C * (2 : ℝ) ^ (-25 : ℤ)) := by
  have ha := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m - 1)
  refine (amnr_flowGrad_abs_le_of_lipschitz I hΦ m hL l t x k p).trans ?_
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left
    (ht.trans (amnr_cutoff_window_fits_flow I hm)) (mul_nonneg hC ha.le)
  have he : (C * AVenhance.a β I.Λ (m - 1)) *
      ((2 : ℝ) ^ (-25 : ℤ) * (AVenhance.a β I.Λ (m - 1))⁻¹) =
      C * (2 : ℝ) ^ (-25 : ℤ) := by field_simp
  exact he ▸ hh

end AVenhance.Infra.Section4
