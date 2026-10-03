/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Ingredients
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.CardinalIntegral
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.BaseCutoffs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.ScaleCutoffs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.TimeScaleFacts

/-! Proof of ingredient statement ingredient existence. -/

@[expose] public section

noncomputable section

namespace AVenhance.Proofs.Ingredients

open AVenhance.Infra.Cutoff

theorem nonempty (β : ℝ) (h1 : 1 < β) (h2 : β < 4 / 3) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ Λ : ℕ, 2 ^ 7 ≤ Λ →
      ∃ I : AVenhance.Ingredients β,
        I.Λ = Λ ∧ I.Czeta ≤ C₀ ∧ I.Cxi ≤ C₀ ∧ I.Chat ≤ C₀ := by
  obtain ⟨Cζ, hCζ, hζderiv⟩ := cardinalZeta_deriv_bound (AVenhance.Nstar β)
  obtain ⟨Cξ, hCξ, hξderiv⟩ := cardinalXi_deriv_bound (AVenhance.Nstar β)
  obtain ⟨M, hM, hstep⟩ := step_iteratedDeriv_bound (AVenhance.Nstar β)
  let Chat : ℝ := max 1 (2 ^ AVenhance.Nstar β * M ^ 2)
  let C₀ : ℝ := max Cζ (max Cξ Chat)
  have hChat : 1 ≤ Chat := le_max_left _ _
  have hC₀ : 1 ≤ C₀ := le_trans hCζ (le_max_left _ _)
  have hCζ₀ : Cζ ≤ C₀ := le_max_left _ _
  have hCξ₀ : Cξ ≤ C₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hChat₀ : Chat ≤ C₀ := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C₀, hC₀, ?_⟩
  intro Λ hΛ
  let I : AVenhance.Ingredients β := {
    one_lt_beta := h1
    beta_lt := h2
    Λ := Λ
    two_pow_seven_le := hΛ
    zeta := cardinalZeta
    zeta_smooth := cardinalZeta_contDiff
    zeta_compact := cardinalZeta_compact
    zeta_even := cardinalZeta_even
    Czeta := Cζ
    one_le_Czeta := hCζ
    zeta_nonneg := cardinalZeta_nonneg
    zeta_le_ind := cardinalZeta_le_indIcc
    zeta_partition := cardinalZeta_partition
    zeta_deriv_le := hζderiv
    zeta_sq_integral := cardinalZeta_sq_integral
    xi := cardinalXi
    xi_smooth := cardinalXi_contDiff
    Cxi := Cξ
    one_le_Cxi := hCξ
    ind_le_xi := cardinalXi_ind_le
    xi_le_ind := cardinalXi_le_indIcc
    xi_partition := cardinalXi_partition
    xi_deriv_le := hξderiv
    hatZeta := fun m => hatZetaCutoff
      (AVenhance.tauPP β Λ m) (AVenhance.tauP β Λ m)
    hatXi := fun m => hatXiCutoff
      (AVenhance.tauPP β Λ m) (AVenhance.tauP β Λ m)
    hatZeta_smooth := by
      intro m
      exact hatZetaCutoff_contDiff _ _
    hatXi_smooth := by
      intro m
      exact hatXiCutoff_contDiff _ _
    Chat := Chat
    one_le_Chat := hChat
    hatZeta_ge := by
      intro m hm l t
      exact hatZeta_shift_ge
        (tauP_pos h1 h2 hΛ) (four_tauP_le_tauPP h1 h2 hΛ) l t
    hatZeta_le := by
      intro m hm l t
      exact hatZeta_shift_le (tauP_pos h1 h2 hΛ) l t
    hatXi_ge := by
      intro m hm l t
      have hspace := four_tauP_le_tauPP h1 h2 hΛ (m := m)
      have hmargin := tauP_pos h1 h2 hΛ (m := m)
      have hspace' : 2 * AVenhance.tauP β Λ m ≤ AVenhance.tauPP β Λ m := by
        nlinarith
      exact hatXi_shift_ge (tauP_pos h1 h2 hΛ) hspace' l t
    hatXi_le := by
      intro m hm l t
      exact hatXi_shift_le (tauP_pos h1 h2 hΛ) l t
    hatXi_partition := by
      intro m hm t
      have hperiod := tauPP_pos h1 h2 hΛ (m := m)
      have hmargin := tauP_pos h1 h2 hΛ (m := m)
      have hspace := four_tauP_le_tauPP h1 h2 hΛ (m := m)
      have hspace' : 2 * AVenhance.tauP β Λ m ≤ AVenhance.tauPP β Λ m := by
        nlinarith
      simpa using hatXi_partition hperiod hmargin hspace' t
    hatZeta_deriv_le := by
      intro m hm l j hj t
      have hbound := hatZeta_scaled_deriv_bound
        (period := AVenhance.tauPP β Λ m) (margin := AVenhance.tauP β Λ m)
        (N := AVenhance.Nstar β) (M := M)
        (tauP_pos h1 h2 hΛ) hM hstep l hj t
      exact hbound.trans (le_max_right 1 (2 ^ AVenhance.Nstar β * M ^ 2))
    hatXi_deriv_le := by
      intro m hm l j hj t
      have hspace := four_tauP_le_tauPP h1 h2 hΛ (m := m)
      have hmargin := tauP_pos h1 h2 hΛ (m := m)
      have hspace' : 2 * AVenhance.tauP β Λ m ≤ AVenhance.tauPP β Λ m := by
        nlinarith
      have hbound := hatXi_scaled_deriv_bound
        (period := AVenhance.tauPP β Λ m) (margin := AVenhance.tauP β Λ m)
        (N := AVenhance.Nstar β) (M := M)
        hmargin hM hstep hspace' l hj t
      exact hbound.trans (le_max_right 1 (2 ^ AVenhance.Nstar β * M ^ 2))
  }
  refine ⟨I, rfl, hCζ₀, hCξ₀, hChat₀⟩

end AVenhance.Proofs.Ingredients
