/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TUpgradeConsumersTrace

/-! # TUpgrade Consumers Final

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance

theorem iterate_T_upgrade_of_analytic (β Ccut : ℝ) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧
    ∀ (I : Ingredients β) (_hz : I.Czeta ≤ Ccut) (_hxi : I.Cxi ≤ Ccut)
      (_hh : I.Chat ≤ Ccut)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (κ : ℝ) (M : ℕ) {m : ℕ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (_hT : I.IsTIterates hΦ m (I.kappaAt κ m (M - m)) (I.kappaAt κ (m - 1)
        (M - (m - 1))) θ₀ θprev T)
    (_hθ : IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaAt κ (m - 1) (M - (m - 1))) (fun _ _ =>
        0) θ₀ θprev)
    (_hm : 2 ≤ m) (_hmM : m ≤ M) (_hPerm : κ ∈ permittedInterval β I.Λ M)
    (Rθ : ℝ)
    (_hRθ : 0 < Rθ)
    (_hradius : epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ Rθ)
    (_hsmall : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ (4 * C₀ ^ 3)⁻¹)
    (_hAnalytic : IsThetaAnalytic Rθ θ₀),
    (Real.sqrt (I.kappaAt κ (m - 1) (M - (m - 1))) * Real.sqrt (spaceTimeGradNormSq
      (fun t => spaceGrad (T (Nstar β) t))) ≤
      (2 * Real.sqrt (l2NormSq θ₀)) * (1 + (C₀ ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β)) *
          (Nstar β : ℝ) * ((2 * Nstar β).factorial : ℝ))) ∧
    (∀ v w : List (Fin 2), v.length = w.length → 1 ≤ v.length →
      ∀ s, 0 ≤ s → s ≤ 1 →
      Real.sqrt (l2NormSq (iterateSpatialWord v (T (Nstar β) s))) +
        Real.sqrt (I.kappaAt κ (m - 1) (M - (m - 1))) *
        Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (T (Nstar β)
            t)))) ≤
      (2 * Real.sqrt (l2NormSq θ₀)) * (4 : ℝ) ^ Nstar β * ((2 * Nstar β).factorial : ℝ) *
          (v.length.factorial : ℝ) *
        ((4 * C₀ ^ 3) * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) ^ v.length) := by
  obtain ⟨C₀, hC1, hu⟩ := iterate_T_upgrade_of_initial_trace β Ccut
  refine ⟨C₀, hC1, ?_⟩
  intro I hz hxi hh Φ hΦ κ M m θ₀ θprev T hT hθ hm hmM hPerm
    Rθ hRθ hradius hsmall hAnalytic
  let N := 2 * Real.sqrt (l2NormSq θ₀)
  have hN : 0 ≤ N := by positivity
  have he : 0 ≤ l2NormSq θ₀ := integral_nonneg (fun _ => sq_nonneg _)
  have hInitial : l2NormSq θ₀ ≤ N ^ 2 := by
    dsimp [N]
    rw [mul_pow, Real.sq_sqrt he]
    nlinarith only [he]
  have hzero := theta_homogeneous_gradient_energy_le_of_initial_l2_sq
    (theta_prev_stream_admissible I Φ hΦ hm) hθ hInitial
  apply hu I hz hxi hh hΦ κ M hT hθ hm hmM hPerm Rθ N hN hRθ hradius hsmall hzero
  intro w _
  have hb := theta_initial_word_l2_le_of_analytic hAnalytic hθ w
  have hn : Real.sqrt (l2NormSq θ₀) ≤ N := by
    dsimp [N]
    linarith only [Real.sqrt_nonneg (l2NormSq θ₀)]
  exact hb.trans (mul_le_mul_of_nonneg_right hn (by positivity))

end AVenhance.Infra.Section4
