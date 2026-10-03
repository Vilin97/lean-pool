/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TUpgradeConsumersPackaging

/-! # TUpgrade Consumers Contracts

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance

theorem iterate_T_analytic_consumer_bounds (β Ccut : ℝ) :
    ∃ C₀ A : ℝ, 1 ≤ C₀ ∧ 1 ≤ A ∧
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
    (Real.sqrt (I.kappaSeq κ M (m - 1)) * Real.sqrt (spaceTimeGradNormSq
      (fun t => spaceGrad (T (Nstar β) t))) ≤ A * Real.sqrt (l2NormSq θ₀)) ∧
    Infra.Section5.AnalyticBridge.TmRegUpgradeLinfL2 A
      (epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) θ₀ (T (Nstar β)) ∧
    (∀ i : Fin 2, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => spaceGrad (T (Nstar β) s) x i)) ≤
        A ^ 2 * Real.sqrt (l2NormSq θ₀) *
          epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2))) := by
  obtain ⟨Dn, hDn, hn⟩ := iterate_T_upgrade_of_analytic β Ccut
  obtain ⟨Ds, hDs, hscalar⟩ := iterate_T_scalar_zero_of_analytic β Ccut
  let C₀ := max Dn Ds
  let P := (4 : ℝ) ^ Nstar β * ((2 * Nstar β).factorial : ℝ)
  let F := (Nstar β : ℝ) * ((2 * Nstar β).factorial : ℝ)
  let Z := 4 * (1 + F / 4)
  let A := max 1 (max (2 * P) (max (4 * C₀ ^ 3) Z))
  have hC1 : 1 ≤ C₀ := hDn.trans (le_max_left _ _)
  have hA1 : 1 ≤ A := le_max_left _ _
  have hPA : 2 * P ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hDA : 4 * C₀ ^ 3 ≤ A :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hZA : Z ≤ A :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨C₀, A, hC1, hA1, ?_⟩
  intro I hz hxi hh Φ hΦ κ M m θ₀ θprev T hT hθ hm hmM hPerm
    Rθ hRθ hradius hsmall hAnalytic
  have he : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hns := iterate_smallness_of_budget_enlargement (by linarith only [hDn])
    (le_max_left Dn Ds) hsmall
  have hss := iterate_smallness_of_budget_enlargement (by linarith only [hDs])
    (le_max_right Dn Ds) hsmall
  have hN := hn I hz hxi hh hΦ κ M hT hθ hm hmM hPerm Rθ hRθ hradius hns hAnalytic
  have hS := hscalar I hz hxi hh hΦ κ M hT hθ hm hmM hPerm Rθ hRθ hradius hss hAnalytic
  have hη := (iterate_T_source_scale he hRθ hDs hradius hss).2.2
  have hZ : 4 * (1 + Ds ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β) * F) ≤ Z := by
    have hF : 0 ≤ F := by positivity
    have hb := mul_le_mul_of_nonneg_right hη hF
    dsimp [Z]
    linarith only [hb]
  have hscalarA : ∀ s, 0 ≤ s → s ≤ 1 →
      Real.sqrt (l2NormSq (T (Nstar β) s)) + Real.sqrt (I.kappaSeq κ M (m - 1)) *
        Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (T (Nstar β) t))) ≤
      A * Real.sqrt (l2NormSq θ₀) := by
    intro s hs hs1
    have hb := hS s hs hs1
    have hm := mul_le_mul_of_nonneg_right (hZ.trans hZA) (Real.sqrt_nonneg (l2NormSq θ₀))
    apply hb.trans
    convert hm using 1
    dsimp [F]
    ring
  have hJets : Infra.Section5.RelativeError.PositiveTemperatureJets A
      (epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2))
      (Real.sqrt (l2NormSq θ₀)) (T (Nstar β)) := by
    apply iterate_positive_temperature_jets_of_word_bound (κ := I.kappaAt κ (m - 1) (M - (m - 1)))
      (fun t ht => tIterate_space_contDiff I hΦ hT hθ le_rfl ht.1)
      (Real.sqrt_nonneg _) (by dsimp [P]; positivity)
      (by positivity : 0 ≤ 4 * Dn ^ 3) (Real.rpow_pos_of_pos he _)
      hPA ((mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith only [hDn]) (le_max_left Dn Ds) 3)
        (by norm_num)).trans hDA)
    intro v w hvw hv t ht ht1
    have hb := hN.2 v w hvw hv t ht ht1
    rw [iterate_source_frequency_eq he] at hb
    convert hb using 1
    dsimp [P]
    ring
  refine ⟨?_, ?_, iterate_ansatz_Tjet_of_positive_jets he hJets⟩
  · exact (le_add_of_nonneg_left (Real.sqrt_nonneg _)).trans (hscalarA 0 le_rfl (by norm_num))
  · intro n i t ht
    by_cases hn0 : n = 0
    · subst n
      have hb := (le_add_of_nonneg_right (by positivity)).trans (hscalarA t ht.1 ht.2)
      simpa only [iteratedFDeriv_zero_apply, Nat.factorial_zero, Nat.cast_one, pow_zero,
        mul_one] using hb
    · exact hJets n i (by omega) t ht

end AVenhance.Infra.Section4
