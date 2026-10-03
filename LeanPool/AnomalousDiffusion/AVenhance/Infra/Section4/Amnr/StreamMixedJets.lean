/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TransportProfileJets

/-! Exact mixed jets of the actual transported stream summands. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- The actual stream summand is jointly smooth, with no quantitative premise. -/
theorem amnr_nextStreamTerm_contDiff_infty {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ) (m : ℕ) (k : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.nextStreamTerm m (Φ (m - 1)) (hΦ.adm_pred m) z.1 z.2 k) := by
  have hh : ContDiff ℝ (⊤ : ℕ∞) (I.hatZetaML m (AVenhance.lIdx β I.Λ m k)) := by
    unfold AVenhance.Ingredients.hatZetaML AVenhance.shiftCutoff
    exact (I.hatZeta_smooth m).comp (by fun_prop)
  have hz : ContDiff ℝ (⊤ : ℕ∞) (I.zetaMK m k) := by
    unfold AVenhance.Ingredients.zetaMK AVenhance.scaledCutoff
    exact I.zeta_smooth.comp (by fun_prop)
  exact ((hh.mul hz).comp contDiff_fst).mul
    (amnr_transportProfile_contDiff_infty I hΦ m k (AVenhance.lIdx β I.Λ m k))

/-- Every actual differential word is smooth; regularity is proved before
identifying its material cancellations. -/
theorem amnr_nextStreamTerm_word_contDiff_infty {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ) (m : ℕ) (k : ℤ)
    (w : List (Option (Fin 2))) :
    ContDiff ℝ (⊤ : ℕ∞) (amnrWord (fun z => AVenhance.streamVel (Φ (m - 1)) z.1 z.2) w
      (fun z => I.nextStreamTerm m (Φ (m - 1)) (hΦ.adm_pred m) z.1 z.2 k)) := by
  exact contDiffOn_univ.mp (amnrWord_contDiffOn_infty isOpen_univ
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)).smooth.contDiffOn
    (amnr_nextStreamTerm_contDiff_infty I hΦ m k).contDiffOn w)

/-- Material derivatives hit only the actual time cutoff, at every spatial order. -/
theorem amnr_nextStreamTerm_mixed_word {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (k : ℤ) (α : List (Fin 2)) (ℓ : ℕ) (z : AmnrSpace) :
    amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
      (α.map some ++ List.replicate ℓ none)
      (fun y => I.nextStreamTerm m (Φ (m - 1)) (hΦ.adm_pred m) y.1 y.2 k) z =
      iteratedDeriv ℓ (I.hatZetaML m (AVenhance.lIdx β I.Λ m k) * I.zetaMK m k) z.1 *
        amnrSpaceWord α (fun y => AVenhance.psi β I.Λ m k
          (I.xFlowInv hΦ m (AVenhance.lIdx β I.Λ m k) z.1 y)) z.2 := by
  rw [amnrWord_append, amnrWord_spatial_slice
    (amnr_nextStreamTerm_word_contDiff_infty I hΦ m k (List.replicate ℓ none))]
  rw [amnr_nextStreamTerm_material_word]
  change amnrSpaceWord α ((iteratedDeriv ℓ (I.hatZetaML m (AVenhance.lIdx β I.Λ m k) * I.zetaMK m
      k) z.1 : ℝ) • _) z.2 = _
  rw [amnrSpaceWord_const_smul]
  rfl

/-- Ordered spatial profile derivatives inherit the actual operator-norm bound. -/
theorem amnr_transportProfile_spatialWord_abs_le_of_A3 {β C : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) (hreg : AVenhance.StreamRegularityBounds C I Φ)
    {m : ℕ} (hm : 1 ≤ m) (k : ℤ) (α : List (Fin 2))
    (hbudget : α.length ≤ AVenhance.Nstar β) (z : AmnrSpace)
    (ht : |z.1 - (AVenhance.lIdx β I.Λ m k : ℝ) * AVenhance.tauPP β I.Λ m| ≤
      AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m) :
    |amnrSpaceWord α (fun y => AVenhance.psi β I.Λ m k
      (I.xFlowInv hΦ m (AVenhance.lIdx β I.Λ m k) z.1 y)) z.2| ≤
      amnrTransportSpatialConstant (AVenhance.Nstar β) * AVenhance.a β I.Λ m *
        AVenhance.epsilon β I.Λ m ^ 2 * (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length := by
  have hY : ContDiff ℝ (⊤ : ℕ∞)
      (I.xFlowInv hΦ m (AVenhance.lIdx β I.Λ m k) z.1) :=
    (amnr_xFlowInv_joint_contDiff_infty I hΦ m (AVenhance.lIdx β I.Λ m k)).comp
      (contDiff_const.prodMk contDiff_id)
  have hs := (amnr_psi_contDiff I m k).comp hY
  change ContDiff ℝ (⊤ : ℕ∞) (fun y => AVenhance.psi β I.Λ m k
    (I.xFlowInv hΦ m (AVenhance.lIdx β I.Λ m k) z.1 y)) at hs
  rw [amnrSpaceWord_eq_iteratedFDeriv hs α]
  have hp : ∏ j : Fin α.length, ‖amnrSpatialDirections α j‖ = 1 := by
    rw [amnrSpatialDirections_eq]
    have hb (p : Fin 2) : ‖basisVec p‖ = 1 := by fin_cases p <;> simp [basisVec, Pi.norm_single]
    simp only [hb, Finset.prod_const_one]
  have hd := (iteratedFDeriv ℝ α.length (fun y => AVenhance.psi β I.Λ m k
    (I.xFlowInv hΦ m (AVenhance.lIdx β I.Λ m k) z.1 y)) z.2).le_opNorm (amnrSpatialDirections α)
  rw [hp, mul_one, Real.norm_eq_abs] at hd
  exact hd.trans (amnr_transportProfile_iteratedFDeriv_norm_le_of_A3 I hΦ hreg hm k
    (AVenhance.lIdx β I.Λ m k) z.1 z.2 ht α.length hbudget)

/-- All actual mixed summand jets have the fine spatial and cutoff-time
rates. The paper's weighted budget is checked before either primitive bound. -/
theorem amnr_nextStreamTerm_mixed_abs_le_of_A3 {β C : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) {m : ℕ} (hm : 1 ≤ m)
    (k : ℤ) (α : List (Fin 2)) (ℓ : ℕ)
    (hbudget : α.length + 2 * ℓ ≤ AVenhance.Nstar β) (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
      (α.map some ++ List.replicate ℓ none)
      (fun y => I.nextStreamTerm m (Φ (m - 1)) (hΦ.adm_pred m) y.1 y.2 k) z| ≤
      ((2 : ℝ) ^ ℓ * I.Chat * I.Czeta) *
        (amnrTransportSpatialConstant (AVenhance.Nstar β) * AVenhance.a β I.Λ m *
          AVenhance.epsilon β I.Λ m ^ 2 * (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length) *
        (AVenhance.tau β I.Λ m)⁻¹ ^ ℓ := by
  by_cases ht : |z.1 - (AVenhance.lIdx β I.Λ m k : ℝ) * AVenhance.tauPP β I.Λ m| ≤
      AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m
  · rw [amnr_nextStreamTerm_mixed_word I hΦ m k α ℓ z, abs_mul]
    have hb := amnr_transportProfile_spatialWord_abs_le_of_A3 I hΦ hreg hm k α (by omega) z ht
    have hc := amnr_stream_timeAmplitude_derivative_abs_le I hm k ℓ (by omega) z.1
    have hnonneg := (abs_nonneg _).trans hc
    have hh := mul_le_mul hc hb (abs_nonneg _) hnonneg
    convert hh using 1
    ring
  · rw [amnr_nextStreamTerm_word_zero_off_large I (hΦ.adm_pred m) hm k _ _ z
      (lt_of_not_ge ht), abs_zero]
    have hK := amnrTransportSpatialConstant_pos (AVenhance.Nstar β)
    have hA := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
    have hE := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m :=
        m)
    have hτ := I.tau_pos' m
    have hChat : 0 < I.Chat := lt_of_lt_of_le zero_lt_one I.one_le_Chat
    have hCzeta : 0 < I.Czeta := lt_of_lt_of_le zero_lt_one I.one_le_Czeta
    positivity

end AVenhance.Infra.Section4
