/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.StreamMixedJets

/-! Locally finite sums of all actual mixed stream jets. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- Every actual stream differential word is a sum of at most three terms. -/
theorem amnr_streamIncrement_word_sum {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) (w : List (Option (Fin 2))) (z : AmnrSpace) :
    ∃ s : Finset ℤ, s.card ≤ 3 ∧
      amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) w
        (fun y => Φ m y.1 y.2 - Φ (m - 1) y.1 y.2) z =
        ∑ k ∈ s, amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) w
          (fun y => I.nextStreamTerm m (Φ (m - 1)) (hΦ.adm_pred m) y.1 y.2 k) z := by
  classical
  obtain ⟨s, hcard, hs⟩ := amnr_zeta_local_finite I m z.1
  let V := {y : AmnrSpace | |y.1 - z.1| < AVenhance.tau β I.Λ m / 8}
  have hV : IsOpen V := isOpen_lt (by fun_prop) continuous_const
  have hz : z ∈ V := by
    change |z.1 - z.1| < AVenhance.tau β I.Λ m / 8
    simpa only [sub_self, abs_zero] using div_pos (I.tau_pos' m) (by norm_num : (0 : ℝ) < 8)
  obtain ⟨hprev, hrec⟩ := hΦ.2 m hm
  have heq : Set.EqOn (fun y => Φ m y.1 y.2 - Φ (m - 1) y.1 y.2)
      (∑ k ∈ s, fun y => I.nextStreamTerm m (Φ (m - 1)) (hΦ.adm_pred m) y.1 y.2 k) V := by
    intro y hy
    simp only [Finset.sum_apply]
    rw [hrec]
    unfold AVenhance.Ingredients.nextStream
    rw [tsum_eq_sum (s := s) (fun k hk => by
      simp only [AVenhance.Ingredients.nextStreamTerm, hs y.1 hy k hk, mul_zero, zero_mul])]
    ring
  refine ⟨s, hcard, ?_⟩
  rw [amnrWord_congr hV (b := fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) heq w hz]
  have hb := (AVenhance.Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)).smooth
  simpa only [Finset.sum_apply, Function.uncurry_def] using (amnrWord_sum hV (hb.of_le (show
      (w.length : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).contDiffOn
    s _ (fun k _ => ((amnr_nextStreamTerm_contDiff_infty I hΦ m k).of_le
      (show (w.length : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).contDiffOn) w le_rfl hz)

/-- Full source mixed stream-increment estimate from the actual three-term
local sum. No mixed derivative estimate is assumed. -/
theorem amnr_streamIncrement_mixed_abs_le_of_A3 {β C : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) {m : ℕ} (hm : 1 ≤ m)
    (α : List (Fin 2)) (ℓ : ℕ) (hbudget : α.length + 2 * ℓ ≤ AVenhance.Nstar β)
    (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
      (α.map some ++ List.replicate ℓ none)
      (fun y => Φ m y.1 y.2 - Φ (m - 1) y.1 y.2) z| ≤
      3 * (((2 : ℝ) ^ ℓ * I.Chat * I.Czeta) *
        (amnrTransportSpatialConstant (AVenhance.Nstar β) * AVenhance.a β I.Λ m *
          AVenhance.epsilon β I.Λ m ^ 2 * (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length) *
        (AVenhance.tau β I.Λ m)⁻¹ ^ ℓ) := by
  obtain ⟨s, hcard, heq⟩ := amnr_streamIncrement_word_sum I hΦ hm
    (α.map some ++ List.replicate ℓ none) z
  rw [heq]
  let B := ((2 : ℝ) ^ ℓ * I.Chat * I.Czeta) *
    (amnrTransportSpatialConstant (AVenhance.Nstar β) * AVenhance.a β I.Λ m *
      AVenhance.epsilon β I.Λ m ^ 2 * (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length) *
    (AVenhance.tau β I.Λ m)⁻¹ ^ ℓ
  have hB : 0 ≤ B := by
    have hK := amnrTransportSpatialConstant_pos (AVenhance.Nstar β)
    have hA := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
    have hE := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m :=
        m)
    have hτ := I.tau_pos' m
    have hChat : 0 < I.Chat := lt_of_lt_of_le zero_lt_one I.one_le_Chat
    have hCzeta : 0 < I.Czeta := lt_of_lt_of_le zero_lt_one I.one_le_Czeta
    dsimp [B]
    positivity
  calc
    _ ≤ ∑ k ∈ s, |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
        (α.map some ++ List.replicate ℓ none)
        (fun y => I.nextStreamTerm m (Φ (m - 1)) (hΦ.adm_pred m) y.1 y.2 k) z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ s, B := Finset.sum_le_sum (fun k _ =>
      amnr_nextStreamTerm_mixed_abs_le_of_A3 I hΦ hreg hm k α ℓ hbudget z)
    _ = (s.card : ℝ) * B := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 3 * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB

end AVenhance.Infra.Section4
