/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.NoSelectionLimit.Limit

/-! # Classical chains, telescoping in sup-`L²`, and the tail of the `ε`-series -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

/-- The classical chain `θ_{m₀-1}, …, θ_M` exists and its diffusivities are positive. -/
theorem chain_exists {β C₀ c₁ Λ₁ : ℝ} (hW : WindowWith β C₀ c₁ Λ₁) (hc₁ : 0 < c₁)
    {I : Ingredients β} (hz : I.Czeta ≤ C₀) (hx : I.Cxi ≤ C₀) (hh : I.Chat ≤ C₀)
    (hΛ₁ : Λ₁ ≤ (I.Λ : ℝ)) {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) {κ : ℝ}
    (hκ : κ ∈ permissibleSet β I.Λ) {M : ℕ} (hM : 1 ≤ M)
    (hκM : κ ∈ permittedInterval β I.Λ M) {R : ℝ} (hR : 0 < R)
    (hMm : mTheta0 β I.Λ R ≤ M) {θ₀ : Vec 2 → ℝ}
    (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) (hper : IsZ2Periodic θ₀) :
    ∃ θs : ℕ → ℝ → Vec 2 → ℝ, ∀ j, mTheta0 β I.Λ R - 1 ≤ j → j ≤ M →
      0 < I.kappaSeq κ M j ∧
      IsClassicalSol (streamVel (Φ j)) (I.kappaSeq κ M j) (fun _ _ => 0) θ₀ (θs j) := by
  have hβ1 := I.one_lt_beta
  have hβ2 := I.beta_lt
  have hΛ7 := I.two_pow_seven_le
  have hm2 : 2 ≤ mTheta0 β I.Λ R := (mTheta0_isLeast hβ1 hβ2 hΛ7 hR).1.1
  set m₀ := mTheta0 β I.Λ R with hm₀
  have hpos : ∀ j, m₀ - 1 ≤ j → j ≤ M → 0 < I.kappaSeq κ M j := by
    intro j hj1 hj2
    by_cases hj : j = m₀ - 1
    · subst hj
      have := (hW I hz hx hh hΛ₁ κ hκ M hM hκM m₀ hm2 hMm (m₀ - 1) (Or.inl rfl)).1
      have hE := Infra.Cutoff.epsilon_pos (Λ := I.Λ) (m := m₀ - 1) hβ1 hβ2 hΛ7
      exact lt_of_lt_of_le (by positivity) this
    · have := (hW I hz hx hh hΛ₁ κ hκ M hM hκM j (by omega) hj2 j (Or.inr rfl)).1
      exact lt_of_lt_of_le (by
        have := Infra.Cutoff.epsilon_pos (Λ := I.Λ) (m := j - 1) hβ1 hβ2 hΛ7
        positivity) this
  obtain ⟨θs, hθs⟩ := exists_classical_chain hΦ hpos hθ₀ hper
  exact ⟨θs, fun j h1 h2 => ⟨hpos j h1 h2, hθs j h1 h2⟩⟩

/-- Telescoping in sup-`L²` at a fixed time. -/
theorem chain_sup {f : ℕ → ℝ → Vec 2 → ℝ} {c : ℕ → ℝ} {ℓ : ℕ} {t : ℝ} :
    ∀ M : ℕ, ℓ ≤ M →
    (∀ n, ℓ ≤ n → n ≤ M → Continuous (f n t)) →
    (∀ n, ℓ < n → n ≤ M →
      Real.sqrt (l2NormSq (fun x => f n t x - f (n - 1) t x)) ≤ c n) →
    Real.sqrt (l2NormSq (fun x => f M t x - f ℓ t x)) ≤ ∑ n ∈ Finset.Ioc ℓ M, c n := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base =>
    intro _ _
    simp [l2NormSq]
  | succ M hM ih =>
    intro hcont hstep
    have ih' := ih (fun n h1 h2 => hcont n h1 (by omega)) (fun n h1 h2 => hstep n h1 (by omega))
    have hD := hstep (M + 1) (by omega) le_rfl
    simp only [Nat.add_sub_cancel] at hD
    rw [Finset.sum_Ioc_succ_top hM]
    have e : (fun x => f (M + 1) t x - f ℓ t x) =
        fun x => (f (M + 1) t x - f M t x) + (f M t x - f ℓ t x) := by
      funext x; ring
    rw [e]
    have hc1 := hcont M hM (by omega)
    have hc2 := hcont (M + 1) (by omega) le_rfl
    have hc0 := hcont ℓ le_rfl (by omega)
    have h := Infra.Section5.Integration.sqrt_l2NormSq_add_le_of_continuous
      (f := fun x => f (M + 1) t x - f M t x) (g := fun x => f M t x - f ℓ t x)
      (hc2.sub hc1) (hc1.sub hc0)
    calc _ ≤ _ := h
      _ ≤ _ := add_le_add hD ih'
      _ = _ := by ring

/-- Tail of the series `∑_{n ∈ (ℓ, M]} ε_{n-1}^s ≤ ε_ℓ^s/(1-Λ^{-s})`. -/
theorem eps_sum_tail_le {β s : ℝ} (I : Ingredients β) (hs : 0 < s) (ℓ M : ℕ) :
    ∑ n ∈ Finset.Ioc ℓ M, epsilon β I.Λ (n - 1) ^ s ≤
      epsilon β I.Λ ℓ ^ s / (1 - (I.Λ : ℝ) ^ (-s)) := by
  have hIoc : Finset.Ioc ℓ M = Finset.Ico (ℓ + 1) (M + 1) := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
  rw [hIoc, Finset.sum_Ico_eq_sum_range]
  have h := Infra.Construction.epsilon_rpow_sum_bound I hs ℓ (M + 1 - (ℓ + 1))
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  omega

end AVenhance.Infra.FullTheorem
