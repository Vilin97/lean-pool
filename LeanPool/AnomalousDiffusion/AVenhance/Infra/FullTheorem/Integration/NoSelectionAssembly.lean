/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.NoSelectionContract
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.SeparatedChainsContract
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.NoSelectionLimit.Family

/-! # The no-selection statement, conditional on the separated chains

`noSelection_of_separated`: from `SeparatedChainsContract` and the proved limit analysis
(`family_limit`) to `NoSelectionContract`. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

theorem noSelection_of_separated (β C₀ : ℝ) (hS : SeparatedChainsContract β C₀) :
    NoSelectionContract β C₀ := by
  obtain ⟨Λ₅, hS⟩ := hS
  obtain ⟨μ, Λ₃, hμ, hF⟩ := family_limit β C₀
  refine ⟨μ / 2, max Λ₅ Λ₃, by positivity, ?_⟩
  intro I hz hx hh hΛ Φ hΦ φ htend
  have hΛ₅ : Λ₅ ≤ (I.Λ : ℝ) := (le_max_left _ _).trans hΛ
  have hΛ₃ : Λ₃ ≤ (I.Λ : ℝ) := (le_max_right _ _).trans hΛ
  obtain ⟨S, hSun, hSn⟩ := hS I hz hx hh hΛ₅ Φ hΦ φ htend
  refine ⟨S, hSun, fun n hn => (hSn n hn).1, ?_⟩
  intro n hn c hc θ hθ
  obtain ⟨t₀, ht₀, σ, hσ, J, hJ⟩ := (hSn n hn).2
  have hn1 : 1 ≤ n := (hSn n hn).1
  have hκ : ∀ t : ℝ, (t = 1 / 2 ∨ t = 2) → ∀ j : ℕ, 0 < kfam β I.Λ t j := by
    intro t ht j
    have := Infra.Cutoff.epsilon_pos (Λ := I.Λ) (m := 2 * j + 1) I.one_lt_beta I.beta_lt
      I.two_pow_seven_le
    unfold kfam
    rcases ht with rfl | rfl <;> positivity
  obtain ⟨Θ₁, h1T, h1M, h1c, h1H⟩ := hF I hz hx hh hΛ₃ Φ hΦ φ htend n hn1 c (1 / 2) (Or.inl rfl) θ
    (fun j => hθ _ (hκ _ (Or.inl rfl) j))
  obtain ⟨Θ₂, h2T, h2M, h2c, h2H⟩ := hF I hz hx hh hΛ₃ Φ hΦ φ htend n hn1 c 2 (Or.inr rfl) θ
    (fun j => hθ _ (hκ _ (Or.inr rfl) j))
  have e1 : ∀ j : ℕ, kfam β I.Λ (1 / 2) j = epsilon β I.Λ (2 * j + 1) ^ (2 * β / (q β + 1)) / 2 :=
      by
    intro j; unfold kfam; ring
  have e2 : ∀ j : ℕ, kfam β I.Λ 2 j = 2 * epsilon β I.Λ (2 * j + 1) ^ (2 * β / (q β + 1)) := by
    intro j; unfold kfam; rfl
  refine ⟨Θ₁, Θ₂, h1T, h2T, ?_, ?_, ?_⟩
  · intro η hη
    simpa only [e1] using h1H η hη
  · intro η hη
    simpa only [e2] using h2H η hη
  · -- the norms stay separated in the limit
    refine ⟨t₀, ht₀, ?_⟩
    intro heq
    have hAB : Real.sqrt (l2NormSq (Θ₁ t₀)) = Real.sqrt (l2NormSq (Θ₂ t₀)) := by rw [heq]
    have hmf : ∀ (t : ℝ) (ht : t = 1 / 2 ∨ t = 2) (j : ℕ),
        MemL2On unitCube (θ (kfam β I.Λ t j) t₀) := by
      intro t ht j
      obtain ⟨Dθ, hDθ⟩ := hθ _ (hκ t ht j)
      exact (hDθ.1 t₀ ht₀).2
    have hle : σ * |c| ≤ 0 := by
      refine le_of_forall_pos_le_add fun η hη => ?_
      obtain ⟨N₁, hN₁⟩ := h1c (η / 2) (by linarith)
      obtain ⟨N₂, hN₂⟩ := h2c (η / 2) (by linarith)
      set j := max (max N₁ N₂) J with hj
      have hsep := hJ c hc j (le_max_right _ _) (θ (kfam β I.Λ (1 / 2) j))
        (θ (kfam β I.Λ 2 j))
        (by rw [← e1 j]; exact hθ _ (hκ _ (Or.inl rfl) j))
        (by rw [← e2 j]; exact hθ _ (hκ _ (Or.inr rfl) j))
      have hm1 := hmf (1 / 2) (Or.inl rfl) j
      have hm2 := hmf 2 (Or.inr rfl) j
      have r1 := abs_sqrt_l2_sub_le hm1 (h1M t₀ ht₀)
      have r2 := abs_sqrt_l2_sub_le hm2 (h2M t₀ ht₀)
      have s1 := hN₁ j (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) le_rfl) t₀ ht₀
      have s2 := hN₂ j (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) le_rfl) t₀ ht₀
      rw [← hAB] at r2
      set a := Real.sqrt (l2NormSq (θ (kfam β I.Λ (1 / 2) j) t₀)) with ha
      set b := Real.sqrt (l2NormSq (θ (kfam β I.Λ 2 j) t₀)) with hb
      set A := Real.sqrt (l2NormSq (Θ₁ t₀)) with hA
      have key : |a - b| ≤ |a - A| + |b - A| := by
        have h := abs_sub (a - A) (b - A)
        have e : (a - A) - (b - A) = a - b := by ring
        rwa [e] at h
      linarith
    exact absurd hle (not_le.2 (by positivity))

end AVenhance.Infra.FullTheorem
