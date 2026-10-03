/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Contracts.FlipFlop
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.NoSelection.Scales

/-! # Consequences of the flip-flop at a fixed level

For the two chains topped at `½ ε_M^p` and `2 ε_M^p` and a level `1 ≤ m ≤ M-1`, with `ε_m` small:
both diffusivities are `≍ ε_m^{β+γ}` (explicit constants `ffk0`, `ffK0`) and their ratio is within
`[3,5]` in one order or the other. -/

@[expose] public section

open Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem.NoSel

open AVenhance

/-- Bound for `|log (t √(80/9))|` over `t ∈ {1/2, 2}`. -/
def ffB : ℝ := |Real.log (1 / 2 * Real.sqrt (80 / 9))| + |Real.log (2 * Real.sqrt (80 / 9))|

/-- Lower constant: `κ ≥ ffk0 · ε^{β+γ}`. -/
def ffk0 : ℝ := Real.sqrt (9 / 80) * Real.exp (-(ffB + 1))

/-- Upper constant: `κ ≤ ffK0 · ε^{β+γ}`. -/
def ffK0 : ℝ := Real.sqrt (9 / 80) * Real.exp (ffB + 1)

theorem ffk0_pos : 0 < ffk0 := by unfold ffk0; positivity

theorem ffk0_le_ffK0 : ffk0 ≤ ffK0 := by
  unfold ffk0 ffK0
  have := Real.exp_le_exp.2 (show -(ffB + 1) ≤ ffB + 1 by
    have : 0 ≤ ffB := by unfold ffB; positivity
    linarith)
  exact mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg _)

theorem ffK0_pos : 0 < ffK0 := ffk0_pos.trans_le ffk0_le_ffK0

theorem log_t_le (t : ℝ) (ht : t = 1 / 2 ∨ t = 2) : |Real.log (t * Real.sqrt (80 / 9))| ≤ ffB := by
  unfold ffB
  rcases ht with rfl | rfl
  · exact le_add_of_nonneg_right (abs_nonneg _)
  · exact le_add_of_nonneg_left (abs_nonneg _)

theorem abs_sign_mul (k : ℕ) (x : ℝ) : |(-1 : ℝ) ^ k * x| = |x| := by
  rcases neg_one_pow_eq_or ℝ k with h | h <;> simp [h]

/-- Constants and level facts of the two chains. -/
theorem kappa_facts (β C₀ : ℝ) :
    ∃ Λ₁ ρ Cff : ℝ, 0 < ρ ∧ 0 ≤ Cff ∧
      ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → Λ₁ ≤ (I.Λ : ℝ) →
      ∀ M : ℕ, 2 ≤ M → ∀ m : ℕ, 1 ≤ m → m ≤ M - 1 →
      Cff * epsilon β I.Λ m ^ ρ ≤ Real.log (5 / 4) / 2 →
      0 < I.kappaSeq (1 / 2 * epsilon β I.Λ M ^ (2 * β / (q β + 1))) M m →
      0 < I.kappaSeq (2 * epsilon β I.Λ M ^ (2 * β / (q β + 1))) M m →
      (ffk0 * epsilon β I.Λ m ^ (β + gamma β) ≤
          I.kappaSeq (1 / 2 * epsilon β I.Λ M ^ (2 * β / (q β + 1))) M m ∧
        I.kappaSeq (1 / 2 * epsilon β I.Λ M ^ (2 * β / (q β + 1))) M m ≤
          ffK0 * epsilon β I.Λ m ^ (β + gamma β)) ∧
      (ffk0 * epsilon β I.Λ m ^ (β + gamma β) ≤
          I.kappaSeq (2 * epsilon β I.Λ M ^ (2 * β / (q β + 1))) M m ∧
        I.kappaSeq (2 * epsilon β I.Λ M ^ (2 * β / (q β + 1))) M m ≤
          ffK0 * epsilon β I.Λ m ^ (β + gamma β)) ∧
      ((3 * I.kappaSeq (1 / 2 * epsilon β I.Λ M ^ (2 * β / (q β + 1))) M m ≤
            I.kappaSeq (2 * epsilon β I.Λ M ^ (2 * β / (q β + 1))) M m ∧
          I.kappaSeq (2 * epsilon β I.Λ M ^ (2 * β / (q β + 1))) M m ≤
            5 * I.kappaSeq (1 / 2 * epsilon β I.Λ M ^ (2 * β / (q β + 1))) M m) ∨
        (3 * I.kappaSeq (2 * epsilon β I.Λ M ^ (2 * β / (q β + 1))) M m ≤
            I.kappaSeq (1 / 2 * epsilon β I.Λ M ^ (2 * β / (q β + 1))) M m ∧
          I.kappaSeq (1 / 2 * epsilon β I.Λ M ^ (2 * β / (q β + 1))) M m ≤
            5 * I.kappaSeq (2 * epsilon β I.Λ M ^ (2 * β / (q β + 1))) M m)) := by
  obtain ⟨ρ, C, Λ₁, hρ, hFF⟩ := Contracts.flipFlop_contract β C₀
  refine ⟨Λ₁, ρ, max C 0, hρ, le_max_right _ _, ?_⟩
  intro I hz hx hh hΛ M hM m hm1 hmM hsmall hk1 hk2
  have hβ1 := I.one_lt_beta
  have hβ2 := I.beta_lt
  have hΛ7 := I.two_pow_seven_le
  have hε : 0 < epsilon β I.Λ m := Infra.Cutoff.epsilon_pos hβ1 hβ2 hΛ7
  have hlog5 : 0 < Real.log (5 / 4) := Real.log_pos (by norm_num)
  have hlog5' : Real.log (5 / 4) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)
    linarith
  set D := Real.sqrt (9 / 80) * epsilon β I.Λ m ^ (β + gamma β) with hD
  have hD0 : 0 < D := by
    have := Real.rpow_pos_of_pos hε (β + gamma β)
    positivity
  have hCε : max C 0 * epsilon β I.Λ m ^ ρ ≥ C * epsilon β I.Λ m ^ ρ :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hε.le _)
  have hbound : ∀ t : ℝ, (t = 1 / 2 ∨ t = 2) →
      |Real.log (I.kappaSeq (t * epsilon β I.Λ M ^ (2 * β / (q β + 1))) M m / D) -
        (-1 : ℝ) ^ (M - 1 - m) * Real.log (t * Real.sqrt (80 / 9))| ≤
        max C 0 * epsilon β I.Λ m ^ ρ := fun t ht =>
    (hFF I hz hx hh hΛ t ht M hM m hm1 hmM).trans hCε
  have hmain : ∀ t : ℝ, (t = 1 / 2 ∨ t = 2) →
      0 < I.kappaSeq (t * epsilon β I.Λ M ^ (2 * β / (q β + 1))) M m →
      ffk0 * epsilon β I.Λ m ^ (β + gamma β) ≤
          I.kappaSeq (t * epsilon β I.Λ M ^ (2 * β / (q β + 1))) M m ∧
        I.kappaSeq (t * epsilon β I.Λ M ^ (2 * β / (q β + 1))) M m ≤
          ffK0 * epsilon β I.Λ m ^ (β + gamma β) := by
    intro t ht hk
    set κ := I.kappaSeq (t * epsilon β I.Λ M ^ (2 * β / (q β + 1))) M m with hκ
    have hs0 : 0 < κ / D := div_pos hk hD0
    have hb := hbound t ht
    have hlog : |Real.log (κ / D)| ≤ ffB + 1 := by
      have h1 := abs_sub_abs_le_abs_sub (Real.log (κ / D))
        ((-1 : ℝ) ^ (M - 1 - m) * Real.log (t * Real.sqrt (80 / 9)))
      rw [abs_sign_mul] at h1
      have := log_t_le t ht
      linarith [hsmall]
    obtain ⟨hl1, hl2⟩ := abs_le.1 hlog
    have e1 : Real.exp (-(ffB + 1)) ≤ κ / D := by
      rw [← Real.exp_log hs0]; exact Real.exp_le_exp.2 hl1
    have e2 : κ / D ≤ Real.exp (ffB + 1) := by
      rw [← Real.exp_log hs0]; exact Real.exp_le_exp.2 hl2
    rw [le_div_iff₀ hD0] at e1
    rw [div_le_iff₀ hD0] at e2
    constructor
    · calc ffk0 * epsilon β I.Λ m ^ (β + gamma β) =
          Real.exp (-(ffB + 1)) * D := by unfold ffk0; rw [hD]; ring
        _ ≤ κ := e1
    · calc κ ≤ Real.exp (ffB + 1) * D := e2
        _ = ffK0 * epsilon β I.Λ m ^ (β + gamma β) := by unfold ffK0; rw [hD]; ring
  have hh1 := hmain (1 / 2) (Or.inl rfl) hk1
  have hh2 := hmain 2 (Or.inr rfl) hk2
  refine ⟨hh1, hh2, ?_⟩
  -- ratio
  set κ1 := I.kappaSeq (1 / 2 * epsilon β I.Λ M ^ (2 * β / (q β + 1))) M m with hκ1
  set κ2 := I.kappaSeq (2 * epsilon β I.Λ M ^ (2 * β / (q β + 1))) M m with hκ2
  have b1 := hbound (1 / 2) (Or.inl rfl)
  have b2 := hbound 2 (Or.inr rfl)
  obtain ⟨b1l, b1u⟩ := abs_le.1 b1
  obtain ⟨b2l, b2u⟩ := abs_le.1 b2
  have hr : 0 < Real.sqrt (80 / 9) := Real.sqrt_pos.2 (by norm_num)
  have hlogdiff : Real.log (2 * Real.sqrt (80 / 9)) - Real.log (1 / 2 * Real.sqrt (80 / 9)) =
      Real.log 4 := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
    norm_num
  have hrat : Real.log (κ2 / κ1) = Real.log (κ2 / D) - Real.log (κ1 / D) := by
    rw [← Real.log_div (div_pos hk2 hD0).ne' (div_pos hk1 hD0).ne']
    congr 1
    field_simp
  have hhalf := hsmall
  have hCC : max C 0 * epsilon β I.Λ m ^ ρ ≤ Real.log (5 / 4) / 2 := hsmall
  rcases neg_one_pow_eq_or ℝ (M - 1 - m) with hs | hs
  · left
    refine ratio_of_log hk1 hk2 ?_
    rw [hs] at b1l b1u b2l b2u
    rw [abs_le]
    constructor <;> linarith
  · right
    refine ratio_of_log' hk1 hk2 ?_
    rw [hs] at b1l b1u b2l b2u
    rw [abs_le]
    constructor <;> linarith

end AVenhance.Infra.FullTheorem.NoSel
