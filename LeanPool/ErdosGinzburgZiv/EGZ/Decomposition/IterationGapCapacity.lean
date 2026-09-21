/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationBounds

/-! # A gap cleanup cannot be followed by another gap cleanup -/

namespace EGZ.FlagDecomposition.Iteration

variable {p d : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}

namespace State

theorem GapCondition.mono_delta {s : State p d f} {δ δ' : ℝ}
    (h : s.GapCondition δ) (hδ' : 0 ≤ δ') (hδ : δ' ≤ δ) : s.GapCondition δ' := by
  intro x
  apply le_trans _ (h x)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hδ' hδ 3) (by positivity)) (Nat.cast_nonneg _)

theorem Event.eq_gap_of_color_ge {s : State p d f} (E : s.Event)
    (h : 2 * (d + 1) ^ 2 ≤ E.color) : E = .gap := by
  cases E with
  | gap => rfl
  | face x Γ =>
    have hl : s.decomposition.level x < (d + 1) ^ 2 := s.decomposition.representation.level_lt x
    dsimp [color] at h
    omega
  | complete x =>
    have hl : s.decomposition.level x < (d + 1) ^ 2 := s.decomposition.representation.level_lt x
    dsimp [color] at h
    omega

end State

theorem no_consecutive_gap {s t u : State p d f} {ε δ δ' : ℝ} {g : ℕ → ℕ}
    (P : Progress s t ε δ g) (Q : Progress t u ε δ' g)
    (hδ' : 0 ≤ δ') (hδ : δ' ≤ δ) : ¬ (P.event = .gap ∧ Q.event = .gap) := by
  rintro ⟨hP, hQ⟩
  have hp := P.resolves
  have hq := Q.valid
  rw [hP] at hp
  rw [hQ] at hq
  exact hq (State.GapCondition.mono_delta hp hδ' hδ)

/-- An interval consisting only of gap colors contains a single stage. -/
theorem card_gap_interval_le_one {s : ℕ → State p d f} {ε : ℝ} {δ : ℕ → ℝ}
    {g : ℕ → ℕ} {N a b : ℕ}
    (P : ∀ i, i < N → Progress (s i) (s (i + 1)) ε (δ i) g)
    (hδ : Antitone δ) (hδnonneg : ∀ i, 0 ≤ δ i)
    (hab : a ≤ b) (hb : b < N)
    (hcolor : ∀ i (hi : i ∈ Finset.Icc a b),
      2 * (d + 1) ^ 2 ≤ (P i ((Finset.mem_Icc.mp hi).2.trans_lt hb)).event.color) :
    (Finset.Icc a b).card ≤ 1 := by
  have hba : b = a := by
    by_contra hne
    have hs : a + 1 ≤ b := by omega
    have haN : a < N := hab.trans_lt hb
    have hsN : a + 1 < N := hs.trans_lt hb
    have ha := (P a haN).event.eq_gap_of_color_ge
      (hcolor a (Finset.mem_Icc.mpr ⟨le_rfl, hab⟩))
    have hb' := (P (a + 1) hsN).event.eq_gap_of_color_ge
      (hcolor (a + 1) (Finset.mem_Icc.mpr ⟨Nat.le_succ a, hs⟩))
    exact no_consecutive_gap (P a haN) (P (a + 1) hsN)
      (hδnonneg _) (hδ (Nat.le_succ a)) ⟨ha, hb'⟩
  simp [hba]

end EGZ.FlagDecomposition.Iteration
