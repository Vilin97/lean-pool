/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationConstants
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationGapCapacity

/-! # Combining the three event capacities -/

@[expose] public section

namespace EGZ.FlagDecomposition.Iteration


variable {p d : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}
    {s : ℕ → State p d f} {ε : ℝ} {δ : ℕ → ℝ} {g : ℕ → ℕ} {N : ℕ}
    (P : ∀ i, i < N → Progress (s i) (s (i + 1)) ε (δ i) g)

open Classical in
/-- Colors outside the finite run are arbitrary and never used. -/
noncomputable def progressColor (i : ℕ) : ℕ :=
  if hi : i < N then (P i hi).event.color else 2 * (d + 1) ^ 2

open Classical in
theorem progressColor_eq (i : ℕ) (hi : i < N) :
    progressColor P i = (P i hi).event.color := dite_eq_left hi

open Classical in
theorem progressColor_lt (i : ℕ) (hi : i < N) :
    progressColor P i < 2 * (d + 1) ^ 2 + 1 := by
  rw [progressColor_eq P i hi]
  exact (P i hi).event.color_lt

open Classical in
/-- Complete and face event bounds, together with the checked gap bound,
give precisely the interval-capacity hypothesis of the finite-color lemma. -/
theorem hasIntervalCapacity_of_event_bounds
    (hδ : Antitone δ) (hδnonneg : ∀ i, 0 ≤ δ i)
    (hcomplete : ∀ a b L, a ≤ b → b < N → L < (d + 1) ^ 2 →
      (∀ i ∈ Finset.Icc a b, 2 * L ≤ progressColor P i) →
      ((Finset.Icc a b).filter fun i ↦ progressColor P i = 2 * L).card ≤ 2 ^ a)
    (hface : ∀ a b L, a ≤ b → b < N → L < (d + 1) ^ 2 →
      (∀ i ∈ Finset.Icc a b, 2 * L + 1 ≤ progressColor P i) →
      ((Finset.Icc a b).filter fun i ↦ progressColor P i = 2 * L + 1).card ≤
        intervalCapacity d ε a) :
    HasIntervalCapacity (progressColor P) (intervalCapacity d ε) N := by
  intro a b l hab hb hlow
  by_cases hn : ((Finset.Icc a b).filter fun i ↦ progressColor P i = l).Nonempty
  · obtain ⟨i, hi⟩ := hn
    obtain ⟨hiab, hil⟩ := Finset.mem_filter.mp hi
    have hiN : i < N := (Finset.mem_Icc.mp hiab).2.trans_lt hb
    have hl : l < 2 * (d + 1) ^ 2 + 1 := hil ▸ progressColor_lt P i hiN
    by_cases hlgap : l = 2 * (d + 1) ^ 2
    · have hgap : (Finset.Icc a b).card ≤ 1 :=
        card_gap_interval_le_one P hδ hδnonneg hab hb (by
          intro j hj
          rw [← progressColor_eq P j ((Finset.mem_Icc.mp hj).2.trans_lt hb), ← hlgap]
          exact hlow j hj)
      exact (Finset.card_filter_le _ _).trans (hgap.trans (one_le_intervalCapacity d ε a))
    · have hL : l / 2 < (d + 1) ^ 2 := by omega
      have hparity : l = 2 * (l / 2) ∨ l = 2 * (l / 2) + 1 := by omega
      rcases hparity with heven | hodd
      · rw [heven] at hlow ⊢
        exact (hcomplete a b (l / 2) hab hb hL hlow).trans (pow_le_intervalCapacity d ε a)
      · rw [hodd] at hlow ⊢
        exact hface a b (l / 2) hab hb hL hlow
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
    exact Nat.zero_le _

open Classical in
theorem length_lt_stoppingBound_of_event_bounds
    (hδ : Antitone δ) (hδnonneg : ∀ i, 0 ≤ δ i)
    (hcomplete : ∀ a b L, a ≤ b → b < N → L < (d + 1) ^ 2 →
      (∀ i ∈ Finset.Icc a b, 2 * L ≤ progressColor P i) →
      ((Finset.Icc a b).filter fun i ↦ progressColor P i = 2 * L).card ≤ 2 ^ a)
    (hface : ∀ a b L, a ≤ b → b < N → L < (d + 1) ^ 2 →
      (∀ i ∈ Finset.Icc a b, 2 * L + 1 ≤ progressColor P i) →
      ((Finset.Icc a b).filter fun i ↦ progressColor P i = 2 * L + 1).card ≤
        intervalCapacity d ε a) :
    N < stoppingBound d ε :=
  length_lt_intervalCapacityBound _ _ N (progressColor P) (progressColor_lt P)
    (hasIntervalCapacity_of_event_bounds P hδ hδnonneg hcomplete hface)

end EGZ.FlagDecomposition.Iteration
