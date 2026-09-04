/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.TwoPoint

/-!
# Calibrated measures on finite chains

This file formalizes the telescoping chain-calibration step used in the
proof of Theorem 2.1.  We use the sentinel convention `K (m + 1) = 0`;
consequently every chain mass, including the last one, is uniformly the
adjacent difference

`q j = K j - K (j + 1)`.

The key fact is that the mass of a terminal segment beginning at `t` is
exactly `K t`, which gives exact chain calibration whenever the rejected
states form that terminal segment.
-/

open scoped BigOperators

namespace Feige

/-- Adjacent-difference mass associated with a decreasing sequence. -/
def chainMass (K : ℕ → ℝ) (j : ℕ) : ℝ :=
  K j - K (j + 1)

/-- A decreasing chain of `m + 1` statistic values, extended by a zero
sentinel at index `m + 1`. -/
structure CalibratedChain (m : ℕ) where
  /-- The statistic along the chain. -/
  K : ℕ → ℝ
  antitone : Antitone K
  initial : K 0 = 1
  sentinel : K (m + 1) = 0

namespace CalibratedChain

variable {m : ℕ} (C : CalibratedChain m)

/-- Total chain mass of states whose statistic does not exceed `α`. -/
noncomputable def rejectedMass (α : ℝ) : ℝ := by
  classical
  exact ∑ j ∈ (Finset.range (m + 1)).filter (fun j ↦ C.K j ≤ α),
    chainMass C.K j

theorem mass_nonneg (j : ℕ) : 0 ≤ chainMass C.K j := by
  exact sub_nonneg.mpr (C.antitone (Nat.le_succ j))

/-- A shifted telescoping sum of adjacent differences. -/
theorem sum_chainMass_shift (K : ℕ → ℝ) (t r : ℕ) :
    (∑ j ∈ Finset.range r, chainMass K (t + j)) = K t - K (t + r) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [chainMass]
      ring_nf

/-- Telescoping over a half-open interval of indices. -/
theorem sum_chainMass_Ico (K : ℕ → ℝ) {t u : ℕ} (htu : t ≤ u) :
    (∑ j ∈ Finset.Ico t u, chainMass K j) = K t - K u := by
  rw [Finset.sum_Ico_eq_sub _ htu]
  have hzero (r : ℕ) :
      (∑ j ∈ Finset.range r, chainMass K j) = K 0 - K r := by
    simpa using sum_chainMass_shift K 0 r
  rw [hzero u, hzero t]
  ring

/-- The adjacent-difference masses telescope to one. -/
theorem total_mass :
    (∑ j ∈ Finset.range (m + 1), chainMass C.K j) = 1 := by
  calc
    (∑ j ∈ Finset.range (m + 1), chainMass C.K j) =
        C.K 0 - C.K (m + 1) := by
          simpa using sum_chainMass_shift C.K 0 (m + 1)
    _ = 1 := by rw [C.initial, C.sentinel, sub_zero]

/-- The mass from position `t` through the final genuine state `m` is
exactly the statistic value at `t`. -/
theorem terminal_mass {t : ℕ} (ht : t ≤ m + 1) :
    (∑ j ∈ Finset.range (m + 1 - t), chainMass C.K (t + j)) = C.K t := by
  rw [sum_chainMass_shift]
  have hadd : t + (m + 1 - t) = m + 1 := Nat.add_sub_of_le ht
  rw [hadd, C.sentinel, sub_zero]

theorem terminal_mass_Ico {t : ℕ} (ht : t ≤ m + 1) :
    (∑ j ∈ Finset.Ico t (m + 1), chainMass C.K j) = C.K t := by
  rw [Finset.sum_Ico_eq_sub _ ht]
  rw [show (∑ j ∈ Finset.range (m + 1), chainMass C.K j) =
      C.K 0 - C.K (m + 1) by
        simpa using sum_chainMass_shift C.K 0 (m + 1)]
  rw [show (∑ j ∈ Finset.range t, chainMass C.K j) =
      C.K 0 - C.K t by
        simpa using sum_chainMass_shift C.K 0 t]
  rw [C.sentinel]
  ring

/-- Terminal-segment form of exact chain calibration: if rejection begins
at `t`, its chain probability is at most its threshold `α`. -/
theorem calibration_terminal {t : ℕ} (ht : t ≤ m + 1) {α : ℝ}
    (hreject : C.K t ≤ α) :
    (∑ j ∈ Finset.range (m + 1 - t), chainMass C.K (t + j)) ≤ α := by
  rw [C.terminal_mass ht]
  exact hreject

/-- Rejection-set formulation of exact chain calibration.  Monotonicity
makes the rejected states a terminal segment; `hterminal` names its first
index.  The case `t = m + 1` represents an empty rejection set. -/
theorem exact_chain_calibration {t : ℕ} (ht : t ≤ m + 1) {α : ℝ}
    (hα : 0 ≤ α)
    (hterminal : ∀ j, j < m + 1 → (C.K j ≤ α ↔ t ≤ j))
    (hreject : t ≤ m → C.K t ≤ α) :
    C.rejectedMass α ≤ α := by
  classical
  have hfilter :
      (Finset.range (m + 1)).filter (fun j ↦ C.K j ≤ α) =
        Finset.Ico t (m + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hj, hK⟩
      exact ⟨(hterminal j hj).mp hK, hj⟩
    · rintro ⟨htj, hj⟩
      exact ⟨hj, (hterminal j hj).mpr htj⟩
  rw [rejectedMass, hfilter]
  by_cases htm : t ≤ m
  · rw [C.terminal_mass_Ico ht]
    exact hreject htm
  · have hteq : t = m + 1 := by omega
    subst t
    simpa using hα

/-- Exact calibration along a chain, with the first rejected state chosen
automatically.  The zero sentinel guarantees that such an index exists; if
it is the sentinel itself, the genuine rejection set is empty. -/
theorem exact_chain_calibration' {α : ℝ} (hα : 0 ≤ α) :
    C.rejectedMass α ≤ α := by
  have hexists : ∃ t : ℕ, C.K t ≤ α := by
    refine ⟨m + 1, ?_⟩
    rw [C.sentinel]
    exact hα
  let t := Nat.find hexists
  have htK : C.K t ≤ α := Nat.find_spec hexists
  have ht : t ≤ m + 1 := by
    apply Nat.find_min' hexists
    rw [C.sentinel]
    exact hα
  apply C.exact_chain_calibration ht hα
  · intro j _
    constructor
    · exact fun hj ↦ Nat.find_min' hexists hj
    · intro htj
      exact (C.antitone htj).trans htK
  · intro _
    exact htK

end CalibratedChain

end Feige
