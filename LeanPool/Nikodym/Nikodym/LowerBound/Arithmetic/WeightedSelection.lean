/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import Mathlib

/-!
# Weighted component selection

Blueprint node C07: from `∑ L i > 0`, `Δ i > 0`, and `∑ Δ i ≤ D`, there is an index with
`L i > 0` and `(∑ L) * Δ i ≤ L i * D`.
-/

namespace Nikodym.LowerBound

open Finset

/-- Blueprint C07: a component whose degree is no larger, relatively, than its line count. -/
theorem exists_weighted_index {ι : Type*} (s : Finset ι) (L Δ : ι → ℕ) (D : ℕ)
    (hL : 0 < ∑ i ∈ s, L i) (hΔ : ∀ i ∈ s, 0 < Δ i) (hD : ∑ i ∈ s, Δ i ≤ D) :
    ∃ i ∈ s, 0 < L i ∧ (∑ j ∈ s, L j) * Δ i ≤ L i * D := by
  have hs : s.Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro h
    simp [h] at hL
  by_contra h
  have hlt : ∀ i ∈ s, L i * D < (∑ j ∈ s, L j) * Δ i := by
    intro i hi
    cases Nat.eq_zero_or_pos (L i) with
    | inl h0 =>
      rw [h0, zero_mul]
      exact Nat.mul_pos hL (hΔ i hi)
    | inr hpos =>
      refine Nat.not_le.mp fun hle ↦ h ⟨i, hi, hpos, hle⟩
  have hsum : (∑ i ∈ s, L i) * D < (∑ i ∈ s, L i) * ∑ i ∈ s, Δ i := by
    simpa [sum_mul, mul_sum] using sum_lt_sum_of_nonempty hs hlt
  exact (Nat.lt_of_mul_lt_mul_left hsum).not_ge hD

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
