/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadTailUnion

/-! # Bad Scale Entry Split -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

/-!
# Splitting absolute bad scales at the annealed entry scale

The quantitative bad-scale estimate is proved after shifting the annealed
entry scale to zero.  The final quenched theorem also has to cover the finite
bottom band below that entry scale.  This file records the deterministic
decomposition separating those two contributions.
-/

noncomputable section

variable {Ω : Type*}

/-- Bad event contributed by pairs whose bottom scale is below the entry
scale. -/
def smallBottomBadScaleEvent
    (H : ℕ → ℕ → Ω → ℝ) (Nentry : ℕ) (t α : ℝ) (N : ℕ) :
    Set Ω :=
  {ω | ∃ m n : ℕ, n < Nentry ∧ n < m ∧ N ≤ m ∧
    (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) * H m n ω >
      (3 : ℝ) ^ (-α * ((m - N : ℕ) : ℝ))}

/-- The absolute bad event splits into the small-bottom band and the shifted
bad event above the entry scale. -/
theorem badScaleEvent_subset_smallBottom_union_shifted
    {H : ℕ → ℕ → Ω → ℝ} {Nentry N : ℕ} {t α : ℝ}
    (hNentryN : Nentry ≤ N) :
    badScaleEvent H t α N ⊆
      smallBottomBadScaleEvent H Nentry t α N ∪
        badScaleEvent
          (fun M K ω => H (Nentry + M) (Nentry + K) ω)
          t α (N - Nentry) := by
  intro ω hω
  rcases hω with ⟨m, n, hnm, hNm, hbad⟩
  by_cases hn_entry : n < Nentry
  · exact Or.inl ⟨m, n, hn_entry, hnm, hNm, hbad⟩
  · have hNentryn : Nentry ≤ n := le_of_not_gt hn_entry
    let M : ℕ := m - Nentry
    let K : ℕ := n - Nentry
    have hNentrym : Nentry ≤ m := le_trans hNentryn (le_of_lt hnm)
    have hK_lt_M : K < M := by
      dsimp [M, K]
      omega
    have hqM : N - Nentry ≤ M := by
      dsimp [M]
      omega
    have hMN : (M - K : ℕ) = m - n := by
      dsimp [M, K]
      omega
    have hMq : (M - (N - Nentry) : ℕ) = m - N := by
      dsimp [M]
      omega
    have hbad_shift :
        (3 : ℝ) ^ (-t * ((M - K : ℕ) : ℝ)) *
            H (Nentry + M) (Nentry + K) ω >
          (3 : ℝ) ^ (-α * ((M - (N - Nentry) : ℕ) : ℝ)) := by
      have hM_eq : Nentry + M = m := by
        dsimp [M]
        exact Nat.add_sub_of_le hNentrym
      have hK_eq : Nentry + K = n := by
        dsimp [K]
        exact Nat.add_sub_of_le hNentryn
      simpa [hMN, hMq, hM_eq, hK_eq] using hbad
    exact Or.inr ⟨M, K, hK_lt_M, hqM, hbad_shift⟩

/-- Tail-event form of `badScaleEvent_subset_smallBottom_union_shifted`. -/
theorem badTailEvent_subset_smallBottom_union_shifted
    {H : ℕ → ℕ → Ω → ℝ} {Nentry N : ℕ} {t α : ℝ}
    (hNentryN : Nentry ≤ N) :
    badTailEvent (badScaleEvent H t α) N ⊆
      badTailEvent (smallBottomBadScaleEvent H Nentry t α) N ∪
        badTailEvent
          (badScaleEvent
            (fun M K ω => H (Nentry + M) (Nentry + K) ω) t α)
          (N - Nentry) := by
  intro ω hω
  rcases hω with ⟨K, hNK, hbadK⟩
  have hNentryK : Nentry ≤ K := hNentryN.trans hNK
  have hsplit :=
    badScaleEvent_subset_smallBottom_union_shifted
      (H := H) (Nentry := Nentry) (N := K) (t := t) (α := α)
      hNentryK hbadK
  rcases hsplit with hsmall | hshift
  · exact Or.inl ⟨K, hNK, hsmall⟩
  · exact Or.inr ⟨K - Nentry, by omega, hshift⟩

end

end Section57
end Ch05
end Book
end Homogenization
