/-
Copyright (c) 2026 Tutte formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tutte formalization contributors
-/
module

public import LeanPool.TuttePath.IndecomposableStep

-- Modified for Lean Pool: module integration, public visibility, and import paths.

/-! The rank-selection consequence of `cor:indecomposable-chain`, obtained by
literally repeating the downward step. This is the chain interface needed below. -/
public section

namespace TutteFormalization
variable {α : Type*} {M : Matroid α} [M.Finite] {S T : Set α}

theorem exists_indecomposable_of_rank (hS : Indecomposable M S) (hT : Indecomposable M T)
    (hTS : T ⊆ S) (k : ℕ) (hTk : natRank M T ≤ k) (hkS : k ≤ natRank M S) :
    ∃ U, Indecomposable M U ∧ T ⊆ U ∧ U ⊆ S ∧ natRank M U = k := by
  generalize hn : natRank M S - k = n
  induction n using Nat.strong_induction_on generalizing S with
  | h n ih =>
    by_cases heq : natRank M S = k
    · exact ⟨S, hS, hTS, Set.Subset.rfl, heq⟩
    have hstrict : T ⊂ S := Set.ssubset_iff_subset_ne.mpr ⟨hTS, by
      intro heqTS; have hr := congrArg (natRank M) heqTS; omega⟩
    obtain ⟨U, hU, hTU, hUS, hr⟩ := exists_indecomposable_step hS hT hstrict
    have hkU : k ≤ natRank M U := by omega
    have hdec : natRank M U - k < n := by omega
    obtain ⟨V, hV, hTV, hVU, hVk⟩ := ih (natRank M U - k) hdec hU hTU hkU rfl
    exact ⟨V, hV, hTV, hVU.trans hUS.subset, hVk⟩
end TutteFormalization
