/-
Copyright (c) 2026 Yann Pequignot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Pequignot
-/
import Mathlib.Data.Nat.Nth

/-!
# Strictly monotone enumerations of infinite sets of naturals

Two thin wrappers around `Nat.nth` packaging an infinite `X : Set ℕ` as a strictly monotone
enumeration `ℕ → ℕ`. They are the bridge between set-valued carriers and the enumeration-first
encoding used by the front machinery (`NashWilliams.Combinatorics.Front.Defs`), and they are also
what turns the `Set`-valued conclusion of `infinite_ramsey` into the sequence form
`infinite_ramsey_seq`.

## Main results

* `Set.Infinite.exists_strictMono_range`: an infinite `X ⊆ ℕ` is the *range* of a strictly
  monotone `N : ℕ → ℕ`.
* `Set.Infinite.exists_strictMono`: the weaker membership form, `∀ i, e i ∈ X`.

Upstream target: `Mathlib/Data/Nat/Nth.lean`.
-/

/-- **Enumeration bridge.** Every infinite set of naturals is the range of its (unique) strictly
monotone enumeration. This recovers, from a set-valued carrier `X`, the enumeration `N` on which
the enumeration-first machinery (`Front.shrink`, ranks, …) operates. -/
theorem Set.Infinite.exists_strictMono_range {X : Set ℕ} (hX : X.Infinite) :
    ∃ N : ℕ → ℕ, StrictMono N ∧ Set.range N = X := by
  have hp : (Set.ofPred fun n => n ∈ X).Infinite := by
    simpa only [Set.ofPred_mem_eq] using hX
  refine ⟨Nat.nth (· ∈ X), Nat.nth_strictMono hp, ?_⟩
  simpa only [Set.ofPred_mem_eq] using Nat.range_nth_of_infinite hp

/-- The membership form of `Set.Infinite.exists_strictMono_range`: an infinite set of naturals
carries a strictly monotone sequence of its elements. -/
theorem Set.Infinite.exists_strictMono {s : Set ℕ} (hs : s.Infinite) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ i, e i ∈ s := by
  obtain ⟨N, hN, hrange⟩ := hs.exists_strictMono_range
  exact ⟨N, hN, fun i => hrange ▸ Set.mem_range_self i⟩
