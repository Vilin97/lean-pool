/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.DensityHalesJewett.DensityHalesJewett.Szemeredi

/-!
# Proofs of the asymptotic forms of the density theorems

This module proves the declarations stated in `Challenge.lean`, deriving them from the explicit
threshold forms `Combinatorics.Line.exists_of_density` and
`Combinatorics.ArithmeticProgression.exists_of_density_nat` developed in this repository.

A *combinatorial line* in the cube of words of length `n` over a finite alphabet `α` is a family
of `#α` words, one for each letter `x : α`, obtained from a single pattern by filling every
occurrence of a wildcard with `x`; at least one coordinate must be a wildcard, so the line is
nonconstant. This is Mathlib's `Combinatorics.Line α (Fin n)`, and `l x` is the word of the line
indexed by the letter `x`.
-/

@[expose] public section

open Filter Finset
open Combinatorics

namespace Combinatorics.Line

/-- The **Density Hales--Jewett theorem**: for a positive density `δ`, every sufficiently long word
length `n` has the property that any set of at least a `δ` fraction of the words of length `n`
over `α` contains a combinatorial line. -/
theorem exists_of_density_atTop (α : Type*) [Fintype α] [Nontrivial α] (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ A : Finset (Fin n → α), δ * (Fintype.card α : ℝ) ^ n ≤ #A →
      ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A := by
  refine eventually_atTop.2 ⟨densityTheoremBound (Fintype.card α) δ, ?_⟩
  intro n hn A hAδ
  exact exists_of_density α δ hδ n hn A hAδ

end Combinatorics.Line

namespace Combinatorics.ArithmeticProgression

/-- **Szemeredi's theorem**: for a positive density `δ`, every sufficiently large `n` has the
property that any subset of `range n` of size at least `δ * n` contains an arithmetic progression
of length `k`, i.e. `k` terms `a, a + d, a + 2 * d, …` with `d ≠ 0`. -/
theorem exists_of_density_nat_atTop (k : ℕ) (hk : 3 ≤ k) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ A : Finset ℕ, A ⊆ range n → δ * n ≤ #A →
      ∃ a d : ℕ, d ≠ 0 ∧ ∀ i : Fin k, a + i * d ∈ A := by
  refine eventually_atTop.2 ⟨densityTheoremBound k δ, ?_⟩
  intro n hn A hAn hAδ
  obtain ⟨P, hP⟩ := exists_of_density_nat k hk δ hδ n hn A hAn hAδ
  refine ⟨P.start, P.diff, P.diff_ne_zero, ?_⟩
  intro i
  simpa [term, nsmul_eq_mul] using hP i

end Combinatorics.ArithmeticProgression
