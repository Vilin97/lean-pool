/-
Copyright (c) 2026 Ricky Cipollini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ricky Cipollini
-/
import LeanPool.Erdos865.UpperBound
import LeanPool.Erdos865.Sharpness

/-!
# A sharp `5/8` bound for Erdős Problem 865

For `A ⊆ {1, …, N}` we say `A` contains a *pairwise-sum triple* if there are distinct
`a, b, c ∈ A` with `a + b, a + c, b + c ∈ A` (`Erdos865.HasTriple`). Let `f₃(N)` be the least
size forcing such a triple. This file assembles the proof that
`f₃(N) = 5N/8 + O(1)`, resolving Erdős Problem 865.

* `Erdos865.erdos865_upper_bound` — every triple-free `A ⊆ [1,N]` has `8|A| ≤ 5N + 53`,
  i.e. `|A| ≤ 5N/8 + O(1)`.
* `Erdos865.erdos865_contains_triple` — every `A ⊆ [1,N]` with `8|A| > 5N + 53` contains a
  pairwise-sum triple (the contrapositive form matching the paper's Theorem 1.1).
* `Erdos865.erdos865` — the packaged existence statement `∃ C, …`.
* `Erdos865.sharpness` — for `N = 8M` (`M ≥ 1`) there is a triple-free `A ⊆ [1,N]` with
  `8|A| = 5N + 16`, so the constant `5/8` is optimal.
-/

open Finset

namespace Erdos865

/-- **Upper bound (Erdős 865).** Every triple-free set `A ⊆ [1,N]` satisfies
`8 * |A| ≤ 5 * N + 53`, i.e. `|A| ≤ (5/8) N + O(1)`. -/
theorem erdos865_upper_bound (N : ℕ) (A : Finset ℕ) (hsub : A ⊆ Finset.Icc 1 N)
    (hA : IsTripleFree A) : 8 * A.card ≤ 5 * N + 53 := by
  have hsub' : A ⊆ Finset.Icc 1 (2 * ((N + 1) / 2)) :=
    hsub.trans (Finset.Icc_subset_Icc_right (by omega))
  have h := even_bound ((N + 1) / 2) A hsub' hA
  omega

/-- **Contains a triple (Erdős 865, Theorem 1.1 form).** Every `A ⊆ [1,N]` with
`5 * N + 53 < 8 * |A|` (i.e. `|A| ≥ (5/8) N + O(1)`) contains a pairwise-sum triple. -/
theorem erdos865_contains_triple (N : ℕ) (A : Finset ℕ) (hsub : A ⊆ Finset.Icc 1 N)
    (hcard : 5 * N + 53 < 8 * A.card) : HasTriple A := by
  by_contra h
  have := erdos865_upper_bound N A hsub h
  omega

/-- The upper bound packaged as an existence statement: there is an absolute constant `C`
such that every triple-free `A ⊆ [1,N]` has `8 * |A| ≤ 5 * N + C`. -/
theorem erdos865 : ∃ C : ℕ, ∀ (N : ℕ) (A : Finset ℕ), A ⊆ Finset.Icc 1 N →
    IsTripleFree A → 8 * A.card ≤ 5 * N + C :=
  ⟨53, erdos865_upper_bound⟩

end Erdos865
