/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
module

public import LeanPool.LanguageGeneration.FiniteWitness.Simplified.Capture

/-!
# Bounded capture for the separation-width hierarchy

The hierarchy uses the direct diagonal construction from `Simplified.Capture`.
These compatibility theorems keep the width API without maintaining a second
finite-state construction and a separate induction on the cardinality bound.
-/

public section

namespace GenLimit.FiniteWitness

variable {α : Type*}

/-- A uniformly bounded finite-set sequence is captured infinitely often by
one set containing none of the prescribed infinite cores. The universe is
arbitrary; no countability or measurability of its points is assumed. -/
theorem bounded_capture (d : ℕ) (U : ℕ → Finset α)
    (hU : ∀ n, (U n).card ≤ d) (C : ℕ → Set α) :
    ∃ D : Set α, {n | (↑(U n) : Set α) ⊆ D}.Infinite ∧
      ∀ m, (C m).Infinite → ¬ C m ⊆ D :=
  Simplified.bounded_capture d U hU C

theorem bounded_capture_indexed {ι : Type*} [Countable ι]
    (d : ℕ) (U : ℕ → Finset α) (hU : ∀ n, (U n).card ≤ d) (C : ι → Set α) :
    ∃ D : Set α, {n | (↑(U n) : Set α) ⊆ D}.Infinite ∧
      ∀ i, (C i).Infinite → ¬ C i ⊆ D :=
  Simplified.bounded_capture_indexed d U hU C

end GenLimit.FiniteWitness
