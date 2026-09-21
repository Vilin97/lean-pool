/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import LeanPool.RearrangementNumber.NonMRR.Relations
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Finset.Card

/-!
# Bounded slaloms as a relation

This defines the actual finite-set-valued slaloms of the manuscript.
Their relation norm is not identified with `nonM` by definition.
-/

open Filter Cardinal

namespace NonMRR

/-- A slalom with the pointwise width bound `r`. -/
def Slalom (r : ℕ → ℕ) := {φ : ℕ → Finset ℕ // ∀ n, (φ n).card ≤ r n}

/-- The slalom relation: the response catches the challenge infinitely often. -/
def slalomRelation (r : ℕ → ℕ) (hr : ∀ n, 0 < r n) : Relation where
  Challenge := ℕ → ℕ
  Response := Slalom r
  relates e φ := ∃ᶠ n in atTop, e n ∈ φ.val n
  total e := by
    refine ⟨⟨fun n ↦ {e n}, ?_⟩, ?_⟩
    · intro n
      simpa only [Finset.card_singleton] using Nat.succ_le_of_lt (hr n)
    · exact Filter.Eventually.frequently (Filter.Eventually.of_forall (by simp))

/-- A slalom family is dominating exactly when it has no common eventual avoider. -/
theorem dominating_slalomRelation_iff (r : ℕ → ℕ) (hr : ∀ n, 0 < r n)
    (s : Set (Slalom r)) :
    (slalomRelation r hr).Dominating s ↔
      ¬ ∃ e : ℕ → ℕ, ∀ φ ∈ s, ∀ᶠ n in atTop, e n ∉ φ.val n := by
  simp only [Relation.Dominating, slalomRelation, Filter.Frequently]
  push Not
  rfl

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
