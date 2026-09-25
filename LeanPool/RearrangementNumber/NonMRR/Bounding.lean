/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
module

/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

public import LeanPool.RearrangementNumber.NonMRR.Relations
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Tactic

/-!
# The bounding relation

The relation `boundingRelation` has `f` related to `g` when `f n < g n`
infinitely often. Its norm is the bounding number in the manuscript.
-/

@[expose] public section

open Filter Cardinal Set

namespace NonMRR

/-- Eventual domination of natural-valued sequences. -/
def EventuallyLE (f g : ℕ → ℕ) : Prop := ∀ᶠ n in atTop, f n ≤ g n

/-- The strict comparison holding at arbitrarily large coordinates. -/
def FrequentlyLT (f g : ℕ → ℕ) : Prop := ∃ᶠ n in atTop, f n < g n

theorem frequentlyLT_iff_not_eventuallyLE (f g : ℕ → ℕ) :
    FrequentlyLT f g ↔ ¬ EventuallyLE g f := by
  simp only [FrequentlyLT, EventuallyLE, Filter.Frequently, not_lt]

/-- The usual relation whose norm is the bounding number. -/
def boundingRelation : Relation where
  Challenge := ℕ → ℕ
  Response := ℕ → ℕ
  relates := FrequentlyLT
  total f := ⟨fun n ↦ f n + 1, Filter.Eventually.frequently (by
    filter_upwards [] with n
    exact Nat.lt_succ_self _)⟩

/-- The least cardinality of an eventually unbounded family. -/
noncomputable def boundingNumber : Cardinal := boundingRelation.norm

theorem dominating_boundingRelation_iff (s : Set (ℕ → ℕ)) :
    boundingRelation.Dominating s ↔ ¬ ∃ f, ∀ g ∈ s, EventuallyLE g f := by
  simp only [Relation.Dominating, boundingRelation, frequentlyLT_iff_not_eventuallyLE]
  push Not
  rfl

/-- Every countable family of functions is eventually bounded. -/
theorem exists_eventually_bounds_of_countable {s : Set (ℕ → ℕ)} (hs : s.Countable) :
    ∃ f, ∀ g ∈ s, EventuallyLE g f := by
  classical
  obtain ⟨e, he⟩ := Set.countable_iff_exists_subset_range.mp hs
  refine ⟨fun n ↦ (Finset.range (n + 1)).sup (fun i ↦ e i n), ?_⟩
  intro g hg
  obtain ⟨i, rfl⟩ := he hg
  filter_upwards [eventually_ge_atTop i] with n hn
  exact Finset.le_sup (f := fun i ↦ e i n) (Finset.mem_range.mpr (by omega))

/-- The bounding number is uncountable. -/
theorem aleph0_lt_boundingNumber : ℵ₀ < boundingNumber := by
  obtain ⟨s, hs, hcard⟩ := boundingRelation.exists_dominating_of_norm
  by_contra h
  have hc : #s ≤ ℵ₀ := by
    rw [hcard]
    exact le_of_not_gt h
  exact (dominating_boundingRelation_iff s).mp hs
    (exists_eventually_bounds_of_countable (Cardinal.mk_le_aleph0_iff.mp hc))

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
