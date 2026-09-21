/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module
public import LeanPool.ConwayRefinement.ConwayRefinement.Data.Multiset.SelectionComplexity
import Mathlib.Tactic.Tauto

/-!
# Distinct-factor complexity checks

The fixture separates the intended first component from the tempting wrong version that
counts every occurrence: the number of factors grows from three to four, but distinct
relevant weights remain unchanged and the selected multiplicity falls. A second check removes
the selected member entirely. Both use only the compiled public selection API.
-/

public noncomputable section
namespace Tests.Selection
open Multiset

/-- Lower priority selects 1 over the heavier member 2. -/
def weights : SelectionWeights.{0, 0} ℕ where
  priority n := if n = 2 then 1 else 0
  weight n := n + 1

private theorem selected_pair :
    weights.selected ((1 ::ₘ {2}) : Multiset ℕ) (by simp) = 1 := by
  symm
  apply weights.eq_selected_of_isSelected
  constructor
  · simp
  · intro y hy
    simp only [mem_cons, mem_singleton] at hy
    rcases hy with rfl | rfl <;> simp [weights]
  · intro y hy hp
    simp only [mem_cons, mem_singleton] at hy
    rcases hy with rfl | rfl <;> simp_all [weights]
  · intro y hy hp _
    simp only [mem_cons, mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact irrefl_of (WellOrderingRel : ℕ → ℕ → Prop) 1
    · simp [weights] at hp

private theorem selected_triple :
    weights.selected ((1 ::ₘ 1 ::ₘ {2}) : Multiset ℕ) (by simp) = 1 := by
  rw [weights.selected_cons_of_mem (by simp) (by simp : 1 ∈ ((1 ::ₘ {2}) : Multiset ℕ))]
  exact selected_pair

/-- Duplicating the heavier, higher-priority member does not change distinct relevant weights.
The selected multiplicity decreases while the total number of factors increases. -/
theorem multiplicity_drop :
    weights.reduced ((1 ::ₘ 1 ::ₘ {2}) : Multiset ℕ) (by simp) {0} = (0 ::ₘ 1 ::ₘ 2 ::ₘ {2}) ∧
      weights.relevantValues ((1 ::ₘ 1 ::ₘ {2}) : Multiset ℕ) (by simp) =
        weights.relevantValues ((0 ::ₘ 1 ::ₘ 2 ::ₘ {2}) : Multiset ℕ) (by simp) ∧
      SelectionWeights.ComplexityLT
        (weights.complexity ((0 ::ₘ 1 ::ₘ 2 ::ₘ {2}) : Multiset ℕ) (by simp))
        (weights.complexity ((1 ::ₘ 1 ::ₘ {2}) : Multiset ℕ) (by simp)) := by
  have hred : weights.reduced ((1 ::ₘ 1 ::ₘ {2}) : Multiset ℕ) (by simp) {0} =
      (0 ::ₘ 1 ::ₘ 2 ::ₘ {2}) := by
    rw [weights.reduced_eq, weights.selectedExponent_eq_count, weights.unselected_eq,
      selected_triple]
    simp [Multiset.filter_singleton, Multiset.cons_swap]
  have ht : ∀ u ∈ ({0} : Multiset ℕ), weights.weight u <
      weights.weight (weights.selected ((1 ::ₘ 1 ::ₘ {2}) : Multiset ℕ) (by simp)) := by
    rw [selected_triple]
    simp [weights]
  have hp : ∀ u ∈ ({0} : Multiset ℕ),
      weights.priority (weights.selected ((1 ::ₘ 1 ::ₘ {2}) : Multiset ℕ) (by simp)) ≤
        weights.priority u := by
    rw [selected_triple]
    simp [weights]
  refine ⟨hred, ?_, ?_⟩
  · have hsel := weights.isSelected_reduced ((1 ::ₘ 1 ::ₘ {2}) : Multiset ℕ) (by simp) {0}
      ht hp (by rw [weights.selectedExponent_eq_count, selected_triple]; simp)
    rw [hred, selected_triple] at hsel
    have hs := weights.eq_selected_of_isSelected (by simp) hsel
    apply weights.relevantValues_congr (by simp) (by simp) (selected_triple.trans hs)
    intro y hy
    rw [selected_triple] at hy
    simp only [weights] at hy
    simp only [mem_cons, mem_singleton]
    constructor
    · tauto
    · rintro (rfl | rfl | rfl | rfl)
      · simp at hy
      all_goals simp
  · simpa only [hred] using weights.complexityLT_reduced ((1 ::ₘ 1 ::ₘ {2}) : Multiset ℕ)
      (by simp) {0} ht hp (by rw [hred]; simp)

/-- Once the selected copy disappears, the first complexity component decreases. -/
theorem selection_disappears :
    SelectionWeights.ComplexityLT
      (weights.complexity ((0 ::ₘ 2 ::ₘ {2}) : Multiset ℕ) (by simp))
      (weights.complexity ((1 ::ₘ {2}) : Multiset ℕ) (by simp)) := by
  have hred : weights.reduced ((1 ::ₘ {2}) : Multiset ℕ) (by simp) {0} = (0 ::ₘ 2 ::ₘ {2}) := by
    rw [weights.reduced_eq, weights.selectedExponent_eq_count, weights.unselected_eq,
      selected_pair]
    simp [Multiset.filter_singleton, Multiset.cons_swap]
  simpa only [hred] using weights.complexityLT_reduced ((1 ::ₘ {2}) : Multiset ℕ)
    (by simp) {0} (by rw [selected_pair]; simp [weights]) (by rw [selected_pair]; simp [weights])
    (by rw [hred]; simp)

end Tests.Selection
