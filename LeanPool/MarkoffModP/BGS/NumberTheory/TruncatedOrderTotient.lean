/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Tactic

/-!
# Exact truncated order budgets in finite cyclic groups

For a cyclic group of order `N`, the number of elements of exact order `e`
is `φ(e)` when `e ∣ N`.  Summing only the non-two-torsion orders at most a
cutoff gives the exact root budget used by the improved Markoff count.
-/

@[expose] public section

namespace BGS.NumberTheory

/-- Root count contributed by divisor orders strictly above two and at most
`bound`. -/
def truncatedOrderTotientSum (N bound : ℕ) : ℕ :=
  ∑ order ∈ N.divisors.filter
      (fun order ↦ 2 < order ∧ order ≤ bound),
    order.totient

/-- Elements whose exact order is in the non-two-torsion truncated range. -/
noncomputable def elementsOfOrderBetweenThreeAnd
    (G : Type*) [Group G] [Fintype G] (bound : ℕ) : Finset G :=
  Finset.univ.filter fun g ↦ 2 < orderOf g ∧ orderOf g ≤ bound

@[simp]
theorem mem_elementsOfOrderBetweenThreeAnd_iff
    {G : Type*} [Group G] [Fintype G] {bound : ℕ} {g : G} :
    g ∈ elementsOfOrderBetweenThreeAnd G bound ↔
      2 < orderOf g ∧ orderOf g ≤ bound := by
  classical
  simp [elementsOfOrderBetweenThreeAnd]

/-- Exact cyclic root count for the truncated non-two-torsion order range. -/
theorem elementsOfOrderBetweenThreeAnd_card_eq_truncatedOrderTotientSum
    (G : Type*) [Group G] [Fintype G] [IsCyclic G] (bound : ℕ) :
    (elementsOfOrderBetweenThreeAnd G bound).card =
      truncatedOrderTotientSum (Fintype.card G) bound := by
  classical
  let orders :=
    (Fintype.card G).divisors.filter
      (fun order ↦ 2 < order ∧ order ≤ bound)
  have hcard : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  rw [elementsOfOrderBetweenThreeAnd]
  rw [Finset.card_eq_sum_card_fiberwise
    (t := orders) (f := orderOf) (by
      intro g hg
      have hgRange := (Finset.mem_filter.mp hg).2
      apply Finset.mem_filter.mpr
      refine ⟨Nat.mem_divisors.mpr ⟨orderOf_dvd_card, hcard⟩, hgRange⟩)]
  rw [truncatedOrderTotientSum]
  change
    (∑ order ∈ orders,
      ((Finset.univ.filter fun g : G ↦
          2 < orderOf g ∧ orderOf g ≤ bound).filter
        fun g ↦ orderOf g = order).card) =
      ∑ order ∈ orders, order.totient
  apply Finset.sum_congr rfl
  intro order horder
  have horderData := (Finset.mem_filter.mp horder)
  have horderDvd : order ∣ Fintype.card G :=
    (Nat.mem_divisors.mp horderData.1).1
  have hfiber :
      ((Finset.univ.filter fun g : G ↦
          2 < orderOf g ∧ orderOf g ≤ bound).filter
        fun g ↦ orderOf g = order) =
        Finset.univ.filter (fun g : G ↦ orderOf g = order) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun hg ↦ hg.2
    · intro hg
      exact ⟨by simpa [hg] using horderData.2, hg⟩
  rw [hfiber, IsCyclic.card_orderOf_eq_totient horderDvd]

end BGS.NumberTheory
