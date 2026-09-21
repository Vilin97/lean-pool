/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.MaxAddDegree
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeAssociatedGraded
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeAssociatedGradedDomain
public import Mathlib.RingTheory.Ideal.Operations

/-!
# A max-additive degree from a separated multiplicative filtration

A decreasing, multiplicative filtration by ideals which is separated — every nonzero element
eventually leaves it — determines a max-additive degree, valued in `OrderDual ℕ` because the
filtration decreases. The generic construction can be reused for scalar extensions and quotient
filtrations.

The file also proves that a ring with a separated multiplicative filtration and domain associated
graded ring is itself a domain. The proof avoids
`MaxAddDegree.quotient_isDomain_of_associatedGraded_isDomain`, whose `[WellFoundedLT M]`
hypothesis fails for `M = ℕᵒᵈ` — precisely the value monoid of a decreasing `ℕ`-indexed
filtration. The elementary route needs no well-foundedness.
-/

open scoped MaxAddDegree

universe u

public noncomputable section

variable {R : Type u} [CommRing R]

/-- A decreasing multiplicative filtration by ideals, separated in the sense that every nonzero
element eventually leaves it. -/
structure IsSeparatedFiltration (F : ℕ → Ideal R) : Prop where
  /-- The filtration is decreasing. -/
  antitone : Antitone F
  /-- The zeroth stage is everything. -/
  top : F 0 = ⊤
  /-- The filtration is multiplicative: `F a · F b ⊆ F (a + b)`. -/
  mul_le : ∀ a b, F a * F b ≤ F (a + b)
  /-- Every nonzero element eventually leaves the filtration. -/
  exists_not_mem : ∀ {x : R}, x ≠ 0 → ∃ j, x ∉ F j

namespace IsSeparatedFiltration

variable {F : ℕ → Ideal R} (hF : IsSeparatedFiltration F)

/-- The first stage a nonzero element is absent from. -/
def firstExcluded {x : R} (hx : x ≠ 0) : ℕ := by
  classical
  exact Nat.find (hF.exists_not_mem hx)

theorem not_mem_firstExcluded {x : R} (hx : x ≠ 0) :
    x ∉ F (hF.firstExcluded hx) := by
  classical
  exact Nat.find_spec (hF.exists_not_mem hx)

theorem firstExcluded_le {x : R} (hx : x ≠ 0) {j : ℕ} (hj : x ∉ F j) :
    hF.firstExcluded hx ≤ j := by
  classical
  exact Nat.find_le hj

theorem firstExcluded_pos {x : R} (hx : x ≠ 0) : 0 < hF.firstExcluded hx := by
  rcases Nat.eq_zero_or_pos (hF.firstExcluded hx) with h | h
  · exfalso
    apply hF.not_mem_firstExcluded hx
    rw [h, hF.top]
    trivial
  · exact h

theorem mem_iff_lt_firstExcluded {x : R} (hx : x ≠ 0) (j : ℕ) :
    x ∈ F j ↔ j < hF.firstExcluded hx := by
  constructor
  · intro hmem
    by_contra hnot
    exact hF.not_mem_firstExcluded hx (hF.antitone (Nat.not_lt.mp hnot) hmem)
  · intro hj
    by_contra hnot
    exact absurd (hF.firstExcluded_le hx hnot) (Nat.not_le.mpr hj)

/-- The largest stage containing a nonzero element. -/
def index {x : R} (hx : x ≠ 0) : ℕ := hF.firstExcluded hx - 1

theorem mem_iff_le_index {x : R} (hx : x ≠ 0) (j : ℕ) :
    x ∈ F j ↔ j ≤ hF.index hx := by
  rw [hF.mem_iff_lt_firstExcluded hx]
  unfold index
  have hpos := hF.firstExcluded_pos hx
  omega

/-- The filtration index as a max-additive degree value, order-reversed. -/
def value (x : R) : WithBot (OrderDual ℕ) := by
  classical
  exact if hx : x = 0 then ⊥ else
    ((OrderDual.toDual (hF.index hx) : OrderDual ℕ) : WithBot (OrderDual ℕ))

@[simp]
theorem value_zero : hF.value 0 = ⊥ := by
  rw [value, dif_pos rfl]

theorem value_of_ne_zero {x : R} (hx : x ≠ 0) :
    hF.value x = ((OrderDual.toDual (hF.index hx) : OrderDual ℕ) :
      WithBot (OrderDual ℕ)) := by
  rw [value, dif_neg hx]

theorem value_eq_bot_iff (x : R) : hF.value x = ⊥ ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    rw [hF.value_of_ne_zero hx] at h
    exact absurd h (WithBot.coe_ne_bot)
  · rintro rfl
    exact hF.value_zero

theorem value_le_toDual_iff (x : R) (j : ℕ) :
    hF.value x ≤ ((OrderDual.toDual j : OrderDual ℕ) : WithBot (OrderDual ℕ)) ↔
      x ∈ F j := by
  by_cases hx : x = 0
  · subst hx
    simp only [hF.value_zero, bot_le, true_iff]
    exact Submodule.zero_mem _
  · rw [hF.value_of_ne_zero hx, WithBot.coe_le_coe, hF.mem_iff_le_index hx]
    exact OrderDual.toDual_le_toDual

private theorem firstExcluded_congr {x y : R} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ∀ j, x ∈ F j ↔ y ∈ F j) : hF.firstExcluded hx = hF.firstExcluded hy := by
  refine le_antisymm ?_ ?_
  · exact hF.firstExcluded_le hx fun hmem ↦
      hF.not_mem_firstExcluded hy ((h _).mp hmem)
  · exact hF.firstExcluded_le hy fun hmem ↦
      hF.not_mem_firstExcluded hx ((h _).mpr hmem)

theorem value_neg (x : R) : hF.value (-x) = hF.value x := by
  by_cases hx : x = 0
  · subst hx
    rw [neg_zero]
  · have hnx : -x ≠ 0 := neg_ne_zero.mpr hx
    rw [hF.value_of_ne_zero hnx, hF.value_of_ne_zero hx]
    have hfirst : hF.firstExcluded hnx = hF.firstExcluded hx :=
      hF.firstExcluded_congr hnx hx fun j ↦
        ⟨fun hmem ↦ by simpa using (F j).neg_mem hmem, fun hmem ↦ (F j).neg_mem hmem⟩
    rw [index, index, hfirst]

/-- The ultrametric inequality, from additivity of each stage. -/
theorem value_add_le_max (x y : R) :
    hF.value (x + y) ≤ max (hF.value x) (hF.value y) := by
  by_cases hx : x = 0
  · subst hx
    rw [zero_add, hF.value_zero]
    exact le_max_right _ _
  by_cases hy : y = 0
  · subst hy
    rw [add_zero, hF.value_zero]
    exact le_max_left _ _
  rcases le_total (hF.index hx) (hF.index hy) with hab | hab
  · have hmax : max (hF.value x) (hF.value y) =
        ((OrderDual.toDual (hF.index hx) : OrderDual ℕ) : WithBot (OrderDual ℕ)) := by
      rw [hF.value_of_ne_zero hx, hF.value_of_ne_zero hy]
      exact max_eq_left (by simpa using hab)
    rw [hmax, hF.value_le_toDual_iff]
    exact Submodule.add_mem _ ((hF.mem_iff_le_index hx _).mpr le_rfl)
      ((hF.mem_iff_le_index hy _).mpr hab)
  · have hmax : max (hF.value x) (hF.value y) =
        ((OrderDual.toDual (hF.index hy) : OrderDual ℕ) : WithBot (OrderDual ℕ)) := by
      rw [hF.value_of_ne_zero hx, hF.value_of_ne_zero hy]
      exact max_eq_right (by simpa using hab)
    rw [hmax, hF.value_le_toDual_iff]
    exact Submodule.add_mem _ ((hF.mem_iff_le_index hx _).mpr hab)
      ((hF.mem_iff_le_index hy _).mpr le_rfl)

/-- Subadditivity under multiplication, from the multiplicativity hypothesis. -/
theorem value_mul_le_add (x y : R) :
    hF.value (x * y) ≤ hF.value x + hF.value y := by
  by_cases hx : x = 0
  · subst hx
    rw [zero_mul, hF.value_zero]
    exact bot_le
  by_cases hy : y = 0
  · subst hy
    rw [mul_zero, hF.value_zero]
    exact bot_le
  have hrhs : hF.value x + hF.value y =
      ((OrderDual.toDual (hF.index hx + hF.index hy) : OrderDual ℕ) :
        WithBot (OrderDual ℕ)) := by
    rw [hF.value_of_ne_zero hx, hF.value_of_ne_zero hy, ← WithBot.coe_add]
    rfl
  rw [hrhs, hF.value_le_toDual_iff]
  exact hF.mul_le _ _ (Ideal.mul_mem_mul ((hF.mem_iff_le_index hx _).mpr le_rfl)
    ((hF.mem_iff_le_index hy _).mpr le_rfl))

theorem value_lt_toDual_iff (x : R) (j : ℕ) :
    hF.value x < ((OrderDual.toDual j : OrderDual ℕ) : WithBot (OrderDual ℕ)) ↔
      x ∈ F (j + 1) := by
  by_cases hx : x = 0
  · subst hx
    simp only [hF.value_zero, bot_lt_iff_ne_bot, ne_eq, WithBot.coe_ne_bot,
      not_false_eq_true, true_iff]
    exact Submodule.zero_mem _
  · rw [hF.value_of_ne_zero hx, WithBot.coe_lt_coe, hF.mem_iff_le_index hx]
    constructor
    · intro hlt
      exact Nat.succ_le_of_lt (OrderDual.toDual_lt_toDual.mp hlt)
    · intro hle
      exact OrderDual.toDual_lt_toDual.mpr (Nat.lt_of_succ_le hle)

/-- The max-additive degree attached to a separated multiplicative filtration. -/
def degree : MaxAddDegree R (OrderDual ℕ) where
  toFun := hF.value
  map_zero' := hF.value_zero
  map_one_le_zero' := by
    change hF.value 1 ≤ ((OrderDual.toDual 0 : OrderDual ℕ) : WithBot (OrderDual ℕ))
    rw [hF.value_le_toDual_iff, hF.top]
    trivial
  map_neg' := hF.value_neg
  map_add_le_max' := hF.value_add_le_max
  map_mul_le_add' := hF.value_mul_le_add

@[simp]
theorem degree_apply (x : R) : hF.degree x = hF.value x := (rfl)

/-- The attached degree is separated. -/
theorem degree_isSeparated : (hF.degree).IsSeparated :=
  (MaxAddDegree.isSeparated_iff hF.degree).mpr fun x ↦ hF.value_eq_bot_iff x

/-- A ring with a separated multiplicative filtration and domain associated graded ring is a
domain.

The proof does not use `MaxAddDegree.quotient_isDomain_of_associatedGraded_isDomain`, whose
`[WellFoundedLT M]` hypothesis fails for `M = ℕᵒᵈ`. Instead it obtains multiplicativity of the
attached degree directly from the domain associated graded ring. -/
theorem isDomain_of_associatedGraded_isDomain
    [IsDomain (hF.degree).AssociatedGraded] : IsDomain R := by
  haveI : Nontrivial R := (hF.degree).nontrivial_of_associatedGraded_isDomain
  haveI : (hF.degree).IsMultiplicative :=
    (hF.degree).isMultiplicative_of_associatedGraded_isDomain hF.degree_isSeparated
  exact (hF.degree).isDomain hF.degree_isSeparated

/-- The degree's weak filtration at dual index `j` is the stage `F j`. -/
theorem mem_degree_filtrationLE_iff (j : ℕ) (x : R) :
    x ∈ (hF.degree).filtrationLE (OrderDual.toDual j) ↔ x ∈ F j := by
  rw [MaxAddDegree.mem_filtrationLE_iff]
  exact hF.value_le_toDual_iff x j

/-- The degree's strict filtration at dual index `j` is the stage `F (j+1)`. -/
theorem mem_degree_lowerFiltration_iff (j : ℕ)
    (x : (hF.degree).filtrationLE (OrderDual.toDual j)) :
    x ∈ (hF.degree).lowerFiltration (OrderDual.toDual j) ↔ (x : R) ∈ F (j + 1) := by
  rw [MaxAddDegree.mem_lowerFiltration_iff]
  exact hF.value_lt_toDual_iff (x : R) j

end IsSeparatedFiltration
