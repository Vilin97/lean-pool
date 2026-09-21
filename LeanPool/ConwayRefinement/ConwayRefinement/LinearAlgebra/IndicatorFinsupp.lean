/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Indicators in the free module on a set

For a set `L` in a module `M` over `R`, the indicator of `y ∈ M` is the basis vector of
`L →₀ R` at `y` when `y ∈ L`, and `0` otherwise. Its linear combination along the inclusion
`L → M` is `y` when `y ∈ L` and `0` otherwise. When `L` is linearly independent, a vanishing
combination of elements of `L` lifts to the free module, where it can be evaluated at a chosen
basis vector; this is how relations among elements of an independent set are resolved.
-/

universe u v

public section

namespace Set

variable {R : Type u} {M : Type v} [Semiring R]

open scoped Classical in
/-- The indicator of `y` in the free `R`-module on `L`: the basis vector at `y` when `y ∈ L`,
and `0` otherwise. -/
noncomputable def indicatorFinsupp (L : Set M) (R : Type u) [Semiring R] (y : M) : L →₀ R :=
  if h : y ∈ L then Finsupp.single ⟨y, h⟩ 1 else 0

open scoped Classical in
theorem indicatorFinsupp_apply_of_mem (L : Set M) {y : M} (h : y ∈ L) (z : L) :
    L.indicatorFinsupp R y z = if (z : M) = y then 1 else 0 := by
  rw [indicatorFinsupp, dif_pos h, Finsupp.single_apply]
  by_cases hz : (z : M) = y
  · rw [if_pos hz, if_pos (Subtype.ext hz).symm]
  · rw [if_neg hz, if_neg fun h' ↦ hz (congrArg Subtype.val h').symm]

theorem indicatorFinsupp_apply_of_notMem (L : Set M) {y : M} (h : y ∉ L) (z : L) :
    L.indicatorFinsupp R y z = 0 := by
  rw [indicatorFinsupp, dif_neg h, Finsupp.zero_apply]

/-- The indicator of `y` evaluated at the basis vector of `y` itself is `1`. -/
theorem indicatorFinsupp_apply_self (L : Set M) {y : M} (h : y ∈ L) :
    L.indicatorFinsupp R y ⟨y, h⟩ = 1 := by
  classical
  rw [indicatorFinsupp_apply_of_mem L h, if_pos rfl]

/-- The indicator of `y` vanishes at a basis vector other than `y`. -/
theorem indicatorFinsupp_apply_of_ne (L : Set M) (y : M) (z : L) (hz : (z : M) ≠ y) :
    L.indicatorFinsupp R y z = 0 := by
  classical
  by_cases h : y ∈ L
  · rw [indicatorFinsupp_apply_of_mem L h, if_neg hz]
  · exact indicatorFinsupp_apply_of_notMem L h z

theorem indicatorFinsupp_apply_nonneg [PartialOrder R] [IsOrderedRing R] (L : Set M) (y : M)
    (z : L) : 0 ≤ L.indicatorFinsupp R y z := by
  classical
  by_cases h : y ∈ L
  · rw [indicatorFinsupp_apply_of_mem L h]
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  · rw [indicatorFinsupp_apply_of_notMem L h]

variable [AddCommMonoid M] [Module R M]

variable (R) in
open scoped Classical in
theorem linearCombination_indicatorFinsupp (L : Set M) (y : M) :
    Finsupp.linearCombination R (fun z : L ↦ (z : M)) (L.indicatorFinsupp R y) =
      if y ∈ L then y else 0 := by
  by_cases h : y ∈ L
  · rw [indicatorFinsupp, dif_pos h, Finsupp.linearCombination_single, one_smul, if_pos h]
  · rw [indicatorFinsupp, dif_neg h, map_zero, if_neg h]

variable (R) in
/-- The linear combination of the indicator of a member of `L` is that member. -/
theorem linearCombination_indicatorFinsupp_of_mem (L : Set M) {y : M} (h : y ∈ L) :
    Finsupp.linearCombination R (fun z : L ↦ (z : M)) (L.indicatorFinsupp R y) = y := by
  rw [linearCombination_indicatorFinsupp, if_pos h]

variable (R) in
/-- The linear combination of the indicator of `0` is `0`, whether or not `0 ∈ L`. -/
theorem linearCombination_indicatorFinsupp_zero (L : Set M) :
    Finsupp.linearCombination R (fun z : L ↦ (z : M)) (L.indicatorFinsupp R 0) = 0 := by
  rw [linearCombination_indicatorFinsupp]
  split_ifs <;> rfl

end Set

end
