/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeAssociatedGraded

/-!
# Initial forms in the associated graded ring

An element of nonbottom degree is placed in the homogeneous component indexed by its exact
degree; an element of bottom degree has initial form zero. Thus the whole kernel of the degree,
not only the literal zero, is sent to zero, as for the semi-valuations of LM24, Section 4. For a
separated degree the kernel is `{0}`, and only zero has initial form zero.

The definition needs no hypothesis on the degree. For a multiplicative degree the initial form
preserves products, and `ConwayRefinement.Algebra.Valuation.RV` shows that it descends
to the RV monoid. The unit is always sent to the unit, since every degree sends `1` to zero or is
bottom
everywhere.
-/

universe u v

public noncomputable section

namespace MaxAddDegree

variable {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M]
  [LinearOrder M] [IsOrderedCancelAddMonoid M]

/-- An element of nonbottom degree, placed in the weak filtration at its exact degree. -/
def initialRepresentative (ν : MaxAddDegree R M) (x : R) (hx : ν x ≠ ⊥) :
    ν.filtrationLE ((ν x).unbot hx) :=
  ⟨x, (ν.mem_filtrationLE_iff _ x).mpr (by rw [WithBot.coe_unbot])⟩

omit [IsOrderedCancelAddMonoid M] in
@[simp]
theorem coe_initialRepresentative (ν : MaxAddDegree R M) (x : R) (hx : ν x ≠ ⊥) :
    (ν.initialRepresentative x hx : R) = x := (rfl)

/-- The initial form of an element in the associated graded ring: its class in the component of
its exact degree, or zero if the degree is bottom. -/
def initialForm (ν : MaxAddDegree R M) (x : R) : ν.AssociatedGraded :=
  if hx : ν x = ⊥ then
    0
  else
    ν.homogeneousMk ((ν x).unbot hx) (ν.initialRepresentative x hx)

theorem initialForm_eq_zero_of_eq_bot (ν : MaxAddDegree R M) {x : R}
    (hx : ν x = ⊥) : ν.initialForm x = 0 := by
  rw [initialForm, dite_eq_left hx]

theorem initialForm_eq_homogeneousMk_of_ne_bot (ν : MaxAddDegree R M) {x : R}
    (hx : ν x ≠ ⊥) :
    ν.initialForm x = ν.homogeneousMk ((ν x).unbot hx) (ν.initialRepresentative x hx) := by
  rw [initialForm, dite_eq_right hx]

omit [IsOrderedCancelAddMonoid M] in
/-- The homogeneous class of an element of nonbottom degree in its exact degree is nonzero. -/
theorem componentMk_initialRepresentative_ne_zero (ν : MaxAddDegree R M) (x : R)
    (hx : ν x ≠ ⊥) :
    ν.componentMk _ (ν.initialRepresentative x hx) ≠ 0 := by
  rw [ne_eq, ν.componentMk_eq_zero_iff, ν.coe_initialRepresentative, WithBot.coe_unbot]
  exact lt_irrefl _

theorem initialForm_ne_zero_of_ne_bot (ν : MaxAddDegree R M) {x : R}
    (hx : ν x ≠ ⊥) : ν.initialForm x ≠ 0 := by
  rw [initialForm, dite_eq_right hx, ne_eq, ν.homogeneousMk_eq_zero_iff,
    ν.coe_initialRepresentative, WithBot.coe_unbot]
  exact lt_irrefl _

/-- The initial form vanishes exactly on the kernel of the degree. -/
theorem initialForm_eq_zero_iff (ν : MaxAddDegree R M) (x : R) :
    ν.initialForm x = 0 ↔ ν x = ⊥ := by
  constructor
  · contrapose!
    exact ν.initialForm_ne_zero_of_ne_bot
  · exact ν.initialForm_eq_zero_of_eq_bot

/-- A nonzero class represented at grade `m` is the initial form of its representative. -/
theorem initialForm_eq_homogeneousMk_of_componentMk_ne_zero
    (ν : MaxAddDegree R M) (m : M) (x : ν.filtrationLE m)
    (hx : ν.componentMk m x ≠ 0) :
    ν.initialForm x = ν.homogeneousMk m x := by
  have hnotlt : ¬ν x < m :=
    fun hlt ↦ hx ((ν.componentMk_eq_zero_iff m x).mpr hlt)
  have hdegree : ν x = (m : WithBot M) :=
    le_antisymm ((ν.mem_filtrationLE_iff m x).mp x.2) (le_of_not_gt hnotlt)
  have hxbot : ν x ≠ ⊥ := by simp [hdegree]
  have hm : (ν x).unbot hxbot = m :=
    (WithBot.unbot_eq_iff hxbot).mpr hdegree
  rw [initialForm, dite_eq_right hxbot, ν.homogeneousMk_apply, ν.homogeneousMk_apply]
  apply DirectSum.of_eq_of_gradedMonoid_eq
  apply Sigma.ext hm
  apply ν.componentMk_heq_of_grade_eq_of_coe_eq hm
  rfl

/-- At its own degree, the homogeneous class of an element is its initial form. -/
theorem homogeneousMk_eq_initialForm_of_degree_eq (ν : MaxAddDegree R M) {d : M} {x : R}
    (hle : x ∈ ν.filtrationLE d) (hx : ν x = (d : WithBot M)) :
    ν.homogeneousMk d ⟨x, hle⟩ = ν.initialForm x := by
  refine (ν.initialForm_eq_homogeneousMk_of_componentMk_ne_zero d ⟨x, hle⟩ ?_).symm
  rw [Ne, ν.componentMk_eq_zero_iff]
  change ¬ ν x < (d : WithBot M)
  rw [hx]
  exact lt_irrefl _

@[simp]
theorem initialForm_zero (ν : MaxAddDegree R M) : ν.initialForm 0 = 0 :=
  ν.initialForm_eq_zero_of_eq_bot ν.map_zero

/-- Elements whose difference has smaller degree than one of them have the same initial form. -/
theorem initialForm_eq_of_sub_lt (ν : MaxAddDegree R M) {x y : R}
    (hxy : ν (x - y) < ν x) : ν.initialForm x = ν.initialForm y := by
  have hdegree : ν x = ν y := ν.map_eq_of_map_sub_lt hxy
  have hx : ν x ≠ ⊥ := ne_bot_of_gt hxy
  have hy : ν y ≠ ⊥ := hdegree ▸ hx
  have hm : (ν x).unbot hx = (ν y).unbot hy :=
    (WithBot.unbot_inj hx hy).mpr hdegree
  rw [initialForm, dite_eq_right hx, initialForm, dite_eq_right hy,
    ν.homogeneousMk_apply, ν.homogeneousMk_apply]
  apply DirectSum.of_eq_of_gradedMonoid_eq
  apply Sigma.ext hm
  apply ν.componentMk_heq_of_grade_eq_of_sub_lt hm
  simpa only [initialRepresentative, WithBot.coe_unbot] using hxy

variable (ν : MaxAddDegree R M) in
/-- The initial form of the unit is the unit: the unit has degree zero, or bottom degree when the
degree is bottom everywhere and the graded ring is trivial. -/
@[simp]
theorem initialForm_one : ν.initialForm 1 = 1 := by
  rcases ν.map_one_eq_bot_or_eq_zero with hone | hone
  · rw [ν.initialForm_eq_zero_of_eq_bot hone, DirectSum.one_def]
    change (0 : ν.AssociatedGraded) = DirectSum.of ν.Component 0 ν.componentOne
    have hcomponentOne : ν.componentOne = 0 := by
      rw [ν.componentOne_eq_componentMk, ν.componentMk_eq_zero_iff, hone]
      exact WithBot.bot_lt_coe 0
    rw [hcomponentOne, (DirectSum.of ν.Component 0).map_zero]
  · have hne : ν 1 ≠ ⊥ := by simp [hone]
    have hm : (ν 1).unbot hne = 0 := (WithBot.unbot_eq_iff hne).mpr hone
    rw [initialForm, dite_eq_right hne, ν.homogeneousMk_apply, DirectSum.one_def]
    change DirectSum.of ν.Component _ _ = DirectSum.of ν.Component 0 ν.componentOne
    rw [ν.componentOne_eq_componentMk]
    apply DirectSum.of_eq_of_gradedMonoid_eq
    apply Sigma.ext hm
    apply ν.componentMk_heq_of_grade_eq_of_coe_eq hm
    rfl

section Multiplicative

variable (ν : MaxAddDegree R M) [ν.IsMultiplicative]

/-- Initial forms of a multiplicative degree preserve multiplication. -/
@[simp]
theorem initialForm_mul (x y : R) :
    ν.initialForm (x * y) = ν.initialForm x * ν.initialForm y := by
  by_cases hx : ν x = ⊥
  · have hxy : ν (x * y) = ⊥ := by simp [hx]
    rw [ν.initialForm_eq_zero_of_eq_bot hxy, ν.initialForm_eq_zero_of_eq_bot hx, zero_mul]
  by_cases hy : ν y = ⊥
  · have hxy : ν (x * y) = ⊥ := by simp [hy]
    rw [ν.initialForm_eq_zero_of_eq_bot hxy, ν.initialForm_eq_zero_of_eq_bot hy, mul_zero]
  · have hxy : ν (x * y) ≠ ⊥ := by
      rw [ν.map_mul, WithBot.add_ne_bot]
      exact ⟨hx, hy⟩
    have hm : (ν (x * y)).unbot hxy = (ν x).unbot hx + (ν y).unbot hy := by
      apply WithBot.coe_injective
      rw [WithBot.coe_unbot, WithBot.coe_add, ν.map_mul, WithBot.coe_unbot, WithBot.coe_unbot]
    rw [initialForm, dite_eq_right hxy, initialForm, dite_eq_right hx, initialForm, dite_eq_right hy,
      ν.homogeneousMk_mul, ν.homogeneousMk_apply, ν.homogeneousMk_apply]
    apply DirectSum.of_eq_of_gradedMonoid_eq
    apply Sigma.ext hm
    apply ν.componentMk_heq_of_grade_eq_of_coe_eq hm
    simp only [coe_initialRepresentative, coe_mulFiltrationLE]

end Multiplicative

section Separated

variable (ν : MaxAddDegree R M)

/-- For a separated degree, every nonzero element has nonzero initial form. -/
theorem initialForm_ne_zero_of_ne_zero (hν : ν.IsSeparated) {x : R} (hx : x ≠ 0) :
    ν.initialForm x ≠ 0 :=
  ν.initialForm_ne_zero_of_ne_bot (ν.map_ne_bot_of_ne_zero hν hx)

/-- For a separated degree, only zero has initial form zero. -/
theorem initialForm_eq_zero_iff_of_isSeparated (hν : ν.IsSeparated) (x : R) :
    ν.initialForm x = 0 ↔ x = 0 := by
  rw [ν.initialForm_eq_zero_iff]
  exact (ν.isSeparated_iff).mp hν x

end Separated

end MaxAddDegree
