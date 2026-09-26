/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Tactic.Abel

/-!
# The quotient of an ordered group by a convex subgroup

A subgroup of a linearly ordered abelian group that is order-connected as a set is *convex*, and
the quotient by it inherits a linear order: one coset lies below another when some representative
of the first lies below some representative of the second. Convexity is exactly what makes that
relation antisymmetric, because an element trapped between zero and a subgroup element belongs to
the subgroup.

The projection is monotone and reflects the strict order (`mk_le_mk`, `lt_of_mk_lt_mk`). Those
two facts are what let order-theoretic hypotheses be transported to the quotient — filling cuts,
in the intended application, where the quotient is taken to gain a small coinitial family of
positive elements that the group itself lacks.
-/

universe u

open Set

public section

namespace ConwayRefinement.Standalone.Hahn

namespace ConvexQuotient

variable {G : Type u} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

/-- A subgroup of an ordered group is convex when it is order-connected. -/
class IsConvex (H : AddSubgroup G) : Prop where
  /-- The carrier of a convex subgroup is order-connected. -/
  ordConnected : (H : Set G).OrdConnected

omit [IsOrderedAddMonoid G] in
/-- A nonnegative element below an element of a convex subgroup lies in the subgroup. -/
theorem mem_of_nonneg_of_le (H : AddSubgroup G) [IsConvex H] {x y : G} (hx : 0 ≤ x)
    (hxy : x ≤ y) (hy : y ∈ H) : x ∈ H :=
  IsConvex.ordConnected.out H.zero_mem hy ⟨hx, hxy⟩

variable {G : Type u} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  {H : AddSubgroup G} [IsConvex H]

/-- One coset lies below another when some representative of the first lies below some
representative of the second. -/
instance instLE : LE (G ⧸ H) where
  le x y := ∃ a b : G, (a : G ⧸ H) = x ∧ (b : G ⧸ H) = y ∧ a ≤ b

/-- **Comparing cosets.** One coset lies below another exactly when the chosen representatives are
already comparable or differ by a subgroup element. Convexity supplies the forward direction: were
the representatives reversed, their difference would be trapped between zero and the subgroup
element relating the two choices. -/
theorem mk_le_mk_iff {a b : G} :
    ((a : G ⧸ H) ≤ (b : G ⧸ H)) ↔ a ≤ b ∨ b - a ∈ H := by
  constructor
  · rintro ⟨a', b', ha', hb', hab⟩
    rw [QuotientAddGroup.eq_iff_sub_mem] at ha' hb'
    rcases le_or_gt a b with h | h
    · exact Or.inl h
    refine Or.inr ?_
    have hsub : a - b ≤ (b' - b) - (a' - a) := by
      rw [← sub_nonneg]
      have heq : (b' - b) - (a' - a) - (a - b) = b' - a' := by abel
      rw [heq]
      exact sub_nonneg.mpr hab
    have hmem := mem_of_nonneg_of_le H (sub_nonneg.mpr h.le) hsub
      (H.sub_mem hb' ha')
    simpa using H.neg_mem hmem
  · rintro (h | h)
    · exact ⟨a, b, rfl, rfl, h⟩
    · exact ⟨a, a, rfl,
        QuotientAddGroup.eq_iff_sub_mem.mpr (by simpa using H.neg_mem h), le_rfl⟩

/-- The projection is monotone. -/
theorem mk_le_mk {a b : G} (h : a ≤ b) : (a : G ⧸ H) ≤ (b : G ⧸ H) :=
  mk_le_mk_iff.mpr (Or.inl h)

open Classical in
noncomputable instance instLinearOrder : LinearOrder (G ⧸ H) where
  le := (· ≤ ·)
  le_refl := by
    refine fun x ↦ QuotientAddGroup.induction_on x fun a ↦ ?_
    exact mk_le_mk le_rfl
  le_trans := by
    refine fun x y z ↦ QuotientAddGroup.induction_on x fun a ↦ QuotientAddGroup.induction_on y
      fun b ↦ QuotientAddGroup.induction_on z fun c hab hbc ↦ ?_
    rw [mk_le_mk_iff] at hab hbc ⊢
    rcases hab with hab | hab
    · rcases hbc with hbc | hbc
      · exact Or.inl (hab.trans hbc)
      -- `c` and `b` differ in the subgroup, so `a ≤ c` unless `a - c` is trapped below `b - c`.
      · rcases le_or_gt a c with h | h
        · exact Or.inl h
        refine Or.inr ?_
        have hbc' : b - c ∈ H := by simpa using H.neg_mem hbc
        have hmem := mem_of_nonneg_of_le H (sub_nonneg.mpr h.le)
          (sub_le_sub_right hab c) hbc'
        simpa using H.neg_mem hmem
    · rcases hbc with hbc | hbc
      · rcases le_or_gt a c with h | h
        · exact Or.inl h
        refine Or.inr ?_
        have hab' : a - b ∈ H := by simpa using H.neg_mem hab
        have hmem := mem_of_nonneg_of_le H (sub_nonneg.mpr h.le)
          (sub_le_sub_left hbc a) hab'
        simpa using H.neg_mem hmem
      · exact Or.inr (by simpa using H.add_mem hbc hab)
  le_antisymm := by
    refine fun x y ↦ QuotientAddGroup.induction_on x fun a ↦ QuotientAddGroup.induction_on y
      fun b hab hba ↦ ?_
    rw [mk_le_mk_iff] at hab hba
    rw [QuotientAddGroup.eq_iff_sub_mem]
    rcases hab with hab | hab
    · rcases hba with hba | hba
      · rw [le_antisymm hab hba, sub_self]
        exact H.zero_mem
      · exact hba
    · simpa using H.neg_mem hab
  le_total := by
    refine fun x y ↦ QuotientAddGroup.induction_on x fun a ↦ QuotientAddGroup.induction_on y
      fun b ↦ ?_
    rcases le_total a b with h | h
    · exact Or.inl (mk_le_mk h)
    · exact Or.inr (mk_le_mk h)
  toDecidableLE := Classical.decRel _

instance instIsOrderedAddMonoid : IsOrderedAddMonoid (G ⧸ H) where
  add_le_add_left := by
    refine fun x y ↦ QuotientAddGroup.induction_on x fun a ↦ QuotientAddGroup.induction_on y
      fun b hab z ↦ QuotientAddGroup.induction_on z fun c ↦ ?_
    rw [mk_le_mk_iff] at hab
    have hc : ((a + c : G) : G ⧸ H) ≤ ((b + c : G) : G ⧸ H) := by
      rw [mk_le_mk_iff]
      rcases hab with hab | hab
      · exact Or.inl (add_le_add hab le_rfl)
      · exact Or.inr (by simpa using hab)
    simpa using hc

/-- **The projection reflects the strict order.** Two representatives whose cosets are strictly
comparable are themselves strictly comparable. -/
theorem lt_of_mk_lt_mk {a b : G} (h : (a : G ⧸ H) < (b : G ⧸ H)) : a < b := by
  rcases mk_le_mk_iff.mp h.le with hab | hab
  · refine hab.lt_of_ne fun hEq ↦ ?_
    exact absurd (le_of_eq (congrArg _ hEq.symm)) (not_le.mpr h)
  · exact absurd (mk_le_mk_iff.mpr (Or.inr (by simpa using H.neg_mem hab))) (not_le.mpr h)

/-- One coset lies strictly below another exactly when the representatives do and their difference
escapes the subgroup. -/
theorem mk_lt_mk_iff {a b : G} :
    ((a : G ⧸ H) < (b : G ⧸ H)) ↔ a < b ∧ b - a ∉ H := by
  refine ⟨fun h ↦ ⟨lt_of_mk_lt_mk h, fun hmem ↦ ?_⟩, fun ⟨hab, hmem⟩ ↦ ?_⟩
  · exact absurd (mk_le_mk_iff.mpr (Or.inr (by simpa using H.neg_mem hmem))) (not_le.mpr h)
  · refine lt_of_le_of_ne (mk_le_mk hab.le) fun hEq ↦ hmem ?_
    simpa using H.neg_mem (QuotientAddGroup.eq_iff_sub_mem.mp hEq)

/-- **Halving descends to the quotient.** If every positive element of `G` is twice a positive
element, the same holds in the quotient: a representative's half stays outside the subgroup,
since otherwise the representative itself would lie inside it. -/
theorem exists_half_of_pos (hG : ∀ x : G, 0 < x → ∃ y, 0 < y ∧ y + y = x) {c : G ⧸ H}
    (hc : 0 < c) : ∃ d : G ⧸ H, 0 < d ∧ d + d ≤ c := by
  induction c using QuotientAddGroup.induction_on with
  | H x =>
    have hpos : ((0 : G) : G ⧸ H) < (x : G ⧸ H) := by
      rw [QuotientAddGroup.mk_zero]
      exact hc
    have hxH : x ∉ H := by simpa using (mk_lt_mk_iff.mp hpos).2
    obtain ⟨y, hy, hyx⟩ := hG x (lt_of_mk_lt_mk hpos)
    have hyH : y ∉ H := fun hmem ↦ hxH (hyx ▸ H.add_mem hmem hmem)
    refine ⟨(y : G ⧸ H), ?_, ?_⟩
    · exact mk_lt_mk_iff.mpr ⟨hy, by simpa using hyH⟩
    · rw [← QuotientAddGroup.mk_add, hyx]

end ConvexQuotient

end ConwayRefinement.Standalone.Hahn
