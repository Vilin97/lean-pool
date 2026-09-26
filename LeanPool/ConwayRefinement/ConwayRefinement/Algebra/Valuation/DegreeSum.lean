/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeInitialForm

import Mathlib.Tactic.Ring

/-!
# Degrees and homogeneous classes of finite sums

For a max-additive degree `ν`, a summand of strictly dominant degree determines the degree of a
sum, a finite sum of elements of degree below `d` has degree below `d`, and the homogeneous class
at level `d` of a finite sum of elements of the weak filtration is the sum of the classes. The
grade-`d` component of a finite sum of homogeneous classes `homogeneousMk (m i) (y i)` is the class
of the sum of the terms with `m i = d`, and the grade-`d` component of an initial form is the class
of the element when its degree is `d` and zero otherwise. Finally, for a well-founded value
monoid, an additive subgroup whose elements of degree at most `d` exhaust the classes at level `d`,
for every `d`, is the whole ring.
-/

universe u v x

public noncomputable section

namespace MaxAddDegree

variable {R : Type u} {M : Type v}
variable [CommRing R] [AddCommMonoid M] [LinearOrder M] [IsOrderedCancelAddMonoid M]

variable (ν : MaxAddDegree R M)

theorem homogeneousMk_eq_zero_of_degree_lt {d : M} {x : R} (hle : x ∈ ν.filtrationLE d)
    (hx : ν x < (d : WithBot M)) : ν.homogeneousMk d ⟨x, hle⟩ = 0 :=
  (ν.homogeneousMk_eq_zero_iff d ⟨x, hle⟩).mpr hx

/-- The homogeneous class of a finite sum at a common level is the sum of the classes. -/
theorem homogeneousMk_finsetSum {ι : Type x} (s : Finset ι) (x : ι → R) {d : M}
    (hx : ∀ i ∈ s, x i ∈ ν.filtrationLE d) (hsum : ∑ i ∈ s, x i ∈ ν.filtrationLE d) :
    ν.homogeneousMk d ⟨∑ i ∈ s, x i, hsum⟩ =
      ∑ i ∈ s.attach, ν.homogeneousMk d ⟨x i, hx i i.2⟩ := by
  rw [← map_sum]
  congr 1
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  simp only
  rw [Finset.sum_attach s x]

omit [IsOrderedCancelAddMonoid M] in
/-- A strictly dominant summand determines the degree of a sum. -/
theorem degree_add_eq_of_lt {x y : R} (h : ν y < ν x) : ν (x + y) = ν x := by
  refine le_antisymm ((ν.map_add_le_max x y).trans (max_le le_rfl h.le)) ?_
  by_contra hcon
  rw [not_le] at hcon
  have hx : x = (x + y) + (-y) := by ring
  have hbound := ν.map_add_le_max (x + y) (-y)
  rw [← hx, ν.map_neg] at hbound
  exact absurd (lt_of_le_of_lt hbound (max_lt hcon h)) (lt_irrefl _)

omit [IsOrderedCancelAddMonoid M] in
theorem degree_finsetSum_lt {ι : Type x} (s : Finset ι) (x : ι → R) {d : M}
    (hx : ∀ i ∈ s, ν (x i) < (d : WithBot M)) : ν (∑ i ∈ s, x i) < (d : WithBot M) := by
  classical
  refine lt_of_le_of_lt (ν.map_sum_le_of_forall_le s x (s.sup fun i ↦ ν (x i))
    fun i hi ↦ Finset.le_sup (f := fun i ↦ ν (x i)) hi) ?_
  exact (Finset.sup_lt_iff (WithBot.bot_lt_coe d)).mpr hx

theorem homogeneousMk_apply_of_eq {m d : M} {y : R} (hy : y ∈ ν.filtrationLE m) (h : m = d) :
    (ν.homogeneousMk m ⟨y, hy⟩) d = ν.componentMk d ⟨y, h ▸ hy⟩ := by
  subst h
  rw [ν.homogeneousMk_apply, DirectSum.of_eq_same]

theorem homogeneousMk_apply_of_ne {m d : M} {y : R} (hy : y ∈ ν.filtrationLE m) (h : m ≠ d) :
    (ν.homogeneousMk m ⟨y, hy⟩) d = 0 := by
  rw [ν.homogeneousMk_apply, DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]

/-- The grade-`d` component of a finite sum of homogeneous classes is the class of the sum of
the terms of grade `d`. -/
theorem homogeneousMk_finsetSum_apply {ι : Type x} (s : Finset ι) (m : ι → M) (y : ι → R)
    (hy : ∀ i, y i ∈ ν.filtrationLE (m i)) (d : M) :
    (∑ i ∈ s, ν.homogeneousMk (m i) ⟨y i, hy i⟩) d =
      ν.componentMk d ⟨∑ i ∈ s.filter (fun i ↦ m i = d), y i,
        (ν.filtrationLE d).sum_mem fun i hi ↦ (Finset.mem_filter.mp hi).2 ▸ hy i⟩ := by
  classical
  rw [DirectSum.sum_apply]
  have hterm : ∀ i ∈ s, (ν.homogeneousMk (m i) ⟨y i, hy i⟩) d =
      if h : m i = d then ν.componentMk d ⟨y i, h ▸ hy i⟩ else 0 := fun i _ ↦ by
    by_cases h : m i = d
    · rw [dite_eq_left h, ν.homogeneousMk_apply_of_eq (hy i) h]
    · rw [dite_eq_right h, ν.homogeneousMk_apply_of_ne (hy i) h]
  rw [Finset.sum_congr rfl hterm, Finset.sum_dite, Finset.sum_const_zero, add_zero, ← map_sum]
  congr 1
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  simp only
  exact Finset.sum_attach (s.filter fun i ↦ m i = d) y

/-- The grade-`d` component of an initial form. -/
theorem initialForm_apply (y : R) (d : M) :
    (ν.initialForm y) d =
      if h : ν y = (d : WithBot M) then
        ν.componentMk d ⟨y, (ν.mem_filtrationLE_iff d y).mpr h.le⟩ else 0 := by
  by_cases hy : ν y = ⊥
  · rw [ν.initialForm_eq_zero_of_eq_bot hy, DirectSum.zero_apply]
    split_ifs with h
    · rw [hy] at h
      exact absurd h WithBot.bot_ne_coe
    · rfl
  · obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hy
    have hmem : y ∈ ν.filtrationLE m := (ν.mem_filtrationLE_iff m y).mpr hm.symm.le
    rw [← ν.homogeneousMk_eq_initialForm_of_degree_eq hmem hm.symm]
    by_cases h : m = d
    · rw [ν.homogeneousMk_apply_of_eq hmem h, dite_eq_left (by rw [← hm, h])]
    · rw [ν.homogeneousMk_apply_of_ne hmem h, dite_eq_right]
      intro h'
      rw [← hm, WithBot.coe_inj] at h'
      exact h h'

omit [IsOrderedCancelAddMonoid M] in
theorem zero_le_degree (hν : ν.IsSeparated) (h0 : ∀ m : M, 0 ≤ m) {x : R} (hx : x ≠ 0) :
    (0 : WithBot M) ≤ ν x := by
  cases h : ν x with
  | bot => exact absurd (((isSeparated_iff ν).mp hν x).mp h) hx
  | coe m => exact WithBot.coe_le_coe.mpr (h0 m)

omit [IsOrderedCancelAddMonoid M] in
/-- An additive subgroup `P` containing, for every degree `d` and every class `g` at level `d`,
an element of degree at most `d` whose class at level `d` is `g`, is the whole ring: by
well-founded induction on the degree, subtracting such an element lowers the degree. -/
theorem mem_of_forall_exists_componentMk_eq [WellFoundedLT M] (hν : ν.IsSeparated)
    (P : AddSubgroup R)
    (h : ∀ (d : M) (g : ν.Component d), ∃ p ∈ P, ∃ hp : p ∈ ν.filtrationLE d,
      ν.componentMk d ⟨p, hp⟩ = g)
    (t : R) : t ∈ P := by
  induction hdeg : ν t using WellFoundedLT.induction generalizing t with
  | _ δ ih =>
  cases hδ : δ with
  | bot =>
    rw [hδ] at hdeg
    rw [((ν.isSeparated_iff).mp hν t).mp hdeg]
    exact zero_mem P
  | coe d =>
    rw [hδ] at hdeg ih
    have hle : t ∈ ν.filtrationLE d := (ν.mem_filtrationLE_iff d t).mpr hdeg.le
    obtain ⟨p, hpP, hple, hp⟩ := h d (ν.componentMk d ⟨t, hle⟩)
    have hsub : ν.componentMk d ⟨t - p, (ν.filtrationLE d).sub_mem hle hple⟩ = 0 := by
      have : (⟨t - p, (ν.filtrationLE d).sub_mem hle hple⟩ : ν.filtrationLE d) =
          ⟨t, hle⟩ - ⟨p, hple⟩ := rfl
      rw [this, map_sub, hp, sub_self]
    rw [ν.componentMk_eq_zero_iff] at hsub
    have hmem := ih _ (hdeg ▸ hsub) (t - p) rfl
    have : t = (t - p) + p := by ring
    rw [this]
    exact P.add_mem hmem hpP

end MaxAddDegree
