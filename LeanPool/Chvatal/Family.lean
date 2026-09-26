/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Combinatorics.SetFamily.Intersecting
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Preorder.Finite

/-
Upstream: https://github.com/boonsuan/chvatal
Commit: c19ed3aaac9e42d446f963a862d39d8a09eddbf9
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Chvatal formalization contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# Finite set families and maximal intersection

This file formalizes the set-family language used in Sections 1 and 4 of
*A proof of Chvátal's conjecture via a sharp correlation inequality*.
In particular, `Family.isMaximalIntersecting_iff` and
`Family.IsMaximalIntersecting.card_eq` give Proposition 4.1. We use mathlib's
`Set.Intersecting`, `IsUpperSet`, and `IsLowerSet`, so intersection includes a
member paired with itself: the empty set cannot belong to an intersecting family.

The dimension-zero exception is explicit. The empty family is maximal
intersecting on an empty ground type, but is not antipodal. Accordingly,
Proposition 4.1 is stated for a nonempty ground type.
-/

public section

namespace Chvatal

/-- A family of subsets of a finite ground type, representing `𝒜 ⊆ 2^[n]`
throughout the paper. -/
abbrev Family (ι : Type*) := Finset (Finset ι)

namespace Family

variable {ι : Type*} [DecidableEq ι]

/-- The hereditary (decreasing) families of Section 1: taking a subset preserves
membership. This is mathlib's lower-set predicate. -/
abbrev IsHereditary (D : Family ι) : Prop := IsLowerSet (D : Set (Finset ι))

/-- The increasing families of Sections 1–4: taking a superset preserves
membership. This is mathlib's upper-set predicate. -/
abbrev IsIncreasing (B : Family ι) : Prop := IsUpperSet (B : Set (Finset ι))

/-- The intersecting families of Sections 1 and 4: any two members, including a
member with itself, have nonempty intersection. -/
abbrev IsIntersecting (B : Family ι) : Prop := (B : Set (Finset ι)).Intersecting

/-- A maximal intersecting family as defined immediately before Proposition 4.1.
Maximality is taken among all families on the given ground type. -/
def IsMaximalIntersecting (B : Family ι) : Prop :=
  B.IsIntersecting ∧ ∀ C : Family ι, C.IsIntersecting → B ⊆ C → B = C

/-- The star `D_i = {S ∈ D : i ∈ S}` appearing in Chvátal's conjecture
(Theorem 1.1 and Section 4). -/
@[expose] def star (D : Family ι) (i : ι) : Family ι := D.filter (i ∈ ·)

/-- Membership in the star from Theorem 1.1. -/
@[simp] theorem mem_star {D : Family ι} {i : ι} {S : Finset ι} :
    S ∈ D.star i ↔ S ∈ D ∧ i ∈ S := by
  simp [star]

/-- A star is a subfamily of its ambient family, as used in Theorem 1.1. -/
theorem star_subset (D : Family ι) (i : ι) : D.star i ⊆ D :=
  Finset.filter_subset _ _

/-- Every star is intersecting; this is the last observation in the proof of
Proposition 5.3, and explains why stars are competitors in Chvátal's conjecture. -/
theorem star_isIntersecting (D : Family ι) (i : ι) : (D.star i).IsIntersecting := by
  intro S hS T hT hdisj
  exact Finset.disjoint_left.mp hdisj (mem_star.mp hS).2 (mem_star.mp hT).2

/-- Intersecting families cannot contain the empty set (Section 4's convention). -/
theorem IsIntersecting.empty_not_mem {B : Family ι} (hB : B.IsIntersecting) : ∅ ∉ B :=
  hB.bot_notMem

/-- Membership in an intersecting family guarantees that the member is nonempty,
including when the two members in the definition coincide. -/
theorem IsIntersecting.nonempty {B : Family ι} (hB : B.IsIntersecting)
    {S : Finset ι} (hS : S ∈ B) : S.Nonempty :=
  Finset.nonempty_iff_ne_empty.mpr (hB.ne_bot hS)

/-- An intersecting subfamily remains intersecting; this is used when restricting
a maximal intersecting family to a hereditary family in Section 4. -/
theorem IsIntersecting.mono {B C : Family ι} (hC : C.IsIntersecting)
    (hBC : B ⊆ C) : B.IsIntersecting := Set.Intersecting.mono hBC hC

/-- Every intersecting family has a maximal intersecting extension, as used at
the end of Section 4 and in the proof of Proposition 5.3. This also holds in dimension
zero. -/
theorem IsIntersecting.exists_maximal_extension [Finite ι] {B : Family ι}
    (hB : B.IsIntersecting) : ∃ C : Family ι, B ⊆ C ∧ C.IsMaximalIntersecting := by
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨C, hBC, hC, hmax⟩ := Finite.exists_le_maximal (p := IsIntersecting) hB
  exact ⟨C, hBC, hC, fun D hD hCD => Finset.Subset.antisymm hCD (hmax hD hCD)⟩

/-- The first assertion in the proof of Proposition 4.1: adjoining supersets
preserves intersection, so every maximal intersecting family is increasing. -/
theorem IsMaximalIntersecting.isIncreasing {B : Family ι}
    (hB : B.IsMaximalIntersecting) : B.IsIncreasing :=
  hB.1.isUpperSet' hB.2

variable [Fintype ι]

/-- The dual family `B* = {S : Sᶜ ∉ B}` from Section 3.1. -/
def dual (B : Family ι) : Family ι := Finset.univ.filter (fun S => Sᶜ ∉ B)

/-- Membership in the dual family, matching the convention in Section 3.1. -/
@[simp] theorem mem_dual {B : Family ι} {S : Finset ι} :
    S ∈ B.dual ↔ Sᶜ ∉ B := by
  simp [dual]

/-- Family duality is an involution, as is the Boolean-function duality in
Sections 1–3. -/
@[simp] theorem dual_dual (B : Family ι) : B.dual.dual = B := by
  ext S
  simp

/-- A family is antipodal when exactly one of each complementary pair belongs to
it, as defined immediately before Proposition 4.1. -/
@[expose] def IsAntipodal (B : Family ι) : Prop := ∀ S : Finset ι, S ∈ B ↔ Sᶜ ∉ B

/-- Antipodality is the self-duality condition used in Section 4. -/
theorem isAntipodal_iff_dual_eq (B : Family ι) : B.IsAntipodal ↔ B.dual = B := by
  simp only [IsAntipodal, Finset.ext_iff, mem_dual]
  exact forall_congr' fun S => iff_comm

/-- Duality preserves increasing families, as used for `𝒢*` in Section 3. -/
theorem IsIncreasing.dual {B : Family ι} (hB : B.IsIncreasing) : B.dual.IsIncreasing := by
  intro S T hST hS
  simp only [Finset.mem_coe, mem_dual] at hS ⊢
  exact fun hTc => hS (hB (compl_le_compl hST) hTc)

/-- Complementing membership in a hereditary family gives an increasing family;
this is the family underlying `f = 1 - 𝟙_D` in Section 4. -/
theorem IsHereditary.isIncreasing_compl {D : Family ι} (hD : D.IsHereditary) :
    Dᶜ.IsIncreasing := by
  intro S T hST hS
  simp only [Finset.mem_coe, Finset.mem_compl] at hS ⊢
  exact fun hT => hS (hD hST hT)

/-- The cardinality bound for intersecting families used by Proposition 4.1,
written without division so it remains valid in dimension zero. -/
theorem IsIntersecting.two_mul_card_le {B : Family ι} (hB : B.IsIntersecting) :
    2 * B.card ≤ 2 ^ Fintype.card ι := by
  simpa only [Fintype.card_finset] using hB.card_le

/-- The equality case in Proposition 4.1, in the division-free form
`2 |B| = 2^n`. The ground type must be nonempty. -/
theorem IsMaximalIntersecting.two_mul_card_eq [Nonempty ι] {B : Family ι}
    (hB : B.IsMaximalIntersecting) : 2 * B.card = 2 ^ Fintype.card ι := by
  simpa only [Fintype.card_finset] using hB.1.is_max_iff_card_eq.mp hB.2

/-- Proposition 4.1: a maximal intersecting family occupies half the cube. -/
theorem IsMaximalIntersecting.card_eq [Nonempty ι] {B : Family ι}
    (hB : B.IsMaximalIntersecting) : B.card = 2 ^ (Fintype.card ι - 1) := by
  have hpos := Fintype.card_pos (α := ι)
  have hcard := hB.two_mul_card_eq
  have hsucc : Fintype.card ι = (Fintype.card ι - 1) + 1 := by omega
  rw [hsucc, pow_succ] at hcard
  omega

/-- The antipodality conclusion of Proposition 4.1, obtained by counting the
disjoint family and its image under complementation. -/
theorem IsMaximalIntersecting.isAntipodal [Nonempty ι] {B : Family ι}
    (hB : B.IsMaximalIntersecting) : B.IsAntipodal := by
  let C := B.map ⟨compl, compl_injective⟩
  have hdisj : Disjoint B C := hB.1.disjoint_map_compl
  have hunion : B ∪ C = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_map, ← Nat.two_mul]
    exact hB.1.is_max_iff_card_eq.mp hB.2
  intro S
  constructor
  · exact hB.1.compl_notMem
  · intro hSc
    have hmem : S ∈ B ∪ C := by rw [hunion]; exact Finset.mem_univ _
    rcases Finset.mem_union.mp hmem with hS | hS
    · exact hS
    · obtain ⟨T, hT, hTS⟩ := Finset.mem_map.mp hS
      apply False.elim (hSc _)
      simpa only [← hTS, Function.Embedding.coeFn_mk, compl_compl] using hT

/-- The converse direction of Proposition 4.1: increasing antipodal families
are intersecting. -/
theorem IsIncreasing.isIntersecting_of_isAntipodal {B : Family ι}
    (hinc : B.IsIncreasing) (hanti : B.IsAntipodal) : B.IsIntersecting := by
  intro S hS T hT hdisj
  exact (hanti S).mp hS (hinc hdisj.le_compl_left hT)

/-- The converse maximality assertion of Proposition 4.1: any newly adjoined
member has its complement already in the original family. -/
theorem IsIncreasing.isMaximalIntersecting_of_isAntipodal {B : Family ι}
    (hinc : B.IsIncreasing) (hanti : B.IsAntipodal) : B.IsMaximalIntersecting := by
  refine ⟨hinc.isIntersecting_of_isAntipodal hanti, ?_⟩
  intro C hC hBC
  apply Finset.Subset.antisymm hBC
  intro S hS
  by_contra hSB
  have hScB : Sᶜ ∈ B := by
    by_contra hScB
    exact hSB ((hanti S).mpr hScB)
  exact hC.compl_notMem hS (hBC hScB)

/-- Proposition 4.1: on a nonempty ground type, maximal intersecting families
are exactly the increasing antipodal families. -/
theorem isMaximalIntersecting_iff [Nonempty ι] (B : Family ι) :
    B.IsMaximalIntersecting ↔ B.IsIncreasing ∧ B.IsAntipodal :=
  ⟨fun hB => ⟨hB.isIncreasing, hB.isAntipodal⟩,
    fun hB => hB.1.isMaximalIntersecting_of_isAntipodal hB.2⟩

/-- A full-cube star is increasing, as used among the examples in Section 5. -/
theorem univ_star_isIncreasing (i : ι) :
    (star (Finset.univ : Family ι) i).IsIncreasing := by
  intro S T hST hS
  exact mem_star.mpr ⟨Finset.mem_univ _, hST (mem_star.mp hS).2⟩

/-- A full-cube star selects exactly one member of each complementary pair;
this is the simplest antipodal family in Proposition 4.1. -/
theorem univ_star_isAntipodal (i : ι) :
    (star (Finset.univ : Family ι) i).IsAntipodal := by
  intro S
  simp

/-- Full-cube stars are maximal intersecting, the basic extremal examples in
Sections 4 and 5. -/
theorem univ_star_isMaximalIntersecting (i : ι) :
    (star (Finset.univ : Family ι) i).IsMaximalIntersecting :=
  (univ_star_isIncreasing i).isMaximalIntersecting_of_isAntipodal
    (univ_star_isAntipodal i)

omit [Fintype ι] in
/-- The last reduction in Section 4: to prove the star bound inside `D`, it
suffices to bound `D ∩ B` for each maximal intersecting family `B`. This lemma
isolates the purely combinatorial reduction from the correlation inequality. -/
theorem exists_star_bound_of_maximal [Finite ι] {D : Family ι}
    (hmax : ∀ B : Family ι, B.IsMaximalIntersecting →
      ∃ i : ι, (D ∩ B).card ≤ (D.star i).card)
    {A : Family ι} (hAD : A ⊆ D) (hA : A.IsIntersecting) :
    ∃ i : ι, A.card ≤ (D.star i).card := by
  obtain ⟨B, hAB, hB⟩ := hA.exists_maximal_extension
  obtain ⟨i, hi⟩ := hmax B hB
  exact ⟨i, (Finset.card_le_card (Finset.subset_inter hAD hAB)).trans hi⟩

end Family
end Chvatal
