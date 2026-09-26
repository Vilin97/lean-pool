/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.SeparatedPieceSum
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Derivative
public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.SeparatedPieceFamily
import Mathlib.Topology.DerivedSet

/-!
# Cantor–Bendixson ranks of sums on separated pieces

Hahn series carried by pairwise disjoint ordered open convex pieces, each bounded above by a
center inside its own piece, combine into one Hahn sum. Inside a piece the weak truncation of the
sum differs from the truncation of that piece only at or below any piece element under the cutoff,
so their local germs agree. When the centers accumulate nowhere, the Cantor–Bendixson ranks of the
summed supports are bounded by the piece stages: no successor loss occurs anywhere, including at
zero. This supplies the rank bound used by the well-founded cofactor induction at arbitrary
cofinality.
-/

public noncomputable section

open Set Filter Topology TopologicalSpace
open scoped NatOrdinal

universe u v w

namespace HahnSeries

variable {G : Type u} {K : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

section Locality

variable [AddCommGroup K]

omit [AddCommGroup G] [IsOrderedAddMonoid G] in
/-- Inside a piece, the weak truncation of the sum differs from the truncation of that piece
only at or below any element of the piece below the cutoff. -/
theorem support_truncLE_separatedHsum_sub_piece_subset
    {X : Type w} [LinearOrder X] (hX : (Set.univ : Set X).IsPWO)
    (C : X → Set G) (f : X → K⟦G⟧)
    (hfC : ∀ x, (f x).support ⊆ C x)
    (hord : ∀ x y : X, x < y → ∀ a ∈ C x, ∀ b ∈ C y, a < b)
    (hsep : ∀ i j, i < j → ∀ a ∈ (f i).support, ∀ b ∈ (f j).support, a < b)
    (x : X) {y : G} (hy : y ∈ C x) {c : G} (hc : c ∈ C x) :
    (truncLE y (separatedHsum hX f hsep) - truncLE y (f x)).support ⊆ Iic c := by
  intro g hg
  rw [mem_support] at hg
  by_contra hgc
  apply hg
  rw [HahnSeries.coeff_sub, HahnSeries.coeff_truncLE, HahnSeries.coeff_truncLE]
  by_cases hgy : g ≤ y
  · rw [ite_eq_left hgy, ite_eq_left hgy, coeff_separatedHsum_eq hX f hsep x g ?_, sub_self]
    intro j hji hgj
    have hgCj : g ∈ C j := hfC j hgj
    rcases lt_or_gt_of_ne hji with hj | hj
    · exact hgc ((hord j x hj g hgCj c hc).le)
    · exact absurd (hord x j hj y hy g hgCj) (not_lt.mpr hgy)
  · rw [ite_eq_right hgy, ite_eq_right hgy, sub_self]

omit [AddCommGroup G] [IsOrderedAddMonoid G] in
/-- Removing the part of a series outside a convex piece changes its weak truncations only at or
below any piece element, provided the removed support lies entirely below the piece. -/
theorem support_truncLE_sub_truncLE_setRestrict_subset
    (C : Set G) [DecidablePred (· ∈ C)] (b : K⟦G⟧) (y : G) {c : G}
    (hb : ∀ p ∈ b.support, p ∉ C → p ≤ y → p ≤ c) :
    (truncLE y b - truncLE y (setRestrict C b)).support ⊆ Iic c := by
  intro g hg
  rw [mem_support] at hg
  by_contra hgc
  apply hg
  rw [HahnSeries.coeff_sub, HahnSeries.coeff_truncLE, HahnSeries.coeff_truncLE,
    coeff_setRestrict]
  by_cases hgy : g ≤ y
  · rw [ite_eq_left hgy, ite_eq_left hgy]
    by_cases hgC : g ∈ C
    · rw [ite_eq_left hgC, sub_self]
    · rw [ite_eq_right hgC]
      have hgb : g ∉ b.support := fun hgb ↦ hgc (hb g hgb hgC hgy)
      rw [not_not.mp fun h ↦ hgb ((mem_support _ _).mpr h), sub_zero]
  · rw [ite_eq_right hgy, ite_eq_right hgy, sub_self]

open Classical in
/-- Inside a piece, translating the difference between the truncated sum and the truncated
source moves its support below the corresponding translated piece element. -/
theorem support_translate_truncLE_separatedHsum_sub_source_subset
    {X : Type w} [LinearOrder X] (hX : (Set.univ : Set X).IsPWO)
    (C : X → Set G) (f : X → K⟦G⟧)
    (hfC : ∀ x, (f x).support ⊆ C x)
    (hord : ∀ x y : X, x < y → ∀ a ∈ C x, ∀ b ∈ C y, a < b)
    (hsep : ∀ i j, i < j → ∀ a ∈ (f i).support, ∀ b ∈ (f j).support, a < b)
    (x : X) {y c : G} (hy : y ∈ C x) (hc : c ∈ C x)
    (b : K⟦G⟧) (hpiece : f x = setRestrict (C x) b)
    (hb : ∀ p ∈ b.support, p ∉ C x → p ≤ y → p ≤ c) :
    (translate (-y) (truncLE y (separatedHsum hX f hsep)) -
      translate (-y) (truncLE y b)).support ⊆ Iic (c - y) := by
  rw [← map_sub, support_translate]
  rintro _ ⟨q, hq, rfl⟩
  have hsplit : truncLE y (separatedHsum hX f hsep) - truncLE y b =
      (truncLE y (separatedHsum hX f hsep) - truncLE y (f x)) -
        (truncLE y b - truncLE y (setRestrict (C x) b)) := by
    rw [hpiece]
    exact (sub_sub_sub_cancel_right _ _ _).symm
  have hq1 := support_truncLE_separatedHsum_sub_piece_subset hX C f hfC hord hsep x hy hc
  have hq2 := support_truncLE_sub_truncLE_setRestrict_subset (C x) b y hb
  rw [hsplit, sub_eq_add_neg] at hq
  rcases support_add_subset _ _ hq with h | h
  · exact mem_Iic.mpr (by
      have := hq1 h
      simpa only [mem_Iic, sub_eq_add_neg, add_comm] using sub_le_sub_right this y)
  · rw [support_neg] at h
    exact mem_Iic.mpr (by
      have := hq2 h
      simpa only [mem_Iic, sub_eq_add_neg, add_comm] using sub_le_sub_right this y)

end Locality

section ConvexClosure

variable [TopologicalSpace G] [OrderTopology G]

omit [AddCommGroup G] [IsOrderedAddMonoid G] in
/-- The closure of a partially well-ordered subset of a convex piece bounded by a piece element
stays inside the piece: well-ordered sets accumulate only from below. -/
theorem closure_subset_of_isPWO_of_ordConnected {C : Set G} (hC : C.OrdConnected)
    {s : Set G} (hs : s.IsPWO) (hsC : s ⊆ C)
    {x : G} (hx : x ∈ C) (hsx : ∀ p ∈ s, p ≤ x) :
    closure s ⊆ C := by
  intro z hz
  have hzx : z ≤ x := closure_minimal (fun p hp ↦ hsx p hp) isClosed_Iic hz
  obtain ⟨p, hps, hpz⟩ := ((mem_closure_iff_frequently.mp hz).and_eventually
    (hs.eventually_le z)).exists
  exact hC.out (hsC hps) hx ⟨hpz hps, hzx⟩

end ConvexClosure

section Rank

variable [TopologicalSpace G] [OrderTopology G] [NoMinOrder G] [NoMaxOrder G] [AddCommGroup K]

omit [AddCommGroup G] [IsOrderedAddMonoid G] in
/-- With nowhere-accumulating centers, the Cantor–Bendixson ranks of the summed supports are
bounded by the piece stages: at most the stage everywhere, and strictly below it away from the
centers. -/
theorem cantorBendixsonRank_separatedHsum_bounds
    {X : Type w} [LinearOrder X] (hX : (Set.univ : Set X).IsPWO)
    (C : X → Set G) (cen : X → G) (f : X → K⟦G⟧)
    (hfC : ∀ x, (f x).support ⊆ C x)
    (hfle : ∀ x, ∀ p ∈ (f x).support, p ≤ cen x)
    (hcen : ∀ x, cen x ∈ C x)
    (hCopen : ∀ x, IsOpen (C x))
    (hdisj : ∀ x y : X, x ≠ y → Disjoint (C x) (C y))
    (hord : ∀ x y : X, x < y → ∀ a ∈ C x, ∀ b ∈ C y, a < b)
    (hsep : ∀ i j, i < j → ∀ a ∈ (f i).support, ∀ b ∈ (f j).support, a < b)
    (hdiscrete : ∀ z : G, ¬ AccPt z (𝓟 (Set.range cen)))
    (o : Ordinal.{u})
    (hstage : ∀ x, (((f x).closedSupport).cantorBendixson o : Set G) ⊆ {cen x}) :
    (∀ z : G, (separatedHsum hX f hsep).cantorBendixsonRank z ≤ o) ∧
      ∀ z : G, z ∉ Set.range cen →
        z ∉ (((separatedHsum hX f hsep).closedSupport).cantorBendixson o : Set G) := by
  classical
  have hclosure : closure (Set.range cen) = Set.range cen := by
    rw [closure_eq_self_union_derivedSet]
    have hder : derivedSet (Set.range cen) = ∅ := by
      ext z
      simp only [mem_derivedSet, Set.mem_empty_iff_false, iff_false]
      exact hdiscrete z
    rw [hder, Set.union_empty]
  have hstage' : ∀ x, ((⟨closure (f x).support, isClosed_closure⟩ :
      Closeds G).cantorBendixson o : Set G) ⊆ {cen x} := by
    intro x
    have he : (f x).closedSupport = (⟨closure (f x).support, isClosed_closure⟩ : Closeds G) := by
      apply Closeds.ext
      simp only [coe_closedSupport]
      rfl
    rw [← he]
    exact hstage x
  have hsupp : (separatedHsum hX f hsep).support = ⋃ x, (f x).support :=
    support_separatedHsum hX f hsep
  have hbclosed : (separatedHsum hX f hsep).closedSupport =
      (⟨closure (⋃ x, (f x).support), isClosed_closure⟩ : Closeds G) := by
    apply Closeds.ext
    simp only [coe_closedSupport, hsupp]
    rfl
  have hderiv : (((separatedHsum hX f hsep).closedSupport).cantorBendixson o : Set G) ⊆
      Set.range cen := by
    rw [hbclosed, ← hclosure]
    exact cantorBendixson_separated_iUnion_subset_closure_range
      (fun x ↦ (f x).support) C cen (fun x ↦ hfC x) (fun x ↦ hfle x) hcen hCopen
      (fun x y hxy ↦ hdisj x y hxy) hord o hstage'
  have hnext : (((separatedHsum hX f hsep).closedSupport).cantorBendixson (o + 1) :
      Set G) = ∅ := by
    rw [Closeds.cantorBendixson_add_one]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    rw [Closeds.coe_derived, mem_derivedSet] at hz
    exact hdiscrete z (hz.mono (Filter.principal_mono.mpr hderiv))
  refine ⟨?_, ?_⟩
  · intro z
    rw [cantorBendixsonRank_eq]
    exact Closeds.cantorBendixsonRank_le_of_notMem _ _ z (by
      rw [hnext]
      exact Set.notMem_empty z)
  · intro z hz hmem
    exact hz (hderiv hmem)

omit [AddCommGroup G] [IsOrderedAddMonoid G] in
/-- **Sums with strict local stages.** If every piece already has an empty stage `o` and the
centers accumulate only at points outside the open region carrying them, then the assembled stage
`o` is carried by that boundary accumulation alone, and the assembled Cantor–Bendixson rank is at
most `o` everywhere. In particular the assembled degree at a boundary accumulation point does not
gain the successor that a nonstrict local bound would cost. -/
theorem cantorBendixsonRank_separatedHsum_le_of_stage_empty
    {X : Type w} [LinearOrder X] (hX : (Set.univ : Set X).IsPWO)
    (C : X → Set G) (cen : X → G) (f : X → K⟦G⟧)
    (hfC : ∀ x, (f x).support ⊆ C x)
    (hfle : ∀ x, ∀ p ∈ (f x).support, p ≤ cen x)
    (hcen : ∀ x, cen x ∈ C x)
    (hCopen : ∀ x, IsOpen (C x))
    (hdisj : ∀ x y : X, x ≠ y → Disjoint (C x) (C y))
    (hord : ∀ x y : X, x < y → ∀ a ∈ C x, ∀ b ∈ C y, a < b)
    (hsep : ∀ i j, i < j → ∀ a ∈ (f i).support, ∀ b ∈ (f j).support, a < b)
    (o : Ordinal.{u})
    (hstage : ∀ x, (((f x).closedSupport).cantorBendixson o : Set G) = ∅)
    (z₀ : G) (hcl : closure (Set.range cen) ⊆ Set.range cen ∪ {z₀}) :
    ∀ z : G, (separatedHsum hX f hsep).cantorBendixsonRank z ≤ o := by
  classical
  have hstage' : ∀ x, ((⟨closure (f x).support, isClosed_closure⟩ :
      Closeds G).cantorBendixson o : Set G) = ∅ := by
    intro x
    have he : (f x).closedSupport = (⟨closure (f x).support, isClosed_closure⟩ : Closeds G) := by
      apply Closeds.ext
      simp only [coe_closedSupport]
      rfl
    rw [← he]
    exact hstage x
  have hsupp : (separatedHsum hX f hsep).support = ⋃ x, (f x).support :=
    support_separatedHsum hX f hsep
  have hbclosed : (separatedHsum hX f hsep).closedSupport =
      (⟨closure (⋃ x, (f x).support), isClosed_closure⟩ : Closeds G) := by
    apply Closeds.ext
    simp only [coe_closedSupport, hsupp]
    rfl
  have hderiv : (((separatedHsum hX f hsep).closedSupport).cantorBendixson o : Set G) ⊆
      {z₀} := by
    rw [hbclosed]
    intro z hz
    have hz' := cantorBendixson_separated_iUnion_subset_of_stage_empty
      (fun x ↦ (f x).support) C cen (fun x ↦ hfC x) (fun x ↦ hfle x) hcen hCopen
      (fun x y hxy ↦ hdisj x y hxy) hord o hstage' hz
    rcases hcl hz'.1 with h | h
    · exact absurd h hz'.2
    · exact h
  have hnext : (((separatedHsum hX f hsep).closedSupport).cantorBendixson (o + 1) :
      Set G) = ∅ := by
    rw [Closeds.cantorBendixson_add_one]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    rw [Closeds.coe_derived, mem_derivedSet] at hz
    have hacc := hz.mono (Filter.principal_mono.mpr hderiv)
    exact (Set.finite_singleton z₀).not_infinite (Set.Infinite.of_accPt hacc)
  intro z
  rw [cantorBendixsonRank_eq]
  exact Closeds.cantorBendixsonRank_le_of_notMem _ _ z (by
    rw [hnext]
    exact Set.notMem_empty z)

end Rank

end HahnSeries
