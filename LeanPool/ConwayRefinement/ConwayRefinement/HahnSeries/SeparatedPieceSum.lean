/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.IncreasingSequenceUnion
public import Mathlib.RingTheory.HahnSeries.Summable

/-!
# Hahn sums of order-separated families

A family of Hahn series whose supports are strictly separated along a partially well-ordered
index is summable: the support union is partially well ordered by the ordered-union lemma, and
each exponent meets at most one member. This drops the half-open interval bookkeeping of the
ordered interval sums; any family carried by pairwise disjoint ordered convex pieces qualifies.
The support of the sum is exactly the union of the member supports, and each coefficient is read
off its unique contributing member.
-/

universe u v w

open Set

public noncomputable section

namespace HahnSeries

variable {Γ : Type u} {R : Type v} {ι : Type w}
  [LinearOrder Γ] [AddCommMonoid R] [LinearOrder ι]

/-- Hahn series with strictly separated supports along a partially well-ordered index form a
summable family. -/
def separatedSummableFamily (hι : (Set.univ : Set ι).IsPWO)
    (f : ι → R⟦Γ⟧)
    (hsep : ∀ i j, i < j → ∀ a ∈ (f i).support, ∀ b ∈ (f j).support, a < b) :
    SummableFamily Γ R ι where
  toFun := f
  isPWO_iUnion_support' :=
    Set.IsPWO.iUnion_of_ordered_index hι (fun i ↦ (f i).support)
      (fun i ↦ (f i).isPWO_support) fun i j hij x hx y hy ↦ hsep i j hij x hx y hy
  finite_co_support' x := by
    refine Set.Subsingleton.finite fun i hi j hj ↦ ?_
    by_contra hne
    have hix : x ∈ (f i).support := (mem_support _ _).mpr hi
    have hjx : x ∈ (f j).support := (mem_support _ _).mpr hj
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact lt_irrefl x (hsep i j hij x hix x hjx)
    · exact lt_irrefl x (hsep j i hji x hjx x hix)

/-- The separated family evaluates to the original series at each index. -/
@[simp]
theorem separatedSummableFamily_apply (hι : (Set.univ : Set ι).IsPWO)
    (f : ι → R⟦Γ⟧)
    (hsep : ∀ i j, i < j → ∀ a ∈ (f i).support, ∀ b ∈ (f j).support, a < b) (i : ι) :
    separatedSummableFamily hι f hsep i = f i := (rfl)

/-- The Hahn sum of an order-separated family. -/
def separatedHsum (hι : (Set.univ : Set ι).IsPWO)
    (f : ι → R⟦Γ⟧)
    (hsep : ∀ i j, i < j → ∀ a ∈ (f i).support, ∀ b ∈ (f j).support, a < b) : R⟦Γ⟧ :=
  (separatedSummableFamily hι f hsep).hsum

/-- Order separation prevents coefficient cancellation, so the support of the sum is exactly the
union of the member supports. -/
theorem support_separatedHsum (hι : (Set.univ : Set ι).IsPWO)
    (f : ι → R⟦Γ⟧)
    (hsep : ∀ i j, i < j → ∀ a ∈ (f i).support, ∀ b ∈ (f j).support, a < b) :
    (separatedHsum hι f hsep).support = ⋃ i, (f i).support := by
  apply Set.Subset.antisymm SummableFamily.support_hsum_subset
  intro g hg
  rw [Set.mem_iUnion] at hg
  obtain ⟨i, hi⟩ := hg
  rw [mem_support] at hi ⊢
  rw [SummableFamily.coeff_hsum, finsum_eq_single _ i]
  · exact hi
  · intro j hji
    by_contra hj
    have hjx : g ∈ (f j).support := (mem_support _ _).mpr fun h ↦ hj (by
      rw [separatedSummableFamily_apply, h])
    rcases lt_or_gt_of_ne hji with hji' | hij'
    · exact lt_irrefl g (hsep j i hji' g hjx g hi)
    · exact lt_irrefl g (hsep i j hij' g hi g hjx)

/-- Each coefficient of an order-separated sum is the coefficient of its unique contributing
member. -/
theorem coeff_separatedHsum_eq (hι : (Set.univ : Set ι).IsPWO)
    (f : ι → R⟦Γ⟧)
    (hsep : ∀ i j, i < j → ∀ a ∈ (f i).support, ∀ b ∈ (f j).support, a < b)
    (i : ι) (g : Γ) (hg : ∀ j, j ≠ i → g ∉ (f j).support) :
    (separatedHsum hι f hsep).coeff g = (f i).coeff g := by
  have hsingle := finsum_eq_single
    (fun j ↦ ((separatedSummableFamily hι f hsep) j).coeff g) i fun j hji ↦ by
      rw [separatedSummableFamily_apply]
      by_contra hj
      exact hg j hji ((mem_support _ _).mpr hj)
  rw [separatedHsum, SummableFamily.coeff_hsum, hsingle, separatedSummableFamily_apply]

/-- A coefficient outside every member support vanishes in an order-separated sum. -/
theorem coeff_separatedHsum_eq_zero (hι : (Set.univ : Set ι).IsPWO)
    (f : ι → R⟦Γ⟧)
    (hsep : ∀ i j, i < j → ∀ a ∈ (f i).support, ∀ b ∈ (f j).support, a < b)
    (g : Γ) (hg : ∀ j, g ∉ (f j).support) :
    (separatedHsum hι f hsep).coeff g = 0 := by
  by_contra hne
  have hmem : g ∈ (separatedHsum hι f hsep).support := (mem_support _ _).mpr hne
  rw [support_separatedHsum, Set.mem_iUnion] at hmem
  obtain ⟨j, hj⟩ := hmem
  exact hg j hj

/-- The restriction of a Hahn series to a set of exponents. -/
def setRestrict (s : Set Γ) [DecidablePred (· ∈ s)] (b : R⟦Γ⟧) : R⟦Γ⟧ where
  coeff g := if g ∈ s then b.coeff g else 0
  isPWO_support' := b.isPWO_support.mono fun g hg ↦ by
    by_contra hgb
    apply hg
    change (if g ∈ s then b.coeff g else 0) = 0
    rcases Classical.em (g ∈ s) with hgs | hgs
    · rw [if_pos hgs]
      exact of_not_not fun h ↦ hgb ((mem_support _ _).mpr h)
    · rw [if_neg hgs]

@[simp]
theorem coeff_setRestrict (s : Set Γ) [DecidablePred (· ∈ s)] (b : R⟦Γ⟧) (g : Γ) :
    (setRestrict s b).coeff g = if g ∈ s then b.coeff g else 0 := (rfl)

theorem support_setRestrict (s : Set Γ) [DecidablePred (· ∈ s)] (b : R⟦Γ⟧) :
    (setRestrict s b).support = b.support ∩ s := by
  ext g
  simp only [mem_support, coeff_setRestrict, Set.mem_inter_iff]
  constructor
  · intro h
    rcases Classical.em (g ∈ s) with hgs | hgs
    · rw [if_pos hgs] at h
      exact ⟨(mem_support _ _).mpr h, hgs⟩
    · rw [if_neg hgs] at h
      exact absurd rfl h
  · rintro ⟨hb, hgs⟩
    rw [if_pos hgs]
    exact (mem_support _ _).mp hb

open Classical in
/-- A Hahn series whose support is covered by the pairwise disjoint ordered pieces of a
separated family is the sum of its restrictions to the pieces. -/
theorem separatedHsum_setRestrict_eq (hι : (Set.univ : Set ι).IsPWO)
    (C : ι → Set Γ) (b : R⟦Γ⟧)
    (hcov : b.support ⊆ ⋃ i, C i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hord : ∀ i j, i < j → ∀ a ∈ C i, ∀ c ∈ C j, a < c) :
    separatedHsum hι (fun i ↦ setRestrict (C i) b)
      (fun i j hij a ha c hc ↦ hord i j hij a
        ((support_setRestrict (C i) b ▸ ha : a ∈ b.support ∩ C i)).2 c
        ((support_setRestrict (C j) b ▸ hc : c ∈ b.support ∩ C j)).2) = b := by
  ext g
  by_cases hgb : g ∈ b.support
  · obtain ⟨i, hgi⟩ := Set.mem_iUnion.mp (hcov hgb)
    rw [coeff_separatedHsum_eq _ _ _ i g ?_, coeff_setRestrict, if_pos hgi]
    intro j hji
    rw [support_setRestrict]
    rintro ⟨-, hgj⟩
    exact Set.disjoint_left.mp (hdisj j i hji) hgj hgi
  · have hz : ∀ j, g ∉ (setRestrict (C j) b).support := by
      intro j
      rw [support_setRestrict]
      rintro ⟨hb, -⟩
      exact hgb hb
    rw [coeff_separatedHsum_eq_zero _ _ _ g hz]
    exact (not_not.mp fun h ↦ hgb ((mem_support _ _).mpr h)).symm

end HahnSeries
