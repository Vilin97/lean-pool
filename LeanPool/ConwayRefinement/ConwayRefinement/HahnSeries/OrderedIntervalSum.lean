/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.IncreasingSequenceUnion
public import Mathlib.RingTheory.HahnSeries.Summable

/-!
# Hahn sums over ordered disjoint intervals

A family of Hahn series supported in half-open intervals is summable when its index is partially
well ordered and every earlier interval lies below every later interval. The index may have
arbitrary cofinality.
-/

universe u v w

open Set

public noncomputable section

namespace HahnSeries

variable {Γ : Type u} {R : Type v} {ι : Type w}
  [LinearOrder Γ] [AddCommMonoid R] [LinearOrder ι]

/-- Hahn series supported in an ordered family of disjoint half-open intervals form a summable
family. -/
def orderedIntervalSummableFamily (hι : (Set.univ : Set ι).IsPWO)
    (f : ι → R⟦Γ⟧) (cut center : ι → Γ)
    (hsupp : ∀ i, (f i).support ⊆ Ioc (cut i) (center i))
    (hord : ∀ i j, i < j → center i ≤ cut j) : SummableFamily Γ R ι where
  toFun := f
  isPWO_iUnion_support' :=
    Set.IsPWO.iUnion_of_ordered_index hι (fun i ↦ (f i).support)
      (fun i ↦ (f i).isPWO_support) fun i j hij x hx y hy ↦ by
        exact (hsupp i hx).2.trans_lt ((hord i j hij).trans_lt (hsupp j hy).1)
  finite_co_support' x := by
    refine Set.Subsingleton.finite fun i hi j hj ↦ ?_
    by_contra hne
    have hix : x ∈ (f i).support := (mem_support _ _).mpr hi
    have hjx : x ∈ (f j).support := (mem_support _ _).mpr hj
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact (not_lt_of_ge (hsupp i hix).2)
        ((hord i j hij).trans_lt (hsupp j hjx).1)
    · exact (not_lt_of_ge (hsupp j hjx).2)
        ((hord j i hji).trans_lt (hsupp i hix).1)

/-- The ordered-interval family evaluates to the original series at each index. -/
@[simp]
theorem orderedIntervalSummableFamily_apply (hι : (Set.univ : Set ι).IsPWO)
    (f : ι → R⟦Γ⟧) (cut center : ι → Γ)
    (hsupp : ∀ i, (f i).support ⊆ Ioc (cut i) (center i))
    (hord : ∀ i j, i < j → center i ≤ cut j) (i : ι) :
    orderedIntervalSummableFamily hι f cut center hsupp hord i = f i := (rfl)

/-- Ordered disjoint intervals prevent coefficient cancellation, so the support of the Hahn sum is
exactly the union of the component supports. -/
theorem support_hsum_orderedIntervalSummableFamily (hι : (Set.univ : Set ι).IsPWO)
    (f : ι → R⟦Γ⟧) (cut center : ι → Γ)
    (hsupp : ∀ i, (f i).support ⊆ Ioc (cut i) (center i))
    (hord : ∀ i j, i < j → center i ≤ cut j) :
    (orderedIntervalSummableFamily hι f cut center hsupp hord).hsum.support =
      ⋃ i, (f i).support := by
  apply Set.Subset.antisymm SummableFamily.support_hsum_subset
  intro g hg
  rw [Set.mem_iUnion] at hg
  obtain ⟨i, hi⟩ := hg
  rw [mem_support] at hi ⊢
  rw [SummableFamily.coeff_hsum, finsum_eq_single _ i]
  · exact hi
  · intro j hji
    have hj : g ∉ (f j).support := by
      intro hj
      rcases lt_or_gt_of_ne hji with hji | hij
      · exact (not_lt_of_ge (hsupp j hj).2)
          ((hord j i hji).trans_lt (hsupp i hi).1)
      · exact (not_lt_of_ge (hsupp i hi).2)
          ((hord i j hij).trans_lt (hsupp j hj).1)
    simpa only [orderedIntervalSummableFamily_apply, mem_support, not_not] using hj

end HahnSeries
