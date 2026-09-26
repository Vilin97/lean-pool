/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.CantorBendixsonValue
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrderedIntervalSum
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Translation
public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.OrderedIntervalFamily

/-!
# Cantor–Bendixson rank of sums over ordered intervals

Hahn series supported on ordered disjoint intervals can be summed over a partially well-ordered
index of arbitrary cofinality. If the `o`-th derivative of every component is supported at its
center, the `o`-th derivative of the summed support is carried by the closure of the centers.
Local reconstruction then bounds its rank by one successor of `o`.
-/

open Set Filter Topology TopologicalSpace

universe u v w

public noncomputable section

namespace HahnSeries

variable {Γ : Type u} {R : Type v} {ι : Type w}
  [LinearOrder Γ] [LinearOrder ι]

section AddCommMonoid

variable [AddCommMonoid R]

/-- The Hahn sum of a family supported in ordered disjoint half-open intervals. -/
def orderedIntervalHsum (hι : (Set.univ : Set ι).IsPWO)
    (f : ι → R⟦Γ⟧) (cut center : ι → Γ)
    (hsupp : ∀ i, (f i).support ⊆ Ioc (cut i) (center i))
    (hord : ∀ i j, i < j → center i ≤ cut j) : R⟦Γ⟧ :=
  (orderedIntervalSummableFamily hι f cut center hsupp hord).hsum

/-- Ordered interval sums have exactly the union of their component supports. -/
theorem support_orderedIntervalHsum (hι : (Set.univ : Set ι).IsPWO)
    (f : ι → R⟦Γ⟧) (cut center : ι → Γ)
    (hsupp : ∀ i, (f i).support ⊆ Ioc (cut i) (center i))
    (hord : ∀ i j, i < j → center i ≤ cut j) :
    (orderedIntervalHsum hι f cut center hsupp hord).support = ⋃ i, (f i).support := by
  exact support_hsum_orderedIntervalSummableFamily hι f cut center hsupp hord

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [AddCommGroup R]

/-- At one interval center, translated weak truncation of the assembled sum differs from that
component only below the interval's left endpoint. -/
theorem support_translatedTruncLE_orderedIntervalHsum_sub_component_subset
    (hι : (Set.univ : Set ι).IsPWO)
    (f : ι → R⟦Γ⟧) (cut center : ι → Γ)
    (hsupp : ∀ i, (f i).support ⊆ Ioc (cut i) (center i))
    (hord : ∀ i j, i < j → center i ≤ cut j) (i : ι) :
    (translate (-center i) (truncLE (center i)
      (orderedIntervalHsum hι f cut center hsupp hord)) -
      translate (-center i) (f i)).support ⊆ Iic (cut i - center i) := by
  intro g hg
  rw [mem_support] at hg
  apply le_of_not_gt
  intro hcgi
  apply hg
  let x := center i + g
  have hx : g - -center i = x := by simp only [x, sub_neg_eq_add, add_comm]
  have hxic : cut i < x := by
    have h := (sub_lt_iff_lt_add).mp hcgi
    simpa only [x, add_comm] using h
  rw [coeff_sub, coeff_translate, coeff_translate, hx]
  by_cases hg0 : g ≤ 0
  · have hxle : x ≤ center i := by
      change center i + g ≤ center i
      simpa only [add_zero, add_comm] using add_le_add_left hg0 (center i)
    have hcoeff :
        (orderedIntervalHsum hι f cut center hsupp hord).coeff x = (f i).coeff x := by
      rw [orderedIntervalHsum, SummableFamily.coeff_hsum]
      calc
        ∑ᶠ j, ((orderedIntervalSummableFamily hι f cut center hsupp hord) j).coeff x =
            ((orderedIntervalSummableFamily hι f cut center hsupp hord) i).coeff x := by
          apply finsum_eq_single
          intro j hji
          rw [orderedIntervalSummableFamily_apply]
          by_contra hj
          have hxj : x ∈ (f j).support := (mem_support _ _).mpr hj
          rcases lt_or_gt_of_ne hji with hji | hij
          · exact (not_lt_of_ge (hsupp j hxj).2)
              ((hord j i hji).trans_lt hxic)
          · exact (not_lt_of_ge (hxle.trans (hord i j hij))) (hsupp j hxj).1
        _ = (f i).coeff x := congrArg (fun q : R⟦Γ⟧ ↦ q.coeff x)
          (orderedIntervalSummableFamily_apply hι f cut center hsupp hord i)
    rw [HahnSeries.coeff_truncLE, ite_eq_left hxle, hcoeff, sub_self]
  · have hnot : ¬x ≤ center i := by
      change ¬center i + g ≤ center i
      exact not_le_of_gt (by
        simpa only [add_zero, add_comm] using add_lt_add_left (not_le.mp hg0) (center i))
    have hfi : (f i).coeff x = 0 := by
      by_contra h
      exact hnot (hsupp i ((mem_support _ _).mpr h)).2
    rw [HahnSeries.coeff_truncLE, ite_eq_right hnot, hfi, sub_zero]

end AddCommGroup

variable [AddCommMonoid R] [TopologicalSpace Γ] [OrderTopology Γ] [NoMinOrder Γ] [NoMaxOrder Γ]

/-- A derivative stage of an ordered interval sum is supported on the closure of its centers when
the same stage of every component is supported at its own center. -/
theorem cantorBendixson_orderedIntervalHsum_subset_closure_range
    (hι : (Set.univ : Set ι).IsPWO)
    (f : ι → R⟦Γ⟧) (cut center : ι → Γ)
    (hsupp : ∀ i, (f i).support ⊆ Ioc (cut i) (center i))
    (hord : ∀ i j, i < j → center i ≤ cut j)
    (o : Ordinal.{u})
    (hstage : ∀ i, ((f i).closedSupport.cantorBendixson o : Set Γ) ⊆ {center i}) :
    ((orderedIntervalHsum hι f cut center hsupp hord).closedSupport.cantorBendixson o :
      Set Γ) ⊆ closure (Set.range center) := by
  let b := orderedIntervalHsum hι f cut center hsupp hord
  have hbsupp : b.support = ⋃ i, (f i).support :=
    support_orderedIntervalHsum hι f cut center hsupp hord
  have hbclosed : b.closedSupport =
      (⟨closure (⋃ i, (f i).support), isClosed_closure⟩ : Closeds Γ) := by
    apply Closeds.ext
    simp only [coe_closedSupport, hbsupp]
    rfl
  rw [hbclosed]
  have hstage' : ∀ i,
      ((⟨closure (f i).support, isClosed_closure⟩ : Closeds Γ).cantorBendixson o :
        Set Γ) ⊆ {center i} := by
    intro i
    have he : (f i).closedSupport =
        (⟨closure (f i).support, isClosed_closure⟩ : Closeds Γ) := by
      apply Closeds.ext
      simp only [coe_closedSupport]
      rfl
    rw [← he]
    exact hstage i
  exact cantorBendixson_ordered_iUnion_subset_closure_range
    (fun i ↦ (f i).support) cut center hsupp hord o hstage'

/-- If the `o`-th derivative of every interval component is supported at its center and the
centers are carried by the `r`-th derivative of `t`, then absence from the next two stages after
`r` bounds the Cantor–Bendixson rank of the assembled support by `o + 1`. -/
theorem cantorBendixsonRank_orderedIntervalHsum_le_add_one_of_centerStage
    (hι : (Set.univ : Set ι).IsPWO)
    (f : ι → R⟦Γ⟧) (cut center : ι → Γ)
    (hsupp : ∀ i, (f i).support ⊆ Ioc (cut i) (center i))
    (hord : ∀ i j, i < j → center i ≤ cut j)
    (o r : Ordinal.{u}) (t : Closeds Γ)
    (hstage : ∀ i, ((f i).closedSupport.cantorBendixson o : Set Γ) ⊆ {center i})
    (hcenter : closure (Set.range center) ⊆ (t.cantorBendixson r : Set Γ))
    (x : Γ) (ht : x ∉ (t.cantorBendixson ((r + 1) + 1) : Set Γ)) :
    (orderedIntervalHsum hι f cut center hsupp hord).cantorBendixsonRank x ≤ o + 1 := by
  let b := orderedIntervalHsum hι f cut center hsupp hord
  have hderiv : (b.closedSupport.cantorBendixson o : Set Γ) ⊆
      closure (Set.range center) := by
    exact cantorBendixson_orderedIntervalHsum_subset_closure_range
      hι f cut center hsupp hord o hstage
  change b.cantorBendixsonRank x ≤ o + 1
  rw [cantorBendixsonRank_eq]
  apply TopologicalSpace.Closeds.cantorBendixsonRank_le_add_one_of_rankLevel_mapsTo_stage
    b.closedSupport t b.closedSupport_isPWO isOpen_univ (by simp) o r
  · intro y _ hy hyrank
    apply hcenter
    apply hderiv
    exact (b.closedSupport.cantorBendixsonRank_eq_iff b.closedSupport_isPWO hy o).mp
      hyrank |>.1
  · exact ht

/-- If the `o`-th derivative of every interval component is supported at its center and the
centers are carried by the `o`-th derivative of `t`, then absence from the next two stages of `t`
bounds the Cantor–Bendixson rank of the assembled support by `o + 1`. -/
theorem cantorBendixsonRank_orderedIntervalHsum_le_add_one
    (hι : (Set.univ : Set ι).IsPWO)
    (f : ι → R⟦Γ⟧) (cut center : ι → Γ)
    (hsupp : ∀ i, (f i).support ⊆ Ioc (cut i) (center i))
    (hord : ∀ i j, i < j → center i ≤ cut j)
    (o : Ordinal.{u}) (t : Closeds Γ)
    (hstage : ∀ i, ((f i).closedSupport.cantorBendixson o : Set Γ) ⊆ {center i})
    (hcenter : closure (Set.range center) ⊆ (t.cantorBendixson o : Set Γ))
    (x : Γ) (ht : x ∉ (t.cantorBendixson ((o + 1) + 1) : Set Γ)) :
    (orderedIntervalHsum hι f cut center hsupp hord).cantorBendixsonRank x ≤ o + 1 := by
  exact cantorBendixsonRank_orderedIntervalHsum_le_add_one_of_centerStage
    hι f cut center hsupp hord o o t hstage hcenter x ht

end HahnSeries
