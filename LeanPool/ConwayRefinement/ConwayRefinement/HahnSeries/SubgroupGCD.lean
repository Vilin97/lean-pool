/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.EPrimitive

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.SubgroupSupport

/-!
# Transferring least common multiples out of a subgroup of the exponents

Gilmer and Parker, Theorem 5.2 computes a least common multiple inside a finitely generated
subgroup of the exponents and observes that it stays one in the whole ring, because the ring is a
free module over the subring on coset representatives.

The same conclusion is reached here without modules. A common multiple is peeled one coset at a
time: multiplying by a factor supported in the subgroup commutes with restricting to a coset, so
each restriction is again a common multiple, and translating it back into the subgroup puts it in
the range of the hypothesis. The remaining part has strictly smaller support, which drives the
induction.
-/

open scoped HahnSeries

universe u v

public noncomputable section

namespace HahnSeries

variable {G : Type u} {K : Type v}
variable [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G]
variable [Field K]

theorem dvdFS_zero (e : K⟦G⟧) : DvdFS e 0 := dvdFS_iff.mpr ⟨0, by simp, by simp⟩

theorem DvdFS.add {e a b : K⟦G⟧} (ha : DvdFS e a) (hb : DvdFS e b) : DvdFS e (a + b) := by
  obtain ⟨u, huf, hu⟩ := dvdFS_iff.mp ha
  obtain ⟨v, hvf, hv⟩ := dvdFS_iff.mp hb
  exact dvdFS_iff.mpr ⟨u + v, (huf.union hvf).subset (HahnSeries.support_add_subset u v),
    by rw [hu, hv, mul_add]⟩

theorem DvdFS.trans {e a b : K⟦G⟧} (h1 : DvdFS e a) (h2 : DvdFS a b) : DvdFS e b := by
  obtain ⟨u, huf, hu⟩ := dvdFS_iff.mp h1
  obtain ⟨v, hvf, hv⟩ := dvdFS_iff.mp h2
  refine dvdFS_iff.mpr ⟨u * v, ?_, by rw [hv, hu, mul_assoc]⟩
  exact (huf.add hvf).subset HahnSeries.support_mul_subset

theorem DvdFS.sub {e a b : K⟦G⟧} (ha : DvdFS e a) (hb : DvdFS e b) : DvdFS e (a - b) := by
  obtain ⟨u, huf, hu⟩ := dvdFS_iff.mp ha
  obtain ⟨v, hvf, hv⟩ := dvdFS_iff.mp hb
  refine dvdFS_iff.mpr ⟨u - v, ?_, by rw [hu, hv, mul_sub]⟩
  refine (huf.union hvf).subset ?_
  rw [sub_eq_add_neg]
  refine (HahnSeries.support_add_subset u (-v)).trans ?_
  rw [HahnSeries.support_neg]

omit [LinearOrder G] [IsOrderedAddMonoid G] in
/-- Membership in a fixed coset is invariant under translation by the subgroup. -/
private theorem coset_invariant (H : AddSubgroup G) (s : G) :
    ∀ i ∈ H, ∀ j : G, (i + j - s ∈ H ↔ j - s ∈ H) := by
  intro i hi j
  constructor
  · intro hij
    have hrw : j - s = i + j - s - i := by abel
    rw [hrw]
    exact H.sub_mem hij hi
  · intro hj
    have hrw : i + j - s = i + (j - s) := by abel
    rw [hrw]
    exact H.add_mem hi hj

open Classical in
/-- Gilmer and Parker, Theorem 5.2: a common multiple property verified inside a subgroup of the
exponents holds against every finite-support common multiple. -/
theorem dvdFS_of_forall_subgroup {H : AddSubgroup G} {f g h : K⟦G⟧}
    (hf : f.support ⊆ (H : Set G)) (hg : g.support ⊆ (H : Set G))
    (hlcm : ∀ m : K⟦G⟧, m.support.Finite → m.support ⊆ (H : Set G) →
      DvdFS f m → DvdFS g m → DvdFS h m)
    {m : K⟦G⟧} (hmfin : m.support.Finite) (h1 : DvdFS f m) (h2 : DvdFS g m) : DvdFS h m := by
  suffices key : ∀ (n : ℕ) (S : Finset G) (w : K⟦G⟧),
      S.card ≤ n → w.support ⊆ (S : Set G) → DvdFS f w → DvdFS g w → DvdFS h w by
    exact key hmfin.toFinset.card hmfin.toFinset m le_rfl (by simp) h1 h2
  intro n
  induction n with
  | zero =>
    intro S w hcard hsub _ _
    have hS : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    rw [hS] at hsub
    have hw : w = 0 := by
      rw [← HahnSeries.support_eq_empty_iff]
      exact Set.subset_empty_iff.mp (by simpa using hsub)
    rw [hw]
    exact dvdFS_zero h
  | succ n ih =>
    intro S w hcard hsub hfw hgw
    rcases eq_or_ne w 0 with rfl | hw0
    · exact dvdFS_zero h
    obtain ⟨s, hs⟩ := HahnSeries.support_nonempty_iff.mpr hw0
    have hsS : s ∈ S := by simpa using hsub hs
    have hwfin : w.support.Finite := (S.finite_toSet).subset hsub
    have hinv := coset_invariant H s
    -- restrict to the coset of `s`; the rest is the difference
    have hdvd : ∀ e : K⟦G⟧, e.support ⊆ (H : Set G) → DvdFS e w →
        DvdFS e (filter (fun g ↦ g - s ∈ H) w) := by
      intro e he hew
      obtain ⟨u, huf, rfl⟩ := dvdFS_iff.mp hew
      exact dvdFS_iff.mpr ⟨filter (fun g ↦ g - s ∈ H) u,
        huf.subset (HahnSeries.support_filter_subset _ u),
        filter_mul_of_invariant he (fun g ↦ g - s ∈ H) hinv⟩
    have hf₀ := hdvd f hf hfw
    have hg₀ := hdvd g hg hgw
    have hcoeff : ∀ x : G,
        (w - filter (fun g ↦ g - s ∈ H) w).coeff x = if x - s ∈ H then 0 else w.coeff x := by
      intro x
      rw [HahnSeries.coeff_sub, HahnSeries.coeff_filter]
      by_cases hx : x - s ∈ H <;> simp [hx]
    -- the remaining part misses `s`, so its support fits in a smaller finset
    have hrest : DvdFS h (w - filter (fun g ↦ g - s ∈ H) w) := by
      refine ih (S.erase s) _ ?_ ?_ (hfw.sub hf₀) (hgw.sub hg₀)
      · have := Finset.card_erase_of_mem hsS
        omega
      · intro x hx
        rw [HahnSeries.mem_support, hcoeff x] at hx
        by_cases hxp : x - s ∈ H
        · exact absurd (if_pos hxp) hx
        · rw [if_neg hxp] at hx
          refine Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨?_, ?_⟩)
          · rintro rfl
            exact hxp (by simp)
          · simpa using hsub ((HahnSeries.mem_support _ _).mpr hx)
    -- the coset part translates into the subgroup, where the hypothesis applies
    have hcoset : DvdFS h (filter (fun g ↦ g - s ∈ H) w) := by
      set w₀ := filter (fun g ↦ g - s ∈ H) w with hw₀
      have hback : translate s (translate (-s) w₀) = w₀ := by
        rw [HahnSeries.translate_add_apply]
        simp
      have hsupp : (translate (-s) w₀).support ⊆ (H : Set G) := by
        rw [HahnSeries.support_translate]
        rintro _ ⟨x, hx, rfl⟩
        rw [hw₀, HahnSeries.support_filter] at hx
        change -s + x ∈ (H : Set G)
        rw [show -s + x = x - s from by abel]
        exact hx.2
      have hfin : (translate (-s) w₀).support.Finite := by
        rw [HahnSeries.support_translate]
        exact (hwfin.subset (hw₀ ▸ HahnSeries.support_filter_subset _ w)).image _
      have hkey := hlcm _ hfin hsupp
        (by rw [← hback] at hf₀; exact dvdFS_translate_iff.mp hf₀)
        (by rw [← hback] at hg₀; exact dvdFS_translate_iff.mp hg₀)
      rw [← hback]
      exact dvdFS_translate_iff.mpr hkey
    have hsum : filter (fun g ↦ g - s ∈ H) w + (w - filter (fun g ↦ g - s ∈ H) w) = w := by
      abel
    rw [← hsum]
    exact hcoset.add hrest

end HahnSeries
