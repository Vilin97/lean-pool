/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import LeanPool.OrdvecFormalization.BitmapNull
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.GroupTheory.Perm.Finite

/-!
# Symmetry of bitmap overlap

This file starts the group-theoretic layer for constant-weight bitmap overlap.
After a query bitmap is fixed, the natural symmetry group is the stabilizer of
that query under coordinate permutations.  The first results here show that
query-stabilizer permutations preserve constant weight and literal overlap.
-/

open scoped Pointwise

namespace OrdvecFormalization

namespace Finset

/--
Given two finite subsets of the same ambient type with the same cardinality,
choose a permutation of the ambient type carrying the first subset to the
second.  This is a small wrapper around `Finset.equivOfCardEq` and
`Equiv.extendSubtype`.
-/
noncomputable def permOfCardEq {α : Type} [Fintype α] [DecidableEq α]
    {s t : Finset α} (hcard : s.card = t.card) : Equiv.Perm α :=
  (Finset.equivOfCardEq hcard).extendSubtype

theorem permOfCardEq_smul_eq {α : Type} [Fintype α] [DecidableEq α]
    {s t : Finset α} (hcard : s.card = t.card) :
    permOfCardEq hcard • s = t := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rcases Finset.mem_smul_finset.mp hx with ⟨y, hy, rfl⟩
    exact Equiv.extendSubtype_mem (Finset.equivOfCardEq hcard) y hy
  · rw [Finset.card_smul_finset, hcard]

end Finset

/-- The coordinate permutation group for a `D`-coordinate bitmap. -/
abbrev BitmapPerm (D : ℕ) := Equiv.Perm (BitmapCoord D)

/-- The subgroup of coordinate permutations preserving a query bitmap. -/
abbrev queryStabilizer {D : ℕ} (q : Finset (BitmapCoord D)) :
    Subgroup (BitmapPerm D) :=
  MulAction.stabilizer (BitmapPerm D) q

/-- Apply a coordinate permutation to every active coordinate of a bitmap. -/
def permuteBitmap {D : ℕ} (σ : BitmapPerm D) (d : Finset (BitmapCoord D)) :
    Finset (BitmapCoord D) :=
  σ • d

/-- The active document coordinates that lie inside the query bitmap. -/
def bitmapQueryPart {D : ℕ} (q d : Finset (BitmapCoord D)) : Finset {x // x ∈ q} :=
  d.subtype fun x => x ∈ q

/-- The active document coordinates that lie outside the query bitmap. -/
def bitmapQueryComplPart {D : ℕ} (q d : Finset (BitmapCoord D)) :
    Finset {x // x ∉ q} :=
  d.subtype fun x => x ∉ q

@[simp]
theorem mem_bitmapQueryPart_iff {D : ℕ} {q d : Finset (BitmapCoord D)}
    {x : {x // x ∈ q}} :
    x ∈ bitmapQueryPart q d ↔ (x : BitmapCoord D) ∈ d := by
  simp [bitmapQueryPart]

@[simp]
theorem mem_bitmapQueryComplPart_iff {D : ℕ} {q d : Finset (BitmapCoord D)}
    {x : {x // x ∉ q}} :
    x ∈ bitmapQueryComplPart q d ↔ (x : BitmapCoord D) ∈ d := by
  simp [bitmapQueryComplPart]

theorem card_bitmapQueryPart_eq_overlap {D : ℕ}
    (q d : Finset (BitmapCoord D)) :
    (bitmapQueryPart q d).card = bitmapOverlap q d := by
  classical
  rw [bitmapQueryPart, Finset.card_subtype]
  rw [Finset.filter_mem_eq_inter]
  simp [bitmapOverlap, Finset.inter_comm]

theorem card_bitmapQueryComplPart_eq_card_sub_overlap {D : ℕ}
    (q d : Finset (BitmapCoord D)) :
    (bitmapQueryComplPart q d).card = d.card - bitmapOverlap q d := by
  classical
  have hsplit :=
    Finset.card_filter_add_card_filter_not (s := d) (p := fun x : BitmapCoord D => x ∈ q)
  rw [bitmapQueryComplPart, Finset.card_subtype]
  have hinside : (d.filter fun x : BitmapCoord D => x ∈ q).card = bitmapOverlap q d := by
    rw [Finset.filter_mem_eq_inter]
    simp [bitmapOverlap, Finset.inter_comm]
  omega

theorem card_bitmapQueryPart_eq_of_overlap_eq {D : ℕ}
    {q d e : Finset (BitmapCoord D)}
    (hoverlap : bitmapOverlap q d = bitmapOverlap q e) :
    (bitmapQueryPart q d).card = (bitmapQueryPart q e).card := by
  rw [card_bitmapQueryPart_eq_overlap, card_bitmapQueryPart_eq_overlap, hoverlap]

theorem card_bitmapQueryComplPart_eq_of_card_eq_of_overlap_eq {D : ℕ}
    {q d e : Finset (BitmapCoord D)}
    (hcard : d.card = e.card)
    (hoverlap : bitmapOverlap q d = bitmapOverlap q e) :
    (bitmapQueryComplPart q d).card = (bitmapQueryComplPart q e).card := by
  rw [card_bitmapQueryComplPart_eq_card_sub_overlap,
    card_bitmapQueryComplPart_eq_card_sub_overlap, hcard, hoverlap]

@[simp]
theorem mem_permuteBitmap_iff {D : ℕ} (σ : BitmapPerm D)
    (d : Finset (BitmapCoord D)) (x : BitmapCoord D) :
    x ∈ permuteBitmap σ d ↔ σ.symm x ∈ d := by
  classical
  rw [permuteBitmap]
  simp only [Finset.mem_smul_finset, Equiv.Perm.smul_def]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨σ.symm x, hx, by simp⟩

@[simp]
theorem card_permuteBitmap {D : ℕ} (σ : BitmapPerm D)
    (d : Finset (BitmapCoord D)) :
    (permuteBitmap σ d).card = d.card := by
  classical
  simp [permuteBitmap]

theorem mem_constantWeightBitmapSpace_permuteBitmap_iff {D K : ℕ}
    (σ : BitmapPerm D) (d : Finset (BitmapCoord D)) :
    permuteBitmap σ d ∈ constantWeightBitmapSpace D K ↔
      d ∈ constantWeightBitmapSpace D K := by
  simp [mem_constantWeightBitmapSpace_iff]

theorem permuteBitmap_mem_constantWeightBitmapSpace {D K : ℕ}
    (σ : BitmapPerm D) {d : Finset (BitmapCoord D)}
    (hd : d ∈ constantWeightBitmapSpace D K) :
    permuteBitmap σ d ∈ constantWeightBitmapSpace D K :=
  (mem_constantWeightBitmapSpace_permuteBitmap_iff σ d).mpr hd

/-- Membership characterization for the query stabilizer. -/
theorem mem_queryStabilizer_iff {D : ℕ} {q : Finset (BitmapCoord D)}
    {σ : BitmapPerm D} :
    σ ∈ queryStabilizer q ↔ permuteBitmap σ q = q := by
  rfl

/-- A query-stabilizer permutation preserves query membership pointwise. -/
theorem queryStabilizer_apply_mem_iff {D : ℕ} {q : Finset (BitmapCoord D)}
    {σ : BitmapPerm D} (hσ : σ ∈ queryStabilizer q) (x : BitmapCoord D) :
    σ x ∈ q ↔ x ∈ q := by
  classical
  exact (MulAction.mem_stabilizer_finset.mp hσ x)

/-- A query-stabilizer permutation preserves literal bitmap overlap. -/
theorem bitmapOverlap_queryStabilizer_eq {D : ℕ}
    {q d : Finset (BitmapCoord D)} {σ : BitmapPerm D}
    (hσ : σ ∈ queryStabilizer q) :
    bitmapOverlap q (permuteBitmap σ d) = bitmapOverlap q d := by
  classical
  have hq : σ • q = q := MulAction.mem_stabilizer_iff.mp hσ
  unfold bitmapOverlap permuteBitmap
  calc
    (q ∩ σ • d).card = (σ • q ∩ σ • d).card := by rw [hq]
    _ = (σ • (q ∩ d)).card := by rw [← Finset.smul_finset_inter]
    _ = (q ∩ d).card := by rw [Finset.card_smul_finset]

/-- Overlap is constant on each query-stabilizer orbit of a document bitmap. -/
theorem bitmapOverlap_eq_of_mem_queryStabilizer_orbit {D : ℕ}
    {q d e : Finset (BitmapCoord D)}
    (horbit : ∃ σ : queryStabilizer q, permuteBitmap (σ : BitmapPerm D) d = e) :
    bitmapOverlap q d = bitmapOverlap q e := by
  rcases horbit with ⟨σ, hσde⟩
  rw [← hσde]
  exact (bitmapOverlap_queryStabilizer_eq σ.property).symm

theorem subtypeCongr_query_mem_iff {D : ℕ} (q : Finset (BitmapCoord D))
    (σq : Equiv.Perm {x // x ∈ q}) (σc : Equiv.Perm {x // x ∉ q})
    (x : BitmapCoord D) :
    σq.subtypeCongr σc x ∈ q ↔ x ∈ q := by
  by_cases hx : x ∈ q
  · rw [Equiv.Perm.subtypeCongr.left_apply σq σc hx]
    exact ⟨fun _ => hx, fun _ => (σq ⟨x, hx⟩).property⟩
  · rw [Equiv.Perm.subtypeCongr.right_apply σq σc hx]
    exact ⟨fun h => False.elim ((σc ⟨x, hx⟩).property h), fun h => False.elim (hx h)⟩

theorem subtypeCongr_mem_queryStabilizer {D : ℕ} (q : Finset (BitmapCoord D))
    (σq : Equiv.Perm {x // x ∈ q}) (σc : Equiv.Perm {x // x ∉ q}) :
    σq.subtypeCongr σc ∈ queryStabilizer q := by
  classical
  rw [MulAction.mem_stabilizer_finset]
  intro x
  simpa [Equiv.Perm.smul_def] using subtypeCongr_query_mem_iff q σq σc x

theorem subtypeCongr_permuteBitmap_eq_of_parts {D : ℕ}
    {q d e : Finset (BitmapCoord D)}
    {σq : Equiv.Perm {x // x ∈ q}} {σc : Equiv.Perm {x // x ∉ q}}
    (hcard : d.card = e.card)
    (hσq : σq • bitmapQueryPart q d = bitmapQueryPart q e)
    (hσc : σc • bitmapQueryComplPart q d = bitmapQueryComplPart q e) :
    permuteBitmap (σq.subtypeCongr σc) d = e := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rcases Finset.mem_smul_finset.mp hx with ⟨y, hy, rfl⟩
    by_cases hyq : y ∈ q
    · have hyPart : (⟨y, hyq⟩ : {x // x ∈ q}) ∈ bitmapQueryPart q d := by
        simp [hy]
      have hmap : σq ⟨y, hyq⟩ ∈ bitmapQueryPart q e := by
        rw [← hσq]
        exact Finset.smul_mem_smul_finset hyPart
      simpa [hyq] using (mem_bitmapQueryPart_iff.mp hmap)
    · have hyPart : (⟨y, hyq⟩ : {x // x ∉ q}) ∈ bitmapQueryComplPart q d := by
        simp [hy]
      have hmap : σc ⟨y, hyq⟩ ∈ bitmapQueryComplPart q e := by
        rw [← hσc]
        exact Finset.smul_mem_smul_finset hyPart
      simpa [hyq] using (mem_bitmapQueryComplPart_iff.mp hmap)
  · rw [permuteBitmap, Finset.card_smul_finset, hcard]

/--
If two document bitmaps have the same cardinality and the same overlap with
the query, then a query-stabilizer permutation maps one document to the other.
-/
theorem exists_queryStabilizer_permuteBitmap_eq_of_card_eq_overlap_eq {D : ℕ}
    {q d e : Finset (BitmapCoord D)}
    (hcard : d.card = e.card)
    (hoverlap : bitmapOverlap q d = bitmapOverlap q e) :
    ∃ σ : queryStabilizer q, permuteBitmap (σ : BitmapPerm D) d = e := by
  classical
  let σq : Equiv.Perm {x // x ∈ q} :=
    Finset.permOfCardEq (card_bitmapQueryPart_eq_of_overlap_eq hoverlap)
  let σc : Equiv.Perm {x // x ∉ q} :=
    Finset.permOfCardEq
      (card_bitmapQueryComplPart_eq_of_card_eq_of_overlap_eq hcard hoverlap)
  refine ⟨⟨σq.subtypeCongr σc, subtypeCongr_mem_queryStabilizer q σq σc⟩, ?_⟩
  exact subtypeCongr_permuteBitmap_eq_of_parts hcard
    (Finset.permOfCardEq_smul_eq (card_bitmapQueryPart_eq_of_overlap_eq hoverlap))
    (Finset.permOfCardEq_smul_eq
      (card_bitmapQueryComplPart_eq_of_card_eq_of_overlap_eq hcard hoverlap))

/-- Query-stabilizer orbits are exactly same-overlap classes among equal-cardinality bitmaps. -/
theorem exists_queryStabilizer_permuteBitmap_eq_iff_overlap_eq_of_card_eq {D : ℕ}
    {q d e : Finset (BitmapCoord D)} (hcard : d.card = e.card) :
    (∃ σ : queryStabilizer q, permuteBitmap (σ : BitmapPerm D) d = e) ↔
      bitmapOverlap q d = bitmapOverlap q e := by
  constructor
  · exact bitmapOverlap_eq_of_mem_queryStabilizer_orbit
  · exact exists_queryStabilizer_permuteBitmap_eq_of_card_eq_overlap_eq hcard

/--
On the constant-weight bitmap space, a query-stabilizer-invariant statistic is
constant on same-overlap fibers.
-/
theorem invariantOn_constantWeightBitmapSpace_eq_of_overlap_eq {D K : ℕ}
    {q d e : Finset (BitmapCoord D)} {β : Type}
    (F : Finset (BitmapCoord D) → β)
    (hInv : ∀ σ : queryStabilizer q, ∀ d : Finset (BitmapCoord D),
      d ∈ constantWeightBitmapSpace D K →
        F (permuteBitmap (σ : BitmapPerm D) d) = F d)
    (hd : d ∈ constantWeightBitmapSpace D K)
    (he : e ∈ constantWeightBitmapSpace D K)
    (hoverlap : bitmapOverlap q d = bitmapOverlap q e) :
    F d = F e := by
  have hcard : d.card = e.card := by
    rw [mem_constantWeightBitmapSpace_iff.mp hd, mem_constantWeightBitmapSpace_iff.mp he]
  rcases exists_queryStabilizer_permuteBitmap_eq_of_card_eq_overlap_eq hcard hoverlap with
    ⟨σ, hσde⟩
  rw [← hσde]
  exact (hInv σ d hd).symm

/--
Maximal-invariant form: on constant-weight bitmap documents, every statistic
invariant under query-preserving coordinate permutations factors through
literal query-document overlap.
-/
theorem invariantOn_constantWeightBitmapSpace_factorsThrough_overlap
    {D K : ℕ} (q : Finset (BitmapCoord D)) {β : Type}
    (F : Finset (BitmapCoord D) → β)
    (hInv : ∀ σ : queryStabilizer q, ∀ d : Finset (BitmapCoord D),
      d ∈ constantWeightBitmapSpace D K →
        F (permuteBitmap (σ : BitmapPerm D) d) = F d) :
    ∃ f : ℕ → β, ∀ d : Finset (BitmapCoord D),
      d ∈ constantWeightBitmapSpace D K → F d = f (bitmapOverlap q d) := by
  classical
  let f : ℕ → β := fun x =>
    if h : ∃ d : Finset (BitmapCoord D),
        d.card = K ∧ bitmapOverlap q d = x then
      F h.choose
    else
      F ∅
  refine ⟨f, ?_⟩
  intro d hd
  have hwitness :
      ∃ e : Finset (BitmapCoord D),
        e.card = K ∧ bitmapOverlap q e = bitmapOverlap q d :=
    ⟨d, mem_constantWeightBitmapSpace_iff.mp hd, rfl⟩
  have hchosen_mem :
      (Classical.choose hwitness) ∈ constantWeightBitmapSpace D K :=
    mem_constantWeightBitmapSpace_iff.mpr (Classical.choose_spec hwitness).1
  have hchosen_overlap :
      bitmapOverlap q (Classical.choose hwitness) = bitmapOverlap q d :=
    (Classical.choose_spec hwitness).2
  change F d = f (bitmapOverlap q d)
  rw [show f (bitmapOverlap q d) = F (Classical.choose hwitness) by
    simp [f, hwitness]]
  exact invariantOn_constantWeightBitmapSpace_eq_of_overlap_eq F hInv hd hchosen_mem
    hchosen_overlap.symm

end OrdvecFormalization
