/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Topology.DerivedSet
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Order.TransfiniteIteration
public import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# Transfinite Cantor–Bendixson derivatives

The derivative is taken in the given ambient topology. Its transfinite iteration on a closed
set takes intersections at limit ordinals. Closed maps with finite fibers lift membership in
every derivative of the image. No countability or scatteredness assumption is imposed.
-/

public noncomputable section

open Set Topology Order

universe u v w

namespace TopologicalSpace.Closeds

variable {X : Type u} [TopologicalSpace X] [T1Space X]

/-- The set of accumulation points of a closed set, in the ambient topology. -/
def derived (s : Closeds X) : Closeds X := ⟨derivedSet (s : Set X), isClosed_derivedSet _⟩

@[simp]
theorem coe_derived (s : Closeds X) : (s.derived : Set X) = derivedSet (s : Set X) := (rfl)

theorem derived_le (s : Closeds X) : s.derived ≤ s :=
  (isClosed_iff_derivedSet_subset _).mp s.isClosed

/-- The transfinite Cantor–Bendixson derivative, with the original closed set at stage zero. -/
def cantorBendixson (s : Closeds X) (o : Ordinal.{w}) : Closeds X :=
  transfiniteIterate (I := (Closeds X)ᵒᵈ) derived o s

@[simp]
theorem cantorBendixson_zero (s : Closeds X) : s.cantorBendixson (0 : Ordinal.{w}) = s := by
  exact transfiniteIterate_bot (I := (Closeds X)ᵒᵈ) derived s

@[simp]
theorem cantorBendixson_add_one (s : Closeds X) (o : Ordinal.{w}) :
    s.cantorBendixson (o + 1) = (s.cantorBendixson o).derived := by
  exact transfiniteIterate_succ (I := (Closeds X)ᵒᵈ) derived s o (not_isMax o)

theorem cantorBendixson_limit (s : Closeds X) (o : Ordinal.{w}) (ho : IsSuccLimit o) :
    s.cantorBendixson o = ⨅ i : Iio o, s.cantorBendixson i.1 := by
  exact transfiniteIterate_limit (I := (Closeds X)ᵒᵈ) derived s o ho

theorem cantorBendixson_mono {s t : Closeds X} (hst : s ≤ t) (o : Ordinal.{w}) :
    s.cantorBendixson o ≤ t.cantorBendixson o := by
  induction o using Ordinal.limitRecOn with
  | zero => simpa using hst
  | add_one o ih =>
    rw [cantorBendixson_add_one, cantorBendixson_add_one]
    exact derivedSet_mono _ _ ih
  | limit o ho ih =>
    rw [cantorBendixson_limit _ _ ho, cantorBendixson_limit _ _ ho]
    exact iInf_mono fun i ↦ ih i.1 i.2

theorem cantorBendixson_antitone (s : Closeds X) :
    Antitone (s.cantorBendixson : Ordinal.{w} → Closeds X) :=
  monotone_transfiniteIterate (I := (Closeds X)ᵒᵈ) derived s derived_le

theorem cantorBendixson_le (s : Closeds X) (o : Ordinal.{w}) : s.cantorBendixson o ≤ s := by
  simpa using s.cantorBendixson_antitone (show 0 ≤ o from zero_le)

end TopologicalSpace.Closeds

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Every accumulation point of the image under a closed map lifts to an accumulation point.
Continuity and finiteness of the fibers are not required for this single derivative. -/
theorem IsClosedMap.derivedSet_image_subset {f : X → Y} (hf : IsClosedMap f) (s : Set X) :
    derivedSet (f '' s) ⊆ f '' derivedSet s := by
  intro y hy
  have hfreq := accPt_iff_frequently.mp (mem_derivedSet.mp hy)
  obtain ⟨x, hx, h⟩ := hf.frequently_nhds_fiber (p := fun x ↦ f x ≠ y ∧ x ∈ s) y
    (hfreq.mono fun z hz ↦ by
      obtain ⟨a, ha, rfl⟩ := hz.2
      exact ⟨a, rfl, hz.1, ha⟩)
  refine ⟨x, mem_derivedSet.mpr (accPt_iff_frequently.mpr ?_), hx⟩
  exact h.mono fun z hz ↦ ⟨fun hzx ↦ hz.1 (hzx ▸ hx), hz.2⟩

/-- A closed map with finite fibers lifts every transfinite derivative of the image.
The statement holds for arbitrary ordinals, including limits of uncountable cofinality. -/
theorem IsClosedMap.cantorBendixson_image_subset [T1Space X] [T1Space Y]
    {f : X → Y} (hf : IsClosedMap f) (hfin : ∀ y, (f ⁻¹' {y}).Finite)
    (s : TopologicalSpace.Closeds X) (o : Ordinal.{w}) :
    ((⟨f '' (s : Set X), hf _ s.isClosed⟩ : TopologicalSpace.Closeds Y).cantorBendixson o :
      Set Y) ⊆ f '' (s.cantorBendixson o : Set X) := by
  induction o using Ordinal.limitRecOn with
  | zero => simp
  | add_one o ih =>
    simp only [TopologicalSpace.Closeds.cantorBendixson_add_one,
      TopologicalSpace.Closeds.coe_derived]
    exact (derivedSet_mono _ _ ih).trans (hf.derivedSet_image_subset _)
  | limit o ho ih =>
    intro y hy
    rw [TopologicalSpace.Closeds.cantorBendixson_limit _ _ ho] at hy ⊢
    have hymem : ∀ i : Iio o, y ∈ f '' (s.cantorBendixson i.1 : Set X) :=
      fun i ↦ ih i.1 i.2 ((TopologicalSpace.Closeds.mem_iInf.mp hy) i)
    let t (i : Iio o) : Set X := (f ⁻¹' {y}) ∩ (s.cantorBendixson i.1 : Set X)
    have htn (i : Iio o) : (t i).Nonempty := by
      obtain ⟨x, hx, hxy⟩ := hymem i
      exact ⟨x, hxy, hx⟩
    have htd : Directed (· ⊇ ·) t := by
      intro i j
      refine ⟨max i j, ?_, ?_⟩
      · exact inter_subset_inter_right _ (s.cantorBendixson_antitone (le_max_left i j))
      · exact inter_subset_inter_right _ (s.cantorBendixson_antitone (le_max_right i j))
    have htf (i : Iio o) : (t i).Finite := (hfin y).subset inter_subset_left
    letI : Nonempty (Iio o) := ⟨⟨0, ho.bot_lt⟩⟩
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      t htd htn (fun i ↦ (htf i).isCompact) (fun i ↦ (htf i).isClosed)
    have hxi := mem_iInter.mp hx
    exact ⟨x, TopologicalSpace.Closeds.mem_iInf.mpr (fun i ↦ (hxi i).2),
      (hxi ⟨0, ho.bot_lt⟩).1⟩

namespace TopologicalSpace.Closeds

variable [T1Space X]

/-- A locally strictly decreasing ordinal label bounds every Cantor–Bendixson stage.
Only other points of the original closed set are required to have smaller nearby labels. -/
theorem cantorBendixson_subset_of_locally_lt (s : Closeds X) (r : X → Ordinal.{w})
    (hr : ∀ x ∈ s, ∀ᶠ y in 𝓝 x, y ∈ s → y ≠ x → r y < r x) (o : Ordinal.{w}) :
    (s.cantorBendixson o : Set X) ⊆ {x | o ≤ r x} := by
  induction o using Ordinal.limitRecOn with
  | zero => exact fun _ _ ↦ (show (0 : Ordinal) ≤ _ from zero_le)
  | add_one o ih =>
    intro x hx
    rw [cantorBendixson_add_one] at hx
    have hacc := accPt_iff_frequently.mp (mem_derivedSet.mp hx)
    have hxs : x ∈ s := s.cantorBendixson_le (o + 1) (by
      rw [cantorBendixson_add_one]; exact hx)
    change o + 1 ≤ r x
    apply Order.succ_le_iff.mpr
    by_contra! hle
    obtain ⟨y, hy, hnear⟩ := (hacc.and_eventually (hr x hxs)).exists
    exact (not_lt_of_ge (ih hy.2))
      ((hnear (s.cantorBendixson_le o hy.2) hy.1).trans_le hle)
  | limit o ho ih =>
    intro x hx
    rw [cantorBendixson_limit _ _ ho] at hx
    exact ho.le_iff_forall_le.mpr fun a ha ↦ ih a ha (mem_iInf.mp hx ⟨a, ha⟩)

/-- Transfinite derivatives commute with binary unions of closed sets. -/
theorem cantorBendixson_sup (s t : Closeds X) (o : Ordinal.{w}) :
    (s ⊔ t).cantorBendixson o = s.cantorBendixson o ⊔ t.cantorBendixson o := by
  apply le_antisymm
  · induction o using Ordinal.limitRecOn with
    | zero => simp
    | add_one o ih =>
      rw [cantorBendixson_add_one, cantorBendixson_add_one, cantorBendixson_add_one]
      change (((s ⊔ t).cantorBendixson o).derived : Set X) ⊆
        ((s.cantorBendixson o).derived : Set X) ∪ ((t.cantorBendixson o).derived : Set X)
      simp only [coe_derived]
      rw [← derivedSet_union]
      exact derivedSet_mono _ _ ih
    | limit o ho ih =>
      intro x hx
      change x ∈ (s.cantorBendixson o : Set X) ∪ (t.cantorBendixson o : Set X)
      by_contra hnot
      have hs : x ∉ s.cantorBendixson o := fun hh ↦ hnot (Or.inl hh)
      have ht : x ∉ t.cantorBendixson o := fun hh ↦ hnot (Or.inr hh)
      rw [cantorBendixson_limit _ _ ho] at hs ht
      obtain ⟨i, hi⟩ : ∃ i : Iio o, x ∉ s.cantorBendixson i.1 := by
        by_contra! hn
        exact hs (mem_iInf.mpr hn)
      obtain ⟨j, hj⟩ : ∃ j : Iio o, x ∉ t.cantorBendixson j.1 := by
        by_contra! hn
        exact ht (mem_iInf.mpr hn)
      have hm := ih (max i.1 j.1) (max_lt i.2 j.2)
        ((s ⊔ t).cantorBendixson_antitone (max_lt i.2 j.2).le hx)
      rcases hm with hm | hm
      · exact hi (s.cantorBendixson_antitone (le_max_left _ _) hm)
      · exact hj (t.cantorBendixson_antitone (le_max_right _ _) hm)
  · exact sup_le (cantorBendixson_mono le_sup_left o) (cantorBendixson_mono le_sup_right o)

end TopologicalSpace.Closeds
