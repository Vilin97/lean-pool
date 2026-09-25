/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Segments.SegmentReflection
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SlopeScript

/-!
# Sub-interval reflection scripts

The same-strand argument needs segment-reflection primitives (`segScript` and
its Laplacian) on an arbitrary sub-interval `[lo, hi]` of a single slot.  They
are stated in the `Bananas` namespace because this is their natural geometric
setting.

This is the `SegmentReflection` plateau transplanted onto an arbitrary
sub-interval `[lo, hi]` of one slot and extended by zero.  Its Laplacian
consumes the chips at path positions `lo` and `hi` and produces chips at
`target` and its mirror `lo + hi - target`.
-/

@[expose] public section

namespace Bananas

open Utilities
open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph

open Utilities.SegmentReflection

variable {n p : ℕ}

/-- Path values of the sub-interval reflection. -/
def segValue (star : Fin p) (lo hi target : ℕ) : Fin p → ℕ → ℤ := fun edge k =>
  if edge = star then
    (if k ≤ hi then value (hi - lo) (target - lo) (k - lo) else 0)
  else 0

/-- The sub-interval reflection script. -/
def segScript (spec : SubdivisionGraph.Spec n p) (star : Fin p)
    (lo hi target : ℕ) : firingScript spec.graph :=
  spec.slotValueScript (fun _ => 0) (segValue star lo hi target)

/-- Unit-step slopes of the sub-interval reflection. -/
def segSlope (star : Fin p) (lo hi target : ℕ) : Fin p → ℕ → ℤ := fun edge k =>
  if edge = star then
    (if lo ≤ k ∧ k < hi then slope (hi - lo) (target - lo) (k - lo) else 0)
  else 0

variable {spec : SubdivisionGraph.Spec n p} {star : Fin p} {lo hi target : ℕ}

theorem segValue_star (star : Fin p) (lo hi target k : ℕ) :
    segValue star lo hi target star k =
      if k ≤ hi then value (hi - lo) (target - lo) (k - lo) else 0 := by
  simp [segValue]

theorem segValue_other {edge : Fin p} (he : edge ≠ star) (lo hi target k : ℕ) :
    segValue star lo hi target edge k = 0 := by
  simp [segValue, he]

theorem segSlope_star (star : Fin p) (lo hi target k : ℕ) :
    segSlope star lo hi target star k =
      if lo ≤ k ∧ k < hi then slope (hi - lo) (target - lo) (k - lo) else 0 := by
  simp [segSlope]

theorem segSlope_other {edge : Fin p} (he : edge ≠ star) (lo hi target k : ℕ) :
    segSlope star lo hi target edge k = 0 := by
  simp [segSlope, he]

theorem segCompatible (hlo : lo < target) (hhi : target < hi)
    (hlen : hi ≤ spec.length star) :
    spec.SlotValueCompatible (fun _ => (0 : ℤ)) (segValue star lo hi target) := by
  constructor
  · intro edge
    by_cases he : edge = star
    · subst he
      rw [segValue_star, if_pos (Nat.zero_le _),
        (by omega : (0 : ℕ) - lo = 0), value_zero]
    · rw [segValue_other he]
  · intro edge
    by_cases he : edge = star
    · subst he
      rw [segValue_star]
      by_cases hcase : spec.length edge ≤ hi
      · have heq : spec.length edge = hi := le_antisymm hcase hlen
        rw [if_pos hcase, heq, value_length (by omega)]
      · rw [if_neg hcase]
    · rw [segValue_other he]

theorem isStepSlope_seg (hlo : lo < target) (hhi : target < hi)
    (hlen : hi ≤ spec.length star) :
    spec.IsStepSlope (segScript spec star lo hi target)
      (segSlope star lo hi target) := by
  intro edge offset
  rw [segScript, spec.slotValueScript_stepRight (segCompatible hlo hhi hlen),
    spec.slotValueScript_stepLeft (segCompatible hlo hhi hlen)]
  by_cases he : edge = star
  · subst he
    rw [segValue_star, segValue_star, segSlope_star]
    by_cases hcase : lo ≤ offset.val ∧ offset.val < hi
    · rw [if_pos hcase, if_pos (by omega : offset.val + 1 ≤ hi),
        if_pos (by omega : offset.val ≤ hi),
        (by omega : offset.val + 1 - lo = (offset.val - lo) + 1)]
      exact value_succ_sub_value (by omega)
    · rw [if_neg hcase]
      simp only [not_and_or, not_le, not_lt] at hcase
      rcases hcase with hcase | hcase
      · rw [if_pos (by omega : offset.val + 1 ≤ hi),
          if_pos (by omega : offset.val ≤ hi),
          (by omega : offset.val + 1 - lo = 0), (by omega : offset.val - lo = 0)]
        simp
      · rw [if_neg (by omega : ¬ (offset.val + 1 ≤ hi))]
        by_cases hEq : offset.val ≤ hi
        · rw [if_pos hEq, (by omega : offset.val - lo = hi - lo),
            value_length (by omega)]
          ring
        · rw [if_neg hEq]
          ring
  · rw [segValue_other he, segValue_other he, segSlope_other he]
    ring

theorem segSlope_zero (hlo : lo < target) (hhi : target < hi) :
    segSlope star lo hi target star 0 = if lo = 0 then -1 else 0 := by
  rw [segSlope_star]
  by_cases hz : lo = 0
  · rw [if_pos (by omega : lo ≤ 0 ∧ 0 < hi), if_pos hz, hz]
    simp only [slope]
    rw [if_pos (by omega : 0 - 0 < min (target - 0) (hi - 0 - (target - 0)))]
  · rw [if_neg (by omega : ¬ (lo ≤ 0 ∧ 0 < hi)), if_neg hz]

theorem segSlope_last (hlo : lo < target) (hhi : target < hi)
    (hlen : hi ≤ spec.length star) :
    segSlope star lo hi target star (spec.length star - 1) =
      if hi = spec.length star then 1 else 0 := by
  have hpos := spec.length_pos star
  rw [segSlope_star]
  by_cases heq : hi = spec.length star
  · rw [if_pos (by omega : lo ≤ spec.length star - 1 ∧
      spec.length star - 1 < hi), if_pos heq]
    simp only [slope]
    rw [if_neg (by omega : ¬ (spec.length star - 1 - lo <
        min (target - lo) (hi - lo - (target - lo)))),
      if_pos (by omega : max (target - lo) (hi - lo - (target - lo)) ≤
        spec.length star - 1 - lo)]
  · rw [if_neg (by omega : ¬ (lo ≤ spec.length star - 1 ∧
      spec.length star - 1 < hi)), if_neg heq]

theorem segSlope_diff (hlo : lo < target) (hhi : target < hi) (k : ℕ)
    (hk : 0 < k) :
    segSlope star lo hi target star k - segSlope star lo hi target star (k - 1) =
      -(if k = lo then (1 : ℤ) else 0) - (if k = hi then 1 else 0) +
        (if k = target then 1 else 0) +
        (if k = lo + hi - target then 1 else 0) := by
  rw [segSlope_star, segSlope_star]
  rcases Nat.lt_or_ge k lo with hcase | hcase
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega : ¬ (k = lo)),
      if_neg (by omega : ¬ (k = hi)), if_neg (by omega : ¬ (k = target)),
      if_neg (by omega : ¬ (k = lo + hi - target))]
    ring
  · rcases Nat.eq_or_lt_of_le hcase with hcase2 | hcase2
    · rw [if_pos (by omega), if_neg (by omega),
        if_pos (by omega : k = lo), if_neg (by omega : ¬ (k = hi)),
        if_neg (by omega : ¬ (k = target)),
        if_neg (by omega : ¬ (k = lo + hi - target)),
        (by omega : k - lo = 0)]
      simp only [slope]
      rw [if_pos (by omega : 0 < min (target - lo) (hi - lo - (target - lo)))]
      ring
    · rcases Nat.lt_or_ge hi k with hcase3 | hcase3
      · rw [if_neg (by omega), if_neg (by omega),
          if_neg (by omega : ¬ (k = lo)), if_neg (by omega : ¬ (k = hi)),
          if_neg (by omega : ¬ (k = target)),
          if_neg (by omega : ¬ (k = lo + hi - target))]
        ring
      · have hdiv := slope_divergence (length := hi - lo)
          (position := target - lo) (j := k - lo)
          (by omega) (by omega) (by omega)
        rw [if_pos (by omega : 0 < k - lo)] at hdiv
        rw [if_pos (by omega : lo ≤ k - 1 ∧ k - 1 < hi),
          (by omega : k - 1 - lo = (k - lo) - 1)]
        by_cases hklt : k < hi
        · rw [if_pos (by omega : lo ≤ k ∧ k < hi)]
          rw [if_pos (by omega : k - lo < hi - lo)] at hdiv
          rw [hdiv, if_neg (by omega : ¬ (k - lo = 0)),
            if_neg (by omega : ¬ (k = lo))]
          have e1 : (k - lo = hi - lo) ↔ (k = hi) := by omega
          have e2 : (k - lo = target - lo) ↔ (k = target) := by omega
          have e3 : (k - lo = hi - lo - (target - lo)) ↔
              (k = lo + hi - target) := by omega
          simp only [e1, e2, e3]
          try ring
        · have hkh : k = hi := by omega
          rw [if_neg (by omega : ¬ (lo ≤ k ∧ k < hi))]
          rw [if_neg (by omega : ¬ (k - lo < hi - lo))] at hdiv
          rw [if_neg (by omega : ¬ (k = lo)), if_pos hkh,
            if_neg (by omega : ¬ (k = target)),
            if_neg (by omega : ¬ (k = lo + hi - target))]
          rw [if_neg (by omega : ¬ (k - lo = 0)),
            if_pos (by omega : k - lo = hi - lo),
            if_neg (by omega : ¬ (k - lo = target - lo)),
            if_neg (by omega : ¬ (k - lo = hi - lo - (target - lo)))] at hdiv
          try omega

theorem prin_seg_core (hlo : lo < target) (hhi : target < hi)
    (hlen : hi ≤ spec.length star) (v : Fin n) :
    prin spec.graph (segScript spec star lo hi target) (spec.coreVertex v) =
      (if spec.core.tail star = v then (if lo = 0 then (-1 : ℤ) else 0) else 0) +
        (if spec.core.head star = v then
          -(if hi = spec.length star then (1 : ℤ) else 0) else 0) := by
  rw [spec.prin_coreVertex_eq_endpointSum (isStepSlope_seg hlo hhi hlen)]
  rw [Fintype.sum_eq_single star ?_]
  · rw [segSlope_zero hlo hhi, segSlope_last hlo hhi hlen]
  · intro e he
    rw [segSlope_other he, segSlope_other he]
    simp

theorem prin_seg_int (hlo : lo < target) (hhi : target < hi)
    (hlen : hi ≤ spec.length star) (edge : Fin p)
    (offset : Fin (spec.length edge - 1)) :
    prin spec.graph (segScript spec star lo hi target)
        (spec.interiorVertex edge offset) =
      if edge = star then
        (-(if offset.val + 1 = lo then (1 : ℤ) else 0) -
          (if offset.val + 1 = hi then 1 else 0) +
          (if offset.val + 1 = target then 1 else 0) +
          (if offset.val + 1 = lo + hi - target then 1 else 0))
      else 0 := by
  rw [spec.prin_interiorVertex_eq_slopeDifference (isStepSlope_seg hlo hhi hlen)]
  by_cases he : edge = star
  · subst he
    rw [if_pos rfl]
    have hd := segSlope_diff (star := edge) hlo hhi (offset.val + 1) (by omega)
    simpa using hd
  · rw [if_neg he, segSlope_other he, segSlope_other he]
    ring

/-! ## Generic vertex and chip lemmas

Elementary facts about subdivision vertices and `oneChip` evaluations,
transplanted verbatim from the `Generic`/`Chips` sections of
`Utilities/GenusFourCore100.lean` and `Utilities/GenusFourCore097.lean`
so that the banana development does not depend on those genus-four case
files. -/

section GenericChips

/-- Distinct interior vertices are distinguished by their slot and offset. -/
theorem interiorVertex_eq_iff (spec : SubdivisionGraph.Spec n p)
    (e e' : Fin p) (off : Fin (spec.length e - 1))
    (off' : Fin (spec.length e' - 1)) :
    spec.interiorVertex e off = spec.interiorVertex e' off' ↔
      e = e' ∧ off.val = off'.val := by
  constructor
  · intro h
    have hs : (⟨e, off⟩ : Σ edge : Fin p, Fin (spec.length edge - 1)) =
        ⟨e', off'⟩ := Sum.inr.inj h
    exact ⟨congrArg Sigma.fst hs,
      congrArg (fun s : (Σ edge : Fin p, Fin (spec.length edge - 1)) =>
        s.2.val) hs⟩
  · rintro ⟨rfl, hv⟩
    have hoff : off = off' := Fin.ext hv
    rw [hoff]

theorem coreVertex_ne_interiorVertex (spec : SubdivisionGraph.Spec n p)
    (v : Fin n) (e : Fin p) (off : Fin (spec.length e - 1)) :
    spec.coreVertex v ≠ spec.interiorVertex e off := by
  simp [SubdivisionGraph.Spec.coreVertex, SubdivisionGraph.Spec.interiorVertex]

variable {spec : SubdivisionGraph.Spec n p}

/-- Two divisors on a subdivision agree once they agree at the core vertices
and at every interior vertex. -/
theorem divisor_ext {D E : CFDiv spec.graph}
    (hcore : ∀ v : Fin n, D (spec.coreVertex v) = E (spec.coreVertex v))
    (hint : ∀ (edge : Fin p) (offset : Fin (spec.length edge - 1)),
      D (spec.interiorVertex edge offset) =
        E (spec.interiorVertex edge offset)) :
    D = E := by
  funext vertex
  rcases vertex with u | ⟨edge, offset⟩
  · exact hcore u
  · exact hint edge offset

/-- A strictly interior path position is an interior vertex. -/
theorem pathVertex_interior (edge : Fin p) (k : ℕ) (hk0 : 0 < k)
    (hk : k < spec.length edge) :
    spec.pathVertex edge ⟨k, by omega⟩ =
      spec.interiorVertex edge ⟨k - 1, by omega⟩ := by
  unfold SubdivisionGraph.Spec.pathVertex
  rw [dif_neg (by omega : ¬ k = 0), dif_neg (by omega : ¬ k = spec.length edge)]

end GenericChips

section GenericChipsExplicit

variable (spec : SubdivisionGraph.Spec n p)

theorem one_chip_pV_core (e : Fin p) (k : ℕ) (hk : k ≤ spec.length e)
    (v : Fin n) :
    oneChip (G := spec.graph) (spec.pathVertex e ⟨k, by omega⟩)
        (spec.coreVertex v) =
      (if k = 0 then (if spec.core.tail e = v then (1 : ℤ) else 0) else 0) +
        (if k = spec.length e then
          (if spec.core.head e = v then (1 : ℤ) else 0) else 0) := by
  have hpos := spec.length_pos e
  by_cases hzero : k = 0
  · have hfin : (⟨k, by omega⟩ : spec.PathPosition e) = ⟨0, by omega⟩ :=
      Fin.ext (by simpa using hzero)
    rw [hfin, spec.pathVertex_zero, if_pos hzero,
      if_neg (by omega : ¬ (k = spec.length e)), add_zero]
    simp only [oneChip, SubdivisionGraph.Spec.coreVertex, Sum.inl.injEq]
    by_cases hv : spec.core.tail e = v
    · rw [if_pos hv.symm, if_pos hv]
    · rw [if_neg (fun hh => hv hh.symm), if_neg hv]
  · by_cases hlast : k = spec.length e
    · have hfin : (⟨k, by omega⟩ : spec.PathPosition e) =
          ⟨spec.length e, by omega⟩ := Fin.ext (by simpa using hlast)
      rw [hfin, spec.pathVertex_length, if_neg hzero, zero_add, if_pos hlast]
      simp only [oneChip, SubdivisionGraph.Spec.coreVertex, Sum.inl.injEq]
      by_cases hv : spec.core.head e = v
      · rw [if_pos hv.symm, if_pos hv]
      · rw [if_neg (fun hh => hv hh.symm), if_neg hv]
    · rw [pathVertex_interior e k (by omega) (by omega), if_neg hzero,
        if_neg hlast]
      simp only [oneChip]
      rw [if_neg (coreVertex_ne_interiorVertex spec v e _)]
      ring

theorem one_chip_pV_int (e : Fin p) (k : ℕ) (hk : k ≤ spec.length e)
    (e' : Fin p) (off : Fin (spec.length e' - 1)) :
    oneChip (G := spec.graph) (spec.pathVertex e ⟨k, by omega⟩)
        (spec.interiorVertex e' off) =
      if e = e' then (if k = off.val + 1 then (1 : ℤ) else 0) else 0 := by
  have hpos := spec.length_pos e
  have hoi := off.isLt
  by_cases hzero : k = 0
  · have hfin : (⟨k, by omega⟩ : spec.PathPosition e) = ⟨0, by omega⟩ :=
      Fin.ext (by simpa using hzero)
    rw [hfin, spec.pathVertex_zero]
    simp only [oneChip]
    rw [if_neg (fun hh =>
      (coreVertex_ne_interiorVertex spec (spec.core.tail e) e' off) hh.symm)]
    by_cases he : e = e'
    · rw [if_pos he, if_neg (by omega : ¬ (k = off.val + 1))]
    · rw [if_neg he]
  · by_cases hlast : k = spec.length e
    · have hfin : (⟨k, by omega⟩ : spec.PathPosition e) =
          ⟨spec.length e, by omega⟩ := Fin.ext (by simpa using hlast)
      rw [hfin, spec.pathVertex_length]
      simp only [oneChip]
      rw [if_neg (fun hh =>
        (coreVertex_ne_interiorVertex spec (spec.core.head e) e' off) hh.symm)]
      by_cases he : e = e'
      · subst he
        rw [if_pos rfl, if_neg (by omega : ¬ (k = off.val + 1))]
      · rw [if_neg he]
    · rw [pathVertex_interior e k (by omega) (by omega)]
      simp only [oneChip]
      by_cases he : e = e'
      · subst he
        rw [if_pos rfl]
        by_cases hoff : k = off.val + 1
        · rw [if_pos hoff, if_pos]
          exact (interiorVertex_eq_iff spec e e off _).mpr
            ⟨rfl, by show off.val = k - 1; omega⟩
        · rw [if_neg hoff, if_neg]
          intro hh
          obtain ⟨-, hv⟩ := (interiorVertex_eq_iff spec e e off _).mp hh
          have hv' : off.val = k - 1 := hv
          omega
      · rw [if_neg he, if_neg]
        intro hh
        obtain ⟨hee, -⟩ := (interiorVertex_eq_iff spec e' e off _).mp hh
        exact he hee.symm

theorem one_chip_pos_core (e : Fin p) (pos : spec.PathPosition e) (v : Fin n) :
    oneChip (G := spec.graph) (spec.pathVertex e pos) (spec.coreVertex v) =
      (if pos.val = 0 then (if spec.core.tail e = v then (1 : ℤ) else 0)
        else 0) +
        (if pos.val = spec.length e then
          (if spec.core.head e = v then (1 : ℤ) else 0) else 0) := by
  have hlt := pos.isLt
  have h := one_chip_pV_core spec e pos.val (by omega) v
  have hfin : (⟨pos.val, by omega⟩ : spec.PathPosition e) = pos := Fin.ext rfl
  rw [hfin] at h
  exact h

theorem one_chip_pos_int (e : Fin p) (pos : spec.PathPosition e) (e' : Fin p)
    (off : Fin (spec.length e' - 1)) :
    oneChip (G := spec.graph) (spec.pathVertex e pos)
        (spec.interiorVertex e' off) =
      if e = e' then (if pos.val = off.val + 1 then (1 : ℤ) else 0) else 0 := by
  have hlt := pos.isLt
  have h := one_chip_pV_int spec e pos.val (by omega) e' off
  have hfin : (⟨pos.val, by omega⟩ : spec.PathPosition e) = pos := Fin.ext rfl
  rw [hfin] at h
  exact h

end GenericChipsExplicit

end Bananas
