/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationMarkedThree

/-!
# The row-authoring layer over a marked script

`GenusFiveRow05` proved AR's sixth family by hand: it named the two marked
slots, built the potential, checked `MarksAdmissible`, read each slot as one or
two ordinary arms, and closed the residual.  All of that except the *tables* is
independent of the row and of which slots carry a mark, and AR's seventh family
(row `08`) needs it three times over -- once per chamber, with a different pair
of marked slots each time.  This file is that layer, stated once.

The whole interface is driven by a single function `mark : Fin 12 → ℕ`.  There
is no separate "is this slot marked" flag, because

* the mark *value* can be defined uniformly,
  `markValue e = if 0 < mark e then 0 else potential (tail e)` -- a marked slot
  whose mark has slid back to the tail carries height zero there anyway; and
* the two endpoint readings can be too,

  ```
   tail e = if 0 < mark e then tailContribution (mark e) hu 0
            else tailContribution (length e) hu hv
   head e = if 0 < mark e then
              (if mark e < length e then headContribution (length e - mark e) 0 hv
               else headContribution (length e) hu hv)
            else headContribution (length e) hu hv
  ```

  which specialize to `ConfigurationCommon`'s single-ramp ledger on every slot
  with `mark e = 0`.  So a chamber marks the one or two slots it needs and says
  nothing at all about the other ten.

What a chamber supplies is a `Profile`: the mark is inside its slot, the height
at each end of a marked slot is bounded by that end's half, one of those two
heights vanishes (the chip sits where a flat stretch meets a full ramp), and
the height is constant across collapsed slots.  Those five facts give
`MarksAdmissible`, the ledger reading of every slot, *and* the hypotheses of
`prin_splitScript_interiorVertex_ge_neg_one` at the mark -- so the interior chip
costs a chamber nothing beyond declaring its profile.
-/

namespace AtanasovRanganathan.ConfigurationMarkedRow

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.DegenerateSpec
open Certificate.DegenerateSpec.DegSpec
open Certificate.StrongSeparator
open Utilities.Certificate.ContractionForestCensusGeneral
open Configurations
open ConfigurationFive
open ConfigurationMarkedThree

variable (d : DegSpec 8 12)

/-! ## The script of a height profile -/

/-- The potential of a height profile, read at the canonical class
representative so that class invariance is definitional. -/
def heightPotential (h : Fin 8 → ℕ) (v : Fin 8) : ℤ := -((h (d.rep v) : ℤ))

theorem heightPotential_repInvariant (h : Fin 8 → ℕ) :
    d.RepInvariant (heightPotential d h) := by
  intro v
  simp [heightPotential, d.rep_idem]

/-- The script's value at each mark.  Zero on a genuinely marked slot -- the
chip sits at the ambient level -- and the tail's own value on an unmarked one,
which is what makes the unmarked slot literally the old single ramp. -/
def markValue (mark : Fin 12 → ℕ) (h : Fin 8 → ℕ) (e : Fin 12) : ℤ :=
  if 0 < mark e then 0 else heightPotential d h (d.core.tail e)

/-- The marked firing script of a height profile. -/
def script (mark : Fin 12 → ℕ) (h : Fin 8 → ℕ) : firingScript d.graph :=
  d.splitScript (heightPotential d h) mark (markValue d mark h)

/-- What a chamber has to say about its height profile.  Everything else in
this file follows from these five facts. -/
structure Profile (mark : Fin 12 → ℕ) (h : Fin 8 → ℕ) : Prop where
  /-- Each mark lies inside its slot. -/
  le : ∀ e : Fin 12, mark e ≤ d.length e
  /-- The near half of a marked slot is long enough for its rise. -/
  inBound : ∀ e : Fin 12, 0 < mark e → h (d.core.tail e) ≤ mark e
  /-- The far half of a marked slot is long enough for its rise. -/
  outBound : ∀ e : Fin 12, 0 < mark e → h (d.core.head e) ≤ d.length e - mark e
  /-- The chip sits where a flat stretch meets a full ramp. -/
  flat : ∀ e : Fin 12, 0 < mark e →
    h (d.core.tail e) = 0 ∨ h (d.core.head e) = 0
  /-- The profile is constant across a collapsed slot, hence on every
  contracted class. -/
  const : ∀ e : Fin 12, d.length e = 0 →
    h (d.core.tail e) = h (d.core.head e)

/-! ## Class constancy -/

theorem height_rep_eq {core : ExplicitPotential.Core 8 12} (hCore : d.core = core)
    {h : Fin 8 → ℕ}
    (hconst : ∀ e : Fin 12, d.length e = 0 →
      h (d.core.tail e) = h (d.core.head e))
    (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8, d.rep x = d.rep y ↔ ReachIn core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0) (v : Fin 8) :
    h (d.rep v) = h v := by
  have hconst' : ∀ e : Fin 12, d.length e = 0 →
      h (core.tail e) = h (core.head e) := by
    intro e he
    rw [← hCore]
    exact hconst e he
  have key : ∀ {u w : Fin 8}, ReachIn core F u w → h u = h w := by
    intro u w hReach
    induction hReach with
    | refl => rfl
    | @tail a b hPrefix hLast ih =>
        rw [ih]
        obtain ⟨e, he, hab | hab⟩ := hLast
        · rw [← hab.1, ← hab.2]
          exact hconst' e ((hFZero e).mp ((mem_edgeList F e).mp he))
        · rw [← hab.1, ← hab.2]
          exact (hconst' e ((hFZero e).mp ((mem_edgeList F e).mp he))).symm
  exact key ((hRepReach (d.rep v) v).mp (d.rep_idem v))

theorem heightPotential_eq {h : Fin 8 → ℕ}
    (hRep : ∀ v : Fin 8, h (d.rep v) = h v) (v : Fin 8) :
    heightPotential d h v = -((h v : ℤ)) := by
  rw [heightPotential, hRep]

theorem heightPotential_rep {h : Fin 8 → ℕ}
    (hRep : ∀ v : Fin 8, h (d.rep v) = h v) (v : Fin 8) :
    heightPotential d h (d.rep v) = -((h v : ℤ)) := by
  rw [heightPotential, d.rep_idem, hRep]

/-! ## Admissibility -/

theorem markValue_of_pos {mark : Fin 12 → ℕ} {h : Fin 8 → ℕ} {e : Fin 12}
    (hpos : 0 < mark e) : markValue d mark h e = 0 := by
  simp [markValue, hpos]

theorem markValue_of_zero {mark : Fin 12 → ℕ} {h : Fin 8 → ℕ} {e : Fin 12}
    (hzero : mark e = 0) :
    markValue d mark h e = heightPotential d h (d.rep (d.core.tail e)) := by
  simp only [markValue, hzero, lt_irrefl, if_false, heightPotential, d.rep_idem]

theorem marks_admissible {mark : Fin 12 → ℕ} {h : Fin 8 → ℕ}
    (hprof : Profile d mark h) (hRep : ∀ v : Fin 8, h (d.rep v) = h v) :
    d.MarksAdmissible (heightPotential d h) mark (markValue d mark h) := by
  intro e
  refine ⟨hprof.le e, ?_, ?_⟩
  · intro hz
    rw [DegSpec.markRiseIn, markValue_of_zero d hz]
    ring
  · intro hz
    by_cases hpos : 0 < mark e
    · rw [DegSpec.markRiseOut, markValue_of_pos d hpos,
        heightPotential_rep d hRep]
      have := hprof.outBound e hpos
      have hlen : d.length e - mark e = 0 := by omega
      omega
    · have hzero : mark e = 0 := by omega
      have hlen : d.length e = 0 := by omega
      have hRepZero := d.rep_zero e hlen
      rw [DegSpec.markRiseOut, markValue_of_zero d hzero, heightPotential,
        heightPotential, hRepZero]
      ring

/-! ## Each slot as one or two ordinary arms -/

def slotTailForm (mark : Fin 12 → ℕ) (h : Fin 8 → ℕ) (e : Fin 12) : ℤ :=
  if 0 < mark e then tailContribution (mark e) (h (d.core.tail e)) 0
  else tailContribution (d.length e) (h (d.core.tail e)) (h (d.core.head e))

def slotHeadForm (mark : Fin 12 → ℕ) (h : Fin 8 → ℕ) (e : Fin 12) : ℤ :=
  if 0 < mark e then
    (if mark e < d.length e then
        headContribution (d.length e - mark e) 0 (h (d.core.head e))
      else headContribution (d.length e) (h (d.core.tail e)) (h (d.core.head e)))
  else headContribution (d.length e) (h (d.core.tail e)) (h (d.core.head e))

theorem slotTailTerm_eq {mark : Fin 12 → ℕ} {h : Fin 8 → ℕ}
    (hprof : Profile d mark h) (hRep : ∀ v : Fin 8, h (d.rep v) = h v)
    (e : Fin 12) :
    slotTailTerm d (heightPotential d h) mark (markValue d mark h) e =
      slotTailForm d mark h e := by
  by_cases hpos : 0 < mark e
  · rw [slotTailTerm_of_marked d (marks_admissible d hprof hRep)
      (markValue_of_pos d hpos)
      (hu := h (d.core.tail e)) (hv := h (d.core.head e))
      (heightPotential_rep d hRep _) (heightPotential_rep d hRep _)
      (hprof.flat e hpos)]
    unfold slotTailForm
    rw [if_pos hpos]
  · have hzero : mark e = 0 := by omega
    rw [slotTailTerm_of_unmarked d hzero (markValue_of_zero d hzero)
      (hu := h (d.core.tail e)) (hv := h (d.core.head e))
      (heightPotential_rep d hRep _) (heightPotential_rep d hRep _)]
    unfold slotTailForm
    rw [if_neg hpos]

theorem slotHeadTerm_eq {mark : Fin 12 → ℕ} {h : Fin 8 → ℕ}
    (hprof : Profile d mark h) (hRep : ∀ v : Fin 8, h (d.rep v) = h v)
    (e : Fin 12) :
    slotHeadTerm d (heightPotential d h) mark (markValue d mark h) e =
      slotHeadForm d mark h e := by
  by_cases hpos : 0 < mark e
  · rw [slotHeadTerm_of_marked d (marks_admissible d hprof hRep)
      (markValue_of_pos d hpos)
      (hu := h (d.core.tail e)) (hv := h (d.core.head e))
      (heightPotential_rep d hRep _) (heightPotential_rep d hRep _)
      (hprof.flat e hpos)]
    unfold slotHeadForm
    rw [if_pos hpos]
  · have hzero : mark e = 0 := by omega
    rw [slotHeadTerm_of_unmarked d hzero (markValue_of_zero d hzero)
      (hu := h (d.core.tail e)) (hv := h (d.core.head e))
      (heightPotential_rep d hRep _) (heightPotential_rep d hRep _)]
    unfold slotHeadForm
    rw [if_neg hpos]

/-! ### Specializations a chamber actually uses

At a marked slot one of the two end heights vanishes.  Which one it is decides
which of the two halves the chamber reads as an arm, and these four lemmas name
the four readings so that a chamber never unfolds `slotTailForm` by hand. -/

section Forms

variable {mark : Fin 12 → ℕ} {h : Fin 8 → ℕ} {e : Fin 12}

/-- The tail end of a slot whose tail height vanishes. -/
theorem slotTailForm_of_flat_tail (htail : h (d.core.tail e) = 0) :
    slotTailForm d mark h e =
      if 0 < mark e then 0
      else tailContribution (d.length e) 0 (h (d.core.head e)) := by
  unfold slotTailForm
  rw [htail]
  by_cases hpos : 0 < mark e
  · rw [if_pos hpos, if_pos hpos, tailContribution_zero_zero]
  · rw [if_neg hpos, if_neg hpos]

/-- The head end of a slot whose head height vanishes.  The extra hypothesis is
free at a marked slot: a mark sitting at the tail carries the tail's height,
which is then zero as well. -/
theorem slotHeadForm_of_flat_head (hhead : h (d.core.head e) = 0)
    (hzero : mark e = 0 → h (d.core.tail e) = 0) :
    slotHeadForm d mark h e =
      if mark e < d.length e then 0
      else headContribution (d.length e) (h (d.core.tail e)) 0 := by
  unfold slotHeadForm
  rw [hhead]
  by_cases hpos : 0 < mark e
  · rw [if_pos hpos]
    by_cases hlt : mark e < d.length e
    · rw [if_pos hlt, if_pos hlt, headContribution_zero_zero]
    · rw [if_neg hlt, if_neg hlt]
  · have hz : mark e = 0 := by omega
    rw [if_neg hpos, hzero hz]
    by_cases hlt : mark e < d.length e
    · rw [if_pos hlt]
      exact headContribution_zero_zero _
    · rw [if_neg hlt]

/-- The near half of a marked slot, read as an arm from the tail. -/
theorem slotTailForm_of_arm (hhead : h (d.core.head e) = 0)
    (hzero : mark e = 0 → h (d.core.tail e) = 0) :
    slotTailForm d mark h e = tailContribution (mark e) (h (d.core.tail e)) 0 := by
  unfold slotTailForm
  by_cases hpos : 0 < mark e
  · rw [if_pos hpos]
  · have hz : mark e = 0 := by omega
    rw [if_neg hpos, hhead, hzero hz, hz]
    simp

/-- The far half of a marked slot, read as an arm from the head. -/
theorem slotHeadForm_of_arm (htail : h (d.core.tail e) = 0)
    (hle : mark e ≤ d.length e)
    (hbound : h (d.core.head e) ≤ d.length e - mark e) :
    slotHeadForm d mark h e =
      headContribution (d.length e - mark e) 0 (h (d.core.head e)) := by
  unfold slotHeadForm
  rw [htail]
  by_cases hpos : 0 < mark e
  · rw [if_pos hpos]
    by_cases hlt : mark e < d.length e
    · rw [if_pos hlt]
    · rw [if_neg hlt, show h (d.core.head e) = 0 by omega]
      simp
  · have hz : mark e = 0 := by omega
    rw [if_neg hpos, hz]
    simp

end Forms

/-- **The endpoint ledger of a chamber.**  Every slot, marked or not, reads as
one or two ordinary arms; a chamber expands this sum against its own core. -/
theorem contribution_eq {mark : Fin 12 → ℕ} {h : Fin 8 → ℕ}
    (hprof : Profile d mark h) (hRep : ∀ v : Fin 8, h (d.rep v) = h v)
    (v : Fin 8) :
    positiveEndpointContribution d (heightPotential d h) mark
        (markValue d mark h) v =
      ∑ e : Fin 12,
        ((if d.core.tail e = v then slotTailForm d mark h e else 0) +
          (if d.core.head e = v then slotHeadForm d mark h e else 0)) := by
  unfold positiveEndpointContribution
  simp only [slotTailTerm_eq d hprof hRep, slotHeadTerm_eq d hprof hRep]

/-! ## From per-vertex coefficients to the residual -/

theorem residual_of_coeff {alloc contrib : Fin 8 → ℤ} {owner : Fin 8}
    (hAll : ∀ v, 0 ≤ alloc v + contrib v)
    (hOwner : 1 ≤ alloc owner + contrib owner) (v : Fin 8) :
    0 ≤ alloc v - indicatorWeight v owner + contrib v := by
  by_cases hv : v = owner
  · subst hv
    simp only [indicatorWeight, if_pos]
    omega
  · have := hAll v
    simp only [indicatorWeight, if_neg hv]
    omega

/-- The hypotheses of the kink lemma, at a mark strictly inside its slot. -/
theorem mark_bounds {mark : Fin 12 → ℕ} {h : Fin 8 → ℕ}
    (hprof : Profile d mark h) (hRep : ∀ v : Fin 8, h (d.rep v) = h v)
    {e : Fin 12} (hpos : 0 < mark e) :
    d.markRiseIn (heightPotential d h) (markValue d mark h) e ≤ (mark e : ℤ) ∧
      -((d.length e - mark e : ℕ) : ℤ) ≤
        d.markRiseOut (heightPotential d h) (markValue d mark h) e ∧
      (d.markRiseIn (heightPotential d h) (markValue d mark h) e = 0 ∨
        d.markRiseOut (heightPotential d h) (markValue d mark h) e = 0) := by
  have hIn : d.markRiseIn (heightPotential d h) (markValue d mark h) e =
      (h (d.core.tail e) : ℤ) := by
    rw [DegSpec.markRiseIn, markValue_of_pos d hpos, heightPotential_rep d hRep]
    ring
  have hOut : d.markRiseOut (heightPotential d h) (markValue d mark h) e =
      -((h (d.core.head e) : ℤ)) := by
    rw [DegSpec.markRiseOut, markValue_of_pos d hpos, heightPotential_rep d hRep]
    ring
  rw [hIn, hOut]
  refine ⟨by exact_mod_cast hprof.inBound e hpos, ?_, ?_⟩
  · have := hprof.outBound e hpos
    omega
  · rcases hprof.flat e hpos with hz | hz
    · exact Or.inl (by rw [hz]; norm_num)
    · exact Or.inr (by rw [hz]; norm_num)

/-- **The local Dhar move of a chamber.**  The divisor is abstract; a chamber
supplies its value on core classes, its nonnegativity at interior vertices, and
the one chip it keeps at each mark. -/
theorem residual_effective {mark : Fin 12 → ℕ} {h : Fin 8 → ℕ}
    (hprof : Profile d mark h) (hRep : ∀ v : Fin 8, h (d.rep v) = h v)
    {D : CFDiv d.graph} {base alloc : Fin 8 → ℤ}
    (hCoreValue : ∀ r : Fin 8, D (d.coreVertex r) =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), base v)
    (hInterior : ∀ (e : Fin 12) (o : Fin (d.length e - 1)),
      0 ≤ D (d.interiorVertex e o))
    (hChip : ∀ (e : Fin 12) (o : Fin (d.length e - 1)),
      o.val + 1 = mark e → mark e < d.length e → 1 ≤ D (d.interiorVertex e o))
    (hAlloc : ∀ r : Fin 8,
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), alloc v =
        ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), base v)
    {center owner : Fin 8} (hOwnerRep : d.rep owner = d.rep center)
    (hLocal : ∀ v : Fin 8, 0 ≤ alloc v - indicatorWeight v owner +
      positiveEndpointContribution d (heightPotential d h) mark
        (markValue d mark h) v) :
    effective (D - oneChip (d.coreVertex center)
      + prin d.graph (script d mark h)) := by
  classical
  have hMarks := marks_admissible d hprof hRep
  intro vertex
  rcases vertex with coreClass | interior
  · obtain ⟨r, hr⟩ := coreClass
    have hVertex : (Sum.inl ⟨r, hr⟩ : d.Vertex) = d.coreVertex r := by
      unfold DegSpec.coreVertex
      congr 1
      exact Subtype.ext hr.symm
    rw [hVertex]
    change 0 ≤ D (d.coreVertex r)
      - oneChip (G := d.graph) (d.coreVertex center) (d.coreVertex r)
      + prin d.graph (script d mark h) (d.coreVertex r)
    rw [hCoreValue r, ← hAlloc r]
    rw [show prin d.graph (script d mark h) (d.coreVertex r) =
        ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
          positiveEndpointContribution d (heightPotential d h) mark
            (markValue d mark h) v from
      (positiveEndpointContribution_classSum_eq d hMarks r).symm]
    have hIndicator := sum_indicatorWeight_class d owner r
    have hOneChip :
        oneChip (G := d.graph) (d.coreVertex center) (d.coreVertex r) =
          ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
            indicatorWeight v owner := by
      rw [hIndicator]
      simp only [oneChip, d.coreVertex_eq_iff]
      rw [hOwnerRep]
      simp only [eq_comm]
    rw [hOneChip, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_nonneg (fun v _ => hLocal v)
  · obtain ⟨edge, offset⟩ := interior
    have hVertex : (Sum.inr ⟨edge, offset⟩ : d.Vertex) =
        d.interiorVertex edge offset := rfl
    rw [hVertex]
    change 0 ≤ D (d.interiorVertex edge offset)
      - oneChip (G := d.graph) (d.coreVertex center) (d.interiorVertex edge offset)
      + prin d.graph (script d mark h) (d.interiorVertex edge offset)
    have hNe : (d.coreVertex center) ≠ d.interiorVertex edge offset := by
      simp [DegSpec.coreVertex, DegSpec.interiorVertex]
    have hZeroChip : oneChip (G := d.graph) (d.coreVertex center)
        (d.interiorVertex edge offset) = 0 := by
      simp only [oneChip, if_neg hNe.symm]
    rw [hZeroChip]
    by_cases hmark : offset.val + 1 = mark edge
    · have hlt : mark edge < d.length edge := by
        have := offset.isLt
        omega
      have hbounds := mark_bounds d hprof hRep (e := edge) (by omega)
      have hprin := d.prin_splitScript_interiorVertex_ge_neg_one hMarks edge offset
        hmark hlt hbounds.1 hbounds.2.1 hbounds.2.2
      have hchip := hChip edge offset hmark hlt
      change 0 ≤ D (d.interiorVertex edge offset) - 0 +
        prin d.graph (d.splitScript (heightPotential d h) mark
          (markValue d mark h)) (d.interiorVertex edge offset)
      omega
    · have hprin := d.prin_splitScript_interiorVertex_nonneg_of_ne hMarks edge
        offset hmark
      have hd := hInterior edge offset
      change 0 ≤ D (d.interiorVertex edge offset) - 0 +
        prin d.graph (d.splitScript (heightPotential d h) mark
          (markValue d mark h)) (d.interiorVertex edge offset)
      omega

/-! ## Divisors with one or two chips inside a slot

A chamber's divisor is a core-class weight plus one chip at each marked slot's
mark.  These wrappers supply the four facts `residual_effective` asks for. -/

section Divisors

/-- A core-class weight plus chips at the marks of two slots. -/
def markedDivisorTwo (W : Fin 8 → ℤ) (mark : Fin 12 → ℕ) (e f : Fin 12) :
    CFDiv d.graph :=
  d.coreClassDivisor W + oneChip (d.pathAt e (mark e))
    + oneChip (d.pathAt f (mark f))

/-- A core-class weight plus a chip at the mark of one slot. -/
def markedDivisorOne (W : Fin 8 → ℤ) (mark : Fin 12 → ℕ) (e : Fin 12) :
    CFDiv d.graph :=
  d.coreClassDivisor W + oneChip (d.pathAt e (mark e))

/-- The core-class weight of a two-mark divisor. -/
def baseTwo (W : Fin 8 → ℤ) (mark : Fin 12 → ℕ) (e f : Fin 12) (v : Fin 8) : ℤ :=
  W v + markChipWeight d mark e v + markChipWeight d mark f v

/-- The core-class weight of a one-mark divisor. -/
def baseOne (W : Fin 8 → ℤ) (mark : Fin 12 → ℕ) (e : Fin 12) (v : Fin 8) : ℤ :=
  W v + markChipWeight d mark e v

variable (W : Fin 8 → ℤ) (mark : Fin 12 → ℕ)

theorem markedDivisorTwo_effective (hW : ∀ v, 0 ≤ W v) (e f : Fin 12) :
    effective (markedDivisorTwo d W mark e f) :=
  (Eff d.graph).add_mem
    ((Eff d.graph).add_mem (d.coreClassDivisor_effective W hW) (eff_one_chip _))
    (eff_one_chip _)

theorem markedDivisorOne_effective (hW : ∀ v, 0 ≤ W v) (e : Fin 12) :
    effective (markedDivisorOne d W mark e) :=
  (Eff d.graph).add_mem (d.coreClassDivisor_effective W hW) (eff_one_chip _)

theorem deg_markedDivisorTwo (e f : Fin 12) :
    deg (markedDivisorTwo d W mark e f) = (∑ v : Fin 8, W v) + 2 := by
  simp only [markedDivisorTwo, deg.map_add, d.deg_coreClassDivisor, deg_one_chip]
  ring

theorem deg_markedDivisorOne (e : Fin 12) :
    deg (markedDivisorOne d W mark e) = (∑ v : Fin 8, W v) + 1 := by
  simp only [markedDivisorOne, deg.map_add, d.deg_coreClassDivisor, deg_one_chip]

theorem baseTwo_nonneg (hW : ∀ v, 0 ≤ W v) (e f : Fin 12) (v : Fin 8) :
    0 ≤ baseTwo d W mark e f v := by
  have h1 := hW v
  have h2 := markChipWeight_nonneg d mark e v
  have h3 := markChipWeight_nonneg d mark f v
  unfold baseTwo
  omega

theorem baseOne_nonneg (hW : ∀ v, 0 ≤ W v) (e : Fin 12) (v : Fin 8) :
    0 ≤ baseOne d W mark e v := by
  have h1 := hW v
  have h2 := markChipWeight_nonneg d mark e v
  unfold baseOne
  omega

theorem markedDivisorTwo_coreVertex (e f : Fin 12) (r : Fin 8) :
    markedDivisorTwo d W mark e f (d.coreVertex r) =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        baseTwo d W mark e f v := by
  classical
  show d.coreClassDivisor W (d.coreVertex r)
      + oneChip (G := d.graph) (d.pathAt e (mark e)) (d.coreVertex r)
      + oneChip (G := d.graph) (d.pathAt f (mark f)) (d.coreVertex r) = _
  rw [d.coreClassDivisor_coreVertex, markChip_classSum_eq d mark e r,
    markChip_classSum_eq d mark f r]
  unfold baseTwo
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

theorem markedDivisorOne_coreVertex (e : Fin 12) (r : Fin 8) :
    markedDivisorOne d W mark e (d.coreVertex r) =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        baseOne d W mark e v := by
  classical
  show d.coreClassDivisor W (d.coreVertex r)
      + oneChip (G := d.graph) (d.pathAt e (mark e)) (d.coreVertex r) = _
  rw [d.coreClassDivisor_coreVertex, markChip_classSum_eq d mark e r]
  unfold baseOne
  rw [Finset.sum_add_distrib]

theorem markedDivisorTwo_interior (hW : ∀ v, 0 ≤ W v) (e f : Fin 12)
    (g : Fin 12) (o : Fin (d.length g - 1)) :
    0 ≤ markedDivisorTwo d W mark e f (d.interiorVertex g o) :=
  markedDivisorTwo_effective d W mark hW e f _

theorem markedDivisorOne_interior (hW : ∀ v, 0 ≤ W v) (e : Fin 12)
    (g : Fin 12) (o : Fin (d.length g - 1)) :
    0 ≤ markedDivisorOne d W mark e (d.interiorVertex g o) :=
  markedDivisorOne_effective d W mark hW e _

/-- The chip a two-mark divisor keeps at each mark.  `hsupp` says the mark
function is supported on the two named slots, which is how a chamber declares
which slots it marks. -/
theorem markedDivisorTwo_chip {e f : Fin 12}
    (hsupp : ∀ g : Fin 12, 0 < mark g → g = e ∨ g = f)
    (g : Fin 12) (o : Fin (d.length g - 1)) (hmark : o.val + 1 = mark g)
    (hlt : mark g < d.length g) :
    1 ≤ markedDivisorTwo d W mark e f (d.interiorVertex g o) := by
  have hpos : 0 < mark g := by omega
  have hpath : d.pathAt g (mark g) = d.interiorVertex g o := by
    rw [d.pathAt_interior (by omega) hlt]
    exact congrArg (d.interiorVertex g) (Fin.ext (by simp; omega))
  show 1 ≤ d.coreClassDivisor W (d.interiorVertex g o)
      + oneChip (G := d.graph) (d.pathAt e (mark e)) (d.interiorVertex g o)
      + oneChip (G := d.graph) (d.pathAt f (mark f)) (d.interiorVertex g o)
  rw [d.coreClassDivisor_interiorVertex]
  rcases hsupp g hpos with rfl | rfl
  · have hz := eff_one_chip (G := d.graph) (d.pathAt f (mark f))
      (d.interiorVertex g o)
    rw [hpath, one_chip_apply_v]
    omega
  · have hz := eff_one_chip (G := d.graph) (d.pathAt e (mark e))
      (d.interiorVertex g o)
    rw [hpath, one_chip_apply_v]
    omega

theorem markedDivisorOne_chip {e : Fin 12}
    (hsupp : ∀ g : Fin 12, 0 < mark g → g = e)
    (g : Fin 12) (o : Fin (d.length g - 1)) (hmark : o.val + 1 = mark g)
    (hlt : mark g < d.length g) :
    1 ≤ markedDivisorOne d W mark e (d.interiorVertex g o) := by
  have hpos : 0 < mark g := by omega
  have hpath : d.pathAt g (mark g) = d.interiorVertex g o := by
    rw [d.pathAt_interior (by omega) hlt]
    exact congrArg (d.interiorVertex g) (Fin.ext (by simp; omega))
  show 1 ≤ d.coreClassDivisor W (d.interiorVertex g o)
      + oneChip (G := d.graph) (d.pathAt e (mark e)) (d.interiorVertex g o)
  rw [d.coreClassDivisor_interiorVertex]
  rcases hsupp g hpos with rfl
  rw [hpath, one_chip_apply_v]
  omega

theorem one_le_markedDivisorTwo_at_chip (e f : Fin 12) (hW : ∀ v, 0 ≤ W v)
    {c : Fin 8} (hc : 1 ≤ W c) :
    1 ≤ markedDivisorTwo d W mark e f (d.coreVertex c) := by
  classical
  rw [markedDivisorTwo_coreVertex]
  have hMem : c ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep c) := by simp
  have hSingle := Finset.single_le_sum
    (s := Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep c))
    (f := baseTwo d W mark e f)
    (fun v _ => baseTwo_nonneg d W mark hW e f v) hMem
  have hval : 1 ≤ baseTwo d W mark e f c := by
    have h2 := markChipWeight_nonneg d mark e c
    have h3 := markChipWeight_nonneg d mark f c
    unfold baseTwo
    omega
  omega

theorem one_le_markedDivisorOne_at_chip (e : Fin 12) (hW : ∀ v, 0 ≤ W v)
    {c : Fin 8} (hc : 1 ≤ W c) :
    1 ≤ markedDivisorOne d W mark e (d.coreVertex c) := by
  classical
  rw [markedDivisorOne_coreVertex]
  have hMem : c ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep c) := by simp
  have hSingle := Finset.single_le_sum
    (s := Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep c))
    (f := baseOne d W mark e)
    (fun v _ => baseOne_nonneg d W mark hW e v) hMem
  have hval : 1 ≤ baseOne d W mark e c := by
    have h2 := markChipWeight_nonneg d mark e c
    unfold baseOne
    omega
  omega

end Divisors

end AtanasovRanganathan.ConfigurationMarkedRow
