/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationMarkedThree
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow05Symmetry

/-!
# The Atanasov--Ranganathan construction on row 05

Row 05 is AR's *sixth* genus-five family: two bananas, each attached by one leg
to each of the two opposite vertices of a four-cycle.

```
 e0, e1 : 0 == 1     e2 : 2 -> 0     e3 : 1 -> 3
 e4 : 2 -> 5   e5 : 3 -> 5   e9 : 4 -> 3   e7 : 2 -> 4        (the square)
 e6 : 5 -> 7   e8 : 4 -> 6   e10, e11 : 6 == 7
```

AR's own figure does not use a core-supported divisor: two of its four chips
sit at interior points of a leg, at an offset equal to another leg's length.
The certificate here is therefore a *marked* script
(`Utilities/Subdivision/SplitRampScript.lean`), which bends downward
at the chip and lets the chip pay for the kink.

The proof below uses the marked divisor displayed in the source and a script
that bends at each interior chip. The chamber hypotheses ensure that the local
configuration lemmas apply.

On chamber A -- `|e2| ≤ |e3|` and `|e6| ≤ |e8|` -- the displayed divisor is

```
 D = [2] + [5] + (e3 at offset |e2| from 1) + (e8 at offset |e8| - |e6| from 4)
```

and the six chip-free vertices fall into three pictures:

* `{0, 1}` and `{6, 7}` -- AR's *seventh* picture, a banana pair whose two arms
  have **equal length** (`|e2|` on the left, `|e6|` on the right).  That equality
  is exactly what the interior chip placement buys.
* `{3, 4}` -- AR's *third* picture, a chip-free pair with two chip arms each,
  read through `ConfigurationMarkedThree`: vertex `3`'s arms are the far half of
  `e3` and the slot `e5`, vertex `4`'s are `e7` and the near half of `e8`.

The other three chambers are the images of this one under the two leg swaps, so
`GenusFiveRow05Symmetry` and `ClosedOrbit.closedConstruction_of_chamber` finish
the closed orthant.
-/

namespace AtanasovRanganathan.GenusFiveRow05

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.DegenerateSpec
open Certificate.DegenerateSpec.DegSpec
open Certificate.StrongSeparator
open Utilities.Certificate.ContractionForestCensusGeneral
open Configurations
open GenusFiveCoreAtlas
open ConfigurationFive
open ConfigurationMarkedThree

/-! ## The two marks

The left chip sits on `e3` at distance `|e2|` from vertex `1`; the right chip
sits on `e8` at distance `|e6|` from vertex `6`, i.e. at offset `|e8| - |e6|`
from vertex `4`. -/

def markL (d : DegSpec 8 12) : ℕ := d.length 2

def markR (d : DegSpec 8 12) : ℕ := d.length 8 - d.length 6

def rowMark (d : DegSpec 8 12) (e : Fin 12) : ℕ :=
  if e = 3 then markL d else if e = 8 then markR d else 0

@[simp] theorem rowMark_three (d : DegSpec 8 12) : rowMark d 3 = markL d := by
  simp [rowMark]

@[simp] theorem rowMark_eight (d : DegSpec 8 12) : rowMark d 8 = markR d := by
  simp [rowMark]

theorem rowMark_other (d : DegSpec 8 12) {e : Fin 12} (h3 : e ≠ 3) (h8 : e ≠ 8) :
    rowMark d e = 0 := by
  simp [rowMark, h3, h8]

theorem marked_of_rowMark_pos (d : DegSpec 8 12) {e : Fin 12}
    (h : 0 < rowMark d e) : e = 3 ∨ e = 8 := by
  by_cases h3 : e = 3
  · exact Or.inl h3
  · by_cases h8 : e = 8
    · exact Or.inr h8
    · rw [rowMark_other d h3 h8] at h; omega

/-! ## The four nested-min heights of the pair `{3, 4}` -/

/-- Vertex `3`'s arm minimum: the far half of `e3`, and `e5`. -/
def armA (d : DegSpec 8 12) : ℕ := min (d.length 3 - markL d) (d.length 5)

/-- Vertex `4`'s arm minimum: `e7`, and the near half of `e8`. -/
def armB (d : DegSpec 8 12) : ℕ := min (d.length 7) (markR d)

/-- The partner height, shared by both readings of the pair. -/
def pairLow (d : DegSpec 8 12) : ℕ := min (armA d) (armB d)

/-- The height at vertex `3` when `3` is the target. -/
def targetThree (d : DegSpec 8 12) : ℕ := min (armA d) (pairLow d + d.length 9)

/-- The height at vertex `4` when `4` is the target. -/
def targetFour (d : DegSpec 8 12) : ℕ := min (armB d) (pairLow d + d.length 9)

/-! ## The four height profiles -/

/-- The left banana pair `{0, 1}`, both arms of length `|e2|`. -/
def heightLB (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 0 then d.length 2 else if v = 1 then d.length 2 else 0

/-- The right banana pair `{6, 7}`, both arms of length `|e6|`. -/
def heightRB (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 6 then d.length 6 else if v = 7 then d.length 6 else 0

/-- The configuration-3 pair read at the target `3`. -/
def heightT3 (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 3 then targetThree d else if v = 4 then pairLow d else 0

/-- The configuration-3 pair read at the target `4`. -/
def heightT4 (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 4 then targetFour d else if v = 3 then pairLow d else 0

/-! ## The script -/

/-- The potential of a height profile, read at the canonical class
representative so that class invariance is definitional. -/
def rowPotential (d : DegSpec 8 12) (h : Fin 8 → ℕ) (v : Fin 8) : ℤ :=
  -((h (d.rep v) : ℤ))

theorem rowPotential_repInvariant (d : DegSpec 8 12) (h : Fin 8 → ℕ) :
    d.RepInvariant (rowPotential d h) := by
  intro v
  simp [rowPotential, d.rep_idem]

/-- The script's value at each mark: zero on the two marked slots (the chips sit
at the ambient level), the tail's own value elsewhere. -/
def rowMarkValue (d : DegSpec 8 12) (h : Fin 8 → ℕ) (e : Fin 12) : ℤ :=
  if e = 3 ∨ e = 8 then 0 else rowPotential d h (d.core.tail e)

theorem rowMarkValue_other (d : DegSpec 8 12) (h : Fin 8 → ℕ) {e : Fin 12}
    (h3 : e ≠ 3) (h8 : e ≠ 8) :
    rowMarkValue d h e = rowPotential d h (d.rep (d.core.tail e)) := by
  simp only [rowMarkValue, h3, h8, or_self, if_false, rowPotential, d.rep_idem]

@[simp] theorem rowMarkValue_three (d : DegSpec 8 12) (h : Fin 8 → ℕ) :
    rowMarkValue d h 3 = 0 := by simp [rowMarkValue]

@[simp] theorem rowMarkValue_eight (d : DegSpec 8 12) (h : Fin 8 → ℕ) :
    rowMarkValue d h 8 = 0 := by simp [rowMarkValue]

/-! ## Class constancy of a profile -/

theorem height_eq_of_zero_edge (d : DegSpec 8 12) (h : Fin 8 → ℕ)
    (hConst : ∀ e : Fin 12, d.length e = 0 →
      h (row05Core.tail e) = h (row05Core.head e))
    {e : Fin 12} (hZero : d.length e = 0) :
    h (row05Core.tail e) = h (row05Core.head e) := hConst e hZero

theorem height_eq_of_reach (d : DegSpec 8 12) (h : Fin 8 → ℕ)
    (hConst : ∀ e : Fin 12, d.length e = 0 →
      h (row05Core.tail e) = h (row05Core.head e))
    (F : Finset (Fin 12))
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0)
    {u v : Fin 8} (hReach : ReachIn row05Core F u v) :
    h u = h v := by
  induction hReach with
  | refl => rfl
  | @tail a b hPrefix hLast ih =>
      rw [ih]
      obtain ⟨e, he, hab | hab⟩ := hLast
      · rw [← hab.1, ← hab.2]
        exact hConst e ((hFZero e).mp ((mem_edgeList F e).mp he))
      · rw [← hab.1, ← hab.2]
        exact (hConst e ((hFZero e).mp ((mem_edgeList F e).mp he))).symm

theorem height_rep_eq (d : DegSpec 8 12) (h : Fin 8 → ℕ)
    (hConst : ∀ e : Fin 12, d.length e = 0 →
      h (row05Core.tail e) = h (row05Core.head e))
    (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8, d.rep x = d.rep y ↔ ReachIn row05Core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0) (v : Fin 8) :
    h (d.rep v) = h v :=
  height_eq_of_reach d h hConst F hFZero ((hRepReach (d.rep v) v).mp (d.rep_idem v))

theorem rowPotential_eq (d : DegSpec 8 12) {h : Fin 8 → ℕ}
    (hRep : ∀ v : Fin 8, h (d.rep v) = h v) (v : Fin 8) :
    rowPotential d h v = -((h v : ℤ)) := by
  rw [rowPotential, hRep]

/-! ## The two marked slots, spelled out -/

section Core

variable {d : DegSpec 8 12} (hCore : d.core = row05Core)
include hCore

theorem tail_three : d.core.tail 3 = 1 := by rw [hCore]; decide
theorem head_three : d.core.head 3 = 3 := by rw [hCore]; decide
theorem tail_eight : d.core.tail 8 = 4 := by rw [hCore]; decide
theorem head_eight : d.core.head 8 = 6 := by rw [hCore]; decide

end Core

section Rises

variable {d : DegSpec 8 12} {h : Fin 8 → ℕ}

theorem riseIn_three (hCore : d.core = row05Core)
    (hRep : ∀ v : Fin 8, h (d.rep v) = h v) :
    d.markRiseIn (rowPotential d h) (rowMarkValue d h) 3 = (h 1 : ℤ) := by
  simp [DegSpec.markRiseIn, tail_three hCore, rowPotential, hRep]

theorem riseOut_three (hCore : d.core = row05Core)
    (hRep : ∀ v : Fin 8, h (d.rep v) = h v) :
    d.markRiseOut (rowPotential d h) (rowMarkValue d h) 3 = -((h 3 : ℤ)) := by
  simp [DegSpec.markRiseOut, head_three hCore, rowPotential, hRep]

theorem riseIn_eight (hCore : d.core = row05Core)
    (hRep : ∀ v : Fin 8, h (d.rep v) = h v) :
    d.markRiseIn (rowPotential d h) (rowMarkValue d h) 8 = (h 4 : ℤ) := by
  simp [DegSpec.markRiseIn, tail_eight hCore, rowPotential, hRep]

theorem riseOut_eight (hCore : d.core = row05Core)
    (hRep : ∀ v : Fin 8, h (d.rep v) = h v) :
    d.markRiseOut (rowPotential d h) (rowMarkValue d h) 8 = -((h 6 : ℤ)) := by
  simp [DegSpec.markRiseOut, head_eight hCore, rowPotential, hRep]

theorem riseIn_other {e : Fin 12} (h3 : e ≠ 3) (h8 : e ≠ 8) :
    d.markRiseIn (rowPotential d h) (rowMarkValue d h) e = 0 := by
  simp [DegSpec.markRiseIn, rowMarkValue_other d h h3 h8]

theorem riseOut_other {e : Fin 12} (h3 : e ≠ 3) (h8 : e ≠ 8)
    (hRep : ∀ v : Fin 8, h (d.rep v) = h v) :
    d.markRiseOut (rowPotential d h) (rowMarkValue d h) e =
      (h (d.core.tail e) : ℤ) - (h (d.core.head e) : ℤ) := by
  rw [DegSpec.markRiseOut, rowMarkValue_other d h h3 h8]
  simp only [rowPotential, hRep]
  ring

end Rises

/-! ## Admissibility of the two marks

`mark 3 ≤ |e3|` is the chamber inequality `|e2| ≤ |e3|`; the degenerate cases
`mark = 0` and `mark = length` are exactly where the profile's height at that
end vanishes. -/

theorem marks_admissible {d : DegSpec 8 12} (hCore : d.core = row05Core)
    {h : Fin 8 → ℕ} (hRep : ∀ v : Fin 8, h (d.rep v) = h v)
    (hL : d.length 2 ≤ d.length 3)
    (hIn3 : h 1 ≤ markL d) (hOut3 : h 3 ≤ d.length 3 - markL d)
    (hIn8 : h 4 ≤ markR d) (hOut8 : h 6 ≤ d.length 8 - markR d) :
    d.MarksAdmissible (rowPotential d h) (rowMark d) (rowMarkValue d h) := by
  intro e
  by_cases h3 : e = 3
  · subst h3
    refine ⟨by simpa [markL] using hL, ?_, ?_⟩
    · intro hz
      rw [riseIn_three hCore hRep]
      rw [rowMark_three] at hz
      omega
    · intro hz
      rw [riseOut_three hCore hRep]
      rw [rowMark_three] at hz
      omega
  · by_cases h8 : e = 8
    · subst h8
      refine ⟨by simp only [rowMark_eight, markR]; omega, ?_, ?_⟩
      · intro hz
        rw [riseIn_eight hCore hRep]
        rw [rowMark_eight] at hz
        omega
      · intro hz
        rw [riseOut_eight hCore hRep]
        rw [rowMark_eight] at hz
        omega
    · refine ⟨by rw [rowMark_other d h3 h8]; omega, ?_, ?_⟩
      · intro _; exact riseIn_other h3 h8
      · intro hz
        rw [rowMark_other d h3 h8] at hz
        rw [riseOut_other h3 h8 hRep]
        have hRepZero := d.rep_zero e hz.symm
        have : h (d.core.tail e) = h (d.core.head e) := by
          rw [← hRep (d.core.tail e), ← hRep (d.core.head e), hRepZero]
        omega

/-! ## Each slot as one or two ordinary arms -/

def slotTailForm (d : DegSpec 8 12) (h : Fin 8 → ℕ) (e : Fin 12) : ℤ :=
  if 0 < rowMark d e then tailContribution (rowMark d e) (h (d.core.tail e)) 0
  else tailContribution (d.length e) (h (d.core.tail e)) (h (d.core.head e))

def slotHeadForm (d : DegSpec 8 12) (h : Fin 8 → ℕ) (e : Fin 12) : ℤ :=
  if e = 3 ∨ e = 8 then
    (if rowMark d e < d.length e then
        headContribution (d.length e - rowMark d e) 0 (h (d.core.head e))
      else headContribution (d.length e) (h (d.core.tail e)) (h (d.core.head e)))
  else headContribution (d.length e) (h (d.core.tail e)) (h (d.core.head e))

theorem slotTailTerm_eq {d : DegSpec 8 12} (hCore : d.core = row05Core)
    {h : Fin 8 → ℕ} (hRep : ∀ v : Fin 8, h (d.rep v) = h v)
    (hMarks : d.MarksAdmissible (rowPotential d h) (rowMark d) (rowMarkValue d h))
    (hflat3 : h 1 = 0 ∨ h 3 = 0) (hflat8 : h 4 = 0 ∨ h 6 = 0) (e : Fin 12) :
    slotTailTerm d (rowPotential d h) (rowMark d) (rowMarkValue d h) e =
      slotTailForm d h e := by
  by_cases h3 : e = 3
  · subst h3
    rw [slotTailTerm_of_marked d hMarks (rowMarkValue_three d h)
      (hu := h 1) (hv := h 3)
      (by simp only [rowPotential, hRep, tail_three hCore])
      (by simp only [rowPotential, hRep, head_three hCore]) hflat3]
    unfold slotTailForm
    rw [tail_three hCore, head_three hCore]
  · by_cases h8 : e = 8
    · subst h8
      rw [slotTailTerm_of_marked d hMarks (rowMarkValue_eight d h)
        (hu := h 4) (hv := h 6)
        (by simp only [rowPotential, hRep, tail_eight hCore])
        (by simp only [rowPotential, hRep, head_eight hCore]) hflat8]
      unfold slotTailForm
      rw [tail_eight hCore, head_eight hCore]
    · rw [slotTailTerm_of_unmarked d (rowMark_other d h3 h8)
        (rowMarkValue_other d h h3 h8)
        (hu := h (d.core.tail e)) (hv := h (d.core.head e))
        (by simp only [rowPotential, hRep]) (by simp only [rowPotential, hRep])]
      unfold slotTailForm
      rw [rowMark_other d h3 h8]
      simp

theorem slotHeadTerm_eq {d : DegSpec 8 12} (hCore : d.core = row05Core)
    {h : Fin 8 → ℕ} (hRep : ∀ v : Fin 8, h (d.rep v) = h v)
    (hMarks : d.MarksAdmissible (rowPotential d h) (rowMark d) (rowMarkValue d h))
    (hflat3 : h 1 = 0 ∨ h 3 = 0) (hflat8 : h 4 = 0 ∨ h 6 = 0) (e : Fin 12) :
    slotHeadTerm d (rowPotential d h) (rowMark d) (rowMarkValue d h) e =
      slotHeadForm d h e := by
  by_cases h3 : e = 3
  · subst h3
    rw [slotHeadTerm_of_marked d hMarks (rowMarkValue_three d h)
      (hu := h 1) (hv := h 3)
      (by simp only [rowPotential, hRep, tail_three hCore])
      (by simp only [rowPotential, hRep, head_three hCore]) hflat3]
    unfold slotHeadForm
    rw [if_pos (Or.inl rfl), tail_three hCore, head_three hCore]
  · by_cases h8 : e = 8
    · subst h8
      rw [slotHeadTerm_of_marked d hMarks (rowMarkValue_eight d h)
        (hu := h 4) (hv := h 6)
        (by simp only [rowPotential, hRep, tail_eight hCore])
        (by simp only [rowPotential, hRep, head_eight hCore]) hflat8]
      unfold slotHeadForm
      rw [if_pos (Or.inr rfl), tail_eight hCore, head_eight hCore]
    · rw [slotHeadTerm_of_unmarked d (rowMark_other d h3 h8)
        (rowMarkValue_other d h h3 h8)
        (hu := h (d.core.tail e)) (hv := h (d.core.head e))
        (by simp only [rowPotential, hRep]) (by simp only [rowPotential, hRep])]
      unfold slotHeadForm
      rw [if_neg (by tauto)]

/-! ## The endpoint ledger, vertex by vertex -/

def contribForm (d : DegSpec 8 12) (h : Fin 8 → ℕ) (v : Fin 8) : ℤ :=
  if v = 0 then
    tailContribution (d.length 0) (h 0) (h 1) + tailContribution (d.length 1) (h 0) (h 1)
      + headContribution (d.length 2) (h 2) (h 0)
  else if v = 1 then
    slotTailForm d h 3 + headContribution (d.length 0) (h 0) (h 1)
      + headContribution (d.length 1) (h 0) (h 1)
  else if v = 2 then
    tailContribution (d.length 2) (h 2) (h 0) + tailContribution (d.length 4) (h 2) (h 5)
      + tailContribution (d.length 7) (h 2) (h 4)
  else if v = 3 then
    tailContribution (d.length 5) (h 3) (h 5) + slotHeadForm d h 3
      + headContribution (d.length 9) (h 4) (h 3)
  else if v = 4 then
    slotTailForm d h 8 + tailContribution (d.length 9) (h 4) (h 3)
      + headContribution (d.length 7) (h 2) (h 4)
  else if v = 5 then
    tailContribution (d.length 6) (h 5) (h 7) + headContribution (d.length 4) (h 2) (h 5)
      + headContribution (d.length 5) (h 3) (h 5)
  else if v = 6 then
    tailContribution (d.length 10) (h 6) (h 7) + tailContribution (d.length 11) (h 6) (h 7)
      + slotHeadForm d h 8
  else
    headContribution (d.length 6) (h 5) (h 7) + headContribution (d.length 10) (h 6) (h 7)
      + headContribution (d.length 11) (h 6) (h 7)

theorem contrib_eq {d : DegSpec 8 12} (hCore : d.core = row05Core)
    {h : Fin 8 → ℕ} (hRep : ∀ v : Fin 8, h (d.rep v) = h v)
    (hMarks : d.MarksAdmissible (rowPotential d h) (rowMark d) (rowMarkValue d h))
    (hflat3 : h 1 = 0 ∨ h 3 = 0) (hflat8 : h 4 = 0 ∨ h 6 = 0) (v : Fin 8) :
    positiveEndpointContribution d (rowPotential d h) (rowMark d)
        (rowMarkValue d h) v = contribForm d h v := by
  unfold positiveEndpointContribution
  simp only [slotTailTerm_eq hCore hRep hMarks hflat3 hflat8,
    slotHeadTerm_eq hCore hRep hMarks hflat3 hflat8]
  fin_cases v <;>
    simp +decide only [hCore, row05Core, Fin.isValue, Fin.zero_eta, slotTailForm, rowMark,
      slotHeadForm, Fin.sum_univ_succ, ↓reduceIte, lt_self_iff_false, Matrix.cons_val_zero,
      add_zero, Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, zero_add,
      Finset.univ_unique, Fin.default_eq_zero, Matrix.cons_val_fin_one, Fin.reduceEq,
      Finset.sum_const_zero, contribForm, Fin.mk_one, Fin.reduceSucc, Matrix.cons_val,
      Fin.reduceFinMk, Finset.sum_singleton]<;> ring

/-! ## The displayed divisor -/

def chipWeight (v : Fin 8) : ℤ := if v = 2 then 1 else if v = 5 then 1 else 0

theorem chipWeight_nonneg (v : Fin 8) : 0 ≤ chipWeight v := by
  unfold chipWeight; split_ifs <;> norm_num

theorem sum_chipWeight : ∑ v : Fin 8, chipWeight v = 2 := by decide

/-- AR's divisor on chamber A: chips at the two square vertices `2` and `5`,
and one chip inside each of the two marked legs. -/
def rowDivisor (d : DegSpec 8 12) : CFDiv d.graph :=
  d.coreClassDivisor chipWeight + one_chip (d.pathAt 3 (rowMark d 3))
    + one_chip (d.pathAt 8 (rowMark d 8))

theorem rowDivisor_effective (d : DegSpec 8 12) : effective (rowDivisor d) :=
  (Eff d.graph).add_mem
    ((Eff d.graph).add_mem
      (d.coreClassDivisor_effective chipWeight chipWeight_nonneg)
      (eff_one_chip _))
    (eff_one_chip _)

theorem rowDivisor_degree (d : DegSpec 8 12) : deg (rowDivisor d) = 4 := by
  simp only [rowDivisor, deg.map_add, d.deg_coreClassDivisor, sum_chipWeight,
    deg_one_chip]
  norm_num

/-- The core-class weight of the divisor: the two square chips, plus each
marked chip when its mark has reached an end of its slot. -/
def baseWeight (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  chipWeight v + markChipWeight d (rowMark d) 3 v + markChipWeight d (rowMark d) 8 v

theorem baseWeight_nonneg (d : DegSpec 8 12) (v : Fin 8) : 0 ≤ baseWeight d v := by
  have h1 := chipWeight_nonneg v
  have h2 := markChipWeight_nonneg d (rowMark d) 3 v
  have h3 := markChipWeight_nonneg d (rowMark d) 8 v
  unfold baseWeight
  omega

theorem rowDivisor_coreVertex_eq (d : DegSpec 8 12) (r : Fin 8) :
    rowDivisor d (d.coreVertex r) =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        baseWeight d v := by
  classical
  show d.coreClassDivisor chipWeight (d.coreVertex r)
      + one_chip (G := d.graph) (d.pathAt 3 (rowMark d 3)) (d.coreVertex r)
      + one_chip (G := d.graph) (d.pathAt 8 (rowMark d 8)) (d.coreVertex r) = _
  rw [d.coreClassDivisor_coreVertex, markChip_classSum_eq d (rowMark d) 3 r,
    markChip_classSum_eq d (rowMark d) 8 r]
  unfold baseWeight
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

theorem rowDivisor_interiorVertex (d : DegSpec 8 12) (e : Fin 12)
    (o : Fin (d.length e - 1)) :
    rowDivisor d (d.interiorVertex e o) =
      one_chip (G := d.graph) (d.pathAt 3 (rowMark d 3)) (d.interiorVertex e o)
        + one_chip (G := d.graph) (d.pathAt 8 (rowMark d 8)) (d.interiorVertex e o) := by
  show d.coreClassDivisor chipWeight (d.interiorVertex e o) + _ + _ = _
  rw [d.coreClassDivisor_interiorVertex]
  ring

theorem one_le_rowDivisor_at_chip (d : DegSpec 8 12) {c : Fin 8}
    (hc : chipWeight c = 1) : 1 ≤ rowDivisor d (d.coreVertex c) := by
  rw [rowDivisor_coreVertex_eq]
  refine d.one_le_classSum_of_chip (baseWeight d) (baseWeight_nonneg d) ?_
  have h2 := markChipWeight_nonneg d (rowMark d) 3 c
  have h3 := markChipWeight_nonneg d (rowMark d) 8 c
  unfold baseWeight
  rw [hc]
  omega

/-- The chip at a mark strictly inside its slot. -/
theorem one_le_rowDivisor_at_mark (d : DegSpec 8 12) {e : Fin 12}
    {o : Fin (d.length e - 1)} (hmark : o.val + 1 = rowMark d e)
    (hlt : rowMark d e < d.length e) :
    1 ≤ rowDivisor d (d.interiorVertex e o) := by
  have hpos : 0 < rowMark d e := by omega
  have hpath : d.pathAt e (rowMark d e) = d.interiorVertex e o := by
    rw [d.pathAt_interior (by omega) hlt]
    exact congrArg (d.interiorVertex e) (Fin.ext (by simp; omega))
  rw [rowDivisor_interiorVertex]
  rcases marked_of_rowMark_pos d hpos with h3 | h8
  · subst h3
    have hz := eff_one_chip (G := d.graph) (d.pathAt 8 (rowMark d 8))
      (d.interiorVertex 3 o)
    rw [hpath, one_chip_apply_v]
    omega
  · subst h8
    have hz := eff_one_chip (G := d.graph) (d.pathAt 3 (rowMark d 3))
      (d.interiorVertex 8 o)
    rw [hpath, one_chip_apply_v]
    omega

/-! ## The two chip allocations

The banana pictures charge the divisor exactly as it stands; the
configuration-3 pair moves each collapsed arm's chip onto the centre it feeds,
which is a transfer inside a contracted class and so leaves every class sum
alone. -/

def pairAlloc (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  baseWeight d v
    + (if d.length 3 = 0 then transferWeight 1 3 v else 0)
    + (if d.length 5 = 0 then transferWeight 5 3 v else 0)
    + (if d.length 7 = 0 then transferWeight 2 4 v else 0)

theorem baseWeight_classSum (d : DegSpec 8 12) (r : Fin 8) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), baseWeight d v =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), baseWeight d v := rfl

theorem pairAlloc_classSum (d : DegSpec 8 12) (hCore : d.core = row05Core)
    (r : Fin 8) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), pairAlloc d v =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        baseWeight d v := by
  classical
  have h3 : d.length 3 = 0 → d.rep 1 = d.rep 3 := by
    intro hz
    have h := d.rep_zero 3 hz
    rwa [tail_three hCore, head_three hCore] at h
  have h5 : d.length 5 = 0 → d.rep 5 = d.rep 3 := by
    intro hz
    have h := d.rep_zero 5 hz
    rw [hCore] at h
    simpa [row05Core] using h.symm
  have h7 : d.length 7 = 0 → d.rep 2 = d.rep 4 := by
    intro hz
    have h := d.rep_zero 7 hz
    rw [hCore] at h
    simpa [row05Core] using h
  simp only [pairAlloc, Finset.sum_add_distrib]
  rw [sum_conditional_transfer_eq_zero d _ 1 3 h3 r,
    sum_conditional_transfer_eq_zero d _ 5 3 h5 r,
    sum_conditional_transfer_eq_zero d _ 2 4 h7 r]
  simp

/-! ## The slot forms of the two marked legs, under a profile -/

theorem slotTailForm_three_eq {d : DegSpec 8 12} (hCore : d.core = row05Core)
    {h : Fin 8 → ℕ} (hHeadZero : h 3 = 0) (hIn3 : h 1 ≤ markL d) :
    slotTailForm d h 3 = tailContribution (markL d) (h 1) 0 := by
  unfold slotTailForm
  rw [rowMark_three, tail_three hCore, head_three hCore, hHeadZero]
  by_cases hm : 0 < markL d
  · rw [if_pos hm]
  · rw [if_neg hm, show h 1 = 0 by omega, show markL d = 0 by omega]
    simp

theorem slotHeadForm_three_eq {d : DegSpec 8 12} (hCore : d.core = row05Core)
    {h : Fin 8 → ℕ} (hTailZero : h 1 = 0)
    (hOut3 : h 3 ≤ d.length 3 - markL d) :
    slotHeadForm d h 3 = headContribution (d.length 3 - markL d) 0 (h 3) := by
  unfold slotHeadForm
  rw [if_pos (Or.inl rfl), rowMark_three, tail_three hCore, head_three hCore,
    hTailZero]
  by_cases hlt : markL d < d.length 3
  · rw [if_pos hlt]
  · rw [if_neg hlt, show h 3 = 0 by omega]
    simp

theorem slotTailForm_eight_eq {d : DegSpec 8 12} (hCore : d.core = row05Core)
    {h : Fin 8 → ℕ} (hHeadZero : h 6 = 0) (hIn8 : h 4 ≤ markR d) :
    slotTailForm d h 8 = tailContribution (markR d) (h 4) 0 := by
  unfold slotTailForm
  rw [rowMark_eight, tail_eight hCore, head_eight hCore, hHeadZero]
  by_cases hm : 0 < markR d
  · rw [if_pos hm]
  · rw [if_neg hm, show h 4 = 0 by omega, show markR d = 0 by omega]
    simp

theorem slotHeadForm_eight_eq {d : DegSpec 8 12} (hCore : d.core = row05Core)
    {h : Fin 8 → ℕ} (hTailZero : h 4 = 0)
    (hOut8 : h 6 ≤ d.length 8 - markR d) :
    slotHeadForm d h 8 = headContribution (d.length 8 - markR d) 0 (h 6) := by
  unfold slotHeadForm
  rw [if_pos (Or.inr rfl), rowMark_eight, tail_eight hCore, head_eight hCore,
    hTailZero]
  by_cases hlt : markR d < d.length 8
  · rw [if_pos hlt]
  · rw [if_neg hlt, show h 6 = 0 by omega]
    simp

/-- The tail of the left marked leg, with the split kept: the profiles of the
pair `{3, 4}` have a nonzero height at the far end. -/
theorem slotTailForm_three_split {d : DegSpec 8 12} (hCore : d.core = row05Core)
    (h : Fin 8 → ℕ) :
    slotTailForm d h 3 =
      if 0 < markL d then tailContribution (markL d) (h 1) 0
      else tailContribution (d.length 3) (h 1) (h 3) := by
  unfold slotTailForm
  rw [rowMark_three, tail_three hCore, head_three hCore]

theorem slotHeadForm_eight_split {d : DegSpec 8 12} (hCore : d.core = row05Core)
    (h : Fin 8 → ℕ) :
    slotHeadForm d h 8 =
      if markR d < d.length 8 then headContribution (d.length 8 - markR d) 0 (h 6)
      else headContribution (d.length 8) (h 4) (h 6) := by
  unfold slotHeadForm
  rw [if_pos (Or.inr rfl), rowMark_eight, tail_eight hCore, head_eight hCore]

theorem slotTailForm_eight_split {d : DegSpec 8 12} (hCore : d.core = row05Core)
    (h : Fin 8 → ℕ) :
    slotTailForm d h 8 =
      if 0 < markR d then tailContribution (markR d) (h 4) 0
      else tailContribution (d.length 8) (h 4) (h 6) := by
  unfold slotTailForm
  rw [rowMark_eight, tail_eight hCore, head_eight hCore]

theorem slotHeadForm_three_split {d : DegSpec 8 12} (hCore : d.core = row05Core)
    (h : Fin 8 → ℕ) :
    slotHeadForm d h 3 =
      if markL d < d.length 3 then headContribution (d.length 3 - markL d) 0 (h 3)
      else headContribution (d.length 3) (h 1) (h 3) := by
  unfold slotHeadForm
  rw [if_pos (Or.inl rfl), rowMark_three, tail_three hCore, head_three hCore]

/-! ## The core-class weights, vertex by vertex -/

theorem baseWeight_eq {d : DegSpec 8 12} (hCore : d.core = row05Core) (v : Fin 8) :
    baseWeight d v = chipWeight v
      + (if markL d = 0 then (if v = 1 then (1 : ℤ) else 0)
          else if d.length 3 ≤ markL d then (if v = 3 then (1 : ℤ) else 0) else 0)
      + (if markR d = 0 then (if v = 4 then (1 : ℤ) else 0)
          else if d.length 8 ≤ markR d then (if v = 6 then (1 : ℤ) else 0) else 0) := by
  unfold baseWeight markChipWeight
  rw [rowMark_three, rowMark_eight, tail_three hCore, head_three hCore,
    tail_eight hCore, head_eight hCore]

/-! ## The banana pair `{0, 1}` -/

theorem heightLB_const (d : DegSpec 8 12) (hL : d.length 2 ≤ d.length 3) (e : Fin 12) :
    d.length e = 0 →
      heightLB d (row05Core.tail e) = heightLB d (row05Core.head e) := by
  fin_cases e
  all_goals simp [heightLB, row05Core]
  all_goals omega

/-- The per-vertex coefficient of the left banana script. -/
def lbCoeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then headContribution (markL d) 0 (markL d)
  else if v = 1 then zeroChip (markL d) + tailContribution (markL d) (markL d) 0
  else if v = 2 then 1 + tailContribution (markL d) 0 (markL d)
  else if v = 3 then
    (if markL d = 0 then (0 : ℤ) else if d.length 3 ≤ markL d then 1 else 0)
      + (if markL d < d.length 3 then (0 : ℤ)
          else headContribution (d.length 3) (markL d) 0)
  else if v = 4 then zeroChip (markR d)
  else if v = 5 then 1
  else if v = 6 then
    (if markR d = 0 then (0 : ℤ) else if d.length 8 ≤ markR d then 1 else 0)
  else 0

theorem lbCoeff_eq {d : DegSpec 8 12} (hCore : d.core = row05Core) (v : Fin 8) :
    baseWeight d v + contribForm d (heightLB d) v = lbCoeff d v := by
  have hT3 := slotTailForm_three_eq hCore (h := heightLB d)
    (by simp [heightLB]) (by simp [heightLB, markL])
  have hH3 := slotHeadForm_three_split hCore (heightLB d)
  have hT8 := slotTailForm_eight_eq hCore (h := heightLB d)
    (by simp [heightLB]) (by simp [heightLB])
  have hH8 := slotHeadForm_eight_eq hCore (h := heightLB d)
    (by simp [heightLB]) (by simp [heightLB])
  rw [baseWeight_eq hCore]
  fin_cases v
  all_goals simp [lbCoeff, contribForm, heightLB, chipWeight, zeroChip,
    markL, markR, hT3, hH3, hT8, hH8]
  all_goals (try (first | ring1 | ring_nf))
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals (first | ring | omega)

theorem lbCoeff_nonneg {d : DegSpec 8 12} (hL : d.length 2 ≤ d.length 3) (v : Fin 8) :
    0 ≤ lbCoeff d v := by
  have hM : markL d = d.length 2 := rfl
  fin_cases v
  · show (0 : ℤ) ≤ headContribution (markL d) 0 (markL d)
    exact headContribution_nonneg (Nat.zero_le _) (by omega)
  · show (0 : ℤ) ≤ zeroChip (markL d) + tailContribution (markL d) (markL d) 0
    have := zeroChip_add_tail_full (markL d)
    omega
  · show (0 : ℤ) ≤ 1 + tailContribution (markL d) 0 (markL d)
    have := tailContribution_ge_neg_one (L := markL d) (hu := 0) (hv := markL d)
      (by omega) (by omega)
    omega
  · show (0 : ℤ) ≤
      (if markL d = 0 then (0 : ℤ) else if d.length 3 ≤ markL d then 1 else 0)
        + (if markL d < d.length 3 then (0 : ℤ)
            else headContribution (d.length 3) (markL d) 0)
    by_cases hlt : markL d < d.length 3
    · rw [if_pos hlt, if_neg (by omega : ¬ d.length 3 ≤ markL d)]
      split_ifs <;> norm_num
    · rw [if_neg hlt, if_pos (by omega : d.length 3 ≤ markL d)]
      have hEq : markL d = d.length 3 := by omega
      have hHead := positiveChip_add_head_nonneg (L := d.length 3) (h := markL d)
        (by omega)
      by_cases hz : markL d = 0
      · rw [if_pos hz]
        have : d.length 3 = 0 := by omega
        simp [headContribution, this]
      · rw [if_neg hz]
        have : positiveChip (d.length 3) = 1 := by simp [positiveChip]; omega
        omega
  · show (0 : ℤ) ≤ zeroChip (markR d)
    exact zeroChip_nonneg _
  · show (0 : ℤ) ≤ (1 : ℤ)
    norm_num
  · show (0 : ℤ) ≤
      (if markR d = 0 then (0 : ℤ) else if d.length 8 ≤ markR d then 1 else 0)
    split_ifs <;> norm_num
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num

/-- The vertex of the class of `0` that owns the delivered chip. -/
def ownerZero (d : DegSpec 8 12) : Fin 8 := if d.length 2 = 0 then 2 else 0

theorem lbCoeff_owner_zero {d : DegSpec 8 12} : 1 ≤ lbCoeff d (ownerZero d) := by
  have hM : markL d = d.length 2 := rfl
  unfold ownerZero
  by_cases hz : d.length 2 = 0
  · rw [if_pos hz]
    show (1 : ℤ) ≤ 1 + tailContribution (markL d) 0 (markL d)
    have : markL d = 0 := by omega
    rw [this]
    simp [tailContribution]
  · rw [if_neg hz]
    show (1 : ℤ) ≤ headContribution (markL d) 0 (markL d)
    rw [headContribution_eq_one_of_full (L := markL d) (hu := 0) (hv := markL d)
      (by omega) (by omega)]

theorem lbCoeff_owner_one {d : DegSpec 8 12} : 1 ≤ lbCoeff d 1 := by
  show (1 : ℤ) ≤ zeroChip (markL d) + tailContribution (markL d) (markL d) 0
  exact zeroChip_add_tail_full (markL d)

/-! ## The banana pair `{6, 7}` -/

theorem heightRB_const (d : DegSpec 8 12) (hR : d.length 6 ≤ d.length 8) (e : Fin 12) :
    d.length e = 0 →
      heightRB d (row05Core.tail e) = heightRB d (row05Core.head e) := by
  fin_cases e
  all_goals simp [heightRB, row05Core]
  all_goals omega

def rbCoeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then 0
  else if v = 1 then zeroChip (markL d)
  else if v = 2 then 1
  else if v = 3 then
    (if markL d = 0 then (0 : ℤ) else if d.length 3 ≤ markL d then 1 else 0)
  else if v = 4 then zeroChip (markR d)
      + (if 0 < markR d then (0 : ℤ)
          else tailContribution (d.length 8) 0 (d.length 6))
  else if v = 5 then 1 + tailContribution (d.length 6) 0 (d.length 6)
  else if v = 6 then
    (if markR d = 0 then (0 : ℤ) else if d.length 8 ≤ markR d then 1 else 0)
      + headContribution (d.length 8 - markR d) 0 (d.length 6)
  else headContribution (d.length 6) 0 (d.length 6)

theorem rbCoeff_eq {d : DegSpec 8 12} (hCore : d.core = row05Core)
    (hR : d.length 6 ≤ d.length 8) (v : Fin 8) :
    baseWeight d v + contribForm d (heightRB d) v = rbCoeff d v := by
  have hT3 := slotTailForm_three_eq hCore (h := heightRB d)
    (by simp [heightRB]) (by simp [heightRB])
  have hH3 := slotHeadForm_three_eq hCore (h := heightRB d)
    (by simp [heightRB]) (by simp [heightRB])
  have hT8 := slotTailForm_eight_split hCore (heightRB d)
  have hH8 := slotHeadForm_eight_eq hCore (h := heightRB d)
    (by simp [heightRB]) (by simp [heightRB, markR]; omega)
  rw [baseWeight_eq hCore]
  fin_cases v
  all_goals simp [rbCoeff, contribForm, heightRB, chipWeight, zeroChip,
    markL, markR, hT3, hH3, hT8, hH8]
  all_goals (try (first | ring1 | ring_nf))
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals (first | ring | omega)

theorem rbCoeff_nonneg {d : DegSpec 8 12} (hR : d.length 6 ≤ d.length 8) (v : Fin 8) :
    0 ≤ rbCoeff d v := by
  have hN : markR d = d.length 8 - d.length 6 := rfl
  fin_cases v
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ zeroChip (markL d)
    exact zeroChip_nonneg _
  · show (0 : ℤ) ≤ (1 : ℤ)
    norm_num
  · show (0 : ℤ) ≤
      (if markL d = 0 then (0 : ℤ) else if d.length 3 ≤ markL d then 1 else 0)
    split_ifs <;> norm_num
  · show (0 : ℤ) ≤ zeroChip (markR d)
      + (if 0 < markR d then (0 : ℤ)
          else tailContribution (d.length 8) 0 (d.length 6))
    by_cases hp : 0 < markR d
    · rw [if_pos hp]
      have := zeroChip_nonneg (markR d)
      omega
    · rw [if_neg hp]
      have hz : zeroChip (markR d) = 1 := by simp [zeroChip]; omega
      have := tailContribution_ge_neg_one (L := d.length 8) (hu := 0)
        (hv := d.length 6) (by omega) (by omega)
      omega
  · show (0 : ℤ) ≤ 1 + tailContribution (d.length 6) 0 (d.length 6)
    have := tailContribution_ge_neg_one (L := d.length 6) (hu := 0)
      (hv := d.length 6) (by omega) (by omega)
    omega
  · show (0 : ℤ) ≤
      (if markR d = 0 then (0 : ℤ) else if d.length 8 ≤ markR d then 1 else 0)
        + headContribution (d.length 8 - markR d) 0 (d.length 6)
    have := headContribution_nonneg (L := d.length 8 - markR d) (hu := 0)
      (hv := d.length 6) (Nat.zero_le _) (by omega)
    split_ifs <;> omega
  · show (0 : ℤ) ≤ headContribution (d.length 6) 0 (d.length 6)
    exact headContribution_nonneg (Nat.zero_le _) (by omega)

def ownerSix (d : DegSpec 8 12) : Fin 8 := if d.length 8 = 0 then 4 else 6

def ownerSeven (d : DegSpec 8 12) : Fin 8 := if d.length 6 = 0 then 5 else 7

theorem rbCoeff_owner_seven {d : DegSpec 8 12} (_hR : d.length 6 ≤ d.length 8) :
    1 ≤ rbCoeff d (ownerSeven d) := by
  unfold ownerSeven
  by_cases hz : d.length 6 = 0
  · rw [if_pos hz]
    show (1 : ℤ) ≤ 1 + tailContribution (d.length 6) 0 (d.length 6)
    rw [hz]
    simp [tailContribution]
  · rw [if_neg hz]
    show (1 : ℤ) ≤ headContribution (d.length 6) 0 (d.length 6)
    rw [headContribution_eq_one_of_full (L := d.length 6) (hu := 0)
      (hv := d.length 6) (by omega) (by omega)]

theorem rbCoeff_owner_six {d : DegSpec 8 12} (hR : d.length 6 ≤ d.length 8) :
    1 ≤ rbCoeff d (ownerSix d) := by
  have hN : markR d = d.length 8 - d.length 6 := rfl
  unfold ownerSix
  by_cases hz : d.length 8 = 0
  · rw [if_pos hz]
    show (1 : ℤ) ≤ zeroChip (markR d)
      + (if 0 < markR d then (0 : ℤ)
          else tailContribution (d.length 8) 0 (d.length 6))
    have hm : markR d = 0 := by omega
    rw [if_neg (by omega), hm, hz, show d.length 6 = 0 by omega]
    simp [zeroChip, tailContribution]
  · rw [if_neg hz]
    show (1 : ℤ) ≤
      (if markR d = 0 then (0 : ℤ) else if d.length 8 ≤ markR d then 1 else 0)
        + headContribution (d.length 8 - markR d) 0 (d.length 6)
    by_cases h6 : d.length 6 = 0
    · have hm : markR d = d.length 8 := by omega
      rw [if_neg (by omega), if_pos (by omega), hm]
      rw [show d.length 8 - d.length 8 = 0 by omega, h6]
      simp [headContribution]
    · have hOne := headContribution_eq_one_of_full (L := d.length 8 - markR d)
        (hu := 0) (hv := d.length 6) (by omega) (by omega)
      rw [hOne]
      split_ifs <;> omega

/-! ## The configuration-3 pair `{3, 4}`, read at the target `3` -/

theorem heightT3_const (d : DegSpec 8 12) (hL : d.length 2 ≤ d.length 3)
    (hR : d.length 6 ≤ d.length 8) (e : Fin 12) :
    d.length e = 0 →
      heightT3 d (row05Core.tail e) = heightT3 d (row05Core.head e) := by
  fin_cases e
  all_goals simp [heightT3, targetThree, pairLow, armA, armB, markL, markR,
    row05Core]
  all_goals omega

def t3Coeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then 0
  else if v = 1 then (zeroChip (markL d) - zeroChip (d.length 3))
      + (if 0 < markL d then (0 : ℤ)
          else tailContribution (d.length 3) 0 (targetThree d))
  else if v = 2 then positiveChip (d.length 7)
      + tailContribution (d.length 7) 0 (pairLow d)
  else if v = 3 then
    zeroChip (d.length 3 - markL d) + zeroChip (d.length 5)
      + (tailContribution (d.length 5) (targetThree d) 0
          + headContribution (d.length 3 - markL d) 0 (targetThree d)
          + headContribution (d.length 9) (pairLow d) (targetThree d))
  else if v = 4 then
    zeroChip (d.length 7) + zeroChip (markR d)
      + (headContribution (d.length 7) 0 (pairLow d)
          + tailContribution (markR d) (pairLow d) 0
          + tailContribution (d.length 9) (pairLow d) (targetThree d))
  else if v = 5 then positiveChip (d.length 5)
      + headContribution (d.length 5) (targetThree d) 0
  else if v = 6 then
    (if markR d = 0 then (0 : ℤ) else if d.length 8 ≤ markR d then 1 else 0)
      + (if markR d < d.length 8 then (0 : ℤ)
          else headContribution (d.length 8) (pairLow d) 0)
  else 0

theorem t3Coeff_eq {d : DegSpec 8 12} (hCore : d.core = row05Core)
    (hL : d.length 2 ≤ d.length 3) (hR : d.length 6 ≤ d.length 8) (v : Fin 8) :
    pairAlloc d v + contribForm d (heightT3 d) v = t3Coeff d v := by
  have hT3 := slotTailForm_three_split hCore (heightT3 d)
  have hH3 := slotHeadForm_three_eq hCore (h := heightT3 d)
    (by simp [heightT3])
    (by simp [heightT3, targetThree, armA, markL])
  have hT8 := slotTailForm_eight_eq hCore (h := heightT3 d)
    (by simp [heightT3])
    (by simp [heightT3, pairLow, armB])
  have hH8 := slotHeadForm_eight_split hCore (heightT3 d)
  simp only [pairAlloc]
  rw [baseWeight_eq hCore]
  fin_cases v
  all_goals simp [t3Coeff, contribForm, heightT3, chipWeight, zeroChip,
    positiveChip, transferWeight, indicatorWeight, markL, markR,
    hT3, hH3, hT8, hH8]
  all_goals (try (first | ring1 | ring_nf))
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals (first | ring | omega)

theorem t3Coeff_nonneg {d : DegSpec 8 12} (hL : d.length 2 ≤ d.length 3)
    (hR : d.length 6 ≤ d.length 8) (v : Fin 8) :
    0 ≤ t3Coeff d v := by
  have hA1 : armA d ≤ d.length 3 - markL d := Nat.min_le_left _ _
  have hA2 : armA d ≤ d.length 5 := Nat.min_le_right _ _
  have hB1 : armB d ≤ d.length 7 := Nat.min_le_left _ _
  have hB2 : armB d ≤ markR d := Nat.min_le_right _ _
  have hg1 : pairLow d ≤ armA d := Nat.min_le_left _ _
  have hg2 : pairLow d ≤ armB d := Nat.min_le_right _ _
  have hO1 : targetThree d ≤ armA d := Nat.min_le_left _ _
  have hN : markR d ≤ d.length 8 := by simp only [markR]; omega
  fin_cases v
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ (zeroChip (markL d) - zeroChip (d.length 3))
      + (if 0 < markL d then (0 : ℤ)
          else tailContribution (d.length 3) 0 (targetThree d))
    by_cases hp : 0 < markL d
    · rw [if_pos hp]
      have hm : markL d = d.length 2 := rfl
      have h1 : zeroChip (markL d) = 0 := by
        have hne : markL d ≠ 0 := by omega
        simp [zeroChip, hne]
      have h2 : zeroChip (d.length 3) = 0 := by
        have hne : d.length 3 ≠ 0 := by omega
        simp [zeroChip, hne]
      omega
    · rw [if_neg hp]
      have h1 : zeroChip (markL d) = 1 := by
        have hz : markL d = 0 := by omega
        simp [zeroChip, hz]
      have hpos := positiveChip_add_tail_nonneg (L := d.length 3)
        (h := targetThree d) (by omega)
      have h2 : positiveChip (d.length 3) = 1 - zeroChip (d.length 3) := by
        unfold positiveChip zeroChip
        split_ifs <;> omega
      omega
  · show (0 : ℤ) ≤ positiveChip (d.length 7)
      + tailContribution (d.length 7) 0 (pairLow d)
    exact positiveChip_add_tail_nonneg (by omega)
  · show (0 : ℤ) ≤ zeroChip (d.length 3 - markL d) + zeroChip (d.length 5)
      + (tailContribution (d.length 5) (targetThree d) 0
          + headContribution (d.length 3 - markL d) 0 (targetThree d)
          + headContribution (d.length 9) (pairLow d) (targetThree d))
    have hpair := pairTarget_nonneg rev fwd rev (k := (0 : ℤ))
      (la := d.length 3 - markL d) (lb := d.length 5) (m := d.length 9)
      (a := armA d) (b := armB d) (g := pairLow d) (o := targetThree d)
      rfl rfl rfl le_rfl (by norm_num)
      (by intro hcon; exact absurd hcon (by norm_num))
    simp only [fwd_tail, rev_tail] at hpair
    omega
  · show (0 : ℤ) ≤ zeroChip (d.length 7) + zeroChip (markR d)
      + (headContribution (d.length 7) 0 (pairLow d)
          + tailContribution (markR d) (pairLow d) 0
          + tailContribution (d.length 9) (pairLow d) (targetThree d))
    have hpair := pairPartner_nonneg rev fwd fwd (k := (0 : ℤ))
      (lc := d.length 7) (ld := markR d) (m := d.length 9)
      (a := armA d) (b := armB d) (g := pairLow d) (o := targetThree d)
      rfl rfl rfl le_rfl (by norm_num)
      (by intro hcon; exact absurd hcon (by norm_num))
    simp only [fwd_tail, rev_tail] at hpair
    omega
  · show (0 : ℤ) ≤ positiveChip (d.length 5)
      + headContribution (d.length 5) (targetThree d) 0
    exact positiveChip_add_head_nonneg (by omega)
  · show (0 : ℤ) ≤
      (if markR d = 0 then (0 : ℤ) else if d.length 8 ≤ markR d then 1 else 0)
        + (if markR d < d.length 8 then (0 : ℤ)
            else headContribution (d.length 8) (pairLow d) 0)
    by_cases hlt : markR d < d.length 8
    · rw [if_pos hlt]
      split_ifs <;> omega
    · rw [if_neg hlt]
      have hpos := positiveChip_add_head_nonneg (L := d.length 8)
        (h := pairLow d) (by omega)
      by_cases hz : markR d = 0
      · rw [if_pos hz]
        have h8 : d.length 8 = 0 := by omega
        have hgz : pairLow d = 0 := by omega
        rw [h8, hgz]
        simp [headContribution]
      · rw [if_neg hz, if_pos (by omega : d.length 8 ≤ markR d)]
        have hne : d.length 8 ≠ 0 := by omega
        have : positiveChip (d.length 8) = 1 := by simp [positiveChip, hne]
        omega
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num

/-- The vertex of the class of `3` that owns the delivered chip: the partner,
when the middle slot has collapsed and the partner's arms are the shorter. -/
def ownerThree (d : DegSpec 8 12) : Fin 8 :=
  if d.length 9 = 0 ∧ ¬ (armA d ≤ armB d) then 4 else 3

theorem t3Coeff_owner {d : DegSpec 8 12} : 1 ≤ t3Coeff d (ownerThree d) := by
  unfold ownerThree
  by_cases hc : d.length 9 = 0 ∧ ¬ (armA d ≤ armB d)
  · obtain ⟨hc1, hc2⟩ := hc
    rw [if_pos ⟨hc1, hc2⟩]
    show (1 : ℤ) ≤ zeroChip (d.length 7) + zeroChip (markR d)
      + (headContribution (d.length 7) 0 (pairLow d)
          + tailContribution (markR d) (pairLow d) 0
          + tailContribution (d.length 9) (pairLow d) (targetThree d))
    have hpair := pairPartner_nonneg rev fwd fwd (k := (1 : ℤ))
      (lc := d.length 7) (ld := markR d) (m := d.length 9)
      (a := armA d) (b := armB d) (g := pairLow d) (o := targetThree d)
      rfl rfl rfl (by norm_num) le_rfl (fun _ => ⟨hc1, by omega⟩)
    simp only [fwd_tail, rev_tail] at hpair
    omega
  · rw [if_neg hc]
    show (1 : ℤ) ≤ zeroChip (d.length 3 - markL d) + zeroChip (d.length 5)
      + (tailContribution (d.length 5) (targetThree d) 0
          + headContribution (d.length 3 - markL d) 0 (targetThree d)
          + headContribution (d.length 9) (pairLow d) (targetThree d))
    have hc' : d.length 9 = 0 → armA d ≤ armB d := by
      intro h9
      by_contra hcon
      exact hc ⟨h9, hcon⟩
    have hpair := pairTarget_nonneg rev fwd rev (k := (1 : ℤ))
      (la := d.length 3 - markL d) (lb := d.length 5) (m := d.length 9)
      (a := armA d) (b := armB d) (g := pairLow d) (o := targetThree d)
      rfl rfl rfl (by norm_num) le_rfl (fun _ hm => hc' hm)
    simp only [fwd_tail, rev_tail] at hpair
    omega

/-! ## The configuration-3 pair `{3, 4}`, read at the target `4` -/

theorem heightT4_const (d : DegSpec 8 12) (hL : d.length 2 ≤ d.length 3)
    (hR : d.length 6 ≤ d.length 8) (e : Fin 12) :
    d.length e = 0 →
      heightT4 d (row05Core.tail e) = heightT4 d (row05Core.head e) := by
  fin_cases e
  all_goals simp [heightT4, targetFour, pairLow, armA, armB, markL, markR,
    row05Core]
  all_goals omega

def t4Coeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then 0
  else if v = 1 then (zeroChip (markL d) - zeroChip (d.length 3))
      + (if 0 < markL d then (0 : ℤ)
          else tailContribution (d.length 3) 0 (pairLow d))
  else if v = 2 then positiveChip (d.length 7)
      + tailContribution (d.length 7) 0 (targetFour d)
  else if v = 3 then
    zeroChip (d.length 3 - markL d) + zeroChip (d.length 5)
      + (tailContribution (d.length 5) (pairLow d) 0
          + headContribution (d.length 3 - markL d) 0 (pairLow d)
          + headContribution (d.length 9) (targetFour d) (pairLow d))
  else if v = 4 then
    zeroChip (d.length 7) + zeroChip (markR d)
      + (headContribution (d.length 7) 0 (targetFour d)
          + tailContribution (markR d) (targetFour d) 0
          + tailContribution (d.length 9) (targetFour d) (pairLow d))
  else if v = 5 then positiveChip (d.length 5)
      + headContribution (d.length 5) (pairLow d) 0
  else if v = 6 then
    (if markR d = 0 then (0 : ℤ) else if d.length 8 ≤ markR d then 1 else 0)
      + (if markR d < d.length 8 then (0 : ℤ)
          else headContribution (d.length 8) (targetFour d) 0)
  else 0

theorem t4Coeff_eq {d : DegSpec 8 12} (hCore : d.core = row05Core)
    (hL : d.length 2 ≤ d.length 3) (hR : d.length 6 ≤ d.length 8) (v : Fin 8) :
    pairAlloc d v + contribForm d (heightT4 d) v = t4Coeff d v := by
  have hT3 := slotTailForm_three_split hCore (heightT4 d)
  have hH3 := slotHeadForm_three_eq hCore (h := heightT4 d)
    (by simp [heightT4])
    (by simp [heightT4, pairLow, armA, markL])
  have hT8 := slotTailForm_eight_eq hCore (h := heightT4 d)
    (by simp [heightT4])
    (by simp [heightT4, targetFour, armB])
  have hH8 := slotHeadForm_eight_split hCore (heightT4 d)
  simp only [pairAlloc]
  rw [baseWeight_eq hCore]
  fin_cases v
  all_goals simp [t4Coeff, contribForm, heightT4, chipWeight, zeroChip,
    positiveChip, transferWeight, indicatorWeight, markL, markR,
    hT3, hH3, hT8, hH8]
  all_goals (try (first | ring1 | ring_nf))
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals (first | ring | omega)

theorem pairLow_comm (d : DegSpec 8 12) : pairLow d = min (armB d) (armA d) := by
  unfold pairLow
  omega

theorem t4Coeff_nonneg {d : DegSpec 8 12} (hL : d.length 2 ≤ d.length 3)
    (hR : d.length 6 ≤ d.length 8) (v : Fin 8) :
    0 ≤ t4Coeff d v := by
  have hA1 : armA d ≤ d.length 3 - markL d := Nat.min_le_left _ _
  have hA2 : armA d ≤ d.length 5 := Nat.min_le_right _ _
  have hB1 : armB d ≤ d.length 7 := Nat.min_le_left _ _
  have hB2 : armB d ≤ markR d := Nat.min_le_right _ _
  have hg1 : pairLow d ≤ armA d := Nat.min_le_left _ _
  have hg2 : pairLow d ≤ armB d := Nat.min_le_right _ _
  have hO1 : targetFour d ≤ armB d := Nat.min_le_left _ _
  have hN : markR d ≤ d.length 8 := by simp only [markR]; omega
  fin_cases v
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ (zeroChip (markL d) - zeroChip (d.length 3))
      + (if 0 < markL d then (0 : ℤ)
          else tailContribution (d.length 3) 0 (pairLow d))
    have hm : markL d = d.length 2 := rfl
    by_cases hp : 0 < markL d
    · rw [if_pos hp]
      have h1 : zeroChip (markL d) = 0 := by
        have hne : markL d ≠ 0 := by omega
        simp [zeroChip, hne]
      have h2 : zeroChip (d.length 3) = 0 := by
        have hne : d.length 3 ≠ 0 := by omega
        simp [zeroChip, hne]
      omega
    · rw [if_neg hp]
      have h1 : zeroChip (markL d) = 1 := by
        have hz : markL d = 0 := by omega
        simp [zeroChip, hz]
      have hpos := positiveChip_add_tail_nonneg (L := d.length 3)
        (h := pairLow d) (by omega)
      have h2 : positiveChip (d.length 3) = 1 - zeroChip (d.length 3) := by
        unfold positiveChip zeroChip
        split_ifs <;> omega
      omega
  · show (0 : ℤ) ≤ positiveChip (d.length 7)
      + tailContribution (d.length 7) 0 (targetFour d)
    exact positiveChip_add_tail_nonneg (by omega)
  · show (0 : ℤ) ≤ zeroChip (d.length 3 - markL d) + zeroChip (d.length 5)
      + (tailContribution (d.length 5) (pairLow d) 0
          + headContribution (d.length 3 - markL d) 0 (pairLow d)
          + headContribution (d.length 9) (targetFour d) (pairLow d))
    have hpair := pairPartner_nonneg rev fwd rev (k := (0 : ℤ))
      (lc := d.length 3 - markL d) (ld := d.length 5) (m := d.length 9)
      (a := armB d) (b := armA d) (g := pairLow d) (o := targetFour d)
      rfl (pairLow_comm d) rfl le_rfl (by norm_num)
      (by intro hcon; exact absurd hcon (by norm_num))
    simp only [fwd_tail, rev_tail] at hpair
    omega
  · show (0 : ℤ) ≤ zeroChip (d.length 7) + zeroChip (markR d)
      + (headContribution (d.length 7) 0 (targetFour d)
          + tailContribution (markR d) (targetFour d) 0
          + tailContribution (d.length 9) (targetFour d) (pairLow d))
    have hpair := pairTarget_nonneg rev fwd fwd (k := (0 : ℤ))
      (la := d.length 7) (lb := markR d) (m := d.length 9)
      (a := armB d) (b := armA d) (g := pairLow d) (o := targetFour d)
      rfl (pairLow_comm d) rfl le_rfl (by norm_num)
      (by intro hcon; exact absurd hcon (by norm_num))
    simp only [fwd_tail, rev_tail] at hpair
    omega
  · show (0 : ℤ) ≤ positiveChip (d.length 5)
      + headContribution (d.length 5) (pairLow d) 0
    exact positiveChip_add_head_nonneg (by omega)
  · show (0 : ℤ) ≤
      (if markR d = 0 then (0 : ℤ) else if d.length 8 ≤ markR d then 1 else 0)
        + (if markR d < d.length 8 then (0 : ℤ)
            else headContribution (d.length 8) (targetFour d) 0)
    by_cases hlt : markR d < d.length 8
    · rw [if_pos hlt]
      split_ifs <;> omega
    · rw [if_neg hlt]
      have hpos := positiveChip_add_head_nonneg (L := d.length 8)
        (h := targetFour d) (by omega)
      by_cases hz : markR d = 0
      · rw [if_pos hz]
        have h8 : d.length 8 = 0 := by omega
        have hgz : targetFour d = 0 := by omega
        rw [h8, hgz]
        simp [headContribution]
      · rw [if_neg hz, if_pos (by omega : d.length 8 ≤ markR d)]
        have hne : d.length 8 ≠ 0 := by omega
        have : positiveChip (d.length 8) = 1 := by simp [positiveChip, hne]
        omega
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num

def ownerFour (d : DegSpec 8 12) : Fin 8 :=
  if d.length 9 = 0 ∧ ¬ (armB d ≤ armA d) then 3 else 4

theorem t4Coeff_owner {d : DegSpec 8 12} : 1 ≤ t4Coeff d (ownerFour d) := by
  unfold ownerFour
  by_cases hc : d.length 9 = 0 ∧ ¬ (armB d ≤ armA d)
  · obtain ⟨hc1, hc2⟩ := hc
    rw [if_pos ⟨hc1, hc2⟩]
    show (1 : ℤ) ≤ zeroChip (d.length 3 - markL d) + zeroChip (d.length 5)
      + (tailContribution (d.length 5) (pairLow d) 0
          + headContribution (d.length 3 - markL d) 0 (pairLow d)
          + headContribution (d.length 9) (targetFour d) (pairLow d))
    have hpair := pairPartner_nonneg rev fwd rev (k := (1 : ℤ))
      (lc := d.length 3 - markL d) (ld := d.length 5) (m := d.length 9)
      (a := armB d) (b := armA d) (g := pairLow d) (o := targetFour d)
      rfl (pairLow_comm d) rfl (by norm_num) le_rfl (fun _ => ⟨hc1, by omega⟩)
    simp only [fwd_tail, rev_tail] at hpair
    omega
  · rw [if_neg hc]
    show (1 : ℤ) ≤ zeroChip (d.length 7) + zeroChip (markR d)
      + (headContribution (d.length 7) 0 (targetFour d)
          + tailContribution (markR d) (targetFour d) 0
          + tailContribution (d.length 9) (targetFour d) (pairLow d))
    have hc' : d.length 9 = 0 → armB d ≤ armA d := by
      intro h9
      by_contra hcon
      exact hc ⟨h9, hcon⟩
    have hpair := pairTarget_nonneg rev fwd fwd (k := (1 : ℤ))
      (la := d.length 7) (lb := markR d) (m := d.length 9)
      (a := armB d) (b := armA d) (g := pairLow d) (o := targetFour d)
      rfl (pairLow_comm d) rfl (by norm_num) le_rfl (fun _ hm => hc' hm)
    simp only [fwd_tail, rev_tail] at hpair
    omega

/-! ## From the per-vertex coefficients to the residual -/

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

/-- The hypotheses of the kink lemma at a mark strictly inside its slot. -/
theorem mark_bounds {d : DegSpec 8 12} (hCore : d.core = row05Core)
    {h : Fin 8 → ℕ} (hRep : ∀ v : Fin 8, h (d.rep v) = h v)
    (hIn3 : h 1 ≤ markL d) (hOut3 : h 3 ≤ d.length 3 - markL d)
    (hIn8 : h 4 ≤ markR d) (hOut8 : h 6 ≤ d.length 8 - markR d)
    (hflat3 : h 1 = 0 ∨ h 3 = 0) (hflat8 : h 4 = 0 ∨ h 6 = 0)
    {e : Fin 12} (hpos : 0 < rowMark d e) :
    d.markRiseIn (rowPotential d h) (rowMarkValue d h) e ≤ (rowMark d e : ℤ) ∧
      -((d.length e - rowMark d e : ℕ) : ℤ) ≤
        d.markRiseOut (rowPotential d h) (rowMarkValue d h) e ∧
      (d.markRiseIn (rowPotential d h) (rowMarkValue d h) e = 0 ∨
        d.markRiseOut (rowPotential d h) (rowMarkValue d h) e = 0) := by
  rcases marked_of_rowMark_pos d hpos with h3 | h8
  · subst h3
    rw [riseIn_three hCore hRep, riseOut_three hCore hRep, rowMark_three]
    refine ⟨by exact_mod_cast hIn3, by omega, ?_⟩
    rcases hflat3 with hz | hz
    · exact Or.inl (by rw [hz]; norm_num)
    · exact Or.inr (by rw [hz]; norm_num)
  · subst h8
    rw [riseIn_eight hCore hRep, riseOut_eight hCore hRep, rowMark_eight]
    refine ⟨by exact_mod_cast hIn8, by omega, ?_⟩
    rcases hflat8 with hz | hz
    · exact Or.inl (by rw [hz]; norm_num)
    · exact Or.inr (by rw [hz]; norm_num)

/-- **The local Dhar move.**  With the profile's four mark bounds and a chip
allocation whose class sums are the divisor's, the marked script leaves an
effective residual at the named centre. -/
theorem residual_effective {d : DegSpec 8 12} (hCore : d.core = row05Core)
    {h : Fin 8 → ℕ} (hRep : ∀ v : Fin 8, h (d.rep v) = h v)
    (hL : d.length 2 ≤ d.length 3)
    (hIn3 : h 1 ≤ markL d) (hOut3 : h 3 ≤ d.length 3 - markL d)
    (hIn8 : h 4 ≤ markR d) (hOut8 : h 6 ≤ d.length 8 - markR d)
    (hflat3 : h 1 = 0 ∨ h 3 = 0) (hflat8 : h 4 = 0 ∨ h 6 = 0)
    {alloc : Fin 8 → ℤ}
    (hAlloc : ∀ r : Fin 8,
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), alloc v =
        ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
          baseWeight d v)
    {center owner : Fin 8} (hOwnerRep : d.rep owner = d.rep center)
    (hLocal : ∀ v : Fin 8,
      0 ≤ alloc v - indicatorWeight v owner + contribForm d h v) :
    effective (rowDivisor d - one_chip (d.coreVertex center)
      + prin d.graph
        (d.splitScript (rowPotential d h) (rowMark d) (rowMarkValue d h))) := by
  classical
  have hMarks := marks_admissible hCore hRep hL hIn3 hOut3 hIn8 hOut8
  intro vertex
  rcases vertex with coreClass | interior
  · obtain ⟨r, hr⟩ := coreClass
    have hVertex : (Sum.inl ⟨r, hr⟩ : d.Vertex) = d.coreVertex r := by
      unfold DegSpec.coreVertex
      congr 1
      exact Subtype.ext hr.symm
    rw [hVertex]
    change 0 ≤ rowDivisor d (d.coreVertex r)
      - one_chip (G := d.graph) (d.coreVertex center) (d.coreVertex r)
      + prin d.graph
          (d.splitScript (rowPotential d h) (rowMark d) (rowMarkValue d h))
          (d.coreVertex r)
    rw [rowDivisor_coreVertex_eq d r, ← hAlloc r,
      ← positiveEndpointContribution_classSum_eq d hMarks r]
    have hIndicator := sum_indicatorWeight_class d owner r
    have hOneChip :
        one_chip (G := d.graph) (d.coreVertex center) (d.coreVertex r) =
          ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
            indicatorWeight v owner := by
      rw [hIndicator]
      simp only [one_chip, d.coreVertex_eq_iff]
      rw [hOwnerRep]
      simp only [eq_comm]
    rw [hOneChip, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_nonneg
    intro v _hv
    rw [contrib_eq hCore hRep hMarks hflat3 hflat8 v]
    exact hLocal v
  · obtain ⟨edge, offset⟩ := interior
    have hVertex : (Sum.inr ⟨edge, offset⟩ : d.Vertex) =
        d.interiorVertex edge offset := rfl
    rw [hVertex]
    change 0 ≤ rowDivisor d (d.interiorVertex edge offset)
      - one_chip (G := d.graph) (d.coreVertex center) (d.interiorVertex edge offset)
      + prin d.graph
          (d.splitScript (rowPotential d h) (rowMark d) (rowMarkValue d h))
          (d.interiorVertex edge offset)
    have hNe : (d.coreVertex center) ≠ d.interiorVertex edge offset := by
      simp [DegSpec.coreVertex, DegSpec.interiorVertex]
    have hZeroChip : one_chip (G := d.graph) (d.coreVertex center)
        (d.interiorVertex edge offset) = 0 := by
      simp only [one_chip, if_neg hNe.symm]
    rw [hZeroChip]
    by_cases hmark : offset.val + 1 = rowMark d edge
    · have hlt : rowMark d edge < d.length edge := by
        have := offset.isLt
        omega
      have hbounds := mark_bounds hCore hRep hIn3 hOut3 hIn8 hOut8 hflat3 hflat8
        (e := edge) (by omega)
      have hprin := d.prin_splitScript_interiorVertex_ge_neg_one hMarks edge offset
        hmark hlt hbounds.1 hbounds.2.1 hbounds.2.2
      have hchip := one_le_rowDivisor_at_mark d hmark hlt
      omega
    · have hprin := d.prin_splitScript_interiorVertex_nonneg_of_ne hMarks edge
        offset hmark
      have hd := rowDivisor_effective d (d.interiorVertex edge offset)
      omega

/-! ## The owners lie in their centres' classes -/

theorem ownerZero_rep {d : DegSpec 8 12} (hCore : d.core = row05Core) :
    d.rep (ownerZero d) = d.rep 0 := by
  unfold ownerZero
  by_cases hz : d.length 2 = 0
  · rw [if_pos hz]
    have h := d.rep_zero 2 hz
    rw [hCore] at h
    simpa [row05Core] using h
  · rw [if_neg hz]

theorem ownerSix_rep {d : DegSpec 8 12} (hCore : d.core = row05Core) :
    d.rep (ownerSix d) = d.rep 6 := by
  unfold ownerSix
  by_cases hz : d.length 8 = 0
  · rw [if_pos hz]
    have h := d.rep_zero 8 hz
    rw [hCore] at h
    simpa [row05Core] using h
  · rw [if_neg hz]

theorem ownerSeven_rep {d : DegSpec 8 12} (hCore : d.core = row05Core) :
    d.rep (ownerSeven d) = d.rep 7 := by
  unfold ownerSeven
  by_cases hz : d.length 6 = 0
  · rw [if_pos hz]
    have h := d.rep_zero 6 hz
    rw [hCore] at h
    simpa [row05Core] using h
  · rw [if_neg hz]

theorem ownerThree_rep {d : DegSpec 8 12} (hCore : d.core = row05Core) :
    d.rep (ownerThree d) = d.rep 3 := by
  unfold ownerThree
  by_cases hz : d.length 9 = 0 ∧ ¬ (armA d ≤ armB d)
  · rw [if_pos hz]
    have h := d.rep_zero 9 hz.1
    rw [hCore] at h
    simpa [row05Core] using h
  · rw [if_neg hz]

theorem ownerFour_rep {d : DegSpec 8 12} (hCore : d.core = row05Core) :
    d.rep (ownerFour d) = d.rep 4 := by
  unfold ownerFour
  by_cases hz : d.length 9 = 0 ∧ ¬ (armB d ≤ armA d)
  · rw [if_pos hz]
    have h := d.rep_zero 9 hz.1
    rw [hCore] at h
    simpa [row05Core] using h.symm
  · rw [if_neg hz]

/-! ## Every contracted core class is reached -/

theorem rowDivisor_reaches_coreVertex {d : DegSpec 8 12}
    (hCore : d.core = row05Core)
    (hL : d.length 2 ≤ d.length 3) (hR : d.length 6 ≤ d.length 8)
    (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8, d.rep x = d.rep y ↔ ReachIn row05Core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0) (center : Fin 8) :
    Reaches d.graph (rowDivisor d) (d.coreVertex center) := by
  have hBase : ∀ r : Fin 8,
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
          baseWeight d v =
        ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
          baseWeight d v := fun _ => rfl
  have hRepLB := height_rep_eq d (heightLB d) (heightLB_const d hL) F hRepReach hFZero
  have hRepRB := height_rep_eq d (heightRB d) (heightRB_const d hR) F hRepReach hFZero
  have hRepT3 := height_rep_eq d (heightT3 d) (heightT3_const d hL hR) F hRepReach hFZero
  have hRepT4 := height_rep_eq d (heightT4 d) (heightT4_const d hL hR) F hRepReach hFZero
  fin_cases center
  · -- vertex 0: the left banana pair
    exact (DharMove.ofScript _ (residual_effective hCore hRepLB hL
      (by simp [heightLB, markL]) (by simp [heightLB])
      (by simp [heightLB]) (by simp [heightLB])
      (Or.inr (by simp [heightLB])) (Or.inl (by simp [heightLB]))
      hBase (ownerZero_rep hCore)
      (residual_of_coeff (owner := ownerZero d)
        (fun v => by rw [lbCoeff_eq hCore v]; exact lbCoeff_nonneg hL v)
        (by rw [lbCoeff_eq hCore (ownerZero d)]; exact lbCoeff_owner_zero)))).reaches
  · -- vertex 1: the left banana pair
    exact (DharMove.ofScript _ (residual_effective hCore hRepLB hL
      (by simp [heightLB, markL]) (by simp [heightLB])
      (by simp [heightLB]) (by simp [heightLB])
      (Or.inr (by simp [heightLB])) (Or.inl (by simp [heightLB]))
      hBase (rfl : d.rep 1 = d.rep 1)
      (residual_of_coeff (owner := (1 : Fin 8))
        (fun v => by rw [lbCoeff_eq hCore v]; exact lbCoeff_nonneg hL v)
        (by rw [lbCoeff_eq hCore 1]; exact lbCoeff_owner_one)))).reaches
  · -- vertex 2 carries a chip
    exact reaches_of_effective_representative
      (linear_equiv.refl d.graph (rowDivisor d)) (rowDivisor_effective d)
      (one_le_rowDivisor_at_chip d (c := 2) (by norm_num [chipWeight]))
  · -- vertex 3: the configuration-3 pair
    exact (DharMove.ofScript _ (residual_effective hCore hRepT3 hL
      (by simp [heightT3])
      (by simp [heightT3, targetThree, armA, markL])
      (by simp [heightT3, pairLow, armB])
      (by simp [heightT3])
      (Or.inl (by simp [heightT3])) (Or.inr (by simp [heightT3]))
      (pairAlloc_classSum d hCore) (ownerThree_rep hCore)
      (residual_of_coeff (owner := ownerThree d)
        (fun v => by rw [t3Coeff_eq hCore hL hR v]; exact t3Coeff_nonneg hL hR v)
        (by rw [t3Coeff_eq hCore hL hR (ownerThree d)]; exact t3Coeff_owner)))).reaches
  · -- vertex 4: the configuration-3 pair, read at the other centre
    exact (DharMove.ofScript _ (residual_effective hCore hRepT4 hL
      (by simp [heightT4])
      (by simp [heightT4, pairLow, armA, markL])
      (by simp [heightT4, targetFour, armB])
      (by simp [heightT4])
      (Or.inl (by simp [heightT4])) (Or.inr (by simp [heightT4]))
      (pairAlloc_classSum d hCore) (ownerFour_rep hCore)
      (residual_of_coeff (owner := ownerFour d)
        (fun v => by rw [t4Coeff_eq hCore hL hR v]; exact t4Coeff_nonneg hL hR v)
        (by rw [t4Coeff_eq hCore hL hR (ownerFour d)]; exact t4Coeff_owner)))).reaches
  · -- vertex 5 carries a chip
    exact reaches_of_effective_representative
      (linear_equiv.refl d.graph (rowDivisor d)) (rowDivisor_effective d)
      (one_le_rowDivisor_at_chip d (c := 5) (by norm_num [chipWeight]))
  · -- vertex 6: the right banana pair
    exact (DharMove.ofScript _ (residual_effective hCore hRepRB hL
      (by simp [heightRB]) (by simp [heightRB])
      (by simp [heightRB]) (by simp [heightRB, markR]; omega)
      (Or.inl (by simp [heightRB])) (Or.inl (by simp [heightRB]))
      hBase (ownerSix_rep hCore)
      (residual_of_coeff (owner := ownerSix d)
        (fun v => by rw [rbCoeff_eq hCore hR v]; exact rbCoeff_nonneg hR v)
        (by rw [rbCoeff_eq hCore hR (ownerSix d)]; exact rbCoeff_owner_six hR)))).reaches
  · -- vertex 7: the right banana pair
    exact (DharMove.ofScript _ (residual_effective hCore hRepRB hL
      (by simp [heightRB]) (by simp [heightRB])
      (by simp [heightRB]) (by simp [heightRB, markR]; omega)
      (Or.inl (by simp [heightRB])) (Or.inl (by simp [heightRB]))
      hBase (ownerSeven_rep hCore)
      (residual_of_coeff (owner := ownerSeven d)
        (fun v => by rw [rbCoeff_eq hCore hR v]; exact rbCoeff_nonneg hR v)
        (by rw [rbCoeff_eq hCore hR (ownerSeven d)];
            exact rbCoeff_owner_seven hR)))).reaches

/-! ## Chamber A, and the whole closed orthant -/

theorem chamber_pencil (length : Fin 12 → ℕ)
    (forest : IsForest row05Core (zeroSlots length))
    (notLoopy : ¬ IsLoopy row05Core (zeroSlots length))
    (hP : GenusFiveRow05Symmetry.Chamber length) :
    Nonempty (DegreeFourDharPencil
      (faceSpec row05Core (by norm_num) length forest notLoopy).graph) := by
  let d := faceSpec row05Core (by norm_num) length forest notLoopy
  have hCore : d.core = row05Core := rfl
  have hRepReach : ∀ x y : Fin 8,
      d.rep x = d.rep y ↔ ReachIn row05Core (zeroSlots length) x y := fun x y =>
    compFold_iff row05Core (zeroSlots length) x y
  have hFZero : ∀ e : Fin 12, e ∈ zeroSlots length ↔ d.length e = 0 := by
    intro e
    simp [d, faceSpec, zeroSlots]
  refine ⟨DegreeFourDharPencil.ofEffectiveRankOne (rowDivisor d)
    (rowDivisor_effective d) (rowDivisor_degree d) ?_⟩
  apply d.rank_ge_one_of_reaches_coreVertices (by rw [hCore]; exact row05_connected)
  intro center
  exact rowDivisor_reaches_coreVertex hCore hP.1 hP.2 (zeroSlots length)
    hRepReach hFZero center

/-- **AR's sixth family on row 05.**  The paper's own divisor -- two chips on
the square and one inside each of the two marked legs -- has rank at least one
on every nonloopy forest face, all four chambers at once. -/
theorem row05_closedConstruction :
    ClosedSubdivisionDharConstruction row05Core (by norm_num) :=
  ClosedOrbit.closedConstruction_of_chamber row05Core (by norm_num)
    GenusFiveRow05Symmetry.Chamber
    (fun length _ _ => GenusFiveRow05Symmetry.chamber_covers length)
    chamber_pencil

end AtanasovRanganathan.GenusFiveRow05
