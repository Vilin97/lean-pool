/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationChippedTriangle
import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationMarkedRow
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow08Symmetry

/-!
# AR row 08, chamber 2

The second scope AR draw for their seventh family: `|e3| ≤ |e4|` and
`|e2| ≤ |e7|`, i.e. `b ≤ a` and `c ≤ d`.  The displayed divisor is

```
 D = [2] + [3] + (e4 at distance |e3| from 1) + (e7 at distance |e7| - |e2| from 5)
```

so the two marks are `mark e4 = |e3|` (from `e4`'s tail `1`) and
`mark e7 = |e7| - |e2|` (from `e7`'s tail `5`).  The six chip-free vertices are

* `{0, 1}` -- a banana pair whose two arms both have length `|e3|`: the whole of
  `e3` read from its head `0`, and the near half of `e4`.
* `{6, 7}` -- a banana pair whose two arms both have length `|e2|`: the whole of
  `e2` read from its tail `6`, and the far half of `e7`.
* `{4, 5}` -- **not** a pair.  Both would have an arm into the same chip vertex
  `2`, which carries only one chip, so `ConfigurationThree`'s `chipSum` fails and
  the profile drives `2` to `-1`.  AR's own solid subgraph here is the
  **chipped triangle** `2 - 4 - 5`, one chip on `2` and one arm from each
  triangle vertex; that is `ConfigurationChippedTriangle`, read once at `u = 4`
  and once at `u = 5`.  Its docstring records the two repairs that do not work.

The triangle data at the target `4` is `al = |e4| - |e3|` (the far half of the
marked `e4`), `be = |e7| - |e2|` (the near half of the marked `e7`),
`ga = |e9|`, and the triangle slots `p = |e5|`, `q = |e6|`, `r = |e8|`; at the
target `5` the same picture is read with `al ↔ be` and `p ↔ r`.
-/

namespace AtanasovRanganathan.GenusFiveRow08ChamberTwo

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
open ConfigurationMarkedRow
open ConfigurationChippedTriangle

/-! ## The two marks -/

/-- The chip on `e4`, at distance `|e3|` from the tail `1`. -/
def markY (d : DegSpec 8 12) : ℕ := d.length 3

/-- The chip on `e7`, at distance `|e7| - |e2|` from the tail `5`. -/
def markX (d : DegSpec 8 12) : ℕ := d.length 7 - d.length 2

/-- The far half of the marked `e4`: the target `4`'s own arm. -/
def armAl (d : DegSpec 8 12) : ℕ := d.length 4 - markY d

def rowMark (d : DegSpec 8 12) (e : Fin 12) : ℕ :=
  if e = 4 then markY d else if e = 7 then markX d else 0

@[simp] theorem rowMark_four (d : DegSpec 8 12) : rowMark d 4 = markY d := by
  simp [rowMark]

@[simp] theorem rowMark_seven (d : DegSpec 8 12) : rowMark d 7 = markX d := by
  simp [rowMark]

theorem rowMark_other (d : DegSpec 8 12) {e : Fin 12} (h4 : e ≠ 4) (h7 : e ≠ 7) :
    rowMark d e = 0 := by
  simp [rowMark, h4, h7]

theorem marked_of_rowMark_pos (d : DegSpec 8 12) {e : Fin 12}
    (h : 0 < rowMark d e) : e = 4 ∨ e = 7 := by
  by_cases h4 : e = 4
  · exact Or.inl h4
  · by_cases h7 : e = 7
    · exact Or.inr h7
    · rw [rowMark_other d h4 h7] at h; omega

/-! ## The core, spelled out -/

section Core

variable {d : DegSpec 8 12} (hCore : d.core = row08Core)
include hCore

theorem tail_four : d.core.tail 4 = 1 := by rw [hCore]; decide
theorem head_four : d.core.head 4 = 4 := by rw [hCore]; decide
theorem tail_seven : d.core.tail 7 = 5 := by rw [hCore]; decide
theorem head_seven : d.core.head 7 = 7 := by rw [hCore]; decide

end Core

/-! ## The heights -/

/-- The chipped-triangle profile read at the target `4`. -/
def hcT4 (d : DegSpec 8 12) : ℕ := chipHeight (armAl d) (markX d) (d.length 9)
def h0T4 (d : DegSpec 8 12) : ℕ :=
  sideHeight (armAl d) (markX d) (d.length 9) (d.length 8)
def htT4 (d : DegSpec 8 12) : ℕ :=
  targetHeight (armAl d) (markX d) (d.length 9) (d.length 5) (d.length 6)
    (d.length 8)
def hvT4 (d : DegSpec 8 12) : ℕ :=
  partnerHeight (armAl d) (markX d) (d.length 9) (d.length 5) (d.length 6)
    (d.length 8)

/-- The same picture read at the target `5`: `al ↔ be`, `p ↔ r`. -/
def hcT5 (d : DegSpec 8 12) : ℕ := chipHeight (markX d) (armAl d) (d.length 9)
def h0T5 (d : DegSpec 8 12) : ℕ :=
  sideHeight (markX d) (armAl d) (d.length 9) (d.length 5)
def htT5 (d : DegSpec 8 12) : ℕ :=
  targetHeight (markX d) (armAl d) (d.length 9) (d.length 8) (d.length 6)
    (d.length 5)
def hvT5 (d : DegSpec 8 12) : ℕ :=
  partnerHeight (markX d) (armAl d) (d.length 9) (d.length 8) (d.length 6)
    (d.length 5)

theorem boundsT4 (d : DegSpec 8 12) :
    (hcT4 d ≤ d.length 9 ∧ hcT4 d ≤ armAl d ∧ hcT4 d ≤ markX d)
      ∧ (hcT4 d = d.length 9 ∨ hcT4 d = armAl d ∨ hcT4 d = markX d)
      ∧ (h0T4 d ≤ markX d ∧ h0T4 d ≤ hcT4 d + d.length 8 ∧ hcT4 d ≤ h0T4 d)
      ∧ (h0T4 d = markX d ∨ h0T4 d = hcT4 d + d.length 8)
      ∧ (htT4 d ≤ armAl d ∧ htT4 d ≤ hcT4 d + d.length 5
          ∧ htT4 d ≤ h0T4 d + d.length 6 ∧ hcT4 d ≤ htT4 d)
      ∧ (htT4 d = armAl d ∨ htT4 d = hcT4 d + d.length 5
          ∨ htT4 d = h0T4 d + d.length 6)
      ∧ (hvT4 d ≤ h0T4 d ∧ hvT4 d ≤ htT4 d ∧ hcT4 d ≤ hvT4 d
          ∧ htT4 d ≤ hvT4 d + d.length 6 ∧ hvT4 d ≤ hcT4 d + d.length 8
          ∧ hvT4 d ≤ markX d)
      ∧ (hvT4 d = h0T4 d ∨ hvT4 d = htT4 d) :=
  bounds rfl rfl rfl rfl

theorem boundsT5 (d : DegSpec 8 12) :
    (hcT5 d ≤ d.length 9 ∧ hcT5 d ≤ markX d ∧ hcT5 d ≤ armAl d)
      ∧ (hcT5 d = d.length 9 ∨ hcT5 d = markX d ∨ hcT5 d = armAl d)
      ∧ (h0T5 d ≤ armAl d ∧ h0T5 d ≤ hcT5 d + d.length 5 ∧ hcT5 d ≤ h0T5 d)
      ∧ (h0T5 d = armAl d ∨ h0T5 d = hcT5 d + d.length 5)
      ∧ (htT5 d ≤ markX d ∧ htT5 d ≤ hcT5 d + d.length 8
          ∧ htT5 d ≤ h0T5 d + d.length 6 ∧ hcT5 d ≤ htT5 d)
      ∧ (htT5 d = markX d ∨ htT5 d = hcT5 d + d.length 8
          ∨ htT5 d = h0T5 d + d.length 6)
      ∧ (hvT5 d ≤ h0T5 d ∧ hvT5 d ≤ htT5 d ∧ hcT5 d ≤ hvT5 d
          ∧ htT5 d ≤ hvT5 d + d.length 6 ∧ hvT5 d ≤ hcT5 d + d.length 5
          ∧ hvT5 d ≤ armAl d)
      ∧ (hvT5 d = h0T5 d ∨ hvT5 d = htT5 d) :=
  bounds rfl rfl rfl rfl

/-- The left banana pair, both arms of length `|e3|`. -/
def heightLB (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 0 then markY d else if v = 1 then markY d else 0

/-- The right banana pair, both arms of length `|e2|`. -/
def heightRB (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 6 then d.length 2 else if v = 7 then d.length 2 else 0

/-- The chipped triangle read at the target `4`. -/
def heightT4 (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 2 then hcT4 d else if v = 4 then htT4 d
    else if v = 5 then hvT4 d else 0

/-- The chipped triangle read at the target `5`. -/
def heightT5 (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 2 then hcT5 d else if v = 5 then htT5 d
    else if v = 4 then hvT5 d else 0

/-! ## Profiles -/

theorem mkProfile {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (hB : d.length 3 ≤ d.length 4) (hC : d.length 2 ≤ d.length 7)
    {h : Fin 8 → ℕ}
    (hin4 : h 1 ≤ markY d) (hout4 : h 4 ≤ d.length 4 - markY d)
    (hflat4 : h 1 = 0 ∨ h 4 = 0)
    (hin7 : h 5 ≤ markX d) (hout7 : h 7 ≤ d.length 7 - markX d)
    (hflat7 : h 5 = 0 ∨ h 7 = 0)
    (hconst : ∀ e : Fin 12, d.length e = 0 →
      h (row08Core.tail e) = h (row08Core.head e)) :
    Profile d (rowMark d) h := by
  have ht4 : d.core.tail 4 = 1 := tail_four hCore
  have hh4 : d.core.head 4 = 4 := head_four hCore
  have ht7 : d.core.tail 7 = 5 := tail_seven hCore
  have hh7 : d.core.head 7 = 7 := head_seven hCore
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e
    by_cases h4 : e = 4
    · subst h4; rw [rowMark_four]; simpa [markY] using hB
    · by_cases h7 : e = 7
      · subst h7; rw [rowMark_seven]; simp only [markX]; omega
      · rw [rowMark_other d h4 h7]; omega
  · intro e he
    by_cases h4 : e = 4
    · subst h4; rw [ht4, rowMark_four]; exact hin4
    · by_cases h7 : e = 7
      · subst h7; rw [ht7, rowMark_seven]; exact hin7
      · rw [rowMark_other d h4 h7] at he; omega
  · intro e he
    by_cases h4 : e = 4
    · subst h4; rw [hh4, rowMark_four]; exact hout4
    · by_cases h7 : e = 7
      · subst h7; rw [hh7, rowMark_seven]; exact hout7
      · rw [rowMark_other d h4 h7] at he; omega
  · intro e he
    by_cases h4 : e = 4
    · subst h4; rw [ht4, hh4]; exact hflat4
    · by_cases h7 : e = 7
      · subst h7; rw [ht7, hh7]; exact hflat7
      · rw [rowMark_other d h4 h7] at he; omega
  · intro e he
    rw [hCore]
    exact hconst e he

theorem profileLB {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (hB : d.length 3 ≤ d.length 4) (hC : d.length 2 ≤ d.length 7) :
    Profile d (rowMark d) (heightLB d) := by
  have h1 : heightLB d 1 = markY d := rfl
  have h4 : heightLB d 4 = 0 := rfl
  have h5 : heightLB d 5 = 0 := rfl
  have h7 : heightLB d 7 = 0 := rfl
  refine mkProfile hCore hB hC (by rw [h1]) (by rw [h4]; omega) (Or.inr h4)
    (by rw [h5]; omega) (by rw [h7]; omega) (Or.inl h5) ?_
  intro e
  fin_cases e
  all_goals simp [heightLB, markY, row08Core]
  all_goals omega

theorem profileRB {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (hB : d.length 3 ≤ d.length 4) (hC : d.length 2 ≤ d.length 7) :
    Profile d (rowMark d) (heightRB d) := by
  have h1 : heightRB d 1 = 0 := rfl
  have h4 : heightRB d 4 = 0 := rfl
  have h5 : heightRB d 5 = 0 := rfl
  have h7 : heightRB d 7 = d.length 2 := rfl
  refine mkProfile hCore hB hC (by rw [h1]; omega) (by rw [h4]; omega)
    (Or.inl h1) (by rw [h5]; omega)
    (by rw [h7]; simp only [markX]; omega) (Or.inl h5) ?_
  intro e
  fin_cases e
  all_goals simp [heightRB, row08Core]
  all_goals omega

theorem profileT4 {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (hB : d.length 3 ≤ d.length 4) (hC : d.length 2 ≤ d.length 7) :
    Profile d (rowMark d) (heightT4 d) := by
  obtain ⟨⟨hcga, hcal, hcbe⟩, -, ⟨h0be, h0hc, hch0⟩, -,
    ⟨htal, hthc, hth0, hcht⟩, -, ⟨hvh0, hvht, hchv, hthv, hvhcr, hvbe⟩, -⟩ :=
    boundsT4 d
  have hAl : armAl d = d.length 4 - markY d := rfl
  have hmY : markY d = d.length 3 := rfl
  have hmX : markX d = d.length 7 - d.length 2 := rfl
  have h1 : heightT4 d 1 = 0 := rfl
  have h2 : heightT4 d 2 = hcT4 d := rfl
  have h4 : heightT4 d 4 = htT4 d := rfl
  have h5 : heightT4 d 5 = hvT4 d := rfl
  have h7 : heightT4 d 7 = 0 := rfl
  refine mkProfile hCore hB hC (by rw [h1]; omega) (by rw [h4]; omega)
    (Or.inl h1) (by rw [h5]; omega) (by rw [h7]; omega) (Or.inr h7) ?_
  intro e
  fin_cases e
  all_goals simp [heightT4, row08Core]
  all_goals omega

theorem profileT5 {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (hB : d.length 3 ≤ d.length 4) (hC : d.length 2 ≤ d.length 7) :
    Profile d (rowMark d) (heightT5 d) := by
  obtain ⟨⟨hcga, hcbe, hcal⟩, -, ⟨h0al, h0hc, hch0⟩, -,
    ⟨htbe, hthc, hth0, hcht⟩, -, ⟨hvh0, hvht, hchv, hthv, hvhcr, hval⟩, -⟩ :=
    boundsT5 d
  have hAl : armAl d = d.length 4 - markY d := rfl
  have hmY : markY d = d.length 3 := rfl
  have hmX : markX d = d.length 7 - d.length 2 := rfl
  have h1 : heightT5 d 1 = 0 := rfl
  have h2 : heightT5 d 2 = hcT5 d := rfl
  have h4 : heightT5 d 4 = hvT5 d := rfl
  have h5 : heightT5 d 5 = htT5 d := rfl
  have h7 : heightT5 d 7 = 0 := rfl
  refine mkProfile hCore hB hC (by rw [h1]; omega) (by rw [h4]; omega)
    (Or.inl h1) (by rw [h5]; omega) (by rw [h7]; omega) (Or.inr h7) ?_
  intro e
  fin_cases e
  all_goals simp [heightT5, row08Core]
  all_goals omega

/-! ## The endpoint ledger, vertex by vertex -/

def contribForm (d : DegSpec 8 12) (h : Fin 8 → ℕ) (v : Fin 8) : ℤ :=
  if v = 0 then
    tailContribution (d.length 0) (h 0) (h 1)
      + tailContribution (d.length 1) (h 0) (h 1)
      + headContribution (d.length 3) (h 3) (h 0)
  else if v = 1 then
    slotTailForm d (rowMark d) h 4
      + headContribution (d.length 0) (h 0) (h 1)
      + headContribution (d.length 1) (h 0) (h 1)
  else if v = 2 then
    tailContribution (d.length 5) (h 2) (h 4)
      + tailContribution (d.length 9) (h 2) (h 3)
      + headContribution (d.length 8) (h 5) (h 2)
  else if v = 3 then
    tailContribution (d.length 3) (h 3) (h 0)
      + headContribution (d.length 2) (h 6) (h 3)
      + headContribution (d.length 9) (h 2) (h 3)
  else if v = 4 then
    tailContribution (d.length 6) (h 4) (h 5)
      + slotHeadForm d (rowMark d) h 4
      + headContribution (d.length 5) (h 2) (h 4)
  else if v = 5 then
    slotTailForm d (rowMark d) h 7
      + tailContribution (d.length 8) (h 5) (h 2)
      + headContribution (d.length 6) (h 4) (h 5)
  else if v = 6 then
    tailContribution (d.length 2) (h 6) (h 3)
      + tailContribution (d.length 10) (h 6) (h 7)
      + tailContribution (d.length 11) (h 6) (h 7)
  else
    slotHeadForm d (rowMark d) h 7
      + headContribution (d.length 10) (h 6) (h 7)
      + headContribution (d.length 11) (h 6) (h 7)

theorem contrib_eq {d : DegSpec 8 12} (hCore : d.core = row08Core)
    {h : Fin 8 → ℕ} (hprof : Profile d (rowMark d) h)
    (hRep : ∀ v : Fin 8, h (d.rep v) = h v) (v : Fin 8) :
    positiveEndpointContribution d (heightPotential d h) (rowMark d)
        (markValue d (rowMark d) h) v = contribForm d h v := by
  rw [contribution_eq d hprof hRep]
  fin_cases v <;>
    simp +decide only [hCore, row08Core, Fin.isValue, Fin.zero_eta, slotTailForm, rowMark,
      slotHeadForm, Fin.sum_univ_succ, ↓reduceIte, lt_self_iff_false, Matrix.cons_val_zero,
      add_zero, Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc,
      zero_add, Finset.univ_unique, Fin.default_eq_zero, Matrix.cons_val_fin_one, Fin.reduceEq,
      Finset.sum_const_zero, contribForm, Fin.mk_one, Matrix.cons_val, Fin.reduceFinMk,
      Finset.sum_singleton]<;> ring

/-! ## The divisor -/

def chipWeight (v : Fin 8) : ℤ := if v = 2 then 1 else if v = 3 then 1 else 0

theorem chipWeight_nonneg (v : Fin 8) : 0 ≤ chipWeight v := by
  unfold chipWeight; split_ifs <;> norm_num

theorem sum_chipWeight : ∑ v : Fin 8, chipWeight v = 2 := by decide

/-- AR's divisor on chamber 2. -/
def rowDivisor (d : DegSpec 8 12) : CFDiv d.graph :=
  markedDivisorTwo d chipWeight (rowMark d) 4 7

def base (d : DegSpec 8 12) : Fin 8 → ℤ :=
  baseTwo d chipWeight (rowMark d) 4 7

theorem rowDivisor_effective (d : DegSpec 8 12) : effective (rowDivisor d) :=
  markedDivisorTwo_effective d chipWeight (rowMark d) chipWeight_nonneg 4 7

theorem rowDivisor_degree (d : DegSpec 8 12) : deg (rowDivisor d) = 4 := by
  rw [rowDivisor, deg_markedDivisorTwo, sum_chipWeight]
  norm_num

theorem base_eq {d : DegSpec 8 12} (hCore : d.core = row08Core) (v : Fin 8) :
    base d v = chipWeight v
      + (if markY d = 0 then (if v = 1 then (1 : ℤ) else 0)
          else if d.length 4 ≤ markY d then (if v = 4 then (1 : ℤ) else 0)
          else 0)
      + (if markX d = 0 then (if v = 5 then (1 : ℤ) else 0)
          else if d.length 7 ≤ markX d then (if v = 7 then (1 : ℤ) else 0)
          else 0) := by
  unfold base baseTwo markChipWeight
  rw [rowMark_four, rowMark_seven, tail_four hCore, head_four hCore,
    tail_seven hCore, head_seven hCore]

/-! ## Chip allocations for the two triangle scripts -/

def allocT4 (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  base d v
    + (if d.length 9 = 0 then transferWeight 3 2 v else 0)
    + (if d.length 4 = 0 then transferWeight 1 4 v else 0)
    + (if d.length 8 = 0 ∧ hcT4 d < markX d then transferWeight 2 5 v else 0)

def allocT5 (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  base d v
    + (if d.length 9 = 0 then transferWeight 3 2 v else 0)
    + (if d.length 4 = 0 then transferWeight 1 4 v else 0)
    + (if d.length 5 = 0 ∧ hcT5 d < armAl d then transferWeight 2 4 v else 0)

theorem allocT4_classSum {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (r : Fin 8) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), allocT4 d v =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), base d v := by
  classical
  have h9 : d.length 9 = 0 → d.rep 3 = d.rep 2 := by
    intro hz
    have h := d.rep_zero 9 hz
    rw [hCore] at h
    simpa [row08Core] using h.symm
  have h4 : d.length 4 = 0 → d.rep 1 = d.rep 4 := by
    intro hz
    have h := d.rep_zero 4 hz
    rw [hCore] at h
    simpa [row08Core] using h
  have h8 : (d.length 8 = 0 ∧ hcT4 d < markX d) → d.rep 2 = d.rep 5 := by
    intro hz
    have h := d.rep_zero 8 hz.1
    rw [hCore] at h
    simpa [row08Core] using h.symm
  simp only [allocT4, Finset.sum_add_distrib]
  rw [sum_conditional_transfer_eq_zero d _ 3 2 h9,
    sum_conditional_transfer_eq_zero d _ 1 4 h4,
    sum_conditional_transfer_eq_zero d _ 2 5 h8]
  simp

theorem allocT5_classSum {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (r : Fin 8) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), allocT5 d v =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), base d v := by
  classical
  have h9 : d.length 9 = 0 → d.rep 3 = d.rep 2 := by
    intro hz
    have h := d.rep_zero 9 hz
    rw [hCore] at h
    simpa [row08Core] using h.symm
  have h4 : d.length 4 = 0 → d.rep 1 = d.rep 4 := by
    intro hz
    have h := d.rep_zero 4 hz
    rw [hCore] at h
    simpa [row08Core] using h
  have h5 : (d.length 5 = 0 ∧ hcT5 d < armAl d) → d.rep 2 = d.rep 4 := by
    intro hz
    have h := d.rep_zero 5 hz.1
    rw [hCore] at h
    simpa [row08Core] using h
  simp only [allocT5, Finset.sum_add_distrib]
  rw [sum_conditional_transfer_eq_zero d _ 3 2 h9,
    sum_conditional_transfer_eq_zero d _ 1 4 h4,
    sum_conditional_transfer_eq_zero d _ 2 4 h5]
  simp

/-! ## The left banana pair -/

def lbCoeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then headContribution (d.length 3) 0 (markY d)
  else if v = 1 then
    zeroChip (markY d) + tailContribution (markY d) (markY d) 0
  else if v = 2 then 1
  else if v = 3 then 1 + tailContribution (d.length 3) 0 (markY d)
  else if v = 4 then
    (if markY d = 0 then (0 : ℤ)
      else if d.length 4 ≤ markY d then 1 else 0)
      + (if markY d < d.length 4 then (0 : ℤ)
          else headContribution (d.length 4) (markY d) 0)
  else if v = 5 then zeroChip (markX d)
  else if v = 6 then 0
  else
    (if markX d = 0 then (0 : ℤ)
      else if d.length 7 ≤ markX d then 1 else 0)

theorem lbCoeff_eq {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (hB : d.length 3 ≤ d.length 4) (_hC : d.length 2 ≤ d.length 7) (v : Fin 8) :
    base d v + contribForm d (heightLB d) v = lbCoeff d v := by
  have hT4 := slotTailForm_of_arm d (mark := rowMark d) (h := heightLB d) (e := 4)
    (by rw [head_four hCore]; rfl)
    (by intro hz; rw [tail_four hCore]
        rw [rowMark_four] at hz
        show markY d = 0
        exact hz)
  have hH4 := slotHeadForm_of_flat_head d (mark := rowMark d) (h := heightLB d)
    (e := 4) (by rw [head_four hCore]; rfl)
    (by intro hz; rw [tail_four hCore]
        rw [rowMark_four] at hz
        show markY d = 0
        exact hz)
  have hT7 := slotTailForm_of_flat_tail d (mark := rowMark d) (h := heightLB d)
    (e := 7) (by rw [tail_seven hCore]; rfl)
  have hH7 := slotHeadForm_of_flat_head d (mark := rowMark d) (h := heightLB d)
    (e := 7) (by rw [head_seven hCore]; rfl)
    (by intro _; rw [tail_seven hCore]; rfl)
  simp only [tail_four hCore, tail_seven hCore,
    head_seven hCore, rowMark_four, rowMark_seven] at hT4 hH4 hT7 hH7
  rw [base_eq hCore]
  fin_cases v
  all_goals simp [lbCoeff, contribForm, heightLB, chipWeight, zeroChip, markY,
    hT4, hH4, hT7, hH7]
  all_goals (try (first | ring1 | ring_nf))
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals (try split_ifs)
  all_goals (try omega)

theorem lbCoeff_nonneg {d : DegSpec 8 12} (hB : d.length 3 ≤ d.length 4)
    (v : Fin 8) : 0 ≤ lbCoeff d v := by
  have hM : markY d = d.length 3 := rfl
  fin_cases v
  · show (0 : ℤ) ≤ headContribution (d.length 3) 0 (markY d)
    exact headContribution_nonneg (Nat.zero_le _) (by omega)
  · show (0 : ℤ) ≤ zeroChip (markY d) + tailContribution (markY d) (markY d) 0
    have := zeroChip_add_tail_full (markY d)
    omega
  · show (0 : ℤ) ≤ (1 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ 1 + tailContribution (d.length 3) 0 (markY d)
    have := tailContribution_ge_neg_one (L := d.length 3) (hu := 0)
      (hv := markY d) (by omega) (by omega)
    omega
  · show (0 : ℤ) ≤
      (if markY d = 0 then (0 : ℤ)
        else if d.length 4 ≤ markY d then 1 else 0)
        + (if markY d < d.length 4 then (0 : ℤ)
            else headContribution (d.length 4) (markY d) 0)
    have := headContribution_ge_neg_one (L := d.length 4) (hu := markY d)
      (hv := 0) (by omega) (by omega)
    by_cases hlt : markY d < d.length 4
    · rw [if_pos hlt]
      split_ifs <;> omega
    · rw [if_neg hlt]
      by_cases h0 : markY d = 0
      · rw [if_pos h0]
        have h4 : d.length 4 = 0 := by omega
        rw [h4, h0, headContribution_zero_zero]
        norm_num
      · rw [if_neg h0, if_pos (by omega : d.length 4 ≤ markY d)]
        omega
  · show (0 : ℤ) ≤ zeroChip (markX d)
    exact zeroChip_nonneg _
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤
      (if markX d = 0 then (0 : ℤ)
        else if d.length 7 ≤ markX d then 1 else 0)
    split_ifs <;> norm_num

def ownerZero (d : DegSpec 8 12) : Fin 8 := if d.length 3 = 0 then 3 else 0

theorem lbCoeff_owner_zero {d : DegSpec 8 12} : 1 ≤ lbCoeff d (ownerZero d) := by
  have hM : markY d = d.length 3 := rfl
  unfold ownerZero
  by_cases hz : d.length 3 = 0
  · rw [if_pos hz]
    show (1 : ℤ) ≤ 1 + tailContribution (d.length 3) 0 (markY d)
    rw [hz, show markY d = 0 by omega, tailContribution_zero_zero]
    norm_num
  · rw [if_neg hz]
    show (1 : ℤ) ≤ headContribution (d.length 3) 0 (markY d)
    rw [headContribution_eq_one_of_full (L := d.length 3) (hu := 0)
      (hv := markY d) (by omega) (by omega)]

theorem lbCoeff_owner_one {d : DegSpec 8 12} : 1 ≤ lbCoeff d 1 := by
  show (1 : ℤ) ≤ zeroChip (markY d) + tailContribution (markY d) (markY d) 0
  exact zeroChip_add_tail_full (markY d)

/-! ## The right banana pair -/

def rbCoeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then 0
  else if v = 1 then zeroChip (markY d)
  else if v = 2 then 1
  else if v = 3 then 1 + headContribution (d.length 2) (d.length 2) 0
  else if v = 4 then
    (if markY d = 0 then (0 : ℤ)
      else if d.length 4 ≤ markY d then 1 else 0)
  else if v = 5 then
    zeroChip (markX d)
      + (if 0 < markX d then (0 : ℤ)
          else tailContribution (d.length 7) 0 (d.length 2))
  else if v = 6 then tailContribution (d.length 2) (d.length 2) 0
  else
    (if markX d = 0 then (0 : ℤ)
      else if d.length 7 ≤ markX d then 1 else 0)
      + headContribution (d.length 7 - markX d) 0 (d.length 2)

theorem rbCoeff_eq {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (_hB : d.length 3 ≤ d.length 4) (hC : d.length 2 ≤ d.length 7) (v : Fin 8) :
    base d v + contribForm d (heightRB d) v = rbCoeff d v := by
  have hT4 := slotTailForm_of_flat_tail d (mark := rowMark d) (h := heightRB d)
    (e := 4) (by rw [tail_four hCore]; rfl)
  have hH4 := slotHeadForm_of_flat_head d (mark := rowMark d) (h := heightRB d)
    (e := 4) (by rw [head_four hCore]; rfl)
    (by intro _; rw [tail_four hCore]; rfl)
  have hT7 := slotTailForm_of_flat_tail d (mark := rowMark d) (h := heightRB d)
    (e := 7) (by rw [tail_seven hCore]; rfl)
  have hH7 := slotHeadForm_of_arm d (mark := rowMark d) (h := heightRB d) (e := 7)
    (by rw [tail_seven hCore]; rfl)
    (by rw [rowMark_seven]; simp only [markX]; omega)
    (by rw [head_seven hCore, rowMark_seven]
        show d.length 2 ≤ d.length 7 - markX d
        simp only [markX]; omega)
  simp only [tail_four hCore, head_four hCore,
    head_seven hCore, rowMark_four, rowMark_seven] at hT4 hH4 hT7 hH7
  rw [base_eq hCore]
  fin_cases v
  all_goals simp [rbCoeff, contribForm, heightRB, chipWeight, zeroChip, markY,
    hT4, hH4, hT7, hH7]
  all_goals (try (first | ring1 | ring_nf))
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals (try split_ifs)
  all_goals (try omega)

theorem rbCoeff_nonneg {d : DegSpec 8 12} (hC : d.length 2 ≤ d.length 7)
    (v : Fin 8) : 0 ≤ rbCoeff d v := by
  have hmX : markX d = d.length 7 - d.length 2 := rfl
  fin_cases v
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ zeroChip (markY d)
    exact zeroChip_nonneg _
  · show (0 : ℤ) ≤ (1 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ 1 + headContribution (d.length 2) (d.length 2) 0
    have := headContribution_ge_neg_one (L := d.length 2) (hu := d.length 2)
      (hv := 0) (by omega) (by omega)
    omega
  · show (0 : ℤ) ≤
      (if markY d = 0 then (0 : ℤ)
        else if d.length 4 ≤ markY d then 1 else 0)
    split_ifs <;> norm_num
  · show (0 : ℤ) ≤ zeroChip (markX d)
        + (if 0 < markX d then (0 : ℤ)
            else tailContribution (d.length 7) 0 (d.length 2))
    by_cases hp : 0 < markX d
    · rw [if_pos hp]
      have := zeroChip_nonneg (markX d)
      omega
    · rw [if_neg hp]
      have h1 : zeroChip (markX d) = 1 := by
        have hz : markX d = 0 := by omega
        simp [zeroChip, hz]
      have := tailContribution_ge_neg_one (L := d.length 7) (hu := 0)
        (hv := d.length 2) (by omega) (by omega)
      omega
  · show (0 : ℤ) ≤ tailContribution (d.length 2) (d.length 2) 0
    exact tailContribution_nonneg (Nat.zero_le _) (by omega)
  · show (0 : ℤ) ≤
      (if markX d = 0 then (0 : ℤ)
        else if d.length 7 ≤ markX d then 1 else 0)
        + headContribution (d.length 7 - markX d) 0 (d.length 2)
    have := headContribution_nonneg (L := d.length 7 - markX d) (hu := 0)
      (hv := d.length 2) (Nat.zero_le _) (by omega)
    split_ifs <;> omega

def ownerSix (d : DegSpec 8 12) : Fin 8 := if d.length 2 = 0 then 3 else 6

def ownerSeven (d : DegSpec 8 12) : Fin 8 := if d.length 7 = 0 then 5 else 7

theorem rbCoeff_owner_six {d : DegSpec 8 12} : 1 ≤ rbCoeff d (ownerSix d) := by
  unfold ownerSix
  by_cases hz : d.length 2 = 0
  · rw [if_pos hz]
    show (1 : ℤ) ≤ 1 + headContribution (d.length 2) (d.length 2) 0
    rw [hz, headContribution_zero_zero]
    norm_num
  · rw [if_neg hz]
    show (1 : ℤ) ≤ tailContribution (d.length 2) (d.length 2) 0
    rw [tailContribution_eq_one_of_full (L := d.length 2) (hu := d.length 2)
      (hv := 0) (by omega) (by omega)]

theorem rbCoeff_owner_seven {d : DegSpec 8 12} (hC : d.length 2 ≤ d.length 7) :
    1 ≤ rbCoeff d (ownerSeven d) := by
  have hmX : markX d = d.length 7 - d.length 2 := rfl
  unfold ownerSeven
  by_cases hz : d.length 7 = 0
  · rw [if_pos hz]
    show (1 : ℤ) ≤ zeroChip (markX d)
        + (if 0 < markX d then (0 : ℤ)
            else tailContribution (d.length 7) 0 (d.length 2))
    have hx : markX d = 0 := by omega
    have h2 : d.length 2 = 0 := by omega
    rw [if_neg (by omega : ¬ 0 < markX d), hz, h2, tailContribution_zero_zero,
      show zeroChip (markX d) = 1 by simp [zeroChip, hx]]
    norm_num
  · rw [if_neg hz]
    show (1 : ℤ) ≤
      (if markX d = 0 then (0 : ℤ)
        else if d.length 7 ≤ markX d then 1 else 0)
        + headContribution (d.length 7 - markX d) 0 (d.length 2)
    have hnn := headContribution_nonneg (L := d.length 7 - markX d) (hu := 0)
      (hv := d.length 2) (Nat.zero_le _) (by omega)
    by_cases h2 : d.length 2 = 0
    · have hx : markX d = d.length 7 := by omega
      rw [if_neg (by omega : ¬ markX d = 0),
        if_pos (by omega : d.length 7 ≤ markX d)]
      omega
    · have hone : headContribution (d.length 7 - markX d) 0 (d.length 2) = 1 :=
        headContribution_eq_one_of_full (L := d.length 7 - markX d) (hu := 0)
          (hv := d.length 2) (by omega) (by omega)
      rw [hone]
      split_ifs <;> omega

/-! ## The chipped triangle at the target `4` -/

def t4Coeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then 0
  else if v = 1 then
    (zeroChip (markY d) - zeroChip (d.length 4))
      + (if 0 < markY d then (0 : ℤ)
          else tailContribution (d.length 4) 0 (htT4 d))
  else if v = 2 then
    1 + zeroChip (d.length 9) - lend (d.length 8) (hcT4 d) (markX d)
      + (tailContribution (d.length 9) (hcT4 d) 0
          + tailContribution (d.length 5) (hcT4 d) (htT4 d)
          + headContribution (d.length 8) (hvT4 d) (hcT4 d))
  else if v = 3 then
    positiveChip (d.length 9) + headContribution (d.length 9) (hcT4 d) 0
  else if v = 4 then
    zeroChip (armAl d)
      + (headContribution (armAl d) 0 (htT4 d)
          + headContribution (d.length 5) (hcT4 d) (htT4 d)
          + tailContribution (d.length 6) (htT4 d) (hvT4 d))
  else if v = 5 then
    zeroChip (markX d) + lend (d.length 8) (hcT4 d) (markX d)
      + (tailContribution (markX d) (hvT4 d) 0
          + tailContribution (d.length 8) (hvT4 d) (hcT4 d)
          + headContribution (d.length 6) (htT4 d) (hvT4 d))
  else if v = 6 then 0
  else
    (if markX d = 0 then (0 : ℤ)
      else if d.length 7 ≤ markX d then 1 else 0)
      + (if markX d < d.length 7 then (0 : ℤ)
          else headContribution (d.length 7) (hvT4 d) 0)

theorem t4Coeff_eq {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (hB : d.length 3 ≤ d.length 4) (_hC : d.length 2 ≤ d.length 7) (v : Fin 8) :
    allocT4 d v + contribForm d (heightT4 d) v = t4Coeff d v := by
  obtain ⟨⟨hcga, hcal, hcbe⟩, -, ⟨h0be, h0hc, hch0⟩, -,
    ⟨htal, hthc, hth0, hcht⟩, -, ⟨hvh0, hvht, hchv, hthv, hvhcr, hvbe⟩, -⟩ :=
    boundsT4 d
  have hAl : armAl d = d.length 4 - markY d := rfl
  have hT4 := slotTailForm_of_flat_tail d (mark := rowMark d) (h := heightT4 d)
    (e := 4) (by rw [tail_four hCore]; rfl)
  have hH4 := slotHeadForm_of_arm d (mark := rowMark d) (h := heightT4 d) (e := 4)
    (by rw [tail_four hCore]; rfl)
    (by rw [rowMark_four]; simpa [markY] using hB)
    (by rw [head_four hCore, rowMark_four]
        show htT4 d ≤ d.length 4 - markY d
        omega)
  have hT7 := slotTailForm_of_arm d (mark := rowMark d) (h := heightT4 d) (e := 7)
    (by rw [head_seven hCore]; rfl)
    (by intro hz; rw [tail_seven hCore]
        rw [rowMark_seven] at hz
        show hvT4 d = 0
        omega)
  have hH7 := slotHeadForm_of_flat_head d (mark := rowMark d) (h := heightT4 d)
    (e := 7) (by rw [head_seven hCore]; rfl)
    (by intro hz; rw [tail_seven hCore]
        rw [rowMark_seven] at hz
        show hvT4 d = 0
        omega)
  simp only [head_four hCore, tail_seven hCore,
    rowMark_four, rowMark_seven] at hT4 hH4 hT7 hH7
  simp only [allocT4]
  rw [base_eq hCore]
  fin_cases v
  all_goals simp [t4Coeff, contribForm, heightT4, chipWeight, zeroChip,
    positiveChip, lend, transferWeight, indicatorWeight, armAl, markY,
    hT4, hH4, hT7, hH7]
  all_goals (try (first | ring1 | ring_nf))
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals (try omega)

theorem t4Coeff_nonneg {d : DegSpec 8 12} (hB : d.length 3 ≤ d.length 4)
    (hC : d.length 2 ≤ d.length 7) (v : Fin 8) : 0 ≤ t4Coeff d v := by
  obtain ⟨⟨hcga, hcal, hcbe⟩, -, ⟨h0be, h0hc, hch0⟩, -,
    ⟨htal, hthc, hth0, hcht⟩, -, ⟨hvh0, hvht, hchv, hthv, hvhcr, hvbe⟩, -⟩ :=
    boundsT4 d
  have hAl : armAl d = d.length 4 - markY d := rfl
  have hmX : markX d = d.length 7 - d.length 2 := rfl
  fin_cases v
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ (zeroChip (markY d) - zeroChip (d.length 4))
        + (if 0 < markY d then (0 : ℤ)
            else tailContribution (d.length 4) 0 (htT4 d))
    by_cases hp : 0 < markY d
    · rw [if_pos hp]
      have h1 : zeroChip (markY d) = 0 := by
        have hne : markY d ≠ 0 := by omega
        simp [zeroChip, hne]
      have h2 : zeroChip (d.length 4) = 0 := by
        have hne : d.length 4 ≠ 0 := by
          have : markY d = d.length 3 := rfl
          omega
        simp [zeroChip, hne]
      omega
    · rw [if_neg hp]
      have h1 : zeroChip (markY d) = 1 := by
        have hz : markY d = 0 := by omega
        simp [zeroChip, hz]
      have hpos := positiveChip_add_tail_nonneg (L := d.length 4)
        (h := htT4 d) (by omega)
      have h2 : positiveChip (d.length 4) = 1 - zeroChip (d.length 4) := by
        unfold positiveChip zeroChip
        split_ifs <;> omega
      omega
  · show (0 : ℤ) ≤ 1 + zeroChip (d.length 9)
        - lend (d.length 8) (hcT4 d) (markX d)
        + (tailContribution (d.length 9) (hcT4 d) 0
            + tailContribution (d.length 5) (hcT4 d) (htT4 d)
            + headContribution (d.length 8) (hvT4 d) (hcT4 d))
    have := triangleChipped_nonneg fwd fwd rev (k := (0 : ℤ))
      (al := armAl d) (be := markX d) (ga := d.length 9) (p := d.length 5)
      (q := d.length 6) (r := d.length 8) (hc := hcT4 d) (h0 := h0T4 d)
      (ht := htT4 d) (hv := hvT4 d) rfl rfl rfl rfl le_rfl (by norm_num)
      (by intro hcon; exact absurd hcon (by norm_num))
    simp only [fwd_tail, rev_tail] at this
    omega
  · show (0 : ℤ) ≤ positiveChip (d.length 9)
        + headContribution (d.length 9) (hcT4 d) 0
    exact positiveChip_add_head_nonneg (by omega)
  · show (0 : ℤ) ≤ zeroChip (armAl d)
        + (headContribution (armAl d) 0 (htT4 d)
            + headContribution (d.length 5) (hcT4 d) (htT4 d)
            + tailContribution (d.length 6) (htT4 d) (hvT4 d))
    have := triangleTarget_nonneg rev rev fwd (k := (0 : ℤ))
      (al := armAl d) (be := markX d) (ga := d.length 9) (p := d.length 5)
      (q := d.length 6) (r := d.length 8) (hc := hcT4 d) (h0 := h0T4 d)
      (ht := htT4 d) (hv := hvT4 d) rfl rfl rfl rfl le_rfl (by norm_num)
      (by intro hcon; exact absurd hcon (by norm_num))
    simp only [fwd_tail, rev_tail] at this
    omega
  · show (0 : ℤ) ≤ zeroChip (markX d) + lend (d.length 8) (hcT4 d) (markX d)
        + (tailContribution (markX d) (hvT4 d) 0
            + tailContribution (d.length 8) (hvT4 d) (hcT4 d)
            + headContribution (d.length 6) (htT4 d) (hvT4 d))
    have := trianglePartner_nonneg fwd fwd rev (k := (0 : ℤ))
      (al := armAl d) (be := markX d) (ga := d.length 9) (p := d.length 5)
      (q := d.length 6) (r := d.length 8) (hc := hcT4 d) (h0 := h0T4 d)
      (ht := htT4 d) (hv := hvT4 d) rfl rfl rfl rfl le_rfl (by norm_num)
      (by intro hcon; exact absurd hcon (by norm_num))
    simp only [fwd_tail, rev_tail] at this
    omega
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤
      (if markX d = 0 then (0 : ℤ)
        else if d.length 7 ≤ markX d then 1 else 0)
        + (if markX d < d.length 7 then (0 : ℤ)
            else headContribution (d.length 7) (hvT4 d) 0)
    by_cases hlt : markX d < d.length 7
    · rw [if_pos hlt]
      split_ifs <;> omega
    · rw [if_neg hlt]
      have := headContribution_ge_neg_one (L := d.length 7) (hu := hvT4 d)
        (hv := 0) (by omega) (by omega)
      by_cases h0 : markX d = 0
      · rw [if_pos h0]
        have h7 : d.length 7 = 0 := by omega
        have hv0 : hvT4 d = 0 := by omega
        rw [h7, hv0, headContribution_zero_zero]
        norm_num
      · rw [if_neg h0, if_pos (by omega : d.length 7 ≤ markX d)]
        omega

def ownerFour (d : DegSpec 8 12) : Fin 8 :=
  if Delivers (armAl d) (d.length 5) (d.length 6) (hcT4 d) (h0T4 d) (htT4 d)
    then 4
  else if d.length 5 = 0 ∧ lend (d.length 8) (hcT4 d) (markX d) = 0 then 2
  else 5

theorem t4Coeff_owner {d : DegSpec 8 12} : 1 ≤ t4Coeff d (ownerFour d) := by
  obtain ⟨⟨hcga, hcal, hcbe⟩, -, ⟨h0be, h0hc, hch0⟩, -,
    ⟨htal, hthc, hth0, hcht⟩, -, ⟨hvh0, hvht, hchv, hthv, hvhcr, hvbe⟩, -⟩ :=
    boundsT4 d
  unfold ownerFour
  by_cases hDel : Delivers (armAl d) (d.length 5) (d.length 6) (hcT4 d)
      (h0T4 d) (htT4 d)
  · rw [if_pos hDel]
    show (1 : ℤ) ≤ zeroChip (armAl d)
        + (headContribution (armAl d) 0 (htT4 d)
            + headContribution (d.length 5) (hcT4 d) (htT4 d)
            + tailContribution (d.length 6) (htT4 d) (hvT4 d))
    have := triangleTarget_nonneg rev rev fwd (k := (1 : ℤ))
      (al := armAl d) (be := markX d) (ga := d.length 9) (p := d.length 5)
      (q := d.length 6) (r := d.length 8) (hc := hcT4 d) (h0 := h0T4 d)
      (ht := htT4 d) (hv := hvT4 d) rfl rfl rfl rfl (by norm_num) le_rfl
      (fun _ => hDel)
    simp only [fwd_tail, rev_tail] at this
    omega
  · rw [if_neg hDel]
    by_cases hFall : d.length 5 = 0 ∧ lend (d.length 8) (hcT4 d) (markX d) = 0
    · rw [if_pos hFall]
      show (1 : ℤ) ≤ 1 + zeroChip (d.length 9)
          - lend (d.length 8) (hcT4 d) (markX d)
          + (tailContribution (d.length 9) (hcT4 d) 0
              + tailContribution (d.length 5) (hcT4 d) (htT4 d)
              + headContribution (d.length 8) (hvT4 d) (hcT4 d))
      have := triangleChipped_nonneg fwd fwd rev (k := (1 : ℤ))
        (al := armAl d) (be := markX d) (ga := d.length 9) (p := d.length 5)
        (q := d.length 6) (r := d.length 8) (hc := hcT4 d) (h0 := h0T4 d)
        (ht := htT4 d) (hv := hvT4 d) rfl rfl rfl rfl (by norm_num) le_rfl
        (fun _ => hFall)
      simp only [fwd_tail, rev_tail] at this
      omega
    · rw [if_neg hFall]
      show (1 : ℤ) ≤ zeroChip (markX d) + lend (d.length 8) (hcT4 d) (markX d)
          + (tailContribution (markX d) (hvT4 d) 0
              + tailContribution (d.length 8) (hvT4 d) (hcT4 d)
              + headContribution (d.length 6) (htT4 d) (hvT4 d))
      have hOwn := partnerOwns_of_not_delivers (al := armAl d) (be := markX d)
        (ga := d.length 9) (p := d.length 5) (q := d.length 6) (r := d.length 8)
        (hc := hcT4 d) (h0 := h0T4 d) (ht := htT4 d) (hv := hvT4 d)
        rfl rfl rfl rfl hDel hFall
      have := trianglePartner_nonneg fwd fwd rev (k := (1 : ℤ))
        (al := armAl d) (be := markX d) (ga := d.length 9) (p := d.length 5)
        (q := d.length 6) (r := d.length 8) (hc := hcT4 d) (h0 := h0T4 d)
        (ht := htT4 d) (hv := hvT4 d) rfl rfl rfl rfl (by norm_num) le_rfl
        (fun _ => hOwn)
      simp only [fwd_tail, rev_tail] at this
      omega

/-! ## The chipped triangle at the target `5` -/

def t5Coeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then 0
  else if v = 1 then
    (zeroChip (markY d) - zeroChip (d.length 4))
      + (if 0 < markY d then (0 : ℤ)
          else tailContribution (d.length 4) 0 (hvT5 d))
  else if v = 2 then
    1 + zeroChip (d.length 9) - lend (d.length 5) (hcT5 d) (armAl d)
      + (tailContribution (d.length 9) (hcT5 d) 0
          + headContribution (d.length 8) (htT5 d) (hcT5 d)
          + tailContribution (d.length 5) (hcT5 d) (hvT5 d))
  else if v = 3 then
    positiveChip (d.length 9) + headContribution (d.length 9) (hcT5 d) 0
  else if v = 4 then
    zeroChip (armAl d) + lend (d.length 5) (hcT5 d) (armAl d)
      + (headContribution (armAl d) 0 (hvT5 d)
          + headContribution (d.length 5) (hcT5 d) (hvT5 d)
          + tailContribution (d.length 6) (hvT5 d) (htT5 d))
  else if v = 5 then
    zeroChip (markX d)
      + (tailContribution (markX d) (htT5 d) 0
          + tailContribution (d.length 8) (htT5 d) (hcT5 d)
          + headContribution (d.length 6) (hvT5 d) (htT5 d))
  else if v = 6 then 0
  else
    (if markX d = 0 then (0 : ℤ)
      else if d.length 7 ≤ markX d then 1 else 0)
      + (if markX d < d.length 7 then (0 : ℤ)
          else headContribution (d.length 7) (htT5 d) 0)

theorem t5Coeff_eq {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (hB : d.length 3 ≤ d.length 4) (_hC : d.length 2 ≤ d.length 7) (v : Fin 8) :
    allocT5 d v + contribForm d (heightT5 d) v = t5Coeff d v := by
  obtain ⟨⟨hcga, hcbe, hcal⟩, -, ⟨h0al, h0hc, hch0⟩, -,
    ⟨htbe, hthc, hth0, hcht⟩, -, ⟨hvh0, hvht, hchv, hthv, hvhcr, hval⟩, -⟩ :=
    boundsT5 d
  have hAl : armAl d = d.length 4 - markY d := rfl
  have hT4 := slotTailForm_of_flat_tail d (mark := rowMark d) (h := heightT5 d)
    (e := 4) (by rw [tail_four hCore]; rfl)
  have hH4 := slotHeadForm_of_arm d (mark := rowMark d) (h := heightT5 d) (e := 4)
    (by rw [tail_four hCore]; rfl)
    (by rw [rowMark_four]; simpa [markY] using hB)
    (by rw [head_four hCore, rowMark_four]
        show hvT5 d ≤ d.length 4 - markY d
        omega)
  have hT7 := slotTailForm_of_arm d (mark := rowMark d) (h := heightT5 d) (e := 7)
    (by rw [head_seven hCore]; rfl)
    (by intro hz; rw [tail_seven hCore]
        rw [rowMark_seven] at hz
        show htT5 d = 0
        omega)
  have hH7 := slotHeadForm_of_flat_head d (mark := rowMark d) (h := heightT5 d)
    (e := 7) (by rw [head_seven hCore]; rfl)
    (by intro hz; rw [tail_seven hCore]
        rw [rowMark_seven] at hz
        show htT5 d = 0
        omega)
  simp only [head_four hCore, tail_seven hCore,
    rowMark_four, rowMark_seven] at hT4 hH4 hT7 hH7
  simp only [allocT5]
  rw [base_eq hCore]
  fin_cases v
  all_goals simp [t5Coeff, contribForm, heightT5, chipWeight, zeroChip,
    positiveChip, lend, transferWeight, indicatorWeight, armAl, markY,
    hT4, hH4, hT7, hH7]
  all_goals (try (first | ring1 | ring_nf))
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals (try split_ifs)
  all_goals (try omega)

theorem t5Coeff_nonneg {d : DegSpec 8 12} (hB : d.length 3 ≤ d.length 4)
    (hC : d.length 2 ≤ d.length 7) (v : Fin 8) : 0 ≤ t5Coeff d v := by
  obtain ⟨⟨hcga, hcbe, hcal⟩, -, ⟨h0al, h0hc, hch0⟩, -,
    ⟨htbe, hthc, hth0, hcht⟩, -, ⟨hvh0, hvht, hchv, hthv, hvhcr, hval⟩, -⟩ :=
    boundsT5 d
  have hAl : armAl d = d.length 4 - markY d := rfl
  have hmX : markX d = d.length 7 - d.length 2 := rfl
  fin_cases v
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ (zeroChip (markY d) - zeroChip (d.length 4))
        + (if 0 < markY d then (0 : ℤ)
            else tailContribution (d.length 4) 0 (hvT5 d))
    by_cases hp : 0 < markY d
    · rw [if_pos hp]
      have h1 : zeroChip (markY d) = 0 := by
        have hne : markY d ≠ 0 := by omega
        simp [zeroChip, hne]
      have h2 : zeroChip (d.length 4) = 0 := by
        have hne : d.length 4 ≠ 0 := by
          have : markY d = d.length 3 := rfl
          omega
        simp [zeroChip, hne]
      omega
    · rw [if_neg hp]
      have h1 : zeroChip (markY d) = 1 := by
        have hz : markY d = 0 := by omega
        simp [zeroChip, hz]
      have hpos := positiveChip_add_tail_nonneg (L := d.length 4)
        (h := hvT5 d) (by omega)
      have h2 : positiveChip (d.length 4) = 1 - zeroChip (d.length 4) := by
        unfold positiveChip zeroChip
        split_ifs <;> omega
      omega
  · show (0 : ℤ) ≤ 1 + zeroChip (d.length 9)
        - lend (d.length 5) (hcT5 d) (armAl d)
        + (tailContribution (d.length 9) (hcT5 d) 0
            + headContribution (d.length 8) (htT5 d) (hcT5 d)
            + tailContribution (d.length 5) (hcT5 d) (hvT5 d))
    have := triangleChipped_nonneg fwd rev fwd (k := (0 : ℤ))
      (al := markX d) (be := armAl d) (ga := d.length 9) (p := d.length 8)
      (q := d.length 6) (r := d.length 5) (hc := hcT5 d) (h0 := h0T5 d)
      (ht := htT5 d) (hv := hvT5 d) rfl rfl rfl rfl le_rfl (by norm_num)
      (by intro hcon; exact absurd hcon (by norm_num))
    simp only [fwd_tail, rev_tail] at this
    omega
  · show (0 : ℤ) ≤ positiveChip (d.length 9)
        + headContribution (d.length 9) (hcT5 d) 0
    exact positiveChip_add_head_nonneg (by omega)
  · show (0 : ℤ) ≤ zeroChip (armAl d) + lend (d.length 5) (hcT5 d) (armAl d)
        + (headContribution (armAl d) 0 (hvT5 d)
            + headContribution (d.length 5) (hcT5 d) (hvT5 d)
            + tailContribution (d.length 6) (hvT5 d) (htT5 d))
    have := trianglePartner_nonneg rev rev fwd (k := (0 : ℤ))
      (al := markX d) (be := armAl d) (ga := d.length 9) (p := d.length 8)
      (q := d.length 6) (r := d.length 5) (hc := hcT5 d) (h0 := h0T5 d)
      (ht := htT5 d) (hv := hvT5 d) rfl rfl rfl rfl le_rfl (by norm_num)
      (by intro hcon; exact absurd hcon (by norm_num))
    simp only [fwd_tail, rev_tail] at this
    omega
  · show (0 : ℤ) ≤ zeroChip (markX d)
        + (tailContribution (markX d) (htT5 d) 0
            + tailContribution (d.length 8) (htT5 d) (hcT5 d)
            + headContribution (d.length 6) (hvT5 d) (htT5 d))
    have := triangleTarget_nonneg fwd fwd rev (k := (0 : ℤ))
      (al := markX d) (be := armAl d) (ga := d.length 9) (p := d.length 8)
      (q := d.length 6) (r := d.length 5) (hc := hcT5 d) (h0 := h0T5 d)
      (ht := htT5 d) (hv := hvT5 d) rfl rfl rfl rfl le_rfl (by norm_num)
      (by intro hcon; exact absurd hcon (by norm_num))
    simp only [fwd_tail, rev_tail] at this
    omega
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤
      (if markX d = 0 then (0 : ℤ)
        else if d.length 7 ≤ markX d then 1 else 0)
        + (if markX d < d.length 7 then (0 : ℤ)
            else headContribution (d.length 7) (htT5 d) 0)
    by_cases hlt : markX d < d.length 7
    · rw [if_pos hlt]
      split_ifs <;> omega
    · rw [if_neg hlt]
      have := headContribution_ge_neg_one (L := d.length 7) (hu := htT5 d)
        (hv := 0) (by omega) (by omega)
      by_cases h0 : markX d = 0
      · rw [if_pos h0]
        have h7 : d.length 7 = 0 := by omega
        have hv0 : htT5 d = 0 := by omega
        rw [h7, hv0, headContribution_zero_zero]
        norm_num
      · rw [if_neg h0, if_pos (by omega : d.length 7 ≤ markX d)]
        omega

def ownerFive (d : DegSpec 8 12) : Fin 8 :=
  if Delivers (markX d) (d.length 8) (d.length 6) (hcT5 d) (h0T5 d) (htT5 d)
    then 5
  else if d.length 8 = 0 ∧ lend (d.length 5) (hcT5 d) (armAl d) = 0 then 2
  else 4

theorem t5Coeff_owner {d : DegSpec 8 12} : 1 ≤ t5Coeff d (ownerFive d) := by
  obtain ⟨⟨hcga, hcbe, hcal⟩, -, ⟨h0al, h0hc, hch0⟩, -,
    ⟨htbe, hthc, hth0, hcht⟩, -, ⟨hvh0, hvht, hchv, hthv, hvhcr, hval⟩, -⟩ :=
    boundsT5 d
  unfold ownerFive
  by_cases hDel : Delivers (markX d) (d.length 8) (d.length 6) (hcT5 d)
      (h0T5 d) (htT5 d)
  · rw [if_pos hDel]
    show (1 : ℤ) ≤ zeroChip (markX d)
        + (tailContribution (markX d) (htT5 d) 0
            + tailContribution (d.length 8) (htT5 d) (hcT5 d)
            + headContribution (d.length 6) (hvT5 d) (htT5 d))
    have := triangleTarget_nonneg fwd fwd rev (k := (1 : ℤ))
      (al := markX d) (be := armAl d) (ga := d.length 9) (p := d.length 8)
      (q := d.length 6) (r := d.length 5) (hc := hcT5 d) (h0 := h0T5 d)
      (ht := htT5 d) (hv := hvT5 d) rfl rfl rfl rfl (by norm_num) le_rfl
      (fun _ => hDel)
    simp only [fwd_tail, rev_tail] at this
    omega
  · rw [if_neg hDel]
    by_cases hFall : d.length 8 = 0 ∧ lend (d.length 5) (hcT5 d) (armAl d) = 0
    · rw [if_pos hFall]
      show (1 : ℤ) ≤ 1 + zeroChip (d.length 9)
          - lend (d.length 5) (hcT5 d) (armAl d)
          + (tailContribution (d.length 9) (hcT5 d) 0
              + headContribution (d.length 8) (htT5 d) (hcT5 d)
              + tailContribution (d.length 5) (hcT5 d) (hvT5 d))
      have := triangleChipped_nonneg fwd rev fwd (k := (1 : ℤ))
        (al := markX d) (be := armAl d) (ga := d.length 9) (p := d.length 8)
        (q := d.length 6) (r := d.length 5) (hc := hcT5 d) (h0 := h0T5 d)
        (ht := htT5 d) (hv := hvT5 d) rfl rfl rfl rfl (by norm_num) le_rfl
        (fun _ => hFall)
      simp only [fwd_tail, rev_tail] at this
      omega
    · rw [if_neg hFall]
      show (1 : ℤ) ≤ zeroChip (armAl d) + lend (d.length 5) (hcT5 d) (armAl d)
          + (headContribution (armAl d) 0 (hvT5 d)
              + headContribution (d.length 5) (hcT5 d) (hvT5 d)
              + tailContribution (d.length 6) (hvT5 d) (htT5 d))
      have hOwn := partnerOwns_of_not_delivers (al := markX d) (be := armAl d)
        (ga := d.length 9) (p := d.length 8) (q := d.length 6) (r := d.length 5)
        (hc := hcT5 d) (h0 := h0T5 d) (ht := htT5 d) (hv := hvT5 d)
        rfl rfl rfl rfl hDel hFall
      have := trianglePartner_nonneg rev rev fwd (k := (1 : ℤ))
        (al := markX d) (be := armAl d) (ga := d.length 9) (p := d.length 8)
        (q := d.length 6) (r := d.length 5) (hc := hcT5 d) (h0 := h0T5 d)
        (ht := htT5 d) (hv := hvT5 d) rfl rfl rfl rfl (by norm_num) le_rfl
        (fun _ => hOwn)
      simp only [fwd_tail, rev_tail] at this
      omega

/-! ## Every contracted core class is reached -/

theorem rowDivisor_reaches_coreVertex {d : DegSpec 8 12}
    (hCore : d.core = row08Core)
    (hB : d.length 3 ≤ d.length 4) (hC : d.length 2 ≤ d.length 7)
    (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8, d.rep x = d.rep y ↔ ReachIn row08Core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0) (center : Fin 8) :
    Reaches d.graph (rowDivisor d) (d.coreVertex center) := by
  have hCoreValue : ∀ r : Fin 8, rowDivisor d (d.coreVertex r) =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), base d v :=
    markedDivisorTwo_coreVertex d chipWeight (rowMark d) 4 7
  have hInterior := markedDivisorTwo_interior d chipWeight (rowMark d)
    chipWeight_nonneg 4 7
  have hChip := markedDivisorTwo_chip d chipWeight (rowMark d)
    (fun g hg => marked_of_rowMark_pos d hg)
  have hBase : ∀ r : Fin 8,
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), base d v =
        ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), base d v :=
    fun _ => rfl
  have hA4 := allocT4_classSum hCore
  have hA5 := allocT5_classSum hCore
  have hpLB := profileLB hCore hB hC
  have hpRB := profileRB hCore hB hC
  have hpT4 := profileT4 hCore hB hC
  have hpT5 := profileT5 hCore hB hC
  have hrLB := height_rep_eq d hCore hpLB.const F hRepReach hFZero
  have hrRB := height_rep_eq d hCore hpRB.const F hRepReach hFZero
  have hrT4 := height_rep_eq d hCore hpT4.const F hRepReach hFZero
  have hrT5 := height_rep_eq d hCore hpT5.const F hRepReach hFZero
  have hrep5 : d.length 5 = 0 → d.rep 2 = d.rep 4 := by
    intro hz
    have h := d.rep_zero 5 hz
    rw [hCore] at h
    simpa [row08Core] using h
  have hrep6 : d.length 6 = 0 → d.rep 5 = d.rep 4 := by
    intro hz
    have h := d.rep_zero 6 hz
    rw [hCore] at h
    simpa [row08Core] using h.symm
  have hrep8 : d.length 8 = 0 → d.rep 5 = d.rep 2 := by
    intro hz
    have h := d.rep_zero 8 hz
    rw [hCore] at h
    simpa [row08Core] using h
  have hOZ : d.rep (ownerZero d) = d.rep 0 := by
    unfold ownerZero
    by_cases hz : d.length 3 = 0
    · rw [if_pos hz]
      have h := d.rep_zero 3 hz
      rw [hCore] at h
      simpa [row08Core] using h
    · rw [if_neg hz]
  have hOSix : d.rep (ownerSix d) = d.rep 6 := by
    unfold ownerSix
    by_cases hz : d.length 2 = 0
    · rw [if_pos hz]
      have h := d.rep_zero 2 hz
      rw [hCore] at h
      simpa [row08Core] using h.symm
    · rw [if_neg hz]
  have hOS : d.rep (ownerSeven d) = d.rep 7 := by
    unfold ownerSeven
    by_cases hz : d.length 7 = 0
    · rw [if_pos hz]
      have h := d.rep_zero 7 hz
      rw [hCore] at h
      simpa [row08Core] using h
    · rw [if_neg hz]
  have hOF : d.rep (ownerFour d) = d.rep 4 := by
    unfold ownerFour
    by_cases hDel : Delivers (armAl d) (d.length 5) (d.length 6) (hcT4 d)
        (h0T4 d) (htT4 d)
    · rw [if_pos hDel]
    · rw [if_neg hDel]
      by_cases hFall : d.length 5 = 0 ∧ lend (d.length 8) (hcT4 d) (markX d) = 0
      · rw [if_pos hFall]
        exact hrep5 hFall.1
      · rw [if_neg hFall]
        rcases class_of_not_delivers (al := armAl d) (be := markX d)
          (ga := d.length 9) (p := d.length 5) (q := d.length 6)
          (r := d.length 8) (hc := hcT4 d) (h0 := h0T4 d) (ht := htT4 d)
          (hv := hvT4 d) rfl rfl rfl rfl hDel hFall with h6 | ⟨h5, h8⟩
        · exact hrep6 h6
        · rw [hrep8 h8]; exact hrep5 h5
  have hOFive : d.rep (ownerFive d) = d.rep 5 := by
    unfold ownerFive
    by_cases hDel : Delivers (markX d) (d.length 8) (d.length 6) (hcT5 d)
        (h0T5 d) (htT5 d)
    · rw [if_pos hDel]
    · rw [if_neg hDel]
      by_cases hFall : d.length 8 = 0 ∧ lend (d.length 5) (hcT5 d) (armAl d) = 0
      · rw [if_pos hFall]
        exact (hrep8 hFall.1).symm
      · rw [if_neg hFall]
        rcases class_of_not_delivers (al := markX d) (be := armAl d)
          (ga := d.length 9) (p := d.length 8) (q := d.length 6)
          (r := d.length 5) (hc := hcT5 d) (h0 := h0T5 d) (ht := htT5 d)
          (hv := hvT5 d) rfl rfl rfl rfl hDel hFall with h6 | ⟨h8, h5⟩
        · exact (hrep6 h6).symm
        · rw [← hrep5 h5]; exact (hrep8 h8).symm
  fin_cases center
  · exact (DharMove.ofScript _ (residual_effective d hpLB hrLB hCoreValue
      hInterior hChip hBase hOZ (fun v => by
        rw [contrib_eq hCore hpLB hrLB v]
        exact residual_of_coeff
          (fun w => by rw [lbCoeff_eq hCore hB hC w]; exact lbCoeff_nonneg hB w)
          (by rw [lbCoeff_eq hCore hB hC (ownerZero d)]
              exact lbCoeff_owner_zero) v))).reaches
  · exact (DharMove.ofScript _ (residual_effective d hpLB hrLB hCoreValue
      hInterior hChip hBase (rfl : d.rep 1 = d.rep 1) (fun v => by
        rw [contrib_eq hCore hpLB hrLB v]
        exact residual_of_coeff
          (fun w => by rw [lbCoeff_eq hCore hB hC w]; exact lbCoeff_nonneg hB w)
          (by rw [lbCoeff_eq hCore hB hC 1]; exact lbCoeff_owner_one) v))).reaches
  · exact reaches_of_effective_representative
      (linearEquiv.refl d.graph (rowDivisor d)) (rowDivisor_effective d)
      (one_le_markedDivisorTwo_at_chip d chipWeight (rowMark d) 4 7
        chipWeight_nonneg (c := 2) (by decide))
  · exact reaches_of_effective_representative
      (linearEquiv.refl d.graph (rowDivisor d)) (rowDivisor_effective d)
      (one_le_markedDivisorTwo_at_chip d chipWeight (rowMark d) 4 7
        chipWeight_nonneg (c := 3) (by decide))
  · exact (DharMove.ofScript _ (residual_effective d hpT4 hrT4 hCoreValue
      hInterior hChip hA4 hOF (fun v => by
        rw [contrib_eq hCore hpT4 hrT4 v]
        exact residual_of_coeff
          (fun w => by rw [t4Coeff_eq hCore hB hC w]
                       exact t4Coeff_nonneg hB hC w)
          (by rw [t4Coeff_eq hCore hB hC (ownerFour d)]
              exact t4Coeff_owner) v))).reaches
  · exact (DharMove.ofScript _ (residual_effective d hpT5 hrT5 hCoreValue
      hInterior hChip hA5 hOFive (fun v => by
        rw [contrib_eq hCore hpT5 hrT5 v]
        exact residual_of_coeff
          (fun w => by rw [t5Coeff_eq hCore hB hC w]
                       exact t5Coeff_nonneg hB hC w)
          (by rw [t5Coeff_eq hCore hB hC (ownerFive d)]
              exact t5Coeff_owner) v))).reaches
  · exact (DharMove.ofScript _ (residual_effective d hpRB hrRB hCoreValue
      hInterior hChip hBase hOSix (fun v => by
        rw [contrib_eq hCore hpRB hrRB v]
        exact residual_of_coeff
          (fun w => by rw [rbCoeff_eq hCore hB hC w]; exact rbCoeff_nonneg hC w)
          (by rw [rbCoeff_eq hCore hB hC (ownerSix d)]
              exact rbCoeff_owner_six) v))).reaches
  · exact (DharMove.ofScript _ (residual_effective d hpRB hrRB hCoreValue
      hInterior hChip hBase hOS (fun v => by
        rw [contrib_eq hCore hpRB hrRB v]
        exact residual_of_coeff
          (fun w => by rw [rbCoeff_eq hCore hB hC w]; exact rbCoeff_nonneg hC w)
          (by rw [rbCoeff_eq hCore hB hC (ownerSeven d)]
              exact rbCoeff_owner_seven hC) v))).reaches

/-- **AR's seventh family, second scope.**  The chipped triangle. -/
theorem chamberTwo_pencil (length : Fin 12 → ℕ)
    (forest : IsForest row08Core (zeroSlots length))
    (notLoopy : ¬ IsLoopy row08Core (zeroSlots length))
    (hP : GenusFiveRow08Symmetry.ChamberTwo length) :
    Nonempty (DegreeFourDharPencil
      (faceSpec row08Core (by norm_num) length forest notLoopy).graph) := by
  let d := faceSpec row08Core (by norm_num) length forest notLoopy
  have hCore : d.core = row08Core := rfl
  have hRepReach : ∀ x y : Fin 8,
      d.rep x = d.rep y ↔ ReachIn row08Core (zeroSlots length) x y := fun x y =>
    compFold_iff row08Core (zeroSlots length) x y
  have hFZero : ∀ e : Fin 12, e ∈ zeroSlots length ↔ d.length e = 0 := by
    intro e
    simp [d, faceSpec, zeroSlots]
  refine ⟨DegreeFourDharPencil.ofEffectiveRankOne (rowDivisor d)
    (rowDivisor_effective d) (rowDivisor_degree d) ?_⟩
  apply d.rank_ge_one_of_reaches_coreVertices (by rw [hCore]; exact row08_connected)
  intro center
  exact rowDivisor_reaches_coreVertex hCore hP.1 hP.2 (zeroSlots length)
    hRepReach hFZero center

end AtanasovRanganathan.GenusFiveRow08ChamberTwo
