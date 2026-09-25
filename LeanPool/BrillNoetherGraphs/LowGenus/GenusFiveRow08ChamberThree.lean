/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationBananaDoubleChip
public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationMarkedRow
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow08Symmetry

/-!
# AR row 08, chamber 3

The third scope AR draw for their seventh family: `|e3| ≤ |e4|` and
`|e7| ≤ |e2|`, i.e. `b ≤ a` and `d ≤ c`.  This is the scope whose caption notes
that *"the last divisor has two chips placed on the same vertex"*:

```
 D = 2 * [5] + [3] + (e4 at distance |e3| from 1)
```

so there is a **single** mark, `mark e4 = |e3|` (measured from `e4`'s tail `1`),
and the divisor is `markedDivisorOne` rather than `markedDivisorTwo`.  The six
chip-free vertices split as

* `{0, 1}` -- a banana pair whose two arms both have length `|e3|`: the whole of
  `e3` read from its head `0`, and the near half of `e4`.
* `{2, 4}` -- a `ConfigurationThree` pair across `e5 : 2 → 4`; vertex `2`'s arms
  are `e9` (to the chip `3`) and `e8` (to the double chip `5`), vertex `4`'s are
  `e6` (to `5`) and the far half of `e4` (to the marked chip).  The chip vertex
  `5` is the endpoint of two arms but carries **two** chips, which is exactly
  what `ConfigurationMarkedThree`'s `chipSum`-with-multiplicity phrasing was
  designed for.
* `{6, 7}` -- a **lopsided** banana pair: vertex `6`'s arm is the whole of `e2`
  (length `c`, to the chip `3`) and vertex `7`'s is the whole of `e7` (length
  `d ≤ c`, to the *double* chip `5`).  The short-arm vertex `7` is reached by
  the ordinary equal-arm minimum; the far vertex `6` needs the second profile of
  `ConfigurationBananaDoubleChip`, and only the double chip makes it possible.

The fourth sign pattern `|e4| ≤ |e3|`, `|e2| ≤ |e7|` is the `sigma` image of this
chamber and is discharged by `GenusFiveRow08Symmetry.chamber_covers` together
with `ClosedOrbit.closedConstruction_of_chamber`; there is no chamber-4 file.
-/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow08ChamberThree

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
open ConfigurationBananaDoubleChip

/-! ## The single mark -/

/-- The chip on `e4`, at distance `|e3|` from the tail `1`. -/
def markY (d : DegSpec 8 12) : ℕ := d.length 3

/-- The third chamber marks only slot 4, at offset `markY`; other slots receive offset zero. -/
def rowMark (d : DegSpec 8 12) (e : Fin 12) : ℕ := if e = 4 then markY d else 0

@[simp] theorem rowMark_four (d : DegSpec 8 12) : rowMark d 4 = markY d := by
  simp [rowMark]

theorem rowMark_other (d : DegSpec 8 12) {e : Fin 12} (h4 : e ≠ 4) :
    rowMark d e = 0 := by
  simp [rowMark, h4]

theorem marked_of_rowMark_pos (d : DegSpec 8 12) {e : Fin 12}
    (h : 0 < rowMark d e) : e = 4 := by
  by_cases h4 : e = 4
  · exact h4
  · rw [rowMark_other d h4] at h; omega

/-! ## The core, spelled out -/

section Core

variable {d : DegSpec 8 12} (hCore : d.core = row08Core)
include hCore

theorem tail_four : d.core.tail 4 = 1 := by rw [hCore]; decide
theorem head_four : d.core.head 4 = 4 := by rw [hCore]; decide

end Core

/-! ## The heights -/

/-- Vertex `2`'s arm minimum: `e9` to the chip `3`, `e8` to the double chip `5`. -/
def armTwo (d : DegSpec 8 12) : ℕ := min (d.length 9) (d.length 8)

/-- Vertex `4`'s arm minimum: `e6` to the double chip `5`, and the far half of
the marked slot `e4`. -/
def armFour (d : DegSpec 8 12) : ℕ := min (d.length 6) (d.length 4 - markY d)

/-- The smaller effective arm at vertices 2 and 4, used as the shared height of their pair
configuration. -/
def pairLow (d : DegSpec 8 12) : ℕ := min (armTwo d) (armFour d)

/-- Target height at vertex 2, capped by its effective arm and by the shared height plus the
length of connecting slot 5. -/
def targetTwo (d : DegSpec 8 12) : ℕ := min (armTwo d) (pairLow d + d.length 5)

/-- Target height at vertex 4, capped by its effective arm and by the shared height plus the
length of connecting slot 5. -/
def targetFour (d : DegSpec 8 12) : ℕ := min (armFour d) (pairLow d + d.length 5)

/-- The shorter of the two right-banana slots. -/
def bananaPar (d : DegSpec 8 12) : ℕ := min (d.length 10) (d.length 11)

/-- The equal-arm reading of the right banana pair, which reaches its
short-arm vertex `7`. -/
def bananaLow (d : DegSpec 8 12) : ℕ := min (d.length 2) (d.length 7)

/-- The near vertex `7` under the double-chip profile. -/
def nearSeven (d : DegSpec 8 12) : ℕ := nearHeight (d.length 2) (d.length 7)

/-- The far vertex `6` under the double-chip profile. -/
def farSix (d : DegSpec 8 12) : ℕ :=
  farHeight (d.length 2) (d.length 7) (bananaPar d)

/-- The left banana pair, both arms of length `|e3|`. -/
def heightLB (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 0 then markY d else if v = 1 then markY d else 0

/-- The `{2,4}` pair read at the target `2`. -/
def heightT2 (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 2 then targetTwo d else if v = 4 then pairLow d else 0

/-- The `{2,4}` pair read at the target `4`. -/
def heightT4 (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 4 then targetFour d else if v = 2 then pairLow d else 0

/-- The right banana pair read at its short-arm vertex `7`. -/
def heightRB7 (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 6 then bananaLow d else if v = 7 then bananaLow d else 0

/-- The right banana pair read at the far vertex `6`, under the double chip. -/
def heightRB6 (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 6 then farSix d else if v = 7 then nearSeven d else 0

/-! ## Profiles -/

theorem mkProfile {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (hB : d.length 3 ≤ d.length 4) {h : Fin 8 → ℕ}
    (hin : h 1 ≤ markY d) (hout : h 4 ≤ d.length 4 - markY d)
    (hflat : h 1 = 0 ∨ h 4 = 0)
    (hconst : ∀ e : Fin 12, d.length e = 0 →
      h (row08Core.tail e) = h (row08Core.head e)) :
    Profile d (rowMark d) h := by
  have ht4 : d.core.tail 4 = 1 := tail_four hCore
  have hh4 : d.core.head 4 = 4 := head_four hCore
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e
    by_cases h4 : e = 4
    · subst h4; rw [rowMark_four]; simpa [markY] using hB
    · rw [rowMark_other d h4]; omega
  · intro e he
    by_cases h4 : e = 4
    · subst h4; rw [ht4, rowMark_four]; exact hin
    · rw [rowMark_other d h4] at he; omega
  · intro e he
    by_cases h4 : e = 4
    · subst h4; rw [hh4, rowMark_four]; exact hout
    · rw [rowMark_other d h4] at he; omega
  · intro e he
    by_cases h4 : e = 4
    · subst h4; rw [ht4, hh4]; exact hflat
    · rw [rowMark_other d h4] at he; omega
  · intro e he
    rw [hCore]
    exact hconst e he

theorem profileLB {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (hB : d.length 3 ≤ d.length 4) (_hD : d.length 7 ≤ d.length 2) :
    Profile d (rowMark d) (heightLB d) := by
  have h1 : heightLB d 1 = markY d := rfl
  have h4 : heightLB d 4 = 0 := rfl
  refine mkProfile hCore hB (by rw [h1]) (by rw [h4]; omega) (Or.inr h4) ?_
  intro e
  fin_cases e
  all_goals simp [heightLB, markY, row08Core]
  all_goals omega

theorem profileT2 {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (hB : d.length 3 ≤ d.length 4) (_hD : d.length 7 ≤ d.length 2) :
    Profile d (rowMark d) (heightT2 d) := by
  have h1 : heightT2 d 1 = 0 := rfl
  have h4 : heightT2 d 4 = pairLow d := rfl
  refine mkProfile hCore hB (by rw [h1]; omega)
    (by rw [h4]; simp only [pairLow, armFour]; omega) (Or.inl h1) ?_
  intro e
  fin_cases e
  all_goals simp [heightT2, targetTwo, pairLow, armTwo, armFour, markY, row08Core]
  all_goals omega

theorem profileT4 {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (hB : d.length 3 ≤ d.length 4) (_hD : d.length 7 ≤ d.length 2) :
    Profile d (rowMark d) (heightT4 d) := by
  have h1 : heightT4 d 1 = 0 := rfl
  have h4 : heightT4 d 4 = targetFour d := rfl
  refine mkProfile hCore hB (by rw [h1]; omega)
    (by rw [h4]; simp only [targetFour, armFour]; omega) (Or.inl h1) ?_
  intro e
  fin_cases e
  all_goals simp [heightT4, targetFour, pairLow, armTwo, armFour, markY, row08Core]
  all_goals omega

theorem profileRB7 {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (hB : d.length 3 ≤ d.length 4) (hD : d.length 7 ≤ d.length 2) :
    Profile d (rowMark d) (heightRB7 d) := by
  have h1 : heightRB7 d 1 = 0 := rfl
  have h4 : heightRB7 d 4 = 0 := rfl
  refine mkProfile hCore hB (by rw [h1]; omega) (by rw [h4]; omega)
    (Or.inl h1) ?_
  intro e
  fin_cases e
  all_goals simp [heightRB7, bananaLow, row08Core]
  all_goals omega

theorem profileRB6 {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (hB : d.length 3 ≤ d.length 4) (hD : d.length 7 ≤ d.length 2) :
    Profile d (rowMark d) (heightRB6 d) := by
  have h1 : heightRB6 d 1 = 0 := rfl
  have h4 : heightRB6 d 4 = 0 := rfl
  refine mkProfile hCore hB (by rw [h1]; omega) (by rw [h4]; omega)
    (Or.inl h1) ?_
  intro e
  fin_cases e
  all_goals simp [heightRB6, farSix, nearSeven, farHeight, nearHeight, bananaPar,
    row08Core]
  all_goals omega

/-! ## The endpoint ledger, vertex by vertex -/

/-- Incident-slot contribution at each row-08 core vertex in chamber three, with the marked slot
4 evaluated by its split-ramp formula. -/
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
    tailContribution (d.length 7) (h 5) (h 7)
      + tailContribution (d.length 8) (h 5) (h 2)
      + headContribution (d.length 6) (h 4) (h 5)
  else if v = 6 then
    tailContribution (d.length 2) (h 6) (h 3)
      + tailContribution (d.length 10) (h 6) (h 7)
      + tailContribution (d.length 11) (h 6) (h 7)
  else
    headContribution (d.length 7) (h 5) (h 7)
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

/-- Core-supported part of the third-chamber divisor: two chips at vertex 5 and one at vertex 3. -/
def chipWeight (v : Fin 8) : ℤ := if v = 5 then 2 else if v = 3 then 1 else 0

theorem chipWeight_nonneg (v : Fin 8) : 0 ≤ chipWeight v := by
  unfold chipWeight; split_ifs <;> norm_num

theorem sum_chipWeight : ∑ v : Fin 8, chipWeight v = 3 := by decide

/-- AR's divisor on chamber 3: a double chip at `5`, one chip at `3`, and one
inside the left-top leg. -/
def rowDivisor (d : DegSpec 8 12) : CFDiv d.graph :=
  markedDivisorOne d chipWeight (rowMark d) 4

/-- Base core weight formed from the three core chips and the endpoint contribution of the
marked chip on slot 4. -/
def base (d : DegSpec 8 12) : Fin 8 → ℤ :=
  baseOne d chipWeight (rowMark d) 4

theorem rowDivisor_effective (d : DegSpec 8 12) : effective (rowDivisor d) :=
  markedDivisorOne_effective d chipWeight (rowMark d) chipWeight_nonneg 4

theorem rowDivisor_degree (d : DegSpec 8 12) : deg (rowDivisor d) = 4 := by
  rw [rowDivisor, deg_markedDivisorOne, sum_chipWeight]
  norm_num

theorem base_eq {d : DegSpec 8 12} (hCore : d.core = row08Core) (v : Fin 8) :
    base d v = chipWeight v
      + (if markY d = 0 then (if v = 1 then (1 : ℤ) else 0)
          else if d.length 4 ≤ markY d then (if v = 4 then (1 : ℤ) else 0)
          else 0) := by
  unfold base baseOne markChipWeight
  rw [rowMark_four, tail_four hCore, head_four hCore]

/-! ## Chip allocations

Two of the five profiles move chips inside a contracted class: the `{2,4}` pair
and the double-chip banana.  Both transfers leave every class sum unchanged. -/

/-- The allocation the `{2,4}` pair script uses. -/
def pairAlloc (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  base d v
    + (if d.length 9 = 0 then transferWeight 3 2 v else 0)
    + (if d.length 8 = 0 then transferWeight 5 2 v else 0)
    + (if d.length 6 = 0 then transferWeight 5 4 v else 0)
    + (if d.length 4 = 0 then transferWeight 1 4 v else 0)

/-- The allocation the double-chip banana script uses: the chip at `3` follows a
collapsed `e2` onto `6`, and **both** chips at `5` follow a collapsed `e7` onto
`7`. -/
def bananaAlloc (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  base d v
    + (if d.length 2 = 0 then transferWeight 3 6 v else 0)
    + (if d.length 7 = 0 then transferWeight 5 7 v else 0)
    + (if d.length 7 = 0 then transferWeight 5 7 v else 0)

theorem pairAlloc_classSum {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (r : Fin 8) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), pairAlloc d v =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), base d v := by
  classical
  have h9 : d.length 9 = 0 → d.rep 3 = d.rep 2 := by
    intro hz
    have h := d.rep_zero 9 hz
    rw [hCore] at h
    simpa [row08Core] using h.symm
  have h8 : d.length 8 = 0 → d.rep 5 = d.rep 2 := by
    intro hz
    have h := d.rep_zero 8 hz
    rw [hCore] at h
    simpa [row08Core] using h
  have h6 : d.length 6 = 0 → d.rep 5 = d.rep 4 := by
    intro hz
    have h := d.rep_zero 6 hz
    rw [hCore] at h
    simpa [row08Core] using h.symm
  have h4 : d.length 4 = 0 → d.rep 1 = d.rep 4 := by
    intro hz
    have h := d.rep_zero 4 hz
    rw [hCore] at h
    simpa [row08Core] using h
  simp only [pairAlloc, Finset.sum_add_distrib]
  rw [sum_conditional_transfer_eq_zero d _ 3 2 h9,
    sum_conditional_transfer_eq_zero d _ 5 2 h8,
    sum_conditional_transfer_eq_zero d _ 5 4 h6,
    sum_conditional_transfer_eq_zero d _ 1 4 h4]
  simp

theorem bananaAlloc_classSum {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (r : Fin 8) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        bananaAlloc d v =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), base d v := by
  classical
  have h2 : d.length 2 = 0 → d.rep 3 = d.rep 6 := by
    intro hz
    have h := d.rep_zero 2 hz
    rw [hCore] at h
    simpa [row08Core] using h.symm
  have h7 : d.length 7 = 0 → d.rep 5 = d.rep 7 := by
    intro hz
    have h := d.rep_zero 7 hz
    rw [hCore] at h
    simpa [row08Core] using h
  simp only [bananaAlloc, Finset.sum_add_distrib]
  rw [sum_conditional_transfer_eq_zero d _ 3 6 h2,
    sum_conditional_transfer_eq_zero d _ 5 7 h7]
  simp

/-! ## The left banana pair -/

/-- Expanded core coefficients after the left-banana height script, combining the base with
endpoint contributions. `lbCoeff_eq` identifies this formula with the script computation. -/
def lbCoeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then headContribution (d.length 3) 0 (markY d)
  else if v = 1 then
    zeroChip (markY d) + tailContribution (markY d) (markY d) 0
  else if v = 2 then 0
  else if v = 3 then 1 + tailContribution (d.length 3) 0 (markY d)
  else if v = 4 then
    (if markY d = 0 then (0 : ℤ)
      else if d.length 4 ≤ markY d then 1 else 0)
      + (if markY d < d.length 4 then (0 : ℤ)
          else headContribution (d.length 4) (markY d) 0)
  else if v = 5 then 2
  else 0

theorem lbCoeff_eq {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (hB : d.length 3 ≤ d.length 4) (_hD : d.length 7 ≤ d.length 2) (v : Fin 8) :
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
  simp only [tail_four hCore, rowMark_four] at hT4 hH4
  rw [base_eq hCore]
  fin_cases v
  all_goals simp [lbCoeff, contribForm, heightLB, chipWeight, zeroChip, markY,
    hT4, hH4]
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
  · show (0 : ℤ) ≤ (0 : ℤ)
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
  · show (0 : ℤ) ≤ (2 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num

/-- Target representative for vertex 0, moved to vertex 3 when slot 3 is contracted. -/
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

/-! ## The `{2,4}` pair -/

theorem pairLow_comm (d : DegSpec 8 12) :
    pairLow d = min (armFour d) (armTwo d) := by
  unfold pairLow
  omega

/-- Expanded core coefficients after the vertex-2 height script, combining the pair allocation
with endpoint contributions. `t2Coeff_eq` identifies this formula with the script computation. -/
def t2Coeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then 0
  else if v = 1 then
    (zeroChip (markY d) - zeroChip (d.length 4))
      + (if 0 < markY d then (0 : ℤ)
          else tailContribution (d.length 4) 0 (pairLow d))
  else if v = 2 then
    zeroChip (d.length 9) + zeroChip (d.length 8)
      + (tailContribution (d.length 9) (targetTwo d) 0
          + headContribution (d.length 8) 0 (targetTwo d)
          + tailContribution (d.length 5) (targetTwo d) (pairLow d))
  else if v = 3 then
    positiveChip (d.length 9) + headContribution (d.length 9) (targetTwo d) 0
  else if v = 4 then
    zeroChip (d.length 6) + zeroChip (d.length 4 - markY d)
      + (tailContribution (d.length 6) (pairLow d) 0
          + headContribution (d.length 4 - markY d) 0 (pairLow d)
          + headContribution (d.length 5) (targetTwo d) (pairLow d))
  else if v = 5 then
    (positiveChip (d.length 8) + tailContribution (d.length 8) 0 (targetTwo d))
      + (positiveChip (d.length 6) + headContribution (d.length 6) (pairLow d) 0)
  else 0

theorem t2Coeff_eq {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (hB : d.length 3 ≤ d.length 4) (_hD : d.length 7 ≤ d.length 2) (v : Fin 8) :
    pairAlloc d v + contribForm d (heightT2 d) v = t2Coeff d v := by
  have hT4 := slotTailForm_of_flat_tail d (mark := rowMark d) (h := heightT2 d)
    (e := 4) (by rw [tail_four hCore]; rfl)
  have hH4 := slotHeadForm_of_arm d (mark := rowMark d) (h := heightT2 d) (e := 4)
    (by rw [tail_four hCore]; rfl)
    (by rw [rowMark_four]; simpa [markY] using hB)
    (by rw [head_four hCore, rowMark_four]
        show pairLow d ≤ d.length 4 - markY d
        simp only [pairLow, armFour]; omega)
  simp only [head_four hCore, rowMark_four] at hT4 hH4
  simp only [pairAlloc]
  rw [base_eq hCore]
  fin_cases v
  all_goals simp [t2Coeff, contribForm, heightT2, chipWeight, zeroChip,
    positiveChip, transferWeight, indicatorWeight, markY, hT4, hH4]
  all_goals (try (first | ring1 | ring_nf))
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals (try omega)

theorem t2Coeff_nonneg {d : DegSpec 8 12} (hB : d.length 3 ≤ d.length 4)
    (v : Fin 8) : 0 ≤ t2Coeff d v := by
  have hA1 : armTwo d ≤ d.length 9 := Nat.min_le_left _ _
  have hA2 : armTwo d ≤ d.length 8 := Nat.min_le_right _ _
  have hB1 : armFour d ≤ d.length 6 := Nat.min_le_left _ _
  have hB2 : armFour d ≤ d.length 4 - markY d := Nat.min_le_right _ _
  have hg1 : pairLow d ≤ armTwo d := Nat.min_le_left _ _
  have hg2 : pairLow d ≤ armFour d := Nat.min_le_right _ _
  have hO1 : targetTwo d ≤ armTwo d := Nat.min_le_left _ _
  have hM : markY d = d.length 3 := rfl
  fin_cases v
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ (zeroChip (markY d) - zeroChip (d.length 4))
        + (if 0 < markY d then (0 : ℤ)
            else tailContribution (d.length 4) 0 (pairLow d))
    by_cases hp : 0 < markY d
    · rw [if_pos hp]
      have h1 : zeroChip (markY d) = 0 := by
        have hne : markY d ≠ 0 := by omega
        simp [zeroChip, hne]
      have h2 : zeroChip (d.length 4) = 0 := by
        have hne : d.length 4 ≠ 0 := by omega
        simp [zeroChip, hne]
      omega
    · rw [if_neg hp]
      have h1 : zeroChip (markY d) = 1 := by
        have hz : markY d = 0 := by omega
        simp [zeroChip, hz]
      have hpos := positiveChip_add_tail_nonneg (L := d.length 4)
        (h := pairLow d) (by omega)
      have h2 : positiveChip (d.length 4) = 1 - zeroChip (d.length 4) := by
        unfold positiveChip zeroChip
        split_ifs <;> omega
      omega
  · show (0 : ℤ) ≤ zeroChip (d.length 9) + zeroChip (d.length 8)
        + (tailContribution (d.length 9) (targetTwo d) 0
            + headContribution (d.length 8) 0 (targetTwo d)
            + tailContribution (d.length 5) (targetTwo d) (pairLow d))
    have hpair := pairTarget_nonneg fwd rev fwd (k := (0 : ℤ))
      (la := d.length 9) (lb := d.length 8) (m := d.length 5)
      (a := armTwo d) (b := armFour d) (g := pairLow d) (o := targetTwo d)
      rfl rfl rfl le_rfl (by norm_num)
      (by intro hcon; exact absurd hcon (by norm_num))
    simp only [fwd_tail, rev_tail] at hpair
    omega
  · show (0 : ℤ) ≤ positiveChip (d.length 9)
        + headContribution (d.length 9) (targetTwo d) 0
    exact positiveChip_add_head_nonneg (by omega)
  · show (0 : ℤ) ≤ zeroChip (d.length 6) + zeroChip (d.length 4 - markY d)
        + (tailContribution (d.length 6) (pairLow d) 0
            + headContribution (d.length 4 - markY d) 0 (pairLow d)
            + headContribution (d.length 5) (targetTwo d) (pairLow d))
    have hpair := pairPartner_nonneg fwd rev rev (k := (0 : ℤ))
      (lc := d.length 6) (ld := d.length 4 - markY d) (m := d.length 5)
      (a := armTwo d) (b := armFour d) (g := pairLow d) (o := targetTwo d)
      rfl rfl rfl le_rfl (by norm_num)
      (by intro hcon; exact absurd hcon (by norm_num))
    simp only [fwd_tail, rev_tail] at hpair
    omega
  · show (0 : ℤ) ≤
      (positiveChip (d.length 8) + tailContribution (d.length 8) 0 (targetTwo d))
        + (positiveChip (d.length 6)
            + headContribution (d.length 6) (pairLow d) 0)
    have h1 := positiveChip_add_tail_nonneg (L := d.length 8)
      (h := targetTwo d) (by omega)
    have h2 := positiveChip_add_head_nonneg (L := d.length 6)
      (h := pairLow d) (by omega)
    omega
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num

/-- Target representative for vertex 2, moved to vertex 4 when connecting slot 5 is contracted
and the effective arm at vertex 2 is longer. -/
def ownerTwo (d : DegSpec 8 12) : Fin 8 :=
  if d.length 5 = 0 ∧ ¬ (armTwo d ≤ armFour d) then 4 else 2

theorem t2Coeff_owner {d : DegSpec 8 12} : 1 ≤ t2Coeff d (ownerTwo d) := by
  unfold ownerTwo
  by_cases hc : d.length 5 = 0 ∧ ¬ (armTwo d ≤ armFour d)
  · obtain ⟨hc1, hc2⟩ := hc
    rw [if_pos ⟨hc1, hc2⟩]
    show (1 : ℤ) ≤ zeroChip (d.length 6) + zeroChip (d.length 4 - markY d)
        + (tailContribution (d.length 6) (pairLow d) 0
            + headContribution (d.length 4 - markY d) 0 (pairLow d)
            + headContribution (d.length 5) (targetTwo d) (pairLow d))
    have hpair := pairPartner_nonneg fwd rev rev (k := (1 : ℤ))
      (lc := d.length 6) (ld := d.length 4 - markY d) (m := d.length 5)
      (a := armTwo d) (b := armFour d) (g := pairLow d) (o := targetTwo d)
      rfl rfl rfl (by norm_num) le_rfl (fun _ => ⟨hc1, by omega⟩)
    simp only [fwd_tail, rev_tail] at hpair
    omega
  · rw [if_neg hc]
    show (1 : ℤ) ≤ zeroChip (d.length 9) + zeroChip (d.length 8)
        + (tailContribution (d.length 9) (targetTwo d) 0
            + headContribution (d.length 8) 0 (targetTwo d)
            + tailContribution (d.length 5) (targetTwo d) (pairLow d))
    have hc' : d.length 5 = 0 → armTwo d ≤ armFour d := by
      intro h5
      by_contra hcon
      exact hc ⟨h5, hcon⟩
    have hpair := pairTarget_nonneg fwd rev fwd (k := (1 : ℤ))
      (la := d.length 9) (lb := d.length 8) (m := d.length 5)
      (a := armTwo d) (b := armFour d) (g := pairLow d) (o := targetTwo d)
      rfl rfl rfl (by norm_num) le_rfl (fun _ hm => hc' hm)
    simp only [fwd_tail, rev_tail] at hpair
    omega

/-- Expanded core coefficients after the vertex-4 height script, combining the pair allocation
with endpoint contributions. `t4Coeff_eq` identifies this formula with the script computation. -/
def t4Coeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then 0
  else if v = 1 then
    (zeroChip (markY d) - zeroChip (d.length 4))
      + (if 0 < markY d then (0 : ℤ)
          else tailContribution (d.length 4) 0 (targetFour d))
  else if v = 2 then
    zeroChip (d.length 9) + zeroChip (d.length 8)
      + (tailContribution (d.length 9) (pairLow d) 0
          + headContribution (d.length 8) 0 (pairLow d)
          + tailContribution (d.length 5) (pairLow d) (targetFour d))
  else if v = 3 then
    positiveChip (d.length 9) + headContribution (d.length 9) (pairLow d) 0
  else if v = 4 then
    zeroChip (d.length 6) + zeroChip (d.length 4 - markY d)
      + (tailContribution (d.length 6) (targetFour d) 0
          + headContribution (d.length 4 - markY d) 0 (targetFour d)
          + headContribution (d.length 5) (pairLow d) (targetFour d))
  else if v = 5 then
    (positiveChip (d.length 8) + tailContribution (d.length 8) 0 (pairLow d))
      + (positiveChip (d.length 6)
          + headContribution (d.length 6) (targetFour d) 0)
  else 0

theorem t4Coeff_eq {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (hB : d.length 3 ≤ d.length 4) (_hD : d.length 7 ≤ d.length 2) (v : Fin 8) :
    pairAlloc d v + contribForm d (heightT4 d) v = t4Coeff d v := by
  have hT4 := slotTailForm_of_flat_tail d (mark := rowMark d) (h := heightT4 d)
    (e := 4) (by rw [tail_four hCore]; rfl)
  have hH4 := slotHeadForm_of_arm d (mark := rowMark d) (h := heightT4 d) (e := 4)
    (by rw [tail_four hCore]; rfl)
    (by rw [rowMark_four]; simpa [markY] using hB)
    (by rw [head_four hCore, rowMark_four]
        show targetFour d ≤ d.length 4 - markY d
        simp only [targetFour, armFour]; omega)
  simp only [head_four hCore, rowMark_four] at hT4 hH4
  simp only [pairAlloc]
  rw [base_eq hCore]
  fin_cases v
  all_goals simp [t4Coeff, contribForm, heightT4, chipWeight, zeroChip,
    positiveChip, transferWeight, indicatorWeight, markY, hT4, hH4]
  all_goals (try (first | ring1 | ring_nf))
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals (try omega)

theorem t4Coeff_nonneg {d : DegSpec 8 12} (hB : d.length 3 ≤ d.length 4)
    (v : Fin 8) : 0 ≤ t4Coeff d v := by
  have hA1 : armTwo d ≤ d.length 9 := Nat.min_le_left _ _
  have hA2 : armTwo d ≤ d.length 8 := Nat.min_le_right _ _
  have hB1 : armFour d ≤ d.length 6 := Nat.min_le_left _ _
  have hB2 : armFour d ≤ d.length 4 - markY d := Nat.min_le_right _ _
  have hg1 : pairLow d ≤ armTwo d := Nat.min_le_left _ _
  have hg2 : pairLow d ≤ armFour d := Nat.min_le_right _ _
  have hO1 : targetFour d ≤ armFour d := Nat.min_le_left _ _
  have hM : markY d = d.length 3 := rfl
  fin_cases v
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ (zeroChip (markY d) - zeroChip (d.length 4))
        + (if 0 < markY d then (0 : ℤ)
            else tailContribution (d.length 4) 0 (targetFour d))
    by_cases hp : 0 < markY d
    · rw [if_pos hp]
      have h1 : zeroChip (markY d) = 0 := by
        have hne : markY d ≠ 0 := by omega
        simp [zeroChip, hne]
      have h2 : zeroChip (d.length 4) = 0 := by
        have hne : d.length 4 ≠ 0 := by omega
        simp [zeroChip, hne]
      omega
    · rw [if_neg hp]
      have h1 : zeroChip (markY d) = 1 := by
        have hz : markY d = 0 := by omega
        simp [zeroChip, hz]
      have hpos := positiveChip_add_tail_nonneg (L := d.length 4)
        (h := targetFour d) (by omega)
      have h2 : positiveChip (d.length 4) = 1 - zeroChip (d.length 4) := by
        unfold positiveChip zeroChip
        split_ifs <;> omega
      omega
  · show (0 : ℤ) ≤ zeroChip (d.length 9) + zeroChip (d.length 8)
        + (tailContribution (d.length 9) (pairLow d) 0
            + headContribution (d.length 8) 0 (pairLow d)
            + tailContribution (d.length 5) (pairLow d) (targetFour d))
    have hpair := pairPartner_nonneg fwd rev fwd (k := (0 : ℤ))
      (lc := d.length 9) (ld := d.length 8) (m := d.length 5)
      (a := armFour d) (b := armTwo d) (g := pairLow d) (o := targetFour d)
      rfl (pairLow_comm d) rfl le_rfl (by norm_num)
      (by intro hcon; exact absurd hcon (by norm_num))
    simp only [fwd_tail, rev_tail] at hpair
    omega
  · show (0 : ℤ) ≤ positiveChip (d.length 9)
        + headContribution (d.length 9) (pairLow d) 0
    exact positiveChip_add_head_nonneg (by omega)
  · show (0 : ℤ) ≤ zeroChip (d.length 6) + zeroChip (d.length 4 - markY d)
        + (tailContribution (d.length 6) (targetFour d) 0
            + headContribution (d.length 4 - markY d) 0 (targetFour d)
            + headContribution (d.length 5) (pairLow d) (targetFour d))
    have hpair := pairTarget_nonneg fwd rev rev (k := (0 : ℤ))
      (la := d.length 6) (lb := d.length 4 - markY d) (m := d.length 5)
      (a := armFour d) (b := armTwo d) (g := pairLow d) (o := targetFour d)
      rfl (pairLow_comm d) rfl le_rfl (by norm_num)
      (by intro hcon; exact absurd hcon (by norm_num))
    simp only [fwd_tail, rev_tail] at hpair
    omega
  · show (0 : ℤ) ≤
      (positiveChip (d.length 8) + tailContribution (d.length 8) 0 (pairLow d))
        + (positiveChip (d.length 6)
            + headContribution (d.length 6) (targetFour d) 0)
    have h1 := positiveChip_add_tail_nonneg (L := d.length 8)
      (h := pairLow d) (by omega)
    have h2 := positiveChip_add_head_nonneg (L := d.length 6)
      (h := targetFour d) (by omega)
    omega
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num

/-- Target representative for vertex 4, moved to vertex 2 when connecting slot 5 is contracted
and the effective arm at vertex 4 is longer. -/
def ownerFour (d : DegSpec 8 12) : Fin 8 :=
  if d.length 5 = 0 ∧ ¬ (armFour d ≤ armTwo d) then 2 else 4

theorem t4Coeff_owner {d : DegSpec 8 12} : 1 ≤ t4Coeff d (ownerFour d) := by
  unfold ownerFour
  by_cases hc : d.length 5 = 0 ∧ ¬ (armFour d ≤ armTwo d)
  · obtain ⟨hc1, hc2⟩ := hc
    rw [if_pos ⟨hc1, hc2⟩]
    show (1 : ℤ) ≤ zeroChip (d.length 9) + zeroChip (d.length 8)
        + (tailContribution (d.length 9) (pairLow d) 0
            + headContribution (d.length 8) 0 (pairLow d)
            + tailContribution (d.length 5) (pairLow d) (targetFour d))
    have hpair := pairPartner_nonneg fwd rev fwd (k := (1 : ℤ))
      (lc := d.length 9) (ld := d.length 8) (m := d.length 5)
      (a := armFour d) (b := armTwo d) (g := pairLow d) (o := targetFour d)
      rfl (pairLow_comm d) rfl (by norm_num) le_rfl (fun _ => ⟨hc1, by omega⟩)
    simp only [fwd_tail, rev_tail] at hpair
    omega
  · rw [if_neg hc]
    show (1 : ℤ) ≤ zeroChip (d.length 6) + zeroChip (d.length 4 - markY d)
        + (tailContribution (d.length 6) (targetFour d) 0
            + headContribution (d.length 4 - markY d) 0 (targetFour d)
            + headContribution (d.length 5) (pairLow d) (targetFour d))
    have hc' : d.length 5 = 0 → armFour d ≤ armTwo d := by
      intro h5
      by_contra hcon
      exact hc ⟨h5, hcon⟩
    have hpair := pairTarget_nonneg fwd rev rev (k := (1 : ℤ))
      (la := d.length 6) (lb := d.length 4 - markY d) (m := d.length 5)
      (a := armFour d) (b := armTwo d) (g := pairLow d) (o := targetFour d)
      rfl (pairLow_comm d) rfl (by norm_num) le_rfl (fun _ hm => hc' hm)
    simp only [fwd_tail, rev_tail] at hpair
    omega

/-! ## The right banana pair, short-arm reading -/

/-- Expanded core coefficients after the right-banana vertex-7 height script, combining the base
with endpoint contributions. `rb7Coeff_eq` identifies this formula with the script computation. -/
def rb7Coeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then 0
  else if v = 1 then zeroChip (markY d)
  else if v = 2 then 0
  else if v = 3 then 1 + headContribution (d.length 2) (bananaLow d) 0
  else if v = 4 then
    (if markY d = 0 then (0 : ℤ)
      else if d.length 4 ≤ markY d then 1 else 0)
  else if v = 5 then 2 + tailContribution (d.length 7) 0 (bananaLow d)
  else if v = 6 then tailContribution (d.length 2) (bananaLow d) 0
  else headContribution (d.length 7) 0 (bananaLow d)

theorem rb7Coeff_eq {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (_hB : d.length 3 ≤ d.length 4) (_hD : d.length 7 ≤ d.length 2) (v : Fin 8) :
    base d v + contribForm d (heightRB7 d) v = rb7Coeff d v := by
  have hT4 := slotTailForm_of_flat_tail d (mark := rowMark d) (h := heightRB7 d)
    (e := 4) (by rw [tail_four hCore]; rfl)
  have hH4 := slotHeadForm_of_flat_head d (mark := rowMark d) (h := heightRB7 d)
    (e := 4) (by rw [head_four hCore]; rfl)
    (by intro _; rw [tail_four hCore]; rfl)
  simp only [tail_four hCore, head_four hCore, rowMark_four] at hT4 hH4
  rw [base_eq hCore]
  fin_cases v
  all_goals simp [rb7Coeff, contribForm, heightRB7, chipWeight, zeroChip, markY,
    hT4, hH4]
  all_goals (try (first | ring1 | ring_nf))
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals (try split_ifs)
  all_goals (try omega)

theorem rb7Coeff_nonneg {d : DegSpec 8 12} (_hB : d.length 3 ≤ d.length 4)
    (_hD : d.length 7 ≤ d.length 2) (v : Fin 8) : 0 ≤ rb7Coeff d v := by
  have hg1 : bananaLow d ≤ d.length 2 := Nat.min_le_left _ _
  have hg2 : bananaLow d ≤ d.length 7 := Nat.min_le_right _ _
  have hM : markY d = d.length 3 := rfl
  fin_cases v
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ zeroChip (markY d)
    exact zeroChip_nonneg _
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ 1 + headContribution (d.length 2) (bananaLow d) 0
    have := headContribution_ge_neg_one (L := d.length 2) (hu := bananaLow d)
      (hv := 0) (by omega) (by omega)
    omega
  · show (0 : ℤ) ≤
      (if markY d = 0 then (0 : ℤ)
        else if d.length 4 ≤ markY d then 1 else 0)
    split_ifs <;> norm_num
  · show (0 : ℤ) ≤ 2 + tailContribution (d.length 7) 0 (bananaLow d)
    have := tailContribution_ge_neg_one (L := d.length 7) (hu := 0)
      (hv := bananaLow d) (by omega) (by omega)
    omega
  · show (0 : ℤ) ≤ tailContribution (d.length 2) (bananaLow d) 0
    exact tailContribution_nonneg (Nat.zero_le _) (by omega)
  · show (0 : ℤ) ≤ headContribution (d.length 7) 0 (bananaLow d)
    exact headContribution_nonneg (Nat.zero_le _) (by omega)

/-- Target representative for vertex 7, moved to vertex 5 when slot 7 is contracted. -/
def ownerSeven (d : DegSpec 8 12) : Fin 8 := if d.length 7 = 0 then 5 else 7

theorem rb7Coeff_owner_seven {d : DegSpec 8 12} (hD : d.length 7 ≤ d.length 2) :
    1 ≤ rb7Coeff d (ownerSeven d) := by
  have hg : bananaLow d = min (d.length 2) (d.length 7) := rfl
  unfold ownerSeven
  by_cases hz : d.length 7 = 0
  · rw [if_pos hz]
    show (1 : ℤ) ≤ 2 + tailContribution (d.length 7) 0 (bananaLow d)
    rw [hz, show bananaLow d = 0 by omega, tailContribution_zero_zero]
    norm_num
  · rw [if_neg hz]
    show (1 : ℤ) ≤ headContribution (d.length 7) 0 (bananaLow d)
    rw [headContribution_eq_one_of_full (L := d.length 7) (hu := 0)
      (hv := bananaLow d) (by omega) (by omega)]

/-! ## The right banana pair, far reading under the double chip -/

/-- Expanded core coefficients after the right-banana vertex-6 height script, combining the
adjusted allocation with endpoint contributions. `rb6Coeff_eq` identifies this formula with the
script computation. -/
def rb6Coeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then 0
  else if v = 1 then zeroChip (markY d)
  else if v = 2 then 0
  else if v = 3 then
    positiveChip (d.length 2) + headContribution (d.length 2) (farSix d) 0
  else if v = 4 then
    (if markY d = 0 then (0 : ℤ)
      else if d.length 4 ≤ markY d then 1 else 0)
  else if v = 5 then
    2 * positiveChip (d.length 7) + tailContribution (d.length 7) 0 (nearSeven d)
  else if v = 6 then
    zeroChip (d.length 2)
      + (tailContribution (d.length 2) (farSix d) 0
          + tailContribution (d.length 10) (farSix d) (nearSeven d)
          + tailContribution (d.length 11) (farSix d) (nearSeven d))
  else
    2 * zeroChip (d.length 7)
      + (headContribution (d.length 7) 0 (nearSeven d)
          + headContribution (d.length 10) (farSix d) (nearSeven d)
          + headContribution (d.length 11) (farSix d) (nearSeven d))

theorem rb6Coeff_eq {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (_hB : d.length 3 ≤ d.length 4) (_hD : d.length 7 ≤ d.length 2) (v : Fin 8) :
    bananaAlloc d v + contribForm d (heightRB6 d) v = rb6Coeff d v := by
  have hT4 := slotTailForm_of_flat_tail d (mark := rowMark d) (h := heightRB6 d)
    (e := 4) (by rw [tail_four hCore]; rfl)
  have hH4 := slotHeadForm_of_flat_head d (mark := rowMark d) (h := heightRB6 d)
    (e := 4) (by rw [head_four hCore]; rfl)
    (by intro _; rw [tail_four hCore]; rfl)
  simp only [tail_four hCore, head_four hCore, rowMark_four] at hT4 hH4
  simp only [bananaAlloc]
  rw [base_eq hCore]
  fin_cases v
  all_goals simp [rb6Coeff, contribForm, heightRB6, chipWeight, zeroChip,
    positiveChip, transferWeight, indicatorWeight, markY, hT4, hH4]
  all_goals (try (first | ring1 | ring_nf))
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals (try split_ifs)
  all_goals (try omega)

theorem near_le_far (d : DegSpec 8 12) : nearSeven d ≤ farSix d := by
  unfold nearSeven farSix
  exact nearHeight_le_far

theorem near_le_two (d : DegSpec 8 12) : nearSeven d ≤ 2 * d.length 7 := by
  simp only [nearSeven, nearHeight]
  omega

theorem far_le_long (d : DegSpec 8 12) : farSix d ≤ d.length 2 := by
  simp only [farSix, farHeight]
  omega

theorem rb6Coeff_nonneg {d : DegSpec 8 12} (hD : d.length 7 ≤ d.length 2)
    (v : Fin 8) : 0 ≤ rb6Coeff d v := by
  have hnf := near_le_far d
  have hn2 := near_le_two d
  have hfl := far_le_long d
  fin_cases v
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ zeroChip (markY d)
    exact zeroChip_nonneg _
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ positiveChip (d.length 2)
        + headContribution (d.length 2) (farSix d) 0
    exact positiveChip_add_head_nonneg (by omega)
  · show (0 : ℤ) ≤
      (if markY d = 0 then (0 : ℤ)
        else if d.length 4 ≤ markY d then 1 else 0)
    split_ifs <;> norm_num
  · show (0 : ℤ) ≤ 2 * positiveChip (d.length 7)
        + tailContribution (d.length 7) 0 (nearSeven d)
    exact doubleChip_add_tail_nonneg (by omega)
  · show (0 : ℤ) ≤ zeroChip (d.length 2)
        + (tailContribution (d.length 2) (farSix d) 0
            + tailContribution (d.length 10) (farSix d) (nearSeven d)
            + tailContribution (d.length 11) (farSix d) (nearSeven d))
    have := far_center_nonneg (p := d.length 2) (q := d.length 7)
      (par := bananaPar d) (m1 := d.length 10) (m2 := d.length 11)
      (hv := nearSeven d) (hu := farSix d) (k := (0 : ℤ))
      rfl rfl rfl le_rfl (by norm_num)
      (by intro hcon; exact absurd hcon (by norm_num))
    omega
  · show (0 : ℤ) ≤ 2 * zeroChip (d.length 7)
        + (headContribution (d.length 7) 0 (nearSeven d)
            + headContribution (d.length 10) (farSix d) (nearSeven d)
            + headContribution (d.length 11) (farSix d) (nearSeven d))
    have := far_partner_nonneg (p := d.length 2) (q := d.length 7)
      (par := bananaPar d) (m1 := d.length 10) (m2 := d.length 11)
      (hv := nearSeven d) (hu := farSix d) (k := (0 : ℤ))
      rfl rfl rfl hD le_rfl (by norm_num)
      (by intro hcon; exact absurd hcon (by norm_num))
    omega

/-- Target representative for vertex 6: keep vertex 6 when both parallel banana slots have
positive length, and use vertex 7 otherwise. -/
def ownerSix (d : DegSpec 8 12) : Fin 8 := if 0 < bananaPar d then 6 else 7

theorem rb6Coeff_owner_six {d : DegSpec 8 12} (hD : d.length 7 ≤ d.length 2) :
    1 ≤ rb6Coeff d (ownerSix d) := by
  unfold ownerSix
  by_cases hpar : 0 < bananaPar d
  · rw [if_pos hpar]
    show (1 : ℤ) ≤ zeroChip (d.length 2)
        + (tailContribution (d.length 2) (farSix d) 0
            + tailContribution (d.length 10) (farSix d) (nearSeven d)
            + tailContribution (d.length 11) (farSix d) (nearSeven d))
    have := far_center_nonneg (p := d.length 2) (q := d.length 7)
      (par := bananaPar d) (m1 := d.length 10) (m2 := d.length 11)
      (hv := nearSeven d) (hu := farSix d) (k := (1 : ℤ))
      rfl rfl rfl (by norm_num) le_rfl (fun _ => Or.inl hpar)
    omega
  · rw [if_neg hpar]
    have hpar0 : bananaPar d = 0 := by omega
    show (1 : ℤ) ≤ 2 * zeroChip (d.length 7)
        + (headContribution (d.length 7) 0 (nearSeven d)
            + headContribution (d.length 10) (farSix d) (nearSeven d)
            + headContribution (d.length 11) (farSix d) (nearSeven d))
    by_cases hq : 0 < d.length 7
    · have := far_partner_nonneg (p := d.length 2) (q := d.length 7)
        (par := bananaPar d) (m1 := d.length 10) (m2 := d.length 11)
        (hv := nearSeven d) (hu := farSix d) (k := (1 : ℤ))
        rfl rfl rfl hD (by norm_num) le_rfl (fun _ => ⟨hpar0, hq⟩)
      omega
    · have hq0 : d.length 7 = 0 := by omega
      have hz : zeroChip (d.length 7) = 1 := by simp [zeroChip, hq0]
      have hnear : nearSeven d = 0 := by
        simp only [nearSeven, nearHeight, hq0]
        omega
      have hfar : farSix d = 0 := by
        simp only [farSix, farHeight, nearSeven] at *
        omega
      rw [hz, hnear, hfar, hq0, headContribution_zero_zero,
        headContribution_same, headContribution_same]
      norm_num

/-! ## Every contracted core class is reached -/

theorem rowDivisor_reaches_coreVertex {d : DegSpec 8 12}
    (hCore : d.core = row08Core)
    (hB : d.length 3 ≤ d.length 4) (hD : d.length 7 ≤ d.length 2)
    (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8, d.rep x = d.rep y ↔ ReachIn row08Core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0) (center : Fin 8) :
    Reaches d.graph (rowDivisor d) (d.coreVertex center) := by
  have hCoreValue : ∀ r : Fin 8, rowDivisor d (d.coreVertex r) =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), base d v :=
    markedDivisorOne_coreVertex d chipWeight (rowMark d) 4
  have hInterior := markedDivisorOne_interior d chipWeight (rowMark d)
    chipWeight_nonneg 4
  have hChip := markedDivisorOne_chip d chipWeight (rowMark d)
    (fun g hg => marked_of_rowMark_pos d hg)
  have hBase : ∀ r : Fin 8,
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), base d v =
        ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), base d v :=
    fun _ => rfl
  have hPair := pairAlloc_classSum hCore
  have hBanana := bananaAlloc_classSum hCore
  have hpLB := profileLB hCore hB hD
  have hpT2 := profileT2 hCore hB hD
  have hpT4 := profileT4 hCore hB hD
  have hpRB7 := profileRB7 hCore hB hD
  have hpRB6 := profileRB6 hCore hB hD
  have hrLB := height_rep_eq d hCore hpLB.const F hRepReach hFZero
  have hrT2 := height_rep_eq d hCore hpT2.const F hRepReach hFZero
  have hrT4 := height_rep_eq d hCore hpT4.const F hRepReach hFZero
  have hrRB7 := height_rep_eq d hCore hpRB7.const F hRepReach hFZero
  have hrRB6 := height_rep_eq d hCore hpRB6.const F hRepReach hFZero
  have hOZ : d.rep (ownerZero d) = d.rep 0 := by
    unfold ownerZero
    by_cases hz : d.length 3 = 0
    · rw [if_pos hz]
      have h := d.rep_zero 3 hz
      rw [hCore] at h
      simpa [row08Core] using h
    · rw [if_neg hz]
  have hOT : d.rep (ownerTwo d) = d.rep 2 := by
    unfold ownerTwo
    by_cases hz : d.length 5 = 0 ∧ ¬ (armTwo d ≤ armFour d)
    · rw [if_pos hz]
      have h := d.rep_zero 5 hz.1
      rw [hCore] at h
      simpa [row08Core] using h.symm
    · rw [if_neg hz]
  have hOF : d.rep (ownerFour d) = d.rep 4 := by
    unfold ownerFour
    by_cases hz : d.length 5 = 0 ∧ ¬ (armFour d ≤ armTwo d)
    · rw [if_pos hz]
      have h := d.rep_zero 5 hz.1
      rw [hCore] at h
      simpa [row08Core] using h
    · rw [if_neg hz]
  have hOS : d.rep (ownerSeven d) = d.rep 7 := by
    unfold ownerSeven
    by_cases hz : d.length 7 = 0
    · rw [if_pos hz]
      have h := d.rep_zero 7 hz
      rw [hCore] at h
      simpa [row08Core] using h
    · rw [if_neg hz]
  have hOSix : d.rep (ownerSix d) = d.rep 6 := by
    unfold ownerSix
    by_cases hz : 0 < bananaPar d
    · rw [if_pos hz]
    · rw [if_neg hz]
      have hpar : d.length 10 = 0 ∨ d.length 11 = 0 := by
        simp only [bananaPar] at hz
        omega
      rcases hpar with h10 | h11
      · have h := d.rep_zero 10 h10
        rw [hCore] at h
        simpa [row08Core] using h.symm
      · have h := d.rep_zero 11 h11
        rw [hCore] at h
        simpa [row08Core] using h.symm
  fin_cases center
  · exact (DharMove.ofScript _ (residual_effective d hpLB hrLB hCoreValue
      hInterior hChip hBase hOZ (fun v => by
        rw [contrib_eq hCore hpLB hrLB v]
        exact residual_of_coeff
          (fun w => by rw [lbCoeff_eq hCore hB hD w]; exact lbCoeff_nonneg hB w)
          (by rw [lbCoeff_eq hCore hB hD (ownerZero d)]
              exact lbCoeff_owner_zero) v))).reaches
  · exact (DharMove.ofScript _ (residual_effective d hpLB hrLB hCoreValue
      hInterior hChip hBase (rfl : d.rep 1 = d.rep 1) (fun v => by
        rw [contrib_eq hCore hpLB hrLB v]
        exact residual_of_coeff
          (fun w => by rw [lbCoeff_eq hCore hB hD w]; exact lbCoeff_nonneg hB w)
          (by rw [lbCoeff_eq hCore hB hD 1]; exact lbCoeff_owner_one) v))).reaches
  · exact (DharMove.ofScript _ (residual_effective d hpT2 hrT2 hCoreValue
      hInterior hChip hPair hOT (fun v => by
        rw [contrib_eq hCore hpT2 hrT2 v]
        exact residual_of_coeff
          (fun w => by rw [t2Coeff_eq hCore hB hD w]; exact t2Coeff_nonneg hB w)
          (by rw [t2Coeff_eq hCore hB hD (ownerTwo d)]
              exact t2Coeff_owner) v))).reaches
  · exact reaches_of_effective_representative
      (linearEquiv.refl d.graph (rowDivisor d)) (rowDivisor_effective d)
      (one_le_markedDivisorOne_at_chip d chipWeight (rowMark d) 4
        chipWeight_nonneg (c := 3) (by decide))
  · exact (DharMove.ofScript _ (residual_effective d hpT4 hrT4 hCoreValue
      hInterior hChip hPair hOF (fun v => by
        rw [contrib_eq hCore hpT4 hrT4 v]
        exact residual_of_coeff
          (fun w => by rw [t4Coeff_eq hCore hB hD w]; exact t4Coeff_nonneg hB w)
          (by rw [t4Coeff_eq hCore hB hD (ownerFour d)]
              exact t4Coeff_owner) v))).reaches
  · exact reaches_of_effective_representative
      (linearEquiv.refl d.graph (rowDivisor d)) (rowDivisor_effective d)
      (one_le_markedDivisorOne_at_chip d chipWeight (rowMark d) 4
        chipWeight_nonneg (c := 5) (by decide))
  · exact (DharMove.ofScript _ (residual_effective d hpRB6 hrRB6 hCoreValue
      hInterior hChip hBanana hOSix (fun v => by
        rw [contrib_eq hCore hpRB6 hrRB6 v]
        exact residual_of_coeff
          (fun w => by rw [rb6Coeff_eq hCore hB hD w]; exact rb6Coeff_nonneg hD w)
          (by rw [rb6Coeff_eq hCore hB hD (ownerSix d)]
              exact rb6Coeff_owner_six hD) v))).reaches
  · exact (DharMove.ofScript _ (residual_effective d hpRB7 hrRB7 hCoreValue
      hInterior hChip hBase hOS (fun v => by
        rw [contrib_eq hCore hpRB7 hrRB7 v]
        exact residual_of_coeff
          (fun w => by rw [rb7Coeff_eq hCore hB hD w]
                       exact rb7Coeff_nonneg hB hD w)
          (by rw [rb7Coeff_eq hCore hB hD (ownerSeven d)]
              exact rb7Coeff_owner_seven hD) v))).reaches

/-- **AR's seventh family, third scope.**  The divisor with a double chip. -/
theorem chamberThree_pencil (length : Fin 12 → ℕ)
    (forest : IsForest row08Core (zeroSlots length))
    (notLoopy : ¬ IsLoopy row08Core (zeroSlots length))
    (hP : GenusFiveRow08Symmetry.ChamberThree length) :
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

end AtanasovRanganathan.GenusFiveRow08ChamberThree
