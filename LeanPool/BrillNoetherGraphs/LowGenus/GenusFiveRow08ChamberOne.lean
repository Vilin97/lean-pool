/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationMarkedRow
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow08Symmetry

/-!
# AR row 08, chamber 1

The first scope AR draw for their seventh family: `|e4| ≤ |e3|` and
`|e7| ≤ |e2|`, i.e. `a ≤ b` and `d ≤ c`.  The displayed divisor is

```
 D = [4] + [5] + (e3 at distance |e4| from 0) + (e2 at distance |e7| from 6)
```

so the two marks are `mark e3 = |e3| - |e4|` (measured from `e3`'s tail `3`) and
`mark e2 = |e7|`.  The six chip-free vertices split exactly as in AR's sixth
family:

* `{0, 1}` -- a banana pair whose two arms both have length `|e4|`: the far half
  of `e3`, and the whole of `e4`.
* `{6, 7}` -- a banana pair whose two arms both have length `|e7|`: the near half
  of `e2`, and the whole of `e7`.
* `{2, 3}` -- a `ConfigurationThree` pair across the stem `e9`; vertex `2`'s arms
  are `e5` and `e8`, vertex `3`'s are the near half of `e3` and the far half of
  `e2`.

So this chamber needs no picture that row 05 did not already need, and the whole
file is an instantiation of `ConfigurationMarkedRow` plus four coefficient
tables.
-/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow08ChamberOne

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

/-! ## The two marks -/

/-- The chip on `e3`, at distance `|e4|` from the head `0`. -/
def markY (d : DegSpec 8 12) : ℕ := d.length 3 - d.length 4

/-- The chip on `e2`, at distance `|e7|` from the tail `6`. -/
def markX (d : DegSpec 8 12) : ℕ := d.length 7

/-- The first chamber marks slot 2 at `markX` and slot 3 at `markY`; other slots receive offset
zero. -/
def rowMark (d : DegSpec 8 12) (e : Fin 12) : ℕ :=
  if e = 2 then markX d else if e = 3 then markY d else 0

@[simp] theorem rowMark_two (d : DegSpec 8 12) : rowMark d 2 = markX d := by
  simp [rowMark]

@[simp] theorem rowMark_three (d : DegSpec 8 12) : rowMark d 3 = markY d := by
  simp [rowMark]

theorem rowMark_other (d : DegSpec 8 12) {e : Fin 12} (h2 : e ≠ 2) (h3 : e ≠ 3) :
    rowMark d e = 0 := by
  simp [rowMark, h2, h3]

theorem marked_of_rowMark_pos (d : DegSpec 8 12) {e : Fin 12}
    (h : 0 < rowMark d e) : e = 3 ∨ e = 2 := by
  by_cases h2 : e = 2
  · exact Or.inr h2
  · by_cases h3 : e = 3
    · exact Or.inl h3
    · rw [rowMark_other d h2 h3] at h; omega

/-! ## The core, spelled out -/

section Core

variable {d : DegSpec 8 12} (hCore : d.core = row08Core)
include hCore

theorem tail_two : d.core.tail 2 = 6 := by rw [hCore]; decide
theorem head_two : d.core.head 2 = 3 := by rw [hCore]; decide
theorem tail_three : d.core.tail 3 = 3 := by rw [hCore]; decide
theorem head_three : d.core.head 3 = 0 := by rw [hCore]; decide

end Core

/-! ## The heights -/

/-- Vertex `2`'s arm minimum: `e5` to the chip `4`, `e8` to the chip `5`. -/
def armTwo (d : DegSpec 8 12) : ℕ := min (d.length 5) (d.length 8)

/-- Vertex `3`'s arm minimum: the near half of `e3`, the far half of `e2`. -/
def armThree (d : DegSpec 8 12) : ℕ := min (markY d) (d.length 2 - markX d)

/-- The smaller of the effective arms at vertices 2 and 3, used as the shared height of their
pair configuration. -/
def pairLow (d : DegSpec 8 12) : ℕ := min (armTwo d) (armThree d)

/-- Target height at vertex 2, bounded by its own effective arm and by the shared height plus
the length of the connecting slot 9. -/
def targetTwo (d : DegSpec 8 12) : ℕ := min (armTwo d) (pairLow d + d.length 9)

/-- Target height at vertex 3, bounded by its own effective arm and by the shared height plus
the length of the connecting slot 9. -/
def targetThree (d : DegSpec 8 12) : ℕ := min (armThree d) (pairLow d + d.length 9)

/-- The left banana pair, both arms of length `|e4|`. -/
def heightLB (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 0 then d.length 4 else if v = 1 then d.length 4 else 0

/-- The right banana pair, both arms of length `|e7|`. -/
def heightRB (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 6 then d.length 7 else if v = 7 then d.length 7 else 0

/-- The stem pair read at the target `2`. -/
def heightT2 (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 2 then targetTwo d else if v = 3 then pairLow d else 0

/-- The stem pair read at the target `3`. -/
def heightT3 (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 3 then targetThree d else if v = 2 then pairLow d else 0

/-! ## Profiles -/

theorem mkProfile {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (hC : d.length 7 ≤ d.length 2) {h : Fin 8 → ℕ}
    (hin2 : h 6 ≤ markX d) (hout2 : h 3 ≤ d.length 2 - markX d)
    (hflat2 : h 6 = 0 ∨ h 3 = 0)
    (hin3 : h 3 ≤ markY d) (hout3 : h 0 ≤ d.length 3 - markY d)
    (hflat3 : h 3 = 0 ∨ h 0 = 0)
    (hconst : ∀ e : Fin 12, d.length e = 0 →
      h (row08Core.tail e) = h (row08Core.head e)) :
    Profile d (rowMark d) h := by
  have ht2 : d.core.tail 2 = 6 := tail_two hCore
  have hh2 : d.core.head 2 = 3 := head_two hCore
  have ht3 : d.core.tail 3 = 3 := tail_three hCore
  have hh3 : d.core.head 3 = 0 := head_three hCore
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e
    by_cases h2 : e = 2
    · subst h2; rw [rowMark_two]; simpa [markX] using hC
    · by_cases h3 : e = 3
      · subst h3; rw [rowMark_three]; simp only [markY]; omega
      · rw [rowMark_other d h2 h3]; omega
  · intro e he
    by_cases h2 : e = 2
    · subst h2; rw [ht2, rowMark_two]; exact hin2
    · by_cases h3 : e = 3
      · subst h3; rw [ht3, rowMark_three]; exact hin3
      · rw [rowMark_other d h2 h3] at he; omega
  · intro e he
    by_cases h2 : e = 2
    · subst h2; rw [hh2, rowMark_two]; exact hout2
    · by_cases h3 : e = 3
      · subst h3; rw [hh3, rowMark_three]; exact hout3
      · rw [rowMark_other d h2 h3] at he; omega
  · intro e he
    by_cases h2 : e = 2
    · subst h2; rw [ht2, hh2]; exact hflat2
    · by_cases h3 : e = 3
      · subst h3; rw [ht3, hh3]; exact hflat3
      · rw [rowMark_other d h2 h3] at he; omega
  · intro e he
    rw [hCore]
    exact hconst e he

theorem profileLB {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (hC : d.length 7 ≤ d.length 2) (hA : d.length 4 ≤ d.length 3) :
    Profile d (rowMark d) (heightLB d) := by
  have h0 : heightLB d 0 = d.length 4 := rfl
  have h3 : heightLB d 3 = 0 := rfl
  have h6 : heightLB d 6 = 0 := rfl
  refine mkProfile hCore hC (by rw [h6]; omega) (by rw [h3]; omega)
    (Or.inl h6) (by rw [h3]; omega)
    (by rw [h0]; simp only [markY]; omega) (Or.inl h3) ?_
  intro e
  fin_cases e
  all_goals simp [heightLB, row08Core]
  all_goals omega

theorem profileRB {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (hC : d.length 7 ≤ d.length 2) (_hA : d.length 4 ≤ d.length 3) :
    Profile d (rowMark d) (heightRB d) := by
  have h0 : heightRB d 0 = 0 := rfl
  have h3 : heightRB d 3 = 0 := rfl
  have h6 : heightRB d 6 = d.length 7 := rfl
  refine mkProfile hCore hC (by rw [h6]; exact le_rfl) (by rw [h3]; omega)
    (Or.inr h3) (by rw [h3]; omega) (by rw [h0]; omega) (Or.inl h3) ?_
  intro e
  fin_cases e
  all_goals simp [heightRB, row08Core]
  all_goals omega

theorem profileT2 {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (hC : d.length 7 ≤ d.length 2) (hA : d.length 4 ≤ d.length 3) :
    Profile d (rowMark d) (heightT2 d) := by
  have h0 : heightT2 d 0 = 0 := rfl
  have h3 : heightT2 d 3 = pairLow d := rfl
  have h6 : heightT2 d 6 = 0 := rfl
  refine mkProfile hCore hC (by rw [h6]; omega)
    (by rw [h3]; simp only [pairLow, armThree]; omega) (Or.inl h6)
    (by rw [h3]; simp only [pairLow, armThree]; omega)
    (by rw [h0]; omega) (Or.inr h0) ?_
  intro e
  fin_cases e
  all_goals simp [heightT2, targetTwo, pairLow, armTwo, armThree, markY, markX,
    row08Core]
  all_goals omega

theorem profileT3 {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (hC : d.length 7 ≤ d.length 2) (hA : d.length 4 ≤ d.length 3) :
    Profile d (rowMark d) (heightT3 d) := by
  have h0 : heightT3 d 0 = 0 := rfl
  have h3 : heightT3 d 3 = targetThree d := rfl
  have h6 : heightT3 d 6 = 0 := rfl
  refine mkProfile hCore hC (by rw [h6]; omega)
    (by rw [h3]; simp only [targetThree, armThree]; omega) (Or.inl h6)
    (by rw [h3]; simp only [targetThree, armThree]; omega)
    (by rw [h0]; omega) (Or.inr h0) ?_
  intro e
  fin_cases e
  all_goals simp [heightT3, targetThree, pairLow, armTwo, armThree, markY, markX,
    row08Core]
  all_goals omega

/-! ## The endpoint ledger, vertex by vertex -/

/-- Incident-slot contribution at each row-08 core vertex in chamber one, using split-ramp
formulas at the marks on slots 2 and 3. -/
def contribForm (d : DegSpec 8 12) (h : Fin 8 → ℕ) (v : Fin 8) : ℤ :=
  if v = 0 then
    tailContribution (d.length 0) (h 0) (h 1)
      + tailContribution (d.length 1) (h 0) (h 1)
      + slotHeadForm d (rowMark d) h 3
  else if v = 1 then
    tailContribution (d.length 4) (h 1) (h 4)
      + headContribution (d.length 0) (h 0) (h 1)
      + headContribution (d.length 1) (h 0) (h 1)
  else if v = 2 then
    tailContribution (d.length 5) (h 2) (h 4)
      + tailContribution (d.length 9) (h 2) (h 3)
      + headContribution (d.length 8) (h 5) (h 2)
  else if v = 3 then
    slotTailForm d (rowMark d) h 3 + slotHeadForm d (rowMark d) h 2
      + headContribution (d.length 9) (h 2) (h 3)
  else if v = 4 then
    tailContribution (d.length 6) (h 4) (h 5)
      + headContribution (d.length 4) (h 1) (h 4)
      + headContribution (d.length 5) (h 2) (h 4)
  else if v = 5 then
    tailContribution (d.length 7) (h 5) (h 7)
      + tailContribution (d.length 8) (h 5) (h 2)
      + headContribution (d.length 6) (h 4) (h 5)
  else if v = 6 then
    slotTailForm d (rowMark d) h 2
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
      Finset.sum_const_zero, contribForm, Matrix.cons_val, Fin.mk_one, Fin.reduceFinMk,
      Finset.sum_singleton]<;> ring

/-! ## The divisor -/

/-- The two core-supported chips of chamber one, at vertices 4 and 5. -/
def chipWeight (v : Fin 8) : ℤ := if v = 4 then 1 else if v = 5 then 1 else 0

theorem chipWeight_nonneg (v : Fin 8) : 0 ≤ chipWeight v := by
  unfold chipWeight; split_ifs <;> norm_num

theorem sum_chipWeight : ∑ v : Fin 8, chipWeight v = 2 := by decide

/-- AR's divisor on chamber 1. -/
def rowDivisor (d : DegSpec 8 12) : CFDiv d.graph :=
  markedDivisorTwo d chipWeight (rowMark d) 3 2

/-- Base core weight formed from the chips at vertices 4 and 5 together with the endpoint
contributions of the two marked chips on slots 3 and 2. -/
def base (d : DegSpec 8 12) : Fin 8 → ℤ :=
  baseTwo d chipWeight (rowMark d) 3 2

theorem rowDivisor_effective (d : DegSpec 8 12) : effective (rowDivisor d) :=
  markedDivisorTwo_effective d chipWeight (rowMark d) chipWeight_nonneg 3 2

theorem rowDivisor_degree (d : DegSpec 8 12) : deg (rowDivisor d) = 4 := by
  rw [rowDivisor, deg_markedDivisorTwo, sum_chipWeight]
  norm_num

theorem base_eq {d : DegSpec 8 12} (hCore : d.core = row08Core) (v : Fin 8) :
    base d v = chipWeight v
      + (if markY d = 0 then (if v = 3 then (1 : ℤ) else 0)
          else if d.length 3 ≤ markY d then (if v = 0 then (1 : ℤ) else 0) else 0)
      + (if markX d = 0 then (if v = 6 then (1 : ℤ) else 0)
          else if d.length 2 ≤ markX d then (if v = 3 then (1 : ℤ) else 0)
          else 0) := by
  unfold base baseTwo markChipWeight
  rw [rowMark_three, rowMark_two, tail_three hCore, head_three hCore,
    tail_two hCore, head_two hCore]

/-! ## Chip allocation for the stem pair -/

/-- Core allocation for the pair configuration: transfer chips across contracted slots 5 and 8
to vertex 2, and across contracted slot 2 to vertex 3. -/
def pairAlloc (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  base d v
    + (if d.length 5 = 0 then transferWeight 4 2 v else 0)
    + (if d.length 8 = 0 then transferWeight 5 2 v else 0)
    + (if d.length 2 = 0 then transferWeight 6 3 v else 0)

theorem pairAlloc_classSum {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (r : Fin 8) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), pairAlloc d v =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), base d v := by
  classical
  have h5 : d.length 5 = 0 → d.rep 4 = d.rep 2 := by
    intro hz
    have h := d.rep_zero 5 hz
    rw [hCore] at h
    simpa [row08Core] using h.symm
  have h8 : d.length 8 = 0 → d.rep 5 = d.rep 2 := by
    intro hz
    have h := d.rep_zero 8 hz
    rw [hCore] at h
    simpa [row08Core] using h
  have h2 : d.length 2 = 0 → d.rep 6 = d.rep 3 := by
    intro hz
    have h := d.rep_zero 2 hz
    rw [hCore] at h
    simpa [row08Core] using h
  simp only [pairAlloc, Finset.sum_add_distrib]
  rw [sum_conditional_transfer_eq_zero d _ 4 2 h5,
    sum_conditional_transfer_eq_zero d _ 5 2 h8,
    sum_conditional_transfer_eq_zero d _ 6 3 h2]
  simp

/-! ## The four coefficient tables -/

/-- Expanded core coefficients after the left-banana height script, combining the base with
endpoint contributions. `lbCoeff_eq` identifies this formula with the script computation. -/
def lbCoeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then
    (if markY d = 0 then (0 : ℤ) else if d.length 3 ≤ markY d then 1 else 0)
      + headContribution (d.length 3 - markY d) 0 (d.length 4)
  else if v = 1 then tailContribution (d.length 4) (d.length 4) 0
  else if v = 2 then 0
  else if v = 3 then
    (if markY d = 0 then (1 : ℤ) else 0)
      + (if markX d = 0 then (0 : ℤ)
          else if d.length 2 ≤ markX d then 1 else 0)
      + (if 0 < markY d then (0 : ℤ)
          else tailContribution (d.length 3) 0 (d.length 4))
  else if v = 4 then 1 + headContribution (d.length 4) (d.length 4) 0
  else if v = 5 then 1
  else if v = 6 then (if markX d = 0 then (1 : ℤ) else 0)
  else 0

theorem lbCoeff_eq {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (hC : d.length 7 ≤ d.length 2) (hA : d.length 4 ≤ d.length 3) (v : Fin 8) :
    base d v + contribForm d (heightLB d) v = lbCoeff d v := by
  have hT3 := slotTailForm_of_flat_tail d (mark := rowMark d) (h := heightLB d)
    (e := 3) (by rw [tail_three hCore]; rfl)
  have hH3 := slotHeadForm_of_arm d (mark := rowMark d) (h := heightLB d) (e := 3)
    (by rw [tail_three hCore]; rfl)
    (by rw [rowMark_three]; simp only [markY]; omega)
    (by rw [head_three hCore, rowMark_three]
        show d.length 4 ≤ d.length 3 - markY d
        simp only [markY]; omega)
  have hT2 := slotTailForm_of_arm d (mark := rowMark d) (h := heightLB d) (e := 2)
    (by rw [head_two hCore]; rfl) (by intro _; rw [tail_two hCore]; rfl)
  have hH2 := slotHeadForm_of_arm d (mark := rowMark d) (h := heightLB d) (e := 2)
    (by rw [tail_two hCore]; rfl)
    (by rw [rowMark_two]; simpa [markX] using hC)
    (by rw [head_two hCore]; exact Nat.zero_le _)
  simp only [head_three hCore, tail_two hCore, head_two hCore,
    rowMark_three, rowMark_two] at hT3 hH3 hT2 hH2
  rw [base_eq hCore]
  fin_cases v
  all_goals simp [lbCoeff, contribForm, heightLB, chipWeight, markY, markX,
    hT3, hH3, hT2, hH2]
  all_goals (try (first | ring1 | ring_nf))
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals (try split_ifs)
  all_goals (try omega)

theorem lbCoeff_nonneg {d : DegSpec 8 12} (hA : d.length 4 ≤ d.length 3)
    (v : Fin 8) : 0 ≤ lbCoeff d v := by
  have hM : markY d = d.length 3 - d.length 4 := rfl
  fin_cases v
  · show (0 : ℤ) ≤
      (if markY d = 0 then (0 : ℤ) else if d.length 3 ≤ markY d then 1 else 0)
        + headContribution (d.length 3 - markY d) 0 (d.length 4)
    have h := headContribution_nonneg (L := d.length 3 - markY d) (hu := 0)
      (hv := d.length 4) (Nat.zero_le _) (by omega)
    split_ifs <;> omega
  · show (0 : ℤ) ≤ tailContribution (d.length 4) (d.length 4) 0
    exact tailContribution_nonneg (Nat.zero_le _) (by omega)
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ (if markY d = 0 then (1 : ℤ) else 0)
        + (if markX d = 0 then (0 : ℤ)
            else if d.length 2 ≤ markX d then 1 else 0)
        + (if 0 < markY d then (0 : ℤ)
            else tailContribution (d.length 3) 0 (d.length 4))
    have h := tailContribution_ge_neg_one (L := d.length 3) (hu := 0)
      (hv := d.length 4) (by omega) (by omega)
    split_ifs <;> omega
  · show (0 : ℤ) ≤ 1 + headContribution (d.length 4) (d.length 4) 0
    have h := headContribution_ge_neg_one (L := d.length 4) (hu := d.length 4)
      (hv := 0) (by omega) (by omega)
    omega
  · show (0 : ℤ) ≤ (1 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ (if markX d = 0 then (1 : ℤ) else 0)
    split_ifs <;> norm_num
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num

/-- Target representative for vertex 0, moved to vertex 3 when slot 3 is contracted. -/
def ownerZero (d : DegSpec 8 12) : Fin 8 := if d.length 3 = 0 then 3 else 0

/-- Target representative for vertex 1, moved to vertex 4 when slot 4 is contracted. -/
def ownerOne (d : DegSpec 8 12) : Fin 8 := if d.length 4 = 0 then 4 else 1

theorem lbCoeff_owner_zero {d : DegSpec 8 12} (hA : d.length 4 ≤ d.length 3) :
    1 ≤ lbCoeff d (ownerZero d) := by
  have hM : markY d = d.length 3 - d.length 4 := rfl
  unfold ownerZero
  by_cases hz : d.length 3 = 0
  · rw [ite_eq_left hz]
    show (1 : ℤ) ≤ (if markY d = 0 then (1 : ℤ) else 0)
        + (if markX d = 0 then (0 : ℤ)
            else if d.length 2 ≤ markX d then 1 else 0)
        + (if 0 < markY d then (0 : ℤ)
            else tailContribution (d.length 3) 0 (d.length 4))
    have h4 : d.length 4 = 0 := by omega
    have hzero : tailContribution (d.length 3) 0 (d.length 4) = 0 := by
      rw [hz, h4]
      exact tailContribution_zero_zero 0
    rw [hzero]
    split_ifs <;> omega
  · rw [ite_eq_right hz]
    show (1 : ℤ) ≤
      (if markY d = 0 then (0 : ℤ) else if d.length 3 ≤ markY d then 1 else 0)
        + headContribution (d.length 3 - markY d) 0 (d.length 4)
    by_cases h4 : d.length 4 = 0
    · have hzero : headContribution (d.length 3 - markY d) 0 (d.length 4) = 0 := by
        rw [show d.length 3 - markY d = 0 by omega, h4]
        exact headContribution_zero_zero 0
      rw [hzero, ite_eq_right (by omega : ¬ markY d = 0),
        ite_eq_left (by omega : d.length 3 ≤ markY d)]
      norm_num
    · have hOne : headContribution (d.length 3 - markY d) 0 (d.length 4) = 1 :=
        headContribution_eq_one_of_full (L := d.length 3 - markY d) (hu := 0)
          (hv := d.length 4) (by omega) (by omega)
      rw [hOne]
      split_ifs <;> omega

theorem lbCoeff_owner_one {d : DegSpec 8 12} : 1 ≤ lbCoeff d (ownerOne d) := by
  unfold ownerOne
  by_cases hz : d.length 4 = 0
  · rw [ite_eq_left hz]
    show (1 : ℤ) ≤ 1 + headContribution (d.length 4) (d.length 4) 0
    rw [hz, headContribution_zero_zero]
    norm_num
  · rw [ite_eq_right hz]
    show (1 : ℤ) ≤ tailContribution (d.length 4) (d.length 4) 0
    rw [tailContribution_eq_one_of_full (L := d.length 4) (hu := d.length 4)
      (hv := 0) (by omega) (by omega)]

/-! ### The right banana pair -/

/-- Expanded core coefficients after the right-banana height script, combining the base with
endpoint contributions. `rbCoeff_eq` identifies this formula with the script computation. -/
def rbCoeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then
    (if markY d = 0 then (0 : ℤ) else if d.length 3 ≤ markY d then 1 else 0)
  else if v = 1 then 0
  else if v = 2 then 0
  else if v = 3 then
    (if markY d = 0 then (1 : ℤ) else 0)
      + (if markX d = 0 then (0 : ℤ)
          else if d.length 2 ≤ markX d then 1 else 0)
      + (if markX d < d.length 2 then (0 : ℤ)
          else headContribution (d.length 2) (d.length 7) 0)
  else if v = 4 then 1
  else if v = 5 then 1 + tailContribution (d.length 7) 0 (d.length 7)
  else if v = 6 then
    (if markX d = 0 then (1 : ℤ) else 0)
      + tailContribution (d.length 7) (d.length 7) 0
  else headContribution (d.length 7) 0 (d.length 7)

theorem rbCoeff_eq {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (hC : d.length 7 ≤ d.length 2) (hA : d.length 4 ≤ d.length 3) (v : Fin 8) :
    base d v + contribForm d (heightRB d) v = rbCoeff d v := by
  have hT3 := slotTailForm_of_arm d (mark := rowMark d) (h := heightRB d) (e := 3)
    (by rw [head_three hCore]; rfl) (by intro _; rw [tail_three hCore]; rfl)
  have hH3 := slotHeadForm_of_arm d (mark := rowMark d) (h := heightRB d) (e := 3)
    (by rw [tail_three hCore]; rfl)
    (by rw [rowMark_three]; simp only [markY]; omega)
    (by rw [head_three hCore]; exact Nat.zero_le _)
  have hT2 := slotTailForm_of_arm d (mark := rowMark d) (h := heightRB d) (e := 2)
    (by rw [head_two hCore]; rfl)
    (by intro hz; rw [tail_two hCore]
        rw [rowMark_two] at hz
        show d.length 7 = 0
        simpa [markX] using hz)
  have hH2 := slotHeadForm_of_flat_head d (mark := rowMark d) (h := heightRB d)
    (e := 2) (by rw [head_two hCore]; rfl)
    (by intro hz; rw [tail_two hCore]
        rw [rowMark_two] at hz
        show d.length 7 = 0
        simpa [markX] using hz)
  simp only [tail_three hCore, head_three hCore, tail_two hCore,
    rowMark_three, rowMark_two] at hT3 hH3 hT2 hH2
  rw [base_eq hCore]
  fin_cases v
  all_goals simp [rbCoeff, contribForm, heightRB, chipWeight, markY, markX,
    hT3, hH3, hT2, hH2]
  all_goals (try (first | ring1 | ring_nf))
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals (try split_ifs)
  all_goals (try omega)

theorem rbCoeff_nonneg {d : DegSpec 8 12} (hC : d.length 7 ≤ d.length 2)
    (v : Fin 8) : 0 ≤ rbCoeff d v := by
  have hN : markX d = d.length 7 := rfl
  fin_cases v
  · show (0 : ℤ) ≤
      (if markY d = 0 then (0 : ℤ) else if d.length 3 ≤ markY d then 1 else 0)
    split_ifs <;> norm_num
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ (if markY d = 0 then (1 : ℤ) else 0)
        + (if markX d = 0 then (0 : ℤ)
            else if d.length 2 ≤ markX d then 1 else 0)
        + (if markX d < d.length 2 then (0 : ℤ)
            else headContribution (d.length 2) (d.length 7) 0)
    have h := headContribution_ge_neg_one (L := d.length 2) (hu := d.length 7)
      (hv := 0) (by omega) (by omega)
    by_cases hlt : markX d < d.length 2
    · rw [ite_eq_left hlt]
      have hne : ¬ (d.length 2 ≤ markX d) := by omega
      split_ifs <;> omega
    · rw [ite_eq_right hlt]
      by_cases h0 : markX d = 0
      · rw [ite_eq_left h0]
        have h7 : d.length 7 = 0 := by omega
        have h2 : d.length 2 = 0 := by omega
        rw [h2, h7, headContribution_zero_zero]
        split_ifs <;> norm_num
      · rw [ite_eq_right h0, ite_eq_left (by omega : d.length 2 ≤ markX d)]
        split_ifs <;> omega
  · show (0 : ℤ) ≤ (1 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ 1 + tailContribution (d.length 7) 0 (d.length 7)
    have h := tailContribution_ge_neg_one (L := d.length 7) (hu := 0)
      (hv := d.length 7) (by omega) (by omega)
    omega
  · show (0 : ℤ) ≤ (if markX d = 0 then (1 : ℤ) else 0)
        + tailContribution (d.length 7) (d.length 7) 0
    have h := zeroChip_add_tail_full (d.length 7)
    have hz : zeroChip (d.length 7) = if markX d = 0 then (1 : ℤ) else 0 := by
      unfold zeroChip
      rw [hN]
    omega
  · show (0 : ℤ) ≤ headContribution (d.length 7) 0 (d.length 7)
    exact headContribution_nonneg (Nat.zero_le _) (by omega)

/-- Target representative for vertex 7, moved to vertex 5 when slot 7 is contracted. -/
def ownerSeven (d : DegSpec 8 12) : Fin 8 := if d.length 7 = 0 then 5 else 7

theorem rbCoeff_owner_six {d : DegSpec 8 12} : 1 ≤ rbCoeff d 6 := by
  have hN : markX d = d.length 7 := rfl
  show (1 : ℤ) ≤ (if markX d = 0 then (1 : ℤ) else 0)
      + tailContribution (d.length 7) (d.length 7) 0
  have h := zeroChip_add_tail_full (d.length 7)
  have hz : zeroChip (d.length 7) = if markX d = 0 then (1 : ℤ) else 0 := by
    unfold zeroChip
    rw [hN]
  omega

theorem rbCoeff_owner_seven {d : DegSpec 8 12} : 1 ≤ rbCoeff d (ownerSeven d) := by
  unfold ownerSeven
  by_cases hz : d.length 7 = 0
  · rw [ite_eq_left hz]
    show (1 : ℤ) ≤ 1 + tailContribution (d.length 7) 0 (d.length 7)
    rw [hz, tailContribution_zero_zero]
    norm_num
  · rw [ite_eq_right hz]
    show (1 : ℤ) ≤ headContribution (d.length 7) 0 (d.length 7)
    rw [headContribution_eq_one_of_full (L := d.length 7) (hu := 0)
      (hv := d.length 7) (by omega) (by omega)]

/-! ### The stem pair -/

theorem pairLow_comm (d : DegSpec 8 12) : pairLow d = min (armThree d) (armTwo d) := by
  unfold pairLow
  omega

/-- Expanded core coefficients after the vertex-2 height script, combining the pair allocation
with endpoint contributions. `t2Coeff_eq` identifies this formula with the script computation. -/
def t2Coeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then
    (if markY d = 0 then (0 : ℤ) else if d.length 3 ≤ markY d then 1 else 0)
      + (if markY d < d.length 3 then (0 : ℤ)
          else headContribution (d.length 3) (pairLow d) 0)
  else if v = 1 then 0
  else if v = 2 then
    zeroChip (d.length 5) + zeroChip (d.length 8)
      + (tailContribution (d.length 5) (targetTwo d) 0
          + headContribution (d.length 8) 0 (targetTwo d)
          + tailContribution (d.length 9) (targetTwo d) (pairLow d))
  else if v = 3 then
    zeroChip (markY d) + zeroChip (d.length 2 - markX d)
      + (tailContribution (markY d) (pairLow d) 0
          + headContribution (d.length 2 - markX d) 0 (pairLow d)
          + headContribution (d.length 9) (targetTwo d) (pairLow d))
  else if v = 4 then
    positiveChip (d.length 5) + headContribution (d.length 5) (targetTwo d) 0
  else if v = 5 then
    positiveChip (d.length 8) + tailContribution (d.length 8) 0 (targetTwo d)
  else if v = 6 then
    (zeroChip (markX d) - zeroChip (d.length 2))
      + (if 0 < markX d then (0 : ℤ)
          else tailContribution (d.length 2) 0 (pairLow d))
  else 0

theorem t2Coeff_eq {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (hC : d.length 7 ≤ d.length 2) (hA : d.length 4 ≤ d.length 3) (v : Fin 8) :
    pairAlloc d v + contribForm d (heightT2 d) v = t2Coeff d v := by
  have hlow : rowMark d 3 = 0 → heightT2 d (d.core.tail 3) = 0 := by
    intro hz
    rw [rowMark_three] at hz
    rw [tail_three hCore]
    show pairLow d = 0
    simp only [pairLow, armThree]
    omega
  have hT3 := slotTailForm_of_arm d (mark := rowMark d) (h := heightT2 d) (e := 3)
    (by rw [head_three hCore]; rfl) hlow
  have hH3 := slotHeadForm_of_flat_head d (mark := rowMark d) (h := heightT2 d)
    (e := 3) (by rw [head_three hCore]; rfl) hlow
  have hT2 := slotTailForm_of_flat_tail d (mark := rowMark d) (h := heightT2 d)
    (e := 2) (by rw [tail_two hCore]; rfl)
  have hH2 := slotHeadForm_of_arm d (mark := rowMark d) (h := heightT2 d) (e := 2)
    (by rw [tail_two hCore]; rfl)
    (by rw [rowMark_two]; simpa [markX] using hC)
    (by rw [head_two hCore, rowMark_two]
        show pairLow d ≤ d.length 2 - markX d
        simp only [pairLow, armThree]; omega)
  simp only [tail_three hCore, head_two hCore,
    rowMark_three, rowMark_two] at hT3 hH3 hT2 hH2
  simp only [pairAlloc]
  rw [base_eq hCore]
  fin_cases v
  all_goals simp [t2Coeff, contribForm, heightT2, chipWeight, zeroChip,
    positiveChip, transferWeight, indicatorWeight, markY, markX,
    hT3, hH3, hT2, hH2]
  all_goals (try (first | ring1 | ring_nf))
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals (try split_ifs)
  all_goals (try omega)

theorem t2Coeff_nonneg {d : DegSpec 8 12} (hC : d.length 7 ≤ d.length 2)
    (v : Fin 8) : 0 ≤ t2Coeff d v := by
  have hA1 : armThree d ≤ markY d := Nat.min_le_left _ _
  have hA2 : armThree d ≤ d.length 2 - markX d := Nat.min_le_right _ _
  have hB1 : armTwo d ≤ d.length 5 := Nat.min_le_left _ _
  have hB2 : armTwo d ≤ d.length 8 := Nat.min_le_right _ _
  have hg1 : pairLow d ≤ armTwo d := Nat.min_le_left _ _
  have hg2 : pairLow d ≤ armThree d := Nat.min_le_right _ _
  have hO1 : targetTwo d ≤ armTwo d := Nat.min_le_left _ _
  have hMY : markY d ≤ d.length 3 := by simp only [markY]; omega
  have hMX : markX d ≤ d.length 2 := by simpa [markX] using hC
  fin_cases v
  · show (0 : ℤ) ≤
      (if markY d = 0 then (0 : ℤ) else if d.length 3 ≤ markY d then 1 else 0)
        + (if markY d < d.length 3 then (0 : ℤ)
            else headContribution (d.length 3) (pairLow d) 0)
    by_cases hlt : markY d < d.length 3
    · rw [ite_eq_left hlt]
      split_ifs <;> omega
    · rw [ite_eq_right hlt]
      have h := headContribution_ge_neg_one (L := d.length 3) (hu := pairLow d)
        (hv := 0) (by omega) (by omega)
      by_cases h0 : markY d = 0
      · rw [ite_eq_left h0]
        have h3 : d.length 3 = 0 := by omega
        have hp : pairLow d = 0 := by omega
        rw [h3, hp, headContribution_zero_zero]
        norm_num
      · rw [ite_eq_right h0, ite_eq_left (by omega : d.length 3 ≤ markY d)]
        omega
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ zeroChip (d.length 5) + zeroChip (d.length 8)
        + (tailContribution (d.length 5) (targetTwo d) 0
            + headContribution (d.length 8) 0 (targetTwo d)
            + tailContribution (d.length 9) (targetTwo d) (pairLow d))
    have hpair := pairTarget_nonneg fwd rev fwd (k := (0 : ℤ))
      (la := d.length 5) (lb := d.length 8) (m := d.length 9)
      (a := armTwo d) (b := armThree d) (g := pairLow d) (o := targetTwo d)
      rfl rfl rfl le_rfl (by norm_num)
      (by intro hcon; exact absurd hcon (by norm_num))
    simp only [fwd_tail, rev_tail] at hpair
    omega
  · show (0 : ℤ) ≤ zeroChip (markY d) + zeroChip (d.length 2 - markX d)
        + (tailContribution (markY d) (pairLow d) 0
            + headContribution (d.length 2 - markX d) 0 (pairLow d)
            + headContribution (d.length 9) (targetTwo d) (pairLow d))
    have hpair := pairPartner_nonneg fwd rev rev (k := (0 : ℤ))
      (lc := markY d) (ld := d.length 2 - markX d) (m := d.length 9)
      (a := armTwo d) (b := armThree d) (g := pairLow d) (o := targetTwo d)
      rfl rfl rfl le_rfl (by norm_num)
      (by intro hcon; exact absurd hcon (by norm_num))
    simp only [fwd_tail, rev_tail] at hpair
    omega
  · show (0 : ℤ) ≤ positiveChip (d.length 5)
        + headContribution (d.length 5) (targetTwo d) 0
    exact positiveChip_add_head_nonneg (by omega)
  · show (0 : ℤ) ≤ positiveChip (d.length 8)
        + tailContribution (d.length 8) 0 (targetTwo d)
    exact positiveChip_add_tail_nonneg (by omega)
  · show (0 : ℤ) ≤ (zeroChip (markX d) - zeroChip (d.length 2))
        + (if 0 < markX d then (0 : ℤ)
            else tailContribution (d.length 2) 0 (pairLow d))
    by_cases hp : 0 < markX d
    · rw [ite_eq_left hp]
      have h1 : zeroChip (markX d) = 0 := by
        have hne : markX d ≠ 0 := by omega
        simp [zeroChip, hne]
      have h2 : zeroChip (d.length 2) = 0 := by
        have hne : d.length 2 ≠ 0 := by omega
        simp [zeroChip, hne]
      omega
    · rw [ite_eq_right hp]
      have h1 : zeroChip (markX d) = 1 := by
        have hz : markX d = 0 := by omega
        simp [zeroChip, hz]
      have hpos := positiveChip_add_tail_nonneg (L := d.length 2)
        (h := pairLow d) (by omega)
      have h2 : positiveChip (d.length 2) = 1 - zeroChip (d.length 2) := by
        unfold positiveChip zeroChip
        split_ifs <;> omega
      omega
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num

/-- Target representative for vertex 2, moved to vertex 3 when their connecting slot 9 is
contracted and the effective arm at vertex 2 is longer. -/
def ownerTwo (d : DegSpec 8 12) : Fin 8 :=
  if d.length 9 = 0 ∧ ¬ (armTwo d ≤ armThree d) then 3 else 2

theorem t2Coeff_owner {d : DegSpec 8 12} : 1 ≤ t2Coeff d (ownerTwo d) := by
  unfold ownerTwo
  by_cases hc : d.length 9 = 0 ∧ ¬ (armTwo d ≤ armThree d)
  · obtain ⟨hc1, hc2⟩ := hc
    rw [ite_eq_left ⟨hc1, hc2⟩]
    show (1 : ℤ) ≤ zeroChip (markY d) + zeroChip (d.length 2 - markX d)
        + (tailContribution (markY d) (pairLow d) 0
            + headContribution (d.length 2 - markX d) 0 (pairLow d)
            + headContribution (d.length 9) (targetTwo d) (pairLow d))
    have hpair := pairPartner_nonneg fwd rev rev (k := (1 : ℤ))
      (lc := markY d) (ld := d.length 2 - markX d) (m := d.length 9)
      (a := armTwo d) (b := armThree d) (g := pairLow d) (o := targetTwo d)
      rfl rfl rfl (by norm_num) le_rfl (fun _ => ⟨hc1, by omega⟩)
    simp only [fwd_tail, rev_tail] at hpair
    omega
  · rw [ite_eq_right hc]
    show (1 : ℤ) ≤ zeroChip (d.length 5) + zeroChip (d.length 8)
        + (tailContribution (d.length 5) (targetTwo d) 0
            + headContribution (d.length 8) 0 (targetTwo d)
            + tailContribution (d.length 9) (targetTwo d) (pairLow d))
    have hc' : d.length 9 = 0 → armTwo d ≤ armThree d := by
      intro h9
      by_contra hcon
      exact hc ⟨h9, hcon⟩
    have hpair := pairTarget_nonneg fwd rev fwd (k := (1 : ℤ))
      (la := d.length 5) (lb := d.length 8) (m := d.length 9)
      (a := armTwo d) (b := armThree d) (g := pairLow d) (o := targetTwo d)
      rfl rfl rfl (by norm_num) le_rfl (fun _ hm => hc' hm)
    simp only [fwd_tail, rev_tail] at hpair
    omega

/-- Expanded core coefficients after the vertex-3 height script, combining the pair allocation
with endpoint contributions. `t3Coeff_eq` identifies this formula with the script computation. -/
def t3Coeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then
    (if markY d = 0 then (0 : ℤ) else if d.length 3 ≤ markY d then 1 else 0)
      + (if markY d < d.length 3 then (0 : ℤ)
          else headContribution (d.length 3) (targetThree d) 0)
  else if v = 1 then 0
  else if v = 2 then
    zeroChip (d.length 5) + zeroChip (d.length 8)
      + (tailContribution (d.length 5) (pairLow d) 0
          + headContribution (d.length 8) 0 (pairLow d)
          + tailContribution (d.length 9) (pairLow d) (targetThree d))
  else if v = 3 then
    zeroChip (markY d) + zeroChip (d.length 2 - markX d)
      + (tailContribution (markY d) (targetThree d) 0
          + headContribution (d.length 2 - markX d) 0 (targetThree d)
          + headContribution (d.length 9) (pairLow d) (targetThree d))
  else if v = 4 then
    positiveChip (d.length 5) + headContribution (d.length 5) (pairLow d) 0
  else if v = 5 then
    positiveChip (d.length 8) + tailContribution (d.length 8) 0 (pairLow d)
  else if v = 6 then
    (zeroChip (markX d) - zeroChip (d.length 2))
      + (if 0 < markX d then (0 : ℤ)
          else tailContribution (d.length 2) 0 (targetThree d))
  else 0

theorem t3Coeff_eq {d : DegSpec 8 12} (hCore : d.core = row08Core)
    (hC : d.length 7 ≤ d.length 2) (hA : d.length 4 ≤ d.length 3) (v : Fin 8) :
    pairAlloc d v + contribForm d (heightT3 d) v = t3Coeff d v := by
  have hlow : rowMark d 3 = 0 → heightT3 d (d.core.tail 3) = 0 := by
    intro hz
    rw [rowMark_three] at hz
    rw [tail_three hCore]
    show targetThree d = 0
    simp only [targetThree, armThree]
    omega
  have hT3 := slotTailForm_of_arm d (mark := rowMark d) (h := heightT3 d) (e := 3)
    (by rw [head_three hCore]; rfl) hlow
  have hH3 := slotHeadForm_of_flat_head d (mark := rowMark d) (h := heightT3 d)
    (e := 3) (by rw [head_three hCore]; rfl) hlow
  have hT2 := slotTailForm_of_flat_tail d (mark := rowMark d) (h := heightT3 d)
    (e := 2) (by rw [tail_two hCore]; rfl)
  have hH2 := slotHeadForm_of_arm d (mark := rowMark d) (h := heightT3 d) (e := 2)
    (by rw [tail_two hCore]; rfl)
    (by rw [rowMark_two]; simpa [markX] using hC)
    (by rw [head_two hCore, rowMark_two]
        show targetThree d ≤ d.length 2 - markX d
        simp only [targetThree, armThree]; omega)
  simp only [tail_three hCore, head_two hCore,
    rowMark_three, rowMark_two] at hT3 hH3 hT2 hH2
  simp only [pairAlloc]
  rw [base_eq hCore]
  fin_cases v
  all_goals simp [t3Coeff, contribForm, heightT3, chipWeight, zeroChip,
    positiveChip, transferWeight, indicatorWeight, markY, markX,
    hT3, hH3, hT2, hH2]
  all_goals (try (first | ring1 | ring_nf))
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals (try split_ifs)
  all_goals (try omega)

theorem t3Coeff_nonneg {d : DegSpec 8 12} (hC : d.length 7 ≤ d.length 2)
    (v : Fin 8) : 0 ≤ t3Coeff d v := by
  have hA1 : armThree d ≤ markY d := Nat.min_le_left _ _
  have hA2 : armThree d ≤ d.length 2 - markX d := Nat.min_le_right _ _
  have hB1 : armTwo d ≤ d.length 5 := Nat.min_le_left _ _
  have hB2 : armTwo d ≤ d.length 8 := Nat.min_le_right _ _
  have hg1 : pairLow d ≤ armTwo d := Nat.min_le_left _ _
  have hg2 : pairLow d ≤ armThree d := Nat.min_le_right _ _
  have hO1 : targetThree d ≤ armThree d := Nat.min_le_left _ _
  have hMY : markY d ≤ d.length 3 := by simp only [markY]; omega
  have hMX : markX d ≤ d.length 2 := by simpa [markX] using hC
  fin_cases v
  · show (0 : ℤ) ≤
      (if markY d = 0 then (0 : ℤ) else if d.length 3 ≤ markY d then 1 else 0)
        + (if markY d < d.length 3 then (0 : ℤ)
            else headContribution (d.length 3) (targetThree d) 0)
    by_cases hlt : markY d < d.length 3
    · rw [ite_eq_left hlt]
      split_ifs <;> omega
    · rw [ite_eq_right hlt]
      have h := headContribution_ge_neg_one (L := d.length 3)
        (hu := targetThree d) (hv := 0) (by omega) (by omega)
      by_cases h0 : markY d = 0
      · rw [ite_eq_left h0]
        have h3 : d.length 3 = 0 := by omega
        have hp : targetThree d = 0 := by omega
        rw [h3, hp, headContribution_zero_zero]
        norm_num
      · rw [ite_eq_right h0, ite_eq_left (by omega : d.length 3 ≤ markY d)]
        omega
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ zeroChip (d.length 5) + zeroChip (d.length 8)
        + (tailContribution (d.length 5) (pairLow d) 0
            + headContribution (d.length 8) 0 (pairLow d)
            + tailContribution (d.length 9) (pairLow d) (targetThree d))
    have hpair := pairPartner_nonneg fwd rev fwd (k := (0 : ℤ))
      (lc := d.length 5) (ld := d.length 8) (m := d.length 9)
      (a := armThree d) (b := armTwo d) (g := pairLow d) (o := targetThree d)
      rfl (pairLow_comm d) rfl le_rfl (by norm_num)
      (by intro hcon; exact absurd hcon (by norm_num))
    simp only [fwd_tail, rev_tail] at hpair
    omega
  · show (0 : ℤ) ≤ zeroChip (markY d) + zeroChip (d.length 2 - markX d)
        + (tailContribution (markY d) (targetThree d) 0
            + headContribution (d.length 2 - markX d) 0 (targetThree d)
            + headContribution (d.length 9) (pairLow d) (targetThree d))
    have hpair := pairTarget_nonneg fwd rev rev (k := (0 : ℤ))
      (la := markY d) (lb := d.length 2 - markX d) (m := d.length 9)
      (a := armThree d) (b := armTwo d) (g := pairLow d) (o := targetThree d)
      rfl (pairLow_comm d) rfl le_rfl (by norm_num)
      (by intro hcon; exact absurd hcon (by norm_num))
    simp only [fwd_tail, rev_tail] at hpair
    omega
  · show (0 : ℤ) ≤ positiveChip (d.length 5)
        + headContribution (d.length 5) (pairLow d) 0
    exact positiveChip_add_head_nonneg (by omega)
  · show (0 : ℤ) ≤ positiveChip (d.length 8)
        + tailContribution (d.length 8) 0 (pairLow d)
    exact positiveChip_add_tail_nonneg (by omega)
  · show (0 : ℤ) ≤ (zeroChip (markX d) - zeroChip (d.length 2))
        + (if 0 < markX d then (0 : ℤ)
            else tailContribution (d.length 2) 0 (targetThree d))
    by_cases hp : 0 < markX d
    · rw [ite_eq_left hp]
      have h1 : zeroChip (markX d) = 0 := by
        have hne : markX d ≠ 0 := by omega
        simp [zeroChip, hne]
      have h2 : zeroChip (d.length 2) = 0 := by
        have hne : d.length 2 ≠ 0 := by omega
        simp [zeroChip, hne]
      omega
    · rw [ite_eq_right hp]
      have h1 : zeroChip (markX d) = 1 := by
        have hz : markX d = 0 := by omega
        simp [zeroChip, hz]
      have hpos := positiveChip_add_tail_nonneg (L := d.length 2)
        (h := targetThree d) (by omega)
      have h2 : positiveChip (d.length 2) = 1 - zeroChip (d.length 2) := by
        unfold positiveChip zeroChip
        split_ifs <;> omega
      omega
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num

/-- Target representative for vertex 3, moved to vertex 2 when their connecting slot 9 is
contracted and the effective arm at vertex 3 is longer. -/
def ownerThree (d : DegSpec 8 12) : Fin 8 :=
  if d.length 9 = 0 ∧ ¬ (armThree d ≤ armTwo d) then 2 else 3

theorem t3Coeff_owner {d : DegSpec 8 12} : 1 ≤ t3Coeff d (ownerThree d) := by
  unfold ownerThree
  by_cases hc : d.length 9 = 0 ∧ ¬ (armThree d ≤ armTwo d)
  · obtain ⟨hc1, hc2⟩ := hc
    rw [ite_eq_left ⟨hc1, hc2⟩]
    show (1 : ℤ) ≤ zeroChip (d.length 5) + zeroChip (d.length 8)
        + (tailContribution (d.length 5) (pairLow d) 0
            + headContribution (d.length 8) 0 (pairLow d)
            + tailContribution (d.length 9) (pairLow d) (targetThree d))
    have hpair := pairPartner_nonneg fwd rev fwd (k := (1 : ℤ))
      (lc := d.length 5) (ld := d.length 8) (m := d.length 9)
      (a := armThree d) (b := armTwo d) (g := pairLow d) (o := targetThree d)
      rfl (pairLow_comm d) rfl (by norm_num) le_rfl (fun _ => ⟨hc1, by omega⟩)
    simp only [fwd_tail, rev_tail] at hpair
    omega
  · rw [ite_eq_right hc]
    show (1 : ℤ) ≤ zeroChip (markY d) + zeroChip (d.length 2 - markX d)
        + (tailContribution (markY d) (targetThree d) 0
            + headContribution (d.length 2 - markX d) 0 (targetThree d)
            + headContribution (d.length 9) (pairLow d) (targetThree d))
    have hc' : d.length 9 = 0 → armThree d ≤ armTwo d := by
      intro h9
      by_contra hcon
      exact hc ⟨h9, hcon⟩
    have hpair := pairTarget_nonneg fwd rev rev (k := (1 : ℤ))
      (la := markY d) (lb := d.length 2 - markX d) (m := d.length 9)
      (a := armThree d) (b := armTwo d) (g := pairLow d) (o := targetThree d)
      rfl (pairLow_comm d) rfl (by norm_num) le_rfl (fun _ hm => hc' hm)
    simp only [fwd_tail, rev_tail] at hpair
    omega

/-! ## Every contracted core class is reached -/

theorem rowDivisor_reaches_coreVertex {d : DegSpec 8 12}
    (hCore : d.core = row08Core)
    (hC : d.length 7 ≤ d.length 2) (hA : d.length 4 ≤ d.length 3)
    (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8, d.rep x = d.rep y ↔ ReachIn row08Core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0) (center : Fin 8) :
    Reaches d.graph (rowDivisor d) (d.coreVertex center) := by
  have hCoreValue : ∀ r : Fin 8, rowDivisor d (d.coreVertex r) =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), base d v :=
    markedDivisorTwo_coreVertex d chipWeight (rowMark d) 3 2
  have hInterior := markedDivisorTwo_interior d chipWeight (rowMark d)
    chipWeight_nonneg 3 2
  have hChip := markedDivisorTwo_chip d chipWeight (rowMark d)
    (fun g hg => marked_of_rowMark_pos d hg)
  have hBase : ∀ r : Fin 8,
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), base d v =
        ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), base d v :=
    fun _ => rfl
  have hPair := pairAlloc_classSum hCore
  have hpLB := profileLB hCore hC hA
  have hpRB := profileRB hCore hC hA
  have hpT2 := profileT2 hCore hC hA
  have hpT3 := profileT3 hCore hC hA
  have hrLB := height_rep_eq d hCore hpLB.const F hRepReach hFZero
  have hrRB := height_rep_eq d hCore hpRB.const F hRepReach hFZero
  have hrT2 := height_rep_eq d hCore hpT2.const F hRepReach hFZero
  have hrT3 := height_rep_eq d hCore hpT3.const F hRepReach hFZero
  have hOZ : d.rep (ownerZero d) = d.rep 0 := by
    unfold ownerZero
    by_cases hz : d.length 3 = 0
    · rw [ite_eq_left hz]
      have h := d.rep_zero 3 hz
      rw [hCore] at h
      simpa [row08Core] using h
    · rw [ite_eq_right hz]
  have hOO : d.rep (ownerOne d) = d.rep 1 := by
    unfold ownerOne
    by_cases hz : d.length 4 = 0
    · rw [ite_eq_left hz]
      have h := d.rep_zero 4 hz
      rw [hCore] at h
      simpa [row08Core] using h.symm
    · rw [ite_eq_right hz]
  have hOS : d.rep (ownerSeven d) = d.rep 7 := by
    unfold ownerSeven
    by_cases hz : d.length 7 = 0
    · rw [ite_eq_left hz]
      have h := d.rep_zero 7 hz
      rw [hCore] at h
      simpa [row08Core] using h
    · rw [ite_eq_right hz]
  have hOT : d.rep (ownerTwo d) = d.rep 2 := by
    unfold ownerTwo
    by_cases hz : d.length 9 = 0 ∧ ¬ (armTwo d ≤ armThree d)
    · rw [ite_eq_left hz]
      have h := d.rep_zero 9 hz.1
      rw [hCore] at h
      simpa [row08Core] using h.symm
    · rw [ite_eq_right hz]
  have hOTh : d.rep (ownerThree d) = d.rep 3 := by
    unfold ownerThree
    by_cases hz : d.length 9 = 0 ∧ ¬ (armThree d ≤ armTwo d)
    · rw [ite_eq_left hz]
      have h := d.rep_zero 9 hz.1
      rw [hCore] at h
      simpa [row08Core] using h
    · rw [ite_eq_right hz]
  fin_cases center
  · exact (DharMove.ofScript _ (residual_effective d hpLB hrLB hCoreValue
      hInterior hChip hBase hOZ (fun v => by
        rw [contrib_eq hCore hpLB hrLB v]
        exact residual_of_coeff
          (fun w => by rw [lbCoeff_eq hCore hC hA w]; exact lbCoeff_nonneg hA w)
          (by rw [lbCoeff_eq hCore hC hA (ownerZero d)]
              exact lbCoeff_owner_zero hA) v))).reaches
  · exact (DharMove.ofScript _ (residual_effective d hpLB hrLB hCoreValue
      hInterior hChip hBase hOO (fun v => by
        rw [contrib_eq hCore hpLB hrLB v]
        exact residual_of_coeff
          (fun w => by rw [lbCoeff_eq hCore hC hA w]; exact lbCoeff_nonneg hA w)
          (by rw [lbCoeff_eq hCore hC hA (ownerOne d)]
              exact lbCoeff_owner_one) v))).reaches
  · exact (DharMove.ofScript _ (residual_effective d hpT2 hrT2 hCoreValue
      hInterior hChip hPair hOT (fun v => by
        rw [contrib_eq hCore hpT2 hrT2 v]
        exact residual_of_coeff
          (fun w => by rw [t2Coeff_eq hCore hC hA w]; exact t2Coeff_nonneg hC w)
          (by rw [t2Coeff_eq hCore hC hA (ownerTwo d)]
              exact t2Coeff_owner) v))).reaches
  · exact (DharMove.ofScript _ (residual_effective d hpT3 hrT3 hCoreValue
      hInterior hChip hPair hOTh (fun v => by
        rw [contrib_eq hCore hpT3 hrT3 v]
        exact residual_of_coeff
          (fun w => by rw [t3Coeff_eq hCore hC hA w]; exact t3Coeff_nonneg hC w)
          (by rw [t3Coeff_eq hCore hC hA (ownerThree d)]
              exact t3Coeff_owner) v))).reaches
  · exact reaches_of_effective_representative
      (linearEquiv.refl d.graph (rowDivisor d)) (rowDivisor_effective d)
      (one_le_markedDivisorTwo_at_chip d chipWeight (rowMark d) 3 2
        chipWeight_nonneg (c := 4) (by norm_num [chipWeight]))
  · exact reaches_of_effective_representative
      (linearEquiv.refl d.graph (rowDivisor d)) (rowDivisor_effective d)
      (one_le_markedDivisorTwo_at_chip d chipWeight (rowMark d) 3 2
        chipWeight_nonneg (c := 5) (by norm_num [chipWeight]))
  · exact (DharMove.ofScript _ (residual_effective d hpRB hrRB hCoreValue
      hInterior hChip hBase (rfl : d.rep 6 = d.rep 6) (fun v => by
        rw [contrib_eq hCore hpRB hrRB v]
        exact residual_of_coeff
          (fun w => by rw [rbCoeff_eq hCore hC hA w]; exact rbCoeff_nonneg hC w)
          (by rw [rbCoeff_eq hCore hC hA 6]; exact rbCoeff_owner_six) v))).reaches
  · exact (DharMove.ofScript _ (residual_effective d hpRB hrRB hCoreValue
      hInterior hChip hBase hOS (fun v => by
        rw [contrib_eq hCore hpRB hrRB v]
        exact residual_of_coeff
          (fun w => by rw [rbCoeff_eq hCore hC hA w]; exact rbCoeff_nonneg hC w)
          (by rw [rbCoeff_eq hCore hC hA (ownerSeven d)]
              exact rbCoeff_owner_seven) v))).reaches

/-- **AR's seventh family, first scope.** -/
theorem chamberOne_pencil (length : Fin 12 → ℕ)
    (forest : IsForest row08Core (zeroSlots length))
    (notLoopy : ¬ IsLoopy row08Core (zeroSlots length))
    (hP : GenusFiveRow08Symmetry.ChamberOne length) :
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
  exact rowDivisor_reaches_coreVertex hCore hP.2 hP.1 (zeroSlots length)
    hRepReach hFZero center

end AtanasovRanganathan.GenusFiveRow08ChamberOne
