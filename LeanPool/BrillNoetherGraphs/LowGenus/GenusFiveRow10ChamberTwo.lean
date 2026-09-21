/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationEleven
import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationMarkedTripod
import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationMarkedRow
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow10Symmetry

/-!
# AR row 10, chamber 2

The second scope Atanasov--Ranganathan draw for their *ninth* family: the spoke
`b` realizes the minimum, `|e4| ≤ |e10|` and `|e4| ≤ |e3|`.  The displayed
divisor is

```
 D = [1] + [2] + [7] + (e10 at distance |e4| from 3)
```

so the single mark is `mark e10 = |e10| - |e4|`, measured from `e10`'s tail `0`.
The decomposition is the one of chamber 1 with the mark moved from `e4` to
`e10`: the tripod slides from `1` to `0`, and the half-slot arm slides from `C`
to the apex `A`.

* `{0}` -- a `ConfigurationMarkedTripod` centre: the slots `e0` (to the chip
  `2`), `e2` (to the chip `1`), and the near half of the marked `e10`;
* `{3, 4, 5, 6}` -- **AR's eleventh picture** (`ConfigurationEleven`) with
  `A = 3`, `B = 5`, `C = 4`, `P = 6` and the chip `Q = 7`:

```
 alpha = |e4|   (apex arm: the far half of e10, to the chip at the mark)
 beta  = |e3|   (B arm, to the chip 2)          S = |e9|    t = |e5|
 gamma = |e4|   (C arm, to the chip 1)          u = |e11|   w = |e6|
 m₁, m₂ = |e7|, |e8|
```

Again the chamber's first inequality is exactly `alpha = gamma` and its second is
exactly `gamma ≤ beta`.  The third case, `c = min`, is the `sigma` image of this
chamber and is carried for free by
`GenusFiveRow10Symmetry.chamber_covers`.
-/

namespace AtanasovRanganathan.GenusFiveRow10ChamberTwo

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
open ConfigurationMarkedTripod
open ConfigurationEleven

/-! ## The mark -/

/-- The chip on `e10`, at distance `|e4|` from the head `3`. -/
def markA (d : DegSpec 8 12) : ℕ := d.length 10 - d.length 4

def rowMark (d : DegSpec 8 12) (e : Fin 12) : ℕ := if e = 10 then markA d else 0

@[simp] theorem rowMark_ten (d : DegSpec 8 12) : rowMark d 10 = markA d := by
  simp [rowMark]

theorem rowMark_other (d : DegSpec 8 12) {e : Fin 12} (h10 : e ≠ 10) :
    rowMark d e = 0 := by
  simp [rowMark, h10]

theorem marked_of_rowMark_pos (d : DegSpec 8 12) {e : Fin 12}
    (h : 0 < rowMark d e) : e = 10 := by
  by_cases h10 : e = 10
  · exact h10
  · rw [rowMark_other d h10] at h; omega

/-! ## The core, spelled out -/

section Core

variable {d : DegSpec 8 12} (hCore : d.core = row10Core)
include hCore

theorem tail_ten : d.core.tail 10 = 0 := by rw [hCore]; decide
theorem head_ten : d.core.head 10 = 3 := by rw [hCore]; decide

end Core

/-- The far half of the marked slot -- the apex arm -- has exactly the `C` arm's
length, which is the whole point of the chamber's first inequality. -/
theorem armA_len {d : DegSpec 8 12} (hb : d.length 4 ≤ d.length 10) :
    d.length 10 - markA d = d.length 4 := by
  simp only [markA]; omega

/-! ## The heights

`d.length 4` is `alpha = gamma`, `d.length 3` is `beta`, `d.length 9` is `S`,
`d.length 5` is `t`, `d.length 11` is `u`, `d.length 6` is `w`, and
`d.length 7`, `d.length 8` are the two banana slots. -/

/-- `mB`: `B`'s two resources, its own arm or the apex's arm followed by `S`. -/
def resB (d : DegSpec 8 12) : ℕ := min (d.length 3) (d.length 4 + d.length 9)

/-- `G`: the far route `C1 ⟶ C ⟶ P`, two slots because `C` is chip free. -/
def capG (d : DegSpec 8 12) : ℕ := d.length 4 + d.length 6

/-- The shorter banana slot. -/
def parq (d : DegSpec 8 12) : ℕ := min (d.length 7) (d.length 8)

/-- The height of `B` under the target-`B` profile. -/
def htB (d : DegSpec 8 12) : ℕ := min (resB d) (d.length 4 + d.length 11)

/-- The height of `P` under the target-`P` profile. -/
def htE (d : DegSpec 8 12) : ℕ := min (capG d) (resB d + d.length 11 + parq d)

/-- The height of the chip `Q` under the target-`P` profile. -/
def htD (d : DegSpec 8 12) : ℕ := min (htE d) (resB d + d.length 11)

/-- The height of `B` under the target-`P` profile. -/
def htC (d : DegSpec 8 12) : ℕ := min (htD d) (resB d)

/-- The tripod at `0`: `e0`, then `e2`, then the near half of the marked
`e10`. -/
def tripod (d : DegSpec 8 12) : ℕ :=
  min (d.length 0) (min (d.length 2) (markA d))

/-- The transfer of `B`'s surplus into `Q`'s class when the `B-Q` slot
collapses. -/
def shift (d : DegSpec 8 12) : ℤ :=
  if d.length 11 = 0 ∧ htD d < htE d then 1 else 0

/-- The flat profile, which reaches the apex `3` and the vertex `4` at once. -/
def heightFlat (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 3 then d.length 4 else if v = 4 then d.length 4
  else if v = 5 then d.length 4 else if v = 6 then d.length 4
  else if v = 7 then d.length 4 else 0

/-- The target-`B` profile: `B` alone rises above the flat level. -/
def heightB (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 3 then d.length 4 else if v = 4 then d.length 4
  else if v = 5 then htB d else if v = 6 then d.length 4
  else if v = 7 then d.length 4 else 0

/-- The target-`P` profile: the chip `Q` rides up with `P`. -/
def heightP (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 3 then d.length 4 else if v = 4 then d.length 4
  else if v = 5 then htC d else if v = 6 then htE d
  else if v = 7 then htD d else 0

/-- The tripod profile. -/
def heightT (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 0 then tripod d else 0

/-! ## Profiles -/

theorem mkProfile {d : DegSpec 8 12} (hCore : d.core = row10Core)
    (hb : d.length 4 ≤ d.length 10) {h : Fin 8 → ℕ}
    (hin10 : h 0 ≤ markA d) (hout10 : h 3 ≤ d.length 10 - markA d)
    (hflat10 : h 0 = 0 ∨ h 3 = 0)
    (hconst : ∀ e : Fin 12, d.length e = 0 →
      h (row10Core.tail e) = h (row10Core.head e)) :
    Profile d (rowMark d) h := by
  have ht10 : d.core.tail 10 = 0 := tail_ten hCore
  have hh10 : d.core.head 10 = 3 := head_ten hCore
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e
    by_cases h10 : e = 10
    · subst h10; rw [rowMark_ten]; simp only [markA]; omega
    · rw [rowMark_other d h10]; omega
  · intro e he
    by_cases h10 : e = 10
    · subst h10; rw [ht10, rowMark_ten]; exact hin10
    · rw [rowMark_other d h10] at he; omega
  · intro e he
    by_cases h10 : e = 10
    · subst h10; rw [hh10, rowMark_ten]; exact hout10
    · rw [rowMark_other d h10] at he; omega
  · intro e he
    by_cases h10 : e = 10
    · subst h10; rw [ht10, hh10]; exact hflat10
    · rw [rowMark_other d h10] at he; omega
  · intro e he
    rw [hCore]
    exact hconst e he

theorem profileFlat {d : DegSpec 8 12} (hCore : d.core = row10Core)
    (hb : d.length 4 ≤ d.length 10) (hc : d.length 4 ≤ d.length 3) :
    Profile d (rowMark d) (heightFlat d) := by
  have h0 : heightFlat d 0 = 0 := rfl
  have h3 : heightFlat d 3 = d.length 4 := rfl
  refine mkProfile hCore hb (by rw [h0]; omega)
    (by rw [h3]; simp only [markA]; omega) (Or.inl h0) ?_
  intro e
  fin_cases e
  all_goals simp [heightFlat, row10Core]
  all_goals omega

theorem profileB {d : DegSpec 8 12} (hCore : d.core = row10Core)
    (hb : d.length 4 ≤ d.length 10) (hc : d.length 4 ≤ d.length 3) :
    Profile d (rowMark d) (heightB d) := by
  have h0 : heightB d 0 = 0 := rfl
  have h3 : heightB d 3 = d.length 4 := rfl
  refine mkProfile hCore hb (by rw [h0]; omega)
    (by rw [h3]; simp only [markA]; omega) (Or.inl h0) ?_
  intro e
  fin_cases e
  all_goals simp [heightB, htB, resB, row10Core]
  all_goals omega

theorem profileP {d : DegSpec 8 12} (hCore : d.core = row10Core)
    (hb : d.length 4 ≤ d.length 10) (hc : d.length 4 ≤ d.length 3) :
    Profile d (rowMark d) (heightP d) := by
  have h0 : heightP d 0 = 0 := rfl
  have h3 : heightP d 3 = d.length 4 := rfl
  refine mkProfile hCore hb (by rw [h0]; omega)
    (by rw [h3]; simp only [markA]; omega) (Or.inl h0) ?_
  intro e
  fin_cases e
  all_goals simp [heightP, htC, htD, htE, resB, capG, parq, row10Core]
  all_goals omega

theorem profileT {d : DegSpec 8 12} (hCore : d.core = row10Core)
    (hb : d.length 4 ≤ d.length 10) (_hc : d.length 4 ≤ d.length 3) :
    Profile d (rowMark d) (heightT d) := by
  have h0 : heightT d 0 = tripod d := rfl
  have h3 : heightT d 3 = 0 := rfl
  refine mkProfile hCore hb (by rw [h0]; simp only [tripod]; omega)
    (by rw [h3]; omega) (Or.inr h3) ?_
  intro e
  fin_cases e
  all_goals simp [heightT, tripod, markA, row10Core]
  all_goals omega

/-! ## The endpoint ledger, vertex by vertex -/

def contribForm (d : DegSpec 8 12) (h : Fin 8 → ℕ) (v : Fin 8) : ℤ :=
  if v = 0 then
    slotTailForm d (rowMark d) h 10
      + tailContribution (d.length 0) (h 0) (h 2)
      + headContribution (d.length 2) (h 1) (h 0)
  else if v = 1 then
    tailContribution (d.length 4) (h 1) (h 4)
      + headContribution (d.length 1) (h 2) (h 1)
      + tailContribution (d.length 2) (h 1) (h 0)
  else if v = 2 then
    headContribution (d.length 0) (h 0) (h 2)
      + tailContribution (d.length 1) (h 2) (h 1)
      + tailContribution (d.length 3) (h 2) (h 5)
  else if v = 3 then
    slotHeadForm d (rowMark d) h 10
      + tailContribution (d.length 5) (h 3) (h 4)
      + headContribution (d.length 9) (h 5) (h 3)
  else if v = 4 then
    headContribution (d.length 4) (h 1) (h 4)
      + headContribution (d.length 5) (h 3) (h 4)
      + tailContribution (d.length 6) (h 4) (h 6)
  else if v = 5 then
    headContribution (d.length 3) (h 2) (h 5)
      + tailContribution (d.length 9) (h 5) (h 3)
      + tailContribution (d.length 11) (h 5) (h 7)
  else if v = 6 then
    headContribution (d.length 6) (h 4) (h 6)
      + tailContribution (d.length 7) (h 6) (h 7)
      + tailContribution (d.length 8) (h 6) (h 7)
  else
    headContribution (d.length 7) (h 6) (h 7)
      + headContribution (d.length 8) (h 6) (h 7)
      + headContribution (d.length 11) (h 5) (h 7)

theorem contrib_eq {d : DegSpec 8 12} (hCore : d.core = row10Core)
    {h : Fin 8 → ℕ} (hprof : Profile d (rowMark d) h)
    (hRep : ∀ v : Fin 8, h (d.rep v) = h v) (v : Fin 8) :
    positiveEndpointContribution d (heightPotential d h) (rowMark d)
        (markValue d (rowMark d) h) v = contribForm d h v := by
  rw [contribution_eq d hprof hRep]
  fin_cases v <;>
    simp +decide only [hCore, row10Core, Fin.isValue, Fin.zero_eta, slotTailForm, rowMark,
      slotHeadForm, Fin.sum_univ_succ, ↓reduceIte, lt_self_iff_false, Matrix.cons_val_zero,
      add_zero, Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, zero_add,
      Fin.reduceSucc, Finset.univ_unique, Fin.default_eq_zero, Matrix.cons_val_fin_one,
      Fin.reduceEq, Finset.sum_const_zero, contribForm, Matrix.cons_val, Fin.mk_one,
      Fin.reduceFinMk, Finset.sum_singleton]<;> ring

/-! ## The divisor -/

def chipWeight (v : Fin 8) : ℤ :=
  if v = 1 then 1 else if v = 2 then 1 else if v = 7 then 1 else 0

theorem chipWeight_nonneg (v : Fin 8) : 0 ≤ chipWeight v := by
  unfold chipWeight; split_ifs <;> norm_num

theorem sum_chipWeight : ∑ v : Fin 8, chipWeight v = 3 := by decide

/-- AR's divisor on chamber 2. -/
def rowDivisor (d : DegSpec 8 12) : CFDiv d.graph :=
  markedDivisorOne d chipWeight (rowMark d) 10

def base (d : DegSpec 8 12) : Fin 8 → ℤ :=
  baseOne d chipWeight (rowMark d) 10

theorem rowDivisor_effective (d : DegSpec 8 12) : effective (rowDivisor d) :=
  markedDivisorOne_effective d chipWeight (rowMark d) chipWeight_nonneg 10

theorem rowDivisor_degree (d : DegSpec 8 12) : deg (rowDivisor d) = 4 := by
  rw [rowDivisor, deg_markedDivisorOne, sum_chipWeight]
  norm_num

theorem base_eq {d : DegSpec 8 12} (hCore : d.core = row10Core) (v : Fin 8) :
    base d v = chipWeight v
      + (if markA d = 0 then (if v = 0 then (1 : ℤ) else 0)
          else if d.length 10 ≤ markA d then (if v = 3 then (1 : ℤ) else 0)
          else 0) := by
  unfold base baseOne markChipWeight
  rw [rowMark_ten, tail_ten hCore, head_ten hCore]

/-! ## Chip allocations -/

def allocFlat (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  base d v
    + (if d.length 10 = 0 then transferWeight 0 3 v else 0)
    + (if d.length 4 = 0 then transferWeight 1 4 v else 0)

def allocB (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  allocFlat d v + (if d.length 3 = 0 then transferWeight 2 5 v else 0)

def allocP (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  allocB d v
    + (if d.length 9 = 0 then transferWeight 3 5 v else 0)
    + (if d.length 11 = 0 ∧ htD d < htE d then transferWeight 5 7 v else 0)

def allocT (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  base d v
    + (if d.length 0 = 0 then transferWeight 2 0 v else 0)
    + (if d.length 2 = 0 then transferWeight 1 0 v else 0)

section ClassSums

variable {d : DegSpec 8 12} (hCore : d.core = row10Core)
include hCore

theorem rep_zero_ten (hz : d.length 10 = 0) : d.rep 0 = d.rep 3 := by
  have h := d.rep_zero 10 hz; rw [hCore] at h; simpa [row10Core] using h

theorem rep_zero_four (hz : d.length 4 = 0) : d.rep 1 = d.rep 4 := by
  have h := d.rep_zero 4 hz; rw [hCore] at h; simpa [row10Core] using h

theorem rep_zero_three (hz : d.length 3 = 0) : d.rep 2 = d.rep 5 := by
  have h := d.rep_zero 3 hz; rw [hCore] at h; simpa [row10Core] using h

theorem rep_zero_nine (hz : d.length 9 = 0) : d.rep 3 = d.rep 5 := by
  have h := d.rep_zero 9 hz; rw [hCore] at h; simpa [row10Core] using h.symm

theorem rep_zero_eleven (hz : d.length 11 = 0) : d.rep 5 = d.rep 7 := by
  have h := d.rep_zero 11 hz; rw [hCore] at h; simpa [row10Core] using h

theorem rep_zero_zero (hz : d.length 0 = 0) : d.rep 2 = d.rep 0 := by
  have h := d.rep_zero 0 hz; rw [hCore] at h; simpa [row10Core] using h.symm

theorem rep_zero_two (hz : d.length 2 = 0) : d.rep 1 = d.rep 0 := by
  have h := d.rep_zero 2 hz; rw [hCore] at h; simpa [row10Core] using h

theorem rep_zero_six (hz : d.length 6 = 0) : d.rep 4 = d.rep 6 := by
  have h := d.rep_zero 6 hz; rw [hCore] at h; simpa [row10Core] using h

theorem rep_zero_banana (hz : parq d = 0) : d.rep 7 = d.rep 6 := by
  rcases Nat.le_total (d.length 7) (d.length 8) with hle | hle
  · have h7 : d.length 7 = 0 := by simp only [parq] at hz; omega
    have h := d.rep_zero 7 h7; rw [hCore] at h; simpa [row10Core] using h.symm
  · have h8 : d.length 8 = 0 := by simp only [parq] at hz; omega
    have h := d.rep_zero 8 h8; rw [hCore] at h; simpa [row10Core] using h.symm

theorem allocFlat_classSum (r : Fin 8) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), allocFlat d v =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), base d v := by
  classical
  simp only [allocFlat, Finset.sum_add_distrib]
  rw [sum_conditional_transfer_eq_zero d _ 0 3 (rep_zero_ten hCore),
    sum_conditional_transfer_eq_zero d _ 1 4 (rep_zero_four hCore)]
  simp

theorem allocB_classSum (r : Fin 8) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), allocB d v =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), base d v := by
  classical
  simp only [allocB, Finset.sum_add_distrib]
  rw [sum_conditional_transfer_eq_zero d _ 2 5 (rep_zero_three hCore),
    allocFlat_classSum hCore r]
  simp

theorem allocP_classSum (r : Fin 8) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), allocP d v =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), base d v := by
  classical
  simp only [allocP, Finset.sum_add_distrib]
  rw [sum_conditional_transfer_eq_zero d _ 3 5 (rep_zero_nine hCore),
    sum_conditional_transfer_eq_zero d (d.length 11 = 0 ∧ htD d < htE d) 5 7
      (fun hp => rep_zero_eleven hCore hp.1),
    allocB_classSum hCore r]
  simp

theorem allocT_classSum (r : Fin 8) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), allocT d v =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), base d v := by
  classical
  simp only [allocT, Finset.sum_add_distrib]
  rw [sum_conditional_transfer_eq_zero d _ 2 0 (rep_zero_zero hCore),
    sum_conditional_transfer_eq_zero d _ 1 0 (rep_zero_two hCore)]
  simp

end ClassSums

/-! ## The flat profile: the apex `3` and the vertex `4` -/

def fCoeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then
    zeroChip (markA d) - zeroChip (d.length 10)
      + (if 0 < markA d then (0 : ℤ)
          else tailContribution (d.length 10) 0 (d.length 4))
  else if v = 1 then
    positiveChip (d.length 4) + tailContribution (d.length 4) 0 (d.length 4)
  else if v = 2 then
    1 + tailContribution (d.length 3) 0 (d.length 4)
  else if v = 3 then
    zeroChip (d.length 4) + headContribution (d.length 4) 0 (d.length 4)
  else if v = 4 then
    zeroChip (d.length 4) + headContribution (d.length 4) 0 (d.length 4)
  else if v = 5 then
    headContribution (d.length 3) 0 (d.length 4)
  else if v = 6 then 0
  else 1

theorem fCoeff_eq {d : DegSpec 8 12} (hCore : d.core = row10Core)
    (hb : d.length 4 ≤ d.length 10) (_hc : d.length 4 ≤ d.length 3) (v : Fin 8) :
    allocFlat d v + contribForm d (heightFlat d) v = fCoeff d v := by
  have hT10 := slotTailForm_of_flat_tail d (mark := rowMark d) (h := heightFlat d)
    (e := 10) (by rw [tail_ten hCore]; rfl)
  have hH10 := slotHeadForm_of_arm d (mark := rowMark d) (h := heightFlat d)
    (e := 10) (by rw [tail_ten hCore]; rfl)
    (by rw [rowMark_ten]; simp only [markA]; omega)
    (by rw [head_ten hCore, rowMark_ten]
        show heightFlat d 3 ≤ d.length 10 - markA d
        show d.length 4 ≤ d.length 10 - markA d
        simp only [markA]; omega)
  simp only [head_ten hCore, rowMark_ten] at hT10 hH10
  rw [armA_len hb] at hH10
  simp only [allocFlat]
  rw [base_eq hCore]
  fin_cases v
  all_goals simp [fCoeff, contribForm, heightFlat, chipWeight, zeroChip,
    positiveChip, transferWeight, indicatorWeight, markA, hT10, hH10]
  all_goals (try (first | ring1 | ring_nf))
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals (try omega)

theorem fCoeff_owner_three {d : DegSpec 8 12} : 1 ≤ fCoeff d 3 := by
  show (1 : ℤ) ≤
    zeroChip (d.length 4) + headContribution (d.length 4) 0 (d.length 4)
  have h := armFull_ge_one rev rev fwd (gamma := d.length 4) (lx := d.length 9)
    (ly := d.length 5) (hx := d.length 4) rfl
  simp only [fwd_tail, rev_tail, headContribution_same, tailContribution_same,
    add_zero] at h
  omega

theorem fCoeff_owner_four {d : DegSpec 8 12} : 1 ≤ fCoeff d 4 :=
  fCoeff_owner_three

theorem fCoeff_nonneg {d : DegSpec 8 12} (hb : d.length 4 ≤ d.length 10)
    (hc : d.length 4 ≤ d.length 3) (v : Fin 8) : 0 ≤ fCoeff d v := by
  fin_cases v
  · show (0 : ℤ) ≤ zeroChip (markA d) - zeroChip (d.length 10)
      + (if 0 < markA d then (0 : ℤ)
          else tailContribution (d.length 10) 0 (d.length 4))
    by_cases hp : 0 < markA d
    · rw [if_pos hp]
      have h1 : zeroChip (markA d) = 0 := by simp [zeroChip]; omega
      have h2 : zeroChip (d.length 10) = 0 := by
        have : d.length 10 ≠ 0 := by simp only [markA] at hp; omega
        simp [zeroChip, this]
      omega
    · rw [if_neg hp]
      have h1 : zeroChip (markA d) = 1 := by simp [zeroChip]; omega
      have h2 := positiveChip_add_tail_nonneg
        (L := d.length 10) (h := d.length 4) hb
      have h3 : positiveChip (d.length 10) = 1 - zeroChip (d.length 10) := by
        unfold positiveChip zeroChip; split_ifs <;> omega
      omega
  · show (0 : ℤ) ≤
      positiveChip (d.length 4) + tailContribution (d.length 4) 0 (d.length 4)
    exact positiveChip_add_tail_nonneg (by omega)
  · show (0 : ℤ) ≤ 1 + tailContribution (d.length 3) 0 (d.length 4)
    have := tailContribution_ge_neg_one (L := d.length 3) (hu := 0)
      (hv := d.length 4) (by omega) (by omega)
    omega
  · have := fCoeff_owner_three (d := d)
    have hv : fCoeff d ⟨3, by norm_num⟩ = fCoeff d 3 := rfl
    rw [hv]; omega
  · have := fCoeff_owner_four (d := d)
    have hv : fCoeff d ⟨4, by norm_num⟩ = fCoeff d 4 := rfl
    rw [hv]; omega
  · show (0 : ℤ) ≤ headContribution (d.length 3) 0 (d.length 4)
    exact headContribution_nonneg (Nat.zero_le _) (by omega)
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ (1 : ℤ)
    norm_num

/-! ## The target-`B` profile -/

def bCoeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then
    zeroChip (markA d) - zeroChip (d.length 10)
      + (if 0 < markA d then (0 : ℤ)
          else tailContribution (d.length 10) 0 (d.length 4))
  else if v = 1 then
    positiveChip (d.length 4) + tailContribution (d.length 4) 0 (d.length 4)
  else if v = 2 then
    positiveChip (d.length 3) + tailContribution (d.length 3) 0 (htB d)
  else if v = 3 then
    zeroChip (d.length 4)
      + (headContribution (d.length 4) 0 (d.length 4)
          + headContribution (d.length 9) (htB d) (d.length 4))
  else if v = 4 then
    zeroChip (d.length 4) + headContribution (d.length 4) 0 (d.length 4)
  else if v = 5 then
    zeroChip (d.length 3)
      + (headContribution (d.length 3) 0 (htB d)
          + tailContribution (d.length 9) (htB d) (d.length 4)
          + tailContribution (d.length 11) (htB d) (d.length 4))
  else if v = 6 then 0
  else 1 + headContribution (d.length 11) (htB d) (d.length 4)

theorem bCoeff_eq {d : DegSpec 8 12} (hCore : d.core = row10Core)
    (hb : d.length 4 ≤ d.length 10) (_hc : d.length 4 ≤ d.length 3) (v : Fin 8) :
    allocB d v + contribForm d (heightB d) v = bCoeff d v := by
  have hT10 := slotTailForm_of_flat_tail d (mark := rowMark d) (h := heightB d)
    (e := 10) (by rw [tail_ten hCore]; rfl)
  have hH10 := slotHeadForm_of_arm d (mark := rowMark d) (h := heightB d)
    (e := 10) (by rw [tail_ten hCore]; rfl)
    (by rw [rowMark_ten]; simp only [markA]; omega)
    (by rw [head_ten hCore, rowMark_ten]
        show heightB d 3 ≤ d.length 10 - markA d
        show d.length 4 ≤ d.length 10 - markA d
        simp only [markA]; omega)
  simp only [head_ten hCore, rowMark_ten] at hT10 hH10
  rw [armA_len hb] at hH10
  simp only [allocB, allocFlat]
  rw [base_eq hCore]
  fin_cases v
  all_goals simp [bCoeff, contribForm, heightB, chipWeight, zeroChip,
    positiveChip, transferWeight, indicatorWeight, markA, hT10, hH10]
  all_goals (try (first | ring1 | ring_nf))
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals (try omega)

theorem htB_le_three {d : DegSpec 8 12} : htB d ≤ d.length 3 := by
  simp only [htB, resB]; omega

theorem four_le_htB {d : DegSpec 8 12} (hc : d.length 4 ≤ d.length 3) :
    d.length 4 ≤ htB d := by
  simp only [htB, resB]; omega

theorem bCoeff_nonneg {d : DegSpec 8 12} (hb : d.length 4 ≤ d.length 10)
    (hc : d.length 4 ≤ d.length 3) (v : Fin 8) : 0 ≤ bCoeff d v := by
  have hlo := four_le_htB (d := d) hc
  have hhi := htB_le_three (d := d)
  fin_cases v
  · show (0 : ℤ) ≤ zeroChip (markA d) - zeroChip (d.length 10)
      + (if 0 < markA d then (0 : ℤ)
          else tailContribution (d.length 10) 0 (d.length 4))
    have := fCoeff_nonneg (d := d) hb hc 0
    have hv : fCoeff d 0 = zeroChip (markA d) - zeroChip (d.length 10)
      + (if 0 < markA d then (0 : ℤ)
          else tailContribution (d.length 10) 0 (d.length 4)) := rfl
    rw [hv] at this
    exact this
  · show (0 : ℤ) ≤
      positiveChip (d.length 4) + tailContribution (d.length 4) 0 (d.length 4)
    exact positiveChip_add_tail_nonneg (by omega)
  · show (0 : ℤ) ≤
      positiveChip (d.length 3) + tailContribution (d.length 3) 0 (htB d)
    exact positiveChip_add_tail_nonneg (by omega)
  · show (0 : ℤ) ≤ zeroChip (d.length 4)
      + (headContribution (d.length 4) 0 (d.length 4)
          + headContribution (d.length 9) (htB d) (d.length 4))
    have h := armFull_nonneg rev rev fwd (gamma := d.length 4) (lx := d.length 9)
      (ly := d.length 5) (hx := htB d) hlo (by simp only [htB, resB]; omega)
    simp only [fwd_tail, rev_tail, tailContribution_same, add_zero] at h
    omega
  · have := fCoeff_owner_four (d := d)
    have hv : bCoeff d ⟨4, by norm_num⟩ =
      zeroChip (d.length 4) + headContribution (d.length 4) 0 (d.length 4) := rfl
    rw [hv]
    have hf : fCoeff d 4 =
      zeroChip (d.length 4) + headContribution (d.length 4) 0 (d.length 4) := rfl
    rw [hf] at this
    omega
  · show (0 : ℤ) ≤ zeroChip (d.length 3)
      + (headContribution (d.length 3) 0 (htB d)
          + tailContribution (d.length 9) (htB d) (d.length 4)
          + tailContribution (d.length 11) (htB d) (d.length 4))
    have h := targetB_nonneg rev fwd fwd (beta := d.length 3)
      (gamma := d.length 4) (S := d.length 9) (u := d.length 11) (bt := htB d)
      hc (by simp only [htB, resB]; omega)
    simp only [fwd_tail, rev_tail] at h
    omega
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ 1 + headContribution (d.length 11) (htB d) (d.length 4)
    have := headContribution_ge_neg_one (L := d.length 11) (hu := htB d)
      (hv := d.length 4) (by omega) (by simp only [htB, resB]; omega)
    omega

/-- Which vertex of `B`'s class owns the chip delivered to `5`. -/
def ownerB (d : DegSpec 8 12) : Fin 8 :=
  if d.length 9 = 0 then 3 else if d.length 11 = 0 then 7 else 5

theorem bCoeff_owner {d : DegSpec 8 12} (hc : d.length 4 ≤ d.length 3) :
    1 ≤ bCoeff d (ownerB d) := by
  unfold ownerB
  by_cases h9 : d.length 9 = 0
  · rw [if_pos h9]
    show (1 : ℤ) ≤ zeroChip (d.length 4)
      + (headContribution (d.length 4) 0 (d.length 4)
          + headContribution (d.length 9) (htB d) (d.length 4))
    have hEq : htB d = d.length 4 := by simp only [htB, resB]; omega
    have h := armFull_ge_one rev rev fwd (gamma := d.length 4) (lx := d.length 9)
      (ly := d.length 5) (hx := htB d) hEq
    simp only [fwd_tail, rev_tail, tailContribution_same, add_zero] at h
    omega
  · rw [if_neg h9]
    by_cases h11 : d.length 11 = 0
    · rw [if_pos h11]
      show (1 : ℤ) ≤ 1 + headContribution (d.length 11) (htB d) (d.length 4)
      have hEq : htB d = d.length 4 := by simp only [htB, resB]; omega
      rw [hEq, h11, headContribution_same]
      norm_num
    · rw [if_neg h11]
      show (1 : ℤ) ≤ zeroChip (d.length 3)
        + (headContribution (d.length 3) 0 (htB d)
            + tailContribution (d.length 9) (htB d) (d.length 4)
            + tailContribution (d.length 11) (htB d) (d.length 4))
      have h := targetB_ge_one rev fwd fwd (beta := d.length 3)
        (gamma := d.length 4) (S := d.length 9) (u := d.length 11) (bt := htB d)
        hc (by simp only [htB, resB]; omega) (by omega) (by omega)
      simp only [fwd_tail, rev_tail] at h
      omega

theorem ownerB_rep {d : DegSpec 8 12} (hCore : d.core = row10Core) :
    d.rep (ownerB d) = d.rep 5 := by
  unfold ownerB
  by_cases h9 : d.length 9 = 0
  · rw [if_pos h9]; exact rep_zero_nine hCore h9
  · rw [if_neg h9]
    by_cases h11 : d.length 11 = 0
    · rw [if_pos h11]; exact (rep_zero_eleven hCore h11).symm
    · rw [if_neg h11]

/-! ## The target-`P` profile -/

def pCoeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then
    zeroChip (markA d) - zeroChip (d.length 10)
      + (if 0 < markA d then (0 : ℤ)
          else tailContribution (d.length 10) 0 (d.length 4))
  else if v = 1 then
    positiveChip (d.length 4) + tailContribution (d.length 4) 0 (d.length 4)
  else if v = 2 then
    positiveChip (d.length 3) + tailContribution (d.length 3) 0 (htC d)
  else if v = 3 then
    zeroChip (d.length 4) - zeroChip (d.length 9)
      + (headContribution (d.length 4) 0 (d.length 4)
          + headContribution (d.length 9) (htC d) (d.length 4))
  else if v = 4 then
    zeroChip (d.length 4)
      + (headContribution (d.length 4) 0 (d.length 4)
          + tailContribution (d.length 6) (d.length 4) (htE d))
  else if v = 5 then
    zeroChip (d.length 3) + zeroChip (d.length 9) - shift d
      + (headContribution (d.length 3) 0 (htC d)
          + tailContribution (d.length 9) (htC d) (d.length 4)
          + tailContribution (d.length 11) (htC d) (htD d))
  else if v = 6 then
    tailContribution (d.length 7) (htE d) (htD d)
      + tailContribution (d.length 8) (htE d) (htD d)
      + headContribution (d.length 6) (d.length 4) (htE d)
  else
    1 + shift d
      + (headContribution (d.length 11) (htC d) (htD d)
          + headContribution (d.length 7) (htE d) (htD d)
          + headContribution (d.length 8) (htE d) (htD d))

theorem pCoeff_eq {d : DegSpec 8 12} (hCore : d.core = row10Core)
    (hb : d.length 4 ≤ d.length 10) (_hc : d.length 4 ≤ d.length 3) (v : Fin 8) :
    allocP d v + contribForm d (heightP d) v = pCoeff d v := by
  have hT10 := slotTailForm_of_flat_tail d (mark := rowMark d) (h := heightP d)
    (e := 10) (by rw [tail_ten hCore]; rfl)
  have hH10 := slotHeadForm_of_arm d (mark := rowMark d) (h := heightP d)
    (e := 10) (by rw [tail_ten hCore]; rfl)
    (by rw [rowMark_ten]; simp only [markA]; omega)
    (by rw [head_ten hCore, rowMark_ten]
        show heightP d 3 ≤ d.length 10 - markA d
        show d.length 4 ≤ d.length 10 - markA d
        simp only [markA]; omega)
  simp only [head_ten hCore, rowMark_ten] at hT10 hH10
  rw [armA_len hb] at hH10
  simp only [allocP, allocB, allocFlat]
  rw [base_eq hCore]
  fin_cases v
  all_goals simp [pCoeff, contribForm, heightP, chipWeight, zeroChip, shift,
    positiveChip, transferWeight, indicatorWeight, markA, hT10, hH10]
  all_goals (try (first | ring1 | ring_nf))
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals (try omega)

/-- The nested minima of the target-`P` profile, in the shape
`ConfigurationEleven` consumes. -/
theorem pChain (d : DegSpec 8 12) :
    resB d = min (d.length 3) (d.length 4 + d.length 9) ∧
      parq d = min (d.length 7) (d.length 8) ∧
      capG d = d.length 4 + d.length 6 ∧
      htE d = min (capG d) (resB d + d.length 11 + parq d) ∧
      htD d = min (htE d) (resB d + d.length 11) ∧
      htC d = min (htD d) (resB d) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem pCoeff_nonneg {d : DegSpec 8 12} (hb : d.length 4 ≤ d.length 10)
    (hc : d.length 4 ≤ d.length 3) (v : Fin 8) : 0 ≤ pCoeff d v := by
  obtain ⟨hm, hpq, hG, hE, hD, hC⟩ := pChain d
  have hbnd := chain_bounds (beta := d.length 3) (gamma := d.length 4)
    (S := d.length 9) (u := d.length 11) (w := d.length 6) (m1 := d.length 7)
    (m2 := d.length 8) (pq := parq d) (mB := resB d) (G := capG d) (E := htE d)
    (D := htD d) (C := htC d) hc hm hpq hG hE hD hC
  obtain ⟨hgC, hCD, hDE, hEG, hCb, hCS, hDCu, hEm1, hEm2⟩ := hbnd
  fin_cases v
  · show (0 : ℤ) ≤ zeroChip (markA d) - zeroChip (d.length 10)
      + (if 0 < markA d then (0 : ℤ)
          else tailContribution (d.length 10) 0 (d.length 4))
    have := fCoeff_nonneg (d := d) hb hc 0
    have hv : fCoeff d 0 = zeroChip (markA d) - zeroChip (d.length 10)
      + (if 0 < markA d then (0 : ℤ)
          else tailContribution (d.length 10) 0 (d.length 4)) := rfl
    rw [hv] at this
    exact this
  · show (0 : ℤ) ≤
      positiveChip (d.length 4) + tailContribution (d.length 4) 0 (d.length 4)
    exact positiveChip_add_tail_nonneg (by omega)
  · show (0 : ℤ) ≤
      positiveChip (d.length 3) + tailContribution (d.length 3) 0 (htC d)
    exact positiveChip_add_tail_nonneg (by omega)
  · show (0 : ℤ) ≤ zeroChip (d.length 4) - zeroChip (d.length 9)
      + (headContribution (d.length 4) 0 (d.length 4)
          + headContribution (d.length 9) (htC d) (d.length 4))
    have h := apex_nonneg rev rev fwd (gamma := d.length 4) (lx := d.length 9)
      (ly := d.length 5) (hx := htC d) hgC (by omega)
      (by intro h9; simp only [htC, htD, htE, resB, capG, parq] at *; omega)
    simp only [fwd_tail, rev_tail, tailContribution_same, add_zero] at h
    omega
  · show (0 : ℤ) ≤ zeroChip (d.length 4)
      + (headContribution (d.length 4) 0 (d.length 4)
          + tailContribution (d.length 6) (d.length 4) (htE d))
    have h := armFull_nonneg rev fwd rev (gamma := d.length 4) (lx := d.length 6)
      (ly := d.length 5) (hx := htE d)
      (by simp only [htE, capG, resB, parq] at *; omega) (by omega)
    simp only [fwd_tail, rev_tail, headContribution_same, add_zero] at h
    omega
  · show (0 : ℤ) ≤ zeroChip (d.length 3) + zeroChip (d.length 9) - shift d
      + (headContribution (d.length 3) 0 (htC d)
          + tailContribution (d.length 9) (htC d) (d.length 4)
          + tailContribution (d.length 11) (htC d) (htD d))
    have h := armCenter_nonneg rev fwd fwd (shift d)
      (beta := d.length 3) (gamma := d.length 4) (S := d.length 9)
      (u := d.length 11) (w := d.length 6) (m1 := d.length 7) (m2 := d.length 8)
      (pq := parq d) (mB := resB d) (G := capG d) (E := htE d) (D := htD d)
      (C := htC d) hc hm hpq hG hE hD hC rfl
    simp only [fwd_tail, rev_tail] at h
    omega
  · show (0 : ℤ) ≤ tailContribution (d.length 7) (htE d) (htD d)
      + tailContribution (d.length 8) (htE d) (htD d)
      + headContribution (d.length 6) (d.length 4) (htE d)
    have h := center_nonneg fwd fwd rev
      (beta := d.length 3) (gamma := d.length 4) (S := d.length 9)
      (u := d.length 11) (w := d.length 6) (m1 := d.length 7) (m2 := d.length 8)
      (pq := parq d) (mB := resB d) (G := capG d) (E := htE d) (D := htD d)
      (C := htC d) hc hm hpq hG hE hD hC
    simp only [fwd_tail, rev_tail] at h
    omega
  · show (0 : ℤ) ≤ 1 + shift d
      + (headContribution (d.length 11) (htC d) (htD d)
          + headContribution (d.length 7) (htE d) (htD d)
          + headContribution (d.length 8) (htE d) (htD d))
    have h := bananaChip_nonneg rev rev rev (shift d)
      (beta := d.length 3) (gamma := d.length 4) (S := d.length 9)
      (u := d.length 11) (w := d.length 6) (m1 := d.length 7) (m2 := d.length 8)
      (pq := parq d) (mB := resB d) (G := capG d) (E := htE d) (D := htD d)
      (C := htC d) hc hm hpq hG hE hD hC rfl
    simp only [rev_tail] at h
    omega

/-- Which vertex of `P`'s class owns the chip delivered to `6`. -/
def ownerP (d : DegSpec 8 12) : Fin 8 :=
  if d.length 6 = 0 then 4
  else if parq d = 0 ∧ resB d + d.length 11 < capG d then 7 else 6

theorem pCoeff_owner {d : DegSpec 8 12} (_hb : d.length 4 ≤ d.length 10)
    (hc : d.length 4 ≤ d.length 3) : 1 ≤ pCoeff d (ownerP d) := by
  obtain ⟨hm, hpq, hG, hE, hD, hC⟩ := pChain d
  unfold ownerP
  by_cases h6 : d.length 6 = 0
  · rw [if_pos h6]
    show (1 : ℤ) ≤ zeroChip (d.length 4)
      + (headContribution (d.length 4) 0 (d.length 4)
          + tailContribution (d.length 6) (d.length 4) (htE d))
    have hEq : htE d = d.length 4 := by
      simp only [htE, capG, resB, parq]; omega
    have h := armFull_ge_one rev fwd rev (gamma := d.length 4) (lx := d.length 6)
      (ly := d.length 5) (hx := htE d) hEq
    simp only [fwd_tail, rev_tail, headContribution_same, add_zero] at h
    omega
  · rw [if_neg h6]
    by_cases hq : parq d = 0 ∧ resB d + d.length 11 < capG d
    · rw [if_pos hq]
      show (1 : ℤ) ≤ 1 + shift d
        + (headContribution (d.length 11) (htC d) (htD d)
            + headContribution (d.length 7) (htE d) (htD d)
            + headContribution (d.length 8) (htE d) (htD d))
      have h := bananaChip_ge_one rev rev rev (shift d)
        (beta := d.length 3) (gamma := d.length 4) (S := d.length 9)
        (u := d.length 11) (w := d.length 6) (m1 := d.length 7) (m2 := d.length 8)
        (pq := parq d) (mB := resB d) (G := capG d) (E := htE d) (D := htD d)
        (C := htC d) hc hm hpq hG hE hD hC rfl hq.1
      simp only [rev_tail] at h
      omega
    · rw [if_neg hq]
      show (1 : ℤ) ≤ tailContribution (d.length 7) (htE d) (htD d)
        + tailContribution (d.length 8) (htE d) (htD d)
        + headContribution (d.length 6) (d.length 4) (htE d)
      have h := center_ge_one fwd fwd rev
        (beta := d.length 3) (gamma := d.length 4) (S := d.length 9)
        (u := d.length 11) (w := d.length 6) (m1 := d.length 7) (m2 := d.length 8)
        (pq := parq d) (mB := resB d) (G := capG d) (E := htE d) (D := htD d)
        (C := htC d) hc hm hpq hG hE hD hC (by omega) hq
      simp only [fwd_tail, rev_tail] at h
      omega

theorem ownerP_rep {d : DegSpec 8 12} (hCore : d.core = row10Core) :
    d.rep (ownerP d) = d.rep 6 := by
  unfold ownerP
  by_cases h6 : d.length 6 = 0
  · rw [if_pos h6]; exact rep_zero_six hCore h6
  · rw [if_neg h6]
    by_cases hq : parq d = 0 ∧ resB d + d.length 11 < capG d
    · rw [if_pos hq]; exact rep_zero_banana hCore hq.1
    · rw [if_neg hq]

/-! ## The tripod at `0` -/

def tCoeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then
    zeroChip (d.length 0) + zeroChip (d.length 2) + zeroChip (markA d)
      + (tailContribution (d.length 0) (tripod d) 0
          + headContribution (d.length 2) 0 (tripod d)
          + tailContribution (markA d) (tripod d) 0)
  else if v = 1 then
    positiveChip (d.length 2) + tailContribution (d.length 2) 0 (tripod d)
  else if v = 2 then
    positiveChip (d.length 0) + headContribution (d.length 0) (tripod d) 0
  else if v = 3 then
    (if markA d = 0 then (0 : ℤ) else if d.length 10 ≤ markA d then 1 else 0)
      + (if markA d < d.length 10 then (0 : ℤ)
          else headContribution (d.length 10) (tripod d) 0)
  else if v = 4 then 0
  else if v = 5 then 0
  else if v = 6 then 0
  else 1

theorem tCoeff_eq {d : DegSpec 8 12} (hCore : d.core = row10Core)
    (hb : d.length 4 ≤ d.length 10) (_hc : d.length 4 ≤ d.length 3) (v : Fin 8) :
    allocT d v + contribForm d (heightT d) v = tCoeff d v := by
  have hlow : rowMark d 10 = 0 → heightT d (d.core.tail 10) = 0 := by
    intro hz
    rw [rowMark_ten] at hz
    rw [tail_ten hCore]
    show tripod d = 0
    simp only [tripod]; omega
  have hT10 := slotTailForm_of_arm d (mark := rowMark d) (h := heightT d) (e := 10)
    (by rw [head_ten hCore]; rfl) hlow
  have hH10 := slotHeadForm_of_flat_head d (mark := rowMark d) (h := heightT d)
    (e := 10) (by rw [head_ten hCore]; rfl) hlow
  simp only [tail_ten hCore, rowMark_ten] at hT10 hH10
  simp only [allocT]
  rw [base_eq hCore]
  fin_cases v
  all_goals simp [tCoeff, contribForm, heightT, chipWeight, zeroChip,
    positiveChip, transferWeight, indicatorWeight, markA, hT10, hH10]
  all_goals (try (first | ring1 | ring_nf))
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals (try split_ifs)
  all_goals (try omega)

theorem tCoeff_owner {d : DegSpec 8 12} : 1 ≤ tCoeff d 0 := by
  show (1 : ℤ) ≤
    zeroChip (d.length 0) + zeroChip (d.length 2) + zeroChip (markA d)
      + (tailContribution (d.length 0) (tripod d) 0
          + headContribution (d.length 2) 0 (tripod d)
          + tailContribution (markA d) (tripod d) 0)
  have h := centre_ge_one fwd rev fwd
    (la := d.length 0) (lb := d.length 2) (lc := markA d) (o := tripod d) rfl
  simp only [fwd_tail, rev_tail] at h
  omega

theorem tCoeff_nonneg {d : DegSpec 8 12} (hb : d.length 4 ≤ d.length 10)
    (v : Fin 8) : 0 ≤ tCoeff d v := by
  have hO1 : tripod d ≤ d.length 0 := le_first rfl
  have hO2 : tripod d ≤ d.length 2 := le_second rfl
  have hO3 : tripod d ≤ markA d := le_third rfl
  have hMA : markA d ≤ d.length 10 := by simp only [markA]; omega
  fin_cases v
  · have := tCoeff_owner (d := d)
    have hv : tCoeff d ⟨0, by norm_num⟩ = tCoeff d 0 := rfl
    rw [hv]; omega
  · show (0 : ℤ) ≤
      positiveChip (d.length 2) + tailContribution (d.length 2) 0 (tripod d)
    exact positiveChip_add_tail_nonneg (by omega)
  · show (0 : ℤ) ≤
      positiveChip (d.length 0) + headContribution (d.length 0) (tripod d) 0
    exact positiveChip_add_head_nonneg (by omega)
  · show (0 : ℤ) ≤
      (if markA d = 0 then (0 : ℤ) else if d.length 10 ≤ markA d then 1 else 0)
        + (if markA d < d.length 10 then (0 : ℤ)
            else headContribution (d.length 10) (tripod d) 0)
    by_cases hlt : markA d < d.length 10
    · rw [if_pos hlt]
      split_ifs <;> omega
    · rw [if_neg hlt]
      have hpos := positiveChip_add_head_nonneg (L := d.length 10)
        (h := tripod d) (by omega)
      by_cases hz : markA d = 0
      · rw [if_pos hz]
        have h10 : d.length 10 = 0 := by omega
        have hgz : tripod d = 0 := by omega
        rw [h10, hgz]
        simp [headContribution]
      · rw [if_neg hz, if_pos (by omega : d.length 10 ≤ markA d)]
        have hne : d.length 10 ≠ 0 := by omega
        have : positiveChip (d.length 10) = 1 := by simp [positiveChip, hne]
        omega
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ (1 : ℤ)
    norm_num

/-! ## Every contracted core class is reached -/

theorem rowDivisor_reaches_coreVertex {d : DegSpec 8 12}
    (hCore : d.core = row10Core)
    (hb : d.length 4 ≤ d.length 10) (hc : d.length 4 ≤ d.length 3)
    (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8, d.rep x = d.rep y ↔ ReachIn row10Core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0) (center : Fin 8) :
    Reaches d.graph (rowDivisor d) (d.coreVertex center) := by
  have hCoreValue : ∀ r : Fin 8, rowDivisor d (d.coreVertex r) =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r), base d v :=
    markedDivisorOne_coreVertex d chipWeight (rowMark d) 10
  have hInterior := markedDivisorOne_interior d chipWeight (rowMark d)
    chipWeight_nonneg 10
  have hChip := markedDivisorOne_chip d chipWeight (rowMark d)
    (fun g hg => marked_of_rowMark_pos d hg)
  have hpFlat := profileFlat hCore hb hc
  have hpB := profileB hCore hb hc
  have hpP := profileP hCore hb hc
  have hpT := profileT hCore hb hc
  have hrFlat := height_rep_eq d hCore hpFlat.const F hRepReach hFZero
  have hrB := height_rep_eq d hCore hpB.const F hRepReach hFZero
  have hrP := height_rep_eq d hCore hpP.const F hRepReach hFZero
  have hrT := height_rep_eq d hCore hpT.const F hRepReach hFZero
  have hAFlat := allocFlat_classSum hCore
  have hAB := allocB_classSum hCore
  have hAP := allocP_classSum hCore
  have hAT := allocT_classSum hCore
  fin_cases center
  · exact (DharMove.ofScript _ (residual_effective d hpT hrT hCoreValue
      hInterior hChip hAT (rfl : d.rep 0 = d.rep 0) (fun v => by
        rw [contrib_eq hCore hpT hrT v]
        exact residual_of_coeff
          (fun w => by rw [tCoeff_eq hCore hb hc w]; exact tCoeff_nonneg hb w)
          (by rw [tCoeff_eq hCore hb hc 0]; exact tCoeff_owner) v))).reaches
  · exact reaches_of_effective_representative
      (linear_equiv.refl d.graph (rowDivisor d)) (rowDivisor_effective d)
      (one_le_markedDivisorOne_at_chip d chipWeight (rowMark d) 10
        chipWeight_nonneg (c := 1) (by norm_num [chipWeight]))
  · exact reaches_of_effective_representative
      (linear_equiv.refl d.graph (rowDivisor d)) (rowDivisor_effective d)
      (one_le_markedDivisorOne_at_chip d chipWeight (rowMark d) 10
        chipWeight_nonneg (c := 2) (by norm_num [chipWeight]))
  · exact (DharMove.ofScript _ (residual_effective d hpFlat hrFlat hCoreValue
      hInterior hChip hAFlat (rfl : d.rep 3 = d.rep 3) (fun v => by
        rw [contrib_eq hCore hpFlat hrFlat v]
        exact residual_of_coeff
          (fun w => by rw [fCoeff_eq hCore hb hc w]; exact fCoeff_nonneg hb hc w)
          (by rw [fCoeff_eq hCore hb hc 3]; exact fCoeff_owner_three) v))).reaches
  · exact (DharMove.ofScript _ (residual_effective d hpFlat hrFlat hCoreValue
      hInterior hChip hAFlat (rfl : d.rep 4 = d.rep 4) (fun v => by
        rw [contrib_eq hCore hpFlat hrFlat v]
        exact residual_of_coeff
          (fun w => by rw [fCoeff_eq hCore hb hc w]; exact fCoeff_nonneg hb hc w)
          (by rw [fCoeff_eq hCore hb hc 4]; exact fCoeff_owner_four) v))).reaches
  · exact (DharMove.ofScript _ (residual_effective d hpB hrB hCoreValue
      hInterior hChip hAB (ownerB_rep hCore) (fun v => by
        rw [contrib_eq hCore hpB hrB v]
        exact residual_of_coeff
          (fun w => by rw [bCoeff_eq hCore hb hc w]; exact bCoeff_nonneg hb hc w)
          (by rw [bCoeff_eq hCore hb hc (ownerB d)]
              exact bCoeff_owner hc) v))).reaches
  · exact (DharMove.ofScript _ (residual_effective d hpP hrP hCoreValue
      hInterior hChip hAP (ownerP_rep hCore) (fun v => by
        rw [contrib_eq hCore hpP hrP v]
        exact residual_of_coeff
          (fun w => by rw [pCoeff_eq hCore hb hc w]; exact pCoeff_nonneg hb hc w)
          (by rw [pCoeff_eq hCore hb hc (ownerP d)]
              exact pCoeff_owner hb hc) v))).reaches
  · exact reaches_of_effective_representative
      (linear_equiv.refl d.graph (rowDivisor d)) (rowDivisor_effective d)
      (one_le_markedDivisorOne_at_chip d chipWeight (rowMark d) 10
        chipWeight_nonneg (c := 7) (by norm_num [chipWeight]))

/-- **AR's ninth family, second scope.** -/
theorem chamberTwo_pencil (length : Fin 12 → ℕ)
    (forest : IsForest row10Core (zeroSlots length))
    (notLoopy : ¬ IsLoopy row10Core (zeroSlots length))
    (hP : GenusFiveRow10Symmetry.ChamberTwo length) :
    Nonempty (DegreeFourDharPencil
      (faceSpec row10Core (by norm_num) length forest notLoopy).graph) := by
  let d := faceSpec row10Core (by norm_num) length forest notLoopy
  have hCore : d.core = row10Core := rfl
  have hRepReach : ∀ x y : Fin 8,
      d.rep x = d.rep y ↔ ReachIn row10Core (zeroSlots length) x y := fun x y =>
    compFold_iff row10Core (zeroSlots length) x y
  have hFZero : ∀ e : Fin 12, e ∈ zeroSlots length ↔ d.length e = 0 := by
    intro e
    simp [d, faceSpec, zeroSlots]
  refine ⟨DegreeFourDharPencil.ofEffectiveRankOne (rowDivisor d)
    (rowDivisor_effective d) (rowDivisor_degree d) ?_⟩
  apply d.rank_ge_one_of_reaches_coreVertices (by rw [hCore]; exact row10_connected)
  intro center
  exact rowDivisor_reaches_coreVertex hCore hP.1 hP.2 (zeroSlots length)
    hRepReach hFZero center

end AtanasovRanganathan.GenusFiveRow10ChamberTwo
