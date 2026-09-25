/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationCommon
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SplitRampScript

/-!
# The endpoint layer for a marked script

`ConfigurationCommon` reads the Laplacian at a contracted core class as a sum,
over the slots of the uncontracted core, of one `endpointPair`.  This file is
the same reading for `DegSpec.splitScript`, the script that may bend downward at
one marked offset per slot (`SplitRampScript.lean`).

Two facts make the marked layer cheap.

* **An unmarked slot is not new.**  Setting `mark e = 0` and
  `markValue e = potential (rep (tail e))` makes the marked endpoint pair
  *equal* to `ConfigurationCommon.endpointPair` (`endpointPair_of_unmarked`).
  A row therefore marks only the one or two slots carrying an interior chip and
  keeps the existing single-ramp ledger -- and the existing configuration
  files' arithmetic -- everywhere else.
* **A marked slot splits into two ordinary arms.**  Its tail endpoint sees the
  canonical ramp of rise `markRiseIn` over `mark e` steps, and its head
  endpoint the canonical ramp of rise `markRiseOut` over `length e - mark e`
  steps (`endpointPair_marked_tail`, `endpointPair_marked_head`).  So the
  one-edge ledger of `ConfigurationFive` -- stated on bare naturals,
  independent of any core -- applies to each half unchanged.

Both AR rows that need this (`05`, the sixth family, and `08`, the seventh)
place their interior chips so that one of the two rises is always zero, which
is also the hypothesis under which the chip pays for the kink; see
`Utilities/Subdivision/SplitRampArithmetic.lean`.
-/

@[expose] public section

namespace AtanasovRanganathan.ConfigurationMarkedCommon

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.DegenerateSpec
open Certificate.DegenerateSpec.DegSpec

variable (d : DegSpec 8 12)

/-- The two endpoint terms one original core slot contributes to one contracted
core class, for a marked script.  As in `ConfigurationCommon.endpointPair`,
keeping them paired is what makes a collapsed slot cancel. -/
def endpointPair (potential : Fin 8 → ℤ) (mark : Fin 12 → ℕ)
    (markValue : Fin 12 → ℤ) (e : Fin 12) (r : Fin 8) : ℤ :=
  (if d.rep (d.core.tail e) = d.rep r then
      SubdivisionArithmetic.splitStep (d.length e) (mark e)
        (d.markRiseIn potential markValue e)
        (d.markRiseOut potential markValue e) 0
    else 0) +
  (if d.rep (d.core.head e) = d.rep r then
      -SubdivisionArithmetic.splitStep (d.length e) (mark e)
        (d.markRiseIn potential markValue e)
        (d.markRiseOut potential markValue e) (d.length e - 1)
    else 0)

/-- The core-class Laplacian of a marked script is the sum of its endpoint
pairs.  This is `prin_splitScript_coreVertex_eq_endpointSum` with the summand
named. -/
theorem prin_eq_sum_endpointPair {potential : Fin 8 → ℤ} {mark : Fin 12 → ℕ}
    {markValue : Fin 12 → ℤ}
    (hMarks : d.MarksAdmissible potential mark markValue) (r : Fin 8) :
    prin d.graph (d.splitScript potential mark markValue) (d.coreVertex r) =
      ∑ e : Fin 12, endpointPair d potential mark markValue e r :=
  d.prin_splitScript_coreVertex_eq_endpointSum hMarks r

/-! ## Unmarked slots -/

/-- On an unmarked slot the outgoing rise is the ordinary core rise. -/
theorem markRiseOut_eq_coreRise {potential : Fin 8 → ℤ}
    (hInv : d.RepInvariant potential) {markValue : Fin 12 → ℤ} {e : Fin 12}
    (hValue : markValue e = potential (d.rep (d.core.tail e))) :
    d.markRiseOut potential markValue e = d.coreRise potential e := by
  simp only [DegSpec.markRiseOut, DegSpec.coreRise, hValue]
  rw [hInv (d.core.head e), hInv (d.core.tail e)]

/-- **An unmarked slot is not new.**  Its marked endpoint pair is literally the
single-ramp one. -/
theorem endpointPair_of_unmarked {potential : Fin 8 → ℤ}
    (hInv : d.RepInvariant potential) {mark : Fin 12 → ℕ}
    {markValue : Fin 12 → ℤ} {e : Fin 12} (hMark : mark e = 0)
    (hValue : markValue e = potential (d.rep (d.core.tail e))) (r : Fin 8) :
    endpointPair d potential mark markValue e r =
      ConfigurationCommon.endpointPair d potential e r := by
  unfold endpointPair ConfigurationCommon.endpointPair
  rw [hMark, SubdivisionArithmetic.splitStep_mark_zero,
    SubdivisionArithmetic.splitStep_mark_zero,
    markRiseOut_eq_coreRise d hInv hValue]

/-! ## Marked slots

A marked slot is read as two ordinary arms.  The hypotheses below are the ones
a configuration supplies anyway: the mark lies strictly inside its slot exactly
when neither half has collapsed. -/

/-- At the tail of a marked slot the script is the canonical ramp of rise
`markRiseIn` over `mark e` steps. -/
theorem splitStep_tail_of_pos {potential : Fin 8 → ℤ} {mark : Fin 12 → ℕ}
    {markValue : Fin 12 → ℤ}
    (hMarks : d.MarksAdmissible potential mark markValue) {e : Fin 12}
    (hPos : 0 < mark e) :
    SubdivisionArithmetic.splitStep (d.length e) (mark e)
        (d.markRiseIn potential markValue e)
        (d.markRiseOut potential markValue e) 0 =
      SubdivisionArithmetic.step (mark e)
        (d.markRiseIn potential markValue e) 0 := by
  rw [SubdivisionArithmetic.splitStep_first (hMarks e), if_pos hPos]

/-- At the head of a marked slot the script is the canonical ramp of rise
`markRiseOut` over `length e - mark e` steps. -/
theorem splitStep_head_of_lt {potential : Fin 8 → ℤ} {mark : Fin 12 → ℕ}
    {markValue : Fin 12 → ℤ}
    (hMarks : d.MarksAdmissible potential mark markValue) {e : Fin 12}
    (hPos : 0 < d.length e) (hLt : mark e < d.length e) :
    SubdivisionArithmetic.splitStep (d.length e) (mark e)
        (d.markRiseIn potential markValue e)
        (d.markRiseOut potential markValue e) (d.length e - 1) =
      SubdivisionArithmetic.step (d.length e - mark e)
        (d.markRiseOut potential markValue e)
        (d.length e - 1 - mark e) := by
  rw [SubdivisionArithmetic.splitStep_last (hMarks e) hPos, if_pos hLt]

/-- A marked slot whose *incoming* ramp is flat contributes nothing at its
tail.  This is the shape both AR rows use at the far end of a marked leg. -/
theorem splitStep_tail_eq_zero_of_flat {potential : Fin 8 → ℤ}
    {mark : Fin 12 → ℕ} {markValue : Fin 12 → ℤ}
    (hMarks : d.MarksAdmissible potential mark markValue) {e : Fin 12}
    (hFlat : d.markRiseIn potential markValue e = 0) :
    SubdivisionArithmetic.splitStep (d.length e) (mark e)
        (d.markRiseIn potential markValue e)
        (d.markRiseOut potential markValue e) 0 =
      if 0 < mark e then 0
      else SubdivisionArithmetic.step (d.length e)
        (d.markRiseOut potential markValue e) 0 := by
  rw [SubdivisionArithmetic.splitStep_first (hMarks e)]
  by_cases hPos : 0 < mark e
  · rw [if_pos hPos, if_pos hPos, hFlat]
    exact SubdivisionArithmetic.step_zero_of_lt hPos
  · rw [if_neg hPos, if_neg hPos]

/-- A marked slot whose *outgoing* ramp is flat contributes nothing at its
head. -/
theorem splitStep_head_eq_zero_of_flat {potential : Fin 8 → ℤ}
    {mark : Fin 12 → ℕ} {markValue : Fin 12 → ℤ}
    (hMarks : d.MarksAdmissible potential mark markValue) {e : Fin 12}
    (hPos : 0 < d.length e) (hLt : mark e < d.length e)
    (hFlat : d.markRiseOut potential markValue e = 0) :
    SubdivisionArithmetic.splitStep (d.length e) (mark e)
        (d.markRiseIn potential markValue e)
        (d.markRiseOut potential markValue e) (d.length e - 1) = 0 := by
  rw [splitStep_head_of_lt d hMarks hPos hLt, hFlat]
  exact SubdivisionArithmetic.step_zero_of_lt (by omega)

/-! ## Where a marked slot contributes nothing

A marked slot whose chip lies strictly inside it touches only *one* contracted
class: the one carrying the height.  The chip's own cost is paid at the marked
interior vertex, by `prin_splitScript_interiorVertex_ge_neg_one`, not at any
core class.  These three lemmas are what makes a row's class bookkeeping short.

The hypothesis `mark e < d.length e` (resp. `0 < mark e`) is not cosmetic: when
the mark reaches an end of its slot the chip *is* that core vertex, the split
ramp degenerates to a single ramp, and the slot behaves like an ordinary arm
with its chip at a core class.  A row must case-split there; see the module
docstring of `ConfigurationSeven`. -/

/-- Both ramps flat: the slot moves nothing anywhere. -/
theorem splitStep_eq_zero_of_flat {potential : Fin 8 → ℤ} {mark : Fin 12 → ℕ}
    {markValue : Fin 12 → ℤ}
    (hMarks : d.MarksAdmissible potential mark markValue) {e : Fin 12}
    (hIn : d.markRiseIn potential markValue e = 0)
    (hOut : d.markRiseOut potential markValue e = 0) {k : ℕ}
    (hk : k < d.length e) :
    SubdivisionArithmetic.splitStep (d.length e) (mark e)
      (d.markRiseIn potential markValue e)
      (d.markRiseOut potential markValue e) k = 0 := by
  rcases Nat.lt_or_ge k (mark e) with hlt | hge
  · rw [SubdivisionArithmetic.splitStep_left (hMarks e) (by omega), hIn]
    exact SubdivisionArithmetic.step_zero_of_lt hlt
  · rw [SubdivisionArithmetic.splitStep_right hge, hOut]
    exact SubdivisionArithmetic.step_zero_of_lt (by
      have := (hMarks e).le
      omega)

theorem endpointPair_eq_zero_of_flat {potential : Fin 8 → ℤ} {mark : Fin 12 → ℕ}
    {markValue : Fin 12 → ℤ}
    (hMarks : d.MarksAdmissible potential mark markValue) {e : Fin 12}
    (hIn : d.markRiseIn potential markValue e = 0)
    (hOut : d.markRiseOut potential markValue e = 0) (r : Fin 8) :
    endpointPair d potential mark markValue e r = 0 := by
  rcases Nat.eq_zero_or_pos (d.length e) with hZero | hPos
  · have hRep := d.rep_zero e hZero
    unfold endpointPair
    rw [hRep, hZero]
    by_cases hr : d.rep (d.core.head e) = d.rep r <;> simp [hr]
  · unfold endpointPair
    rw [splitStep_eq_zero_of_flat d hMarks hIn hOut hPos,
      splitStep_eq_zero_of_flat d hMarks hIn hOut (by omega)]
    simp

/-- A marked slot read from its **tail**: nothing reaches any class other than
the tail's. -/
theorem endpointPair_eq_zero_of_ne_tail {potential : Fin 8 → ℤ}
    {mark : Fin 12 → ℕ} {markValue : Fin 12 → ℤ}
    (hMarks : d.MarksAdmissible potential mark markValue) {e : Fin 12}
    (hOut : d.markRiseOut potential markValue e = 0)
    (hPos : 0 < d.length e) (hLt : mark e < d.length e) {r : Fin 8}
    (hNe : d.rep (d.core.tail e) ≠ d.rep r) :
    endpointPair d potential mark markValue e r = 0 := by
  unfold endpointPair
  rw [if_neg hNe, splitStep_head_eq_zero_of_flat d hMarks hPos hLt hOut]
  simp

/-- A marked slot read from its **head**: nothing reaches any class other than
the head's. -/
theorem endpointPair_eq_zero_of_ne_head {potential : Fin 8 → ℤ}
    {mark : Fin 12 → ℕ} {markValue : Fin 12 → ℤ}
    (hMarks : d.MarksAdmissible potential mark markValue) {e : Fin 12}
    (hIn : d.markRiseIn potential markValue e = 0) (hPos : 0 < mark e)
    {r : Fin 8} (hNe : d.rep (d.core.head e) = d.rep r → False) :
    endpointPair d potential mark markValue e r = 0 := by
  unfold endpointPair
  rw [if_neg hNe, splitStep_tail_eq_zero_of_flat d hMarks hIn, if_pos hPos]
  simp

end AtanasovRanganathan.ConfigurationMarkedCommon
