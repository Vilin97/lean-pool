/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationMarkedCommon
import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationThree

/-!
# Atanasov--Ranganathan configuration 7, generic in the core

This is the *seventh* local picture of Atanasov--Ranganathan, Proposition 5.1
(`fig:configurations-for-genus-5`, the scope commented `%Seventh`):

```
      a          b        a, b carry chips
      |          |        u, v are chip free and joined by a banana
      u == v              |u a| = |v b|   (the figure labels both `a`)
```

Two chip-free core vertices joined by two parallel slots, each carrying one
further slot -- an *arm* -- to a chip vertex, and the two arms have **equal
length**.  Interpolate the same negative height `min |u a| |v b|` on both
centres.  The banana then has zero rise and moves nothing, each arm consumes at
most its own chip, and a *shortest* arm delivers a chip to its centre.  With
the two arms equal, one script therefore reaches both centres.

**Why the rows need it, and why the arms are marked.**  AR's sixth and seventh
genus-five families (atlas rows `05` and `08`) each contain two of these
pictures, and in each of them *one of the two arms is half of a slot*: the chip
sits at an interior point whose offset is a length, which is exactly how the
figure arranges for the two arms to be equal.  So this file states the arm
ledger for a marked slot as well as an unmarked one, on top of
`ConfigurationMarkedCommon`.  A marked arm is an ordinary arm of the half
length:

* centre at the **tail**, chip at the mark: the centre sees the canonical ramp
  of rise `height` over `mark e` steps, and the slot's head end sees nothing;
* centre at the **head**, chip at the mark: the centre sees the canonical ramp
  of rise `-height` over `length e - mark e` steps, and the tail end sees
  nothing.

Both readings are `ConfigurationCommon`'s one-slot ramp lemmas at the half
length, so nothing new is proved about ramps here.

**Composability.**  Like `ConfigurationTwo`, the conclusions are stated one
centre at a time; a row declares which of its chip-free vertices form banana
pairs and covers the rest by other pictures.  Rows `05` and `08` pair this file
with `ConfigurationThree`.
-/

namespace AtanasovRanganathan.ConfigurationSeven

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.DegenerateSpec
open Certificate.DegenerateSpec.DegSpec
open ConfigurationCommon
open ConfigurationMarkedCommon

variable (d : DegSpec 8 12)

/-! ## The shared height -/

/-- The height interpolated on both centres of a banana pair: the shorter of
the two arm lengths.  On the AR rows the two arms are equal, so both centres are
targets of the same script. -/
def bananaHeight (first second : ℕ) : ℕ := min first second

theorem bananaHeight_le_first (first second : ℕ) :
    bananaHeight first second ≤ first := Nat.min_le_left _ _

theorem bananaHeight_le_second (first second : ℕ) :
    bananaHeight first second ≤ second := Nat.min_le_right _ _

theorem bananaHeight_eq_of_eq (arm : ℕ) : bananaHeight arm arm = arm := by
  simp [bananaHeight]

/-! ## The banana slots move nothing

Both centres carry the same height, so each parallel slot has zero rise. -/

theorem endpointPair_eq_zero_of_unmarked_flat {potential : Fin 8 → ℤ}
    (hInv : d.RepInvariant potential) {mark : Fin 12 → ℕ}
    {markValue : Fin 12 → ℤ} {e : Fin 12} (hMark : mark e = 0)
    (hValue : markValue e = potential (d.rep (d.core.tail e)))
    (hRise : d.coreRise potential e = 0) (r : Fin 8) :
    ConfigurationMarkedCommon.endpointPair d potential mark markValue e r = 0 := by
  rw [ConfigurationMarkedCommon.endpointPair_of_unmarked d hInv hMark hValue r]
  exact ConfigurationCommon.endpointPair_eq_zero_of_rise_eq_zero d potential e r hRise

/-- The two parallel slots of a banana whose ends carry the same potential
contribute nothing anywhere. -/
theorem bananaSlot_endpointPair_eq_zero {potential : Fin 8 → ℤ}
    (hInv : d.RepInvariant potential) {mark : Fin 12 → ℕ}
    {markValue : Fin 12 → ℤ} {e : Fin 12} (hMark : mark e = 0)
    (hValue : markValue e = potential (d.rep (d.core.tail e)))
    (hEq : potential (d.core.tail e) = potential (d.core.head e)) (r : Fin 8) :
    ConfigurationMarkedCommon.endpointPair d potential mark markValue e r = 0 :=
  endpointPair_eq_zero_of_unmarked_flat d hInv hMark hValue
    (by simp [DegSpec.coreRise, hEq]) r

/-! ## A marked arm, read from its tail

The centre is the tail of `e`, its chip sits at the mark, and the script is flat
beyond the mark: `markRiseIn e = height`, `markRiseOut e = 0`. -/

section MarkedTail

variable {potential : Fin 8 → ℤ} {mark : Fin 12 → ℕ} {markValue : Fin 12 → ℤ}
  {e : Fin 12} {height : ℕ}

/-- The rise data of an arm read from its tail. -/
theorem markRiseIn_tail (hCentre : potential (d.rep (d.core.tail e)) = -(height : ℤ))
    (hMarkValue : markValue e = 0) :
    d.markRiseIn potential markValue e = (height : ℤ) := by
  simp [DegSpec.markRiseIn, hCentre, hMarkValue]

theorem markRiseOut_tail (hHead : potential (d.rep (d.core.head e)) = 0)
    (hMarkValue : markValue e = 0) :
    d.markRiseOut potential markValue e = 0 := by
  simp [DegSpec.markRiseOut, hHead, hMarkValue]

/-- What the centre receives along a marked arm read from its tail: the first
slope of the canonical ramp of rise `height` over `mark e` steps. -/
theorem tailArm_centre (hMarks : d.MarksAdmissible potential mark markValue)
    (hCentre : potential (d.rep (d.core.tail e)) = -(height : ℤ))
    (hMarkValue : markValue e = 0) (hPos : 0 < mark e) :
    SubdivisionArithmetic.splitStep (d.length e) (mark e)
        (d.markRiseIn potential markValue e)
        (d.markRiseOut potential markValue e) 0 =
      SubdivisionArithmetic.step (mark e) (height : ℤ) 0 := by
  rw [ConfigurationMarkedCommon.splitStep_tail_of_pos d hMarks hPos,
    markRiseIn_tail d hCentre hMarkValue]

/-- The far end of a marked arm read from its tail receives nothing: the script
is already flat there. -/
theorem tailArm_head (hMarks : d.MarksAdmissible potential mark markValue)
    (hHead : potential (d.rep (d.core.head e)) = 0) (hMarkValue : markValue e = 0)
    (hPos : 0 < d.length e) (hLt : mark e < d.length e) :
    SubdivisionArithmetic.splitStep (d.length e) (mark e)
        (d.markRiseIn potential markValue e)
        (d.markRiseOut potential markValue e) (d.length e - 1) = 0 :=
  ConfigurationMarkedCommon.splitStep_head_eq_zero_of_flat d hMarks hPos hLt
    (markRiseOut_tail d hHead hMarkValue)

/-- A shortest marked arm delivers one chip to its centre. -/
theorem tailArm_centre_eq_one (hMarks : d.MarksAdmissible potential mark markValue)
    (hCentre : potential (d.rep (d.core.tail e)) = -(height : ℤ))
    (hMarkValue : markValue e = 0) (hPos : 0 < mark e) (hFull : height = mark e) :
    SubdivisionArithmetic.splitStep (d.length e) (mark e)
        (d.markRiseIn potential markValue e)
        (d.markRiseOut potential markValue e) 0 = 1 := by
  rw [tailArm_centre d hMarks hCentre hMarkValue hPos, hFull]
  exact firstStep_full_eq_one hPos

/-- A marked arm never takes a chip away from its centre. -/
theorem tailArm_centre_nonneg (hMarks : d.MarksAdmissible potential mark markValue)
    (hCentre : potential (d.rep (d.core.tail e)) = -(height : ℤ))
    (hMarkValue : markValue e = 0) (hPos : 0 < mark e) :
    0 ≤ SubdivisionArithmetic.splitStep (d.length e) (mark e)
      (d.markRiseIn potential markValue e)
      (d.markRiseOut potential markValue e) 0 := by
  rw [tailArm_centre d hMarks hCentre hMarkValue hPos]
  exact firstStep_pos_nonneg (L := mark e) (k := height) hPos

end MarkedTail

/-! ## A marked arm, read from its head

The centre is the head of `e`, its chip sits at the mark, and the script is flat
before the mark: `markRiseIn e = 0`, `markRiseOut e = -height`. -/

section MarkedHead

variable {potential : Fin 8 → ℤ} {mark : Fin 12 → ℕ} {markValue : Fin 12 → ℤ}
  {e : Fin 12} {height : ℕ}

theorem markRiseIn_head (hTail : potential (d.rep (d.core.tail e)) = 0)
    (hMarkValue : markValue e = 0) :
    d.markRiseIn potential markValue e = 0 := by
  simp [DegSpec.markRiseIn, hTail, hMarkValue]

theorem markRiseOut_head
    (hCentre : potential (d.rep (d.core.head e)) = -(height : ℤ))
    (hMarkValue : markValue e = 0) :
    d.markRiseOut potential markValue e = -(height : ℤ) := by
  simp [DegSpec.markRiseOut, hCentre, hMarkValue]

/-- The near end of a marked arm read from its head receives nothing. -/
theorem headArm_tail (hMarks : d.MarksAdmissible potential mark markValue)
    (hTail : potential (d.rep (d.core.tail e)) = 0) (hMarkValue : markValue e = 0)
    (hPos : 0 < mark e) :
    SubdivisionArithmetic.splitStep (d.length e) (mark e)
        (d.markRiseIn potential markValue e)
        (d.markRiseOut potential markValue e) 0 = 0 := by
  rw [ConfigurationMarkedCommon.splitStep_tail_eq_zero_of_flat d hMarks
    (markRiseIn_head d hTail hMarkValue), if_pos hPos]

/-- What the centre receives along a marked arm read from its head: minus the
last slope of the canonical ramp of rise `-height` over `length e - mark e`
steps. -/
theorem headArm_centre (hMarks : d.MarksAdmissible potential mark markValue)
    (hCentre : potential (d.rep (d.core.head e)) = -(height : ℤ))
    (hMarkValue : markValue e = 0) (hPos : 0 < d.length e)
    (hLt : mark e < d.length e) :
    -SubdivisionArithmetic.splitStep (d.length e) (mark e)
        (d.markRiseIn potential markValue e)
        (d.markRiseOut potential markValue e) (d.length e - 1) =
      -SubdivisionArithmetic.step (d.length e - mark e) (-(height : ℤ))
        (d.length e - mark e - 1) := by
  rw [ConfigurationMarkedCommon.splitStep_head_of_lt d hMarks hPos hLt,
    markRiseOut_head d hCentre hMarkValue,
    show d.length e - 1 - mark e = d.length e - mark e - 1 from by omega]

/-- A shortest marked arm delivers one chip to its centre, read from the head. -/
theorem headArm_centre_eq_one (hMarks : d.MarksAdmissible potential mark markValue)
    (hCentre : potential (d.rep (d.core.head e)) = -(height : ℤ))
    (hMarkValue : markValue e = 0) (hPos : 0 < d.length e)
    (hLt : mark e < d.length e) (hFull : height = d.length e - mark e) :
    -SubdivisionArithmetic.splitStep (d.length e) (mark e)
        (d.markRiseIn potential markValue e)
        (d.markRiseOut potential markValue e) (d.length e - 1) = 1 := by
  rw [headArm_centre d hMarks hCentre hMarkValue hPos hLt, hFull]
  rw [lastStep_neg_full_eq_neg_one (L := d.length e - mark e) (by omega)]
  ring

/-- A marked arm never takes a chip away from its centre, read from the head. -/
theorem headArm_centre_nonneg (hMarks : d.MarksAdmissible potential mark markValue)
    (hCentre : potential (d.rep (d.core.head e)) = -(height : ℤ))
    (hMarkValue : markValue e = 0) (hPos : 0 < d.length e)
    (hLt : mark e < d.length e) (hHeight : 0 < height)
    (hLe : height ≤ d.length e - mark e) :
    0 ≤ -SubdivisionArithmetic.splitStep (d.length e) (mark e)
      (d.markRiseIn potential markValue e)
      (d.markRiseOut potential markValue e) (d.length e - 1) := by
  rw [headArm_centre d hMarks hCentre hMarkValue hPos hLt]
  have hStep := lastStep_neg_nonpos (L := d.length e - mark e) (k := height)
    hHeight hLe
  omega

end MarkedHead

end AtanasovRanganathan.ConfigurationSeven
