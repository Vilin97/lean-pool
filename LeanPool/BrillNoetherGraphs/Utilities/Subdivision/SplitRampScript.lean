/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateSlopeScript
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SplitRampArithmetic

/-!
# Firing scripts with a marked point inside each slot

`DegSpec.interpolatedScript` puts one canonical ramp on each slot, so its
interior Laplacian is nonnegative everywhere and a chip strictly inside a slot
is never used.  Atanasov--Ranganathan's sixth and seventh genus-five families
place chips exactly there, and no core-supported degree-four divisor covers
either row, so those rows need a script whose slot value may bend downward at
one marked offset.

This file is that script.  A slot `e` carries a **mark** `mark e` -- the offset
of its chip -- and a **mark value** `markValue e`, the script's value there;
the slot value is the canonical ramp from the tail class up to the mark,
followed by the canonical ramp from the mark down to the head class.  Taking
`mark e = 0` and `markValue e = potential (rep (tail e))` recovers
`interpolatedScript` on that slot, so a row may mark only the slots it needs.

The two Laplacian formulas come from `DegenerateSlopeScript` unchanged: they
are stated for an arbitrary slot-value function.  What this file adds is

* `splitValueCompatible`, so the value really assembles into a script;
* `isStepSlope_splitScript`, naming the slope as `SubdivisionArithmetic.splitStep`;
* `prin_splitScript_interiorVertex_nonneg_of_ne`, the interior residual away
  from the mark; and
* `prin_splitScript_interiorVertex_ge_neg_one`, the residual **at** the mark,
  which is where the chip is spent.

The arithmetic lives in `SplitRampArithmetic.lean`.
-/

namespace Utilities.Certificate.DegenerateSpec.DegSpec

open Utilities.Certificate

open Finset ExplicitPotential

variable {n p : ℕ} (d : DegSpec n p)

/-- The rise of the ramp from the tail class up to the mark. -/
def markRiseIn (potential : Fin n → ℤ) (markValue : Fin p → ℤ) (e : Fin p) : ℤ :=
  markValue e - potential (d.rep (d.core.tail e))

/-- The rise of the ramp from the mark down to the head class. -/
def markRiseOut (potential : Fin n → ℤ) (markValue : Fin p → ℤ) (e : Fin p) : ℤ :=
  potential (d.rep (d.core.head e)) - markValue e

/-- Admissibility of the marks: each sits inside its slot, and a mark at an end
of its slot carries that end's value. -/
def MarksAdmissible (potential : Fin n → ℤ) (mark : Fin p → ℕ)
    (markValue : Fin p → ℤ) : Prop :=
  ∀ e : Fin p, SubdivisionArithmetic.SplitRamp (d.length e) (mark e)
    (d.markRiseIn potential markValue e) (d.markRiseOut potential markValue e)

/-- The slot value: two canonical ramps meeting at the mark. -/
def splitValue (potential : Fin n → ℤ) (mark : Fin p → ℕ)
    (markValue : Fin p → ℤ) (e : Fin p) (k : ℕ) : ℤ :=
  potential (d.rep (d.core.tail e)) +
    SubdivisionArithmetic.splitPotential (d.length e) (mark e)
      (d.markRiseIn potential markValue e) (d.markRiseOut potential markValue e) k

/-- The firing script assembled from the marked slot values. -/
def splitScript (potential : Fin n → ℤ) (mark : Fin p → ℕ)
    (markValue : Fin p → ℤ) : firing_script d.graph :=
  d.slotValueScript potential (d.splitValue potential mark markValue)

theorem splitValueCompatible {potential : Fin n → ℤ} {mark : Fin p → ℕ}
    {markValue : Fin p → ℤ}
    (hMarks : d.MarksAdmissible potential mark markValue) :
    d.SlotValueCompatible potential (d.splitValue potential mark markValue) where
  tail := by
    intro e
    rw [splitValue, SubdivisionArithmetic.splitPotential_zero (hMarks e), add_zero]
  head := by
    intro e
    rw [splitValue, SubdivisionArithmetic.splitPotential_length (hMarks e),
      markRiseIn, markRiseOut]
    ring

/-- The slope of the marked script is the split ramp's slope. -/
theorem isStepSlope_splitScript {potential : Fin n → ℤ} {mark : Fin p → ℕ}
    {markValue : Fin p → ℤ}
    (hMarks : d.MarksAdmissible potential mark markValue) :
    d.IsStepSlope (d.splitScript potential mark markValue)
      (fun e k => SubdivisionArithmetic.splitStep (d.length e) (mark e)
        (d.markRiseIn potential markValue e)
        (d.markRiseOut potential markValue e) k) := by
  intro e o
  have hBase := d.isStepSlope_slotValueScript (d.splitValueCompatible hMarks) e o
  unfold splitScript
  rw [hBase]
  simp only [splitValue, SubdivisionArithmetic.splitStep]
  ring

/-! ## The core-class formula

`prin_coreVertex_eq_endpointSum` applies verbatim; the two endpoint slopes are
identified with the surviving half's own endpoint slopes by
`SubdivisionArithmetic.splitStep_first` and `splitStep_last`. -/

theorem prin_splitScript_coreVertex_eq_endpointSum {potential : Fin n → ℤ}
    {mark : Fin p → ℕ} {markValue : Fin p → ℤ}
    (hMarks : d.MarksAdmissible potential mark markValue) (r : Fin n) :
    prin d.graph (d.splitScript potential mark markValue) (d.coreVertex r) =
      ∑ e : Fin p,
        ((if d.rep (d.core.tail e) = d.rep r then
            SubdivisionArithmetic.splitStep (d.length e) (mark e)
              (d.markRiseIn potential markValue e)
              (d.markRiseOut potential markValue e) 0
          else 0) +
          (if d.rep (d.core.head e) = d.rep r then
            -SubdivisionArithmetic.splitStep (d.length e) (mark e)
              (d.markRiseIn potential markValue e)
              (d.markRiseOut potential markValue e) (d.length e - 1)
          else 0)) :=
  d.prin_coreVertex_eq_endpointSum (d.isStepSlope_splitScript hMarks) r

/-! ## The interior formula -/

theorem prin_splitScript_interiorVertex_eq_slopeDifference
    {potential : Fin n → ℤ} {mark : Fin p → ℕ} {markValue : Fin p → ℤ}
    (hMarks : d.MarksAdmissible potential mark markValue)
    (e : Fin p) (o : Fin (d.length e - 1)) :
    prin d.graph (d.splitScript potential mark markValue)
        (d.interiorVertex e o) =
      SubdivisionArithmetic.splitStep (d.length e) (mark e)
          (d.markRiseIn potential markValue e)
          (d.markRiseOut potential markValue e) (o.val + 1) -
        SubdivisionArithmetic.splitStep (d.length e) (mark e)
          (d.markRiseIn potential markValue e)
          (d.markRiseOut potential markValue e) o.val :=
  d.prin_interiorVertex_eq_slopeDifference (d.isStepSlope_splitScript hMarks) e o

/-- Away from the mark the marked script is still convex, so its interior
residual is nonnegative exactly as for `interpolatedScript`. -/
theorem prin_splitScript_interiorVertex_nonneg_of_ne
    {potential : Fin n → ℤ} {mark : Fin p → ℕ} {markValue : Fin p → ℤ}
    (hMarks : d.MarksAdmissible potential mark markValue)
    (e : Fin p) (o : Fin (d.length e - 1)) (hne : o.val + 1 ≠ mark e) :
    0 ≤ prin d.graph (d.splitScript potential mark markValue)
      (d.interiorVertex e o) := by
  rw [d.prin_splitScript_interiorVertex_eq_slopeDifference hMarks e o]
  have hdiff := SubdivisionArithmetic.splitStep_diff_nonneg_of_ne
    (L := d.length e) (t := mark e) (i := o.val + 1)
    (first := d.markRiseIn potential markValue e)
    (second := d.markRiseOut potential markValue e)
    (hMarks e) (by omega) hne
  simpa using hdiff

/-- **At the mark.**  The residual drops by at most one, so a divisor carrying
one chip at the marked vertex stays effective there.  The two rise bounds and
the flatness disjunction are what a configuration supplies. -/
theorem prin_splitScript_interiorVertex_ge_neg_one
    {potential : Fin n → ℤ} {mark : Fin p → ℕ} {markValue : Fin p → ℤ}
    (hMarks : d.MarksAdmissible potential mark markValue)
    (e : Fin p) (o : Fin (d.length e - 1)) (hmark : o.val + 1 = mark e)
    (hlt : mark e < d.length e)
    (hIn : d.markRiseIn potential markValue e ≤ (mark e : ℤ))
    (hOut : -((d.length e - mark e : ℕ) : ℤ) ≤
      d.markRiseOut potential markValue e)
    (hflat : d.markRiseIn potential markValue e = 0 ∨
      d.markRiseOut potential markValue e = 0) :
    -1 ≤ prin d.graph (d.splitScript potential mark markValue)
      (d.interiorVertex e o) := by
  rw [d.prin_splitScript_interiorVertex_eq_slopeDifference hMarks e o]
  have hkink := SubdivisionArithmetic.splitStep_kink_ge_neg_one
    (L := d.length e) (t := mark e)
    (first := d.markRiseIn potential markValue e)
    (second := d.markRiseOut potential markValue e)
    (hMarks e) (by omega) hlt hIn hOut hflat
  have hone : mark e - 1 = o.val := by omega
  rw [hone] at hkink
  rw [hmark]
  exact hkink

end Utilities.Certificate.DegenerateSpec.DegSpec
