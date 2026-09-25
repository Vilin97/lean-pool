/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationFive
public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationSeven

/-!
# The chip-free pair over a marked script

`ConfigurationThree` states Atanasov--Ranganathan's *third* local picture -- two
adjacent chip-free vertices, two chip arms each -- against
`DegSpec.interpolatedScript`, one canonical ramp per slot.  AR's sixth and
seventh genus-five families need the same picture when two of the four arms are
*halves* of a marked slot, because their figures put a chip at an interior point
whose offset is a length (`Utilities/Subdivision/SplitRampScript.lean`).

Nothing about the profile changes: the two heights are still

```
 h₂ = min a b            -- the partner
 h₁ = min a (h₂ + m)     -- the target
```

with `a`, `b` the two arm minima and `m` the middle slot.  What changes is only
*which* one-edge quantity an arm contributes, and this file supplies the three
missing pieces.

* **The endpoint ledger of a marked script.**  `positiveEndpointContribution`
  is the marked analogue of the per-vertex sum a row uses, and
  `positiveEndpointContribution_classSum_eq` identifies its class sums with the
  Laplacian.  The three reading lemmas `slot*_of_unmarked`, `slot*_of_markedTail`
  and `slot*_of_markedHead` turn each slot's two terms into
  `ConfigurationFive`'s `tailContribution` / `headContribution` at the relevant
  *half* length.  A marked slot always has one flat half in the intended
  configurations, which is why exactly two readings suffice.
* **The chip at a mark, read at a core class.**  `markChipWeight` records where
  the interior chip lands when the mark degenerates to an end of its slot
  (`mark = 0` on a collapsed leg, `mark = length` on a chamber wall), and
  `markChip_classSum_eq` proves the class sum.
* **The pair profile itself**, `pairTarget_nonneg` and `pairPartner_nonneg`,
  stated through a `PairLedger` so that each of the four arms may be a whole
  slot read from either end or the half of a marked slot, and so that the pair
  is proved once and instantiated at both centres.

The `k` parameter of the two pair statements is the indicator of *which vertex
of the contracted class owns the delivered chip*: when the middle slot collapses
the two centres merge, and the chip may have to be charged to the partner.  That
is the `targetOwner` device every finished row already uses.
-/

@[expose] public section

namespace AtanasovRanganathan.ConfigurationMarkedThree

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.DegenerateSpec
open Certificate.DegenerateSpec.DegSpec
open ConfigurationFive

variable (d : DegSpec 8 12)

/-! ## The two endpoint terms of one slot under a marked script -/

/-- What one slot contributes at its tail class, with a collapsed slot's
artificial term suppressed. -/
def slotTailTerm (potential : Fin 8 → ℤ) (mark : Fin 12 → ℕ)
    (markValue : Fin 12 → ℤ) (e : Fin 12) : ℤ :=
  if d.length e = 0 then 0
  else SubdivisionArithmetic.splitStep (d.length e) (mark e)
    (d.markRiseIn potential markValue e) (d.markRiseOut potential markValue e) 0

/-- What one slot contributes at its head class, with a collapsed slot's
artificial term suppressed. -/
def slotHeadTerm (potential : Fin 8 → ℤ) (mark : Fin 12 → ℕ)
    (markValue : Fin 12 → ℤ) (e : Fin 12) : ℤ :=
  if d.length e = 0 then 0
  else -SubdivisionArithmetic.splitStep (d.length e) (mark e)
    (d.markRiseIn potential markValue e) (d.markRiseOut potential markValue e)
    (d.length e - 1)

/-- The per-vertex endpoint ledger of a marked script. -/
def positiveEndpointContribution (potential : Fin 8 → ℤ) (mark : Fin 12 → ℕ)
    (markValue : Fin 12 → ℤ) (v : Fin 8) : ℤ :=
  ∑ e : Fin 12,
    ((if d.core.tail e = v then slotTailTerm d potential mark markValue e
      else 0) +
    (if d.core.head e = v then slotHeadTerm d potential mark markValue e
      else 0))

/-- **The class sum is the Laplacian.**  The artificial endpoint terms of a
collapsed slot cancel, which is what lets a row work vertex by vertex on the
uncontracted core. -/
theorem positiveEndpointContribution_classSum_eq
    {potential : Fin 8 → ℤ} {mark : Fin 12 → ℕ} {markValue : Fin 12 → ℤ}
    (hMarks : d.MarksAdmissible potential mark markValue) (r : Fin 8) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        positiveEndpointContribution d potential mark markValue v =
      prin d.graph (d.splitScript potential mark markValue) (d.coreVertex r) := by
  classical
  rw [d.prin_splitScript_coreVertex_eq_endpointSum hMarks]
  unfold positiveEndpointContribution
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hZero : d.length e = 0
  · have hRep := d.rep_zero e hZero
    simp only [slotTailTerm, slotHeadTerm, hZero, ite_true, ite_self,
      add_zero, Finset.sum_const_zero]
    rw [hRep]
    by_cases h : d.rep (d.core.head e) = d.rep r <;> simp [h]
  · simp only [slotTailTerm, slotHeadTerm, hZero, ite_false,
      Finset.sum_add_distrib]
    by_cases hTail : d.rep (d.core.tail e) = d.rep r <;>
      by_cases hHead : d.rep (d.core.head e) = d.rep r <;>
      simp [hTail, hHead]

/-! ## Reading one slot as one or two ordinary arms

Throughout, `hu` is the height at the tail class and `hv` the height at the head
class; the script is `potential = -height`.  The two marked readings are the
ones the AR rows use: the chip at the mark sits where a flat stretch meets a
full ramp, so exactly one of the two heights is zero. -/

section Readings

variable {potential : Fin 8 → ℤ} {mark : Fin 12 → ℕ} {markValue : Fin 12 → ℤ}
  {e : Fin 12} {hu hv : ℕ}

/-- An unmarked slot is an ordinary arm of its own length. -/
theorem slotTailTerm_of_unmarked (hMark : mark e = 0)
    (hValue : markValue e = potential (d.rep (d.core.tail e)))
    (hTail : potential (d.rep (d.core.tail e)) = -(hu : ℤ))
    (hHead : potential (d.rep (d.core.head e)) = -(hv : ℤ)) :
    slotTailTerm d potential mark markValue e = tailContribution (d.length e) hu hv := by
  unfold slotTailTerm tailContribution
  by_cases hZero : d.length e = 0
  · rw [ite_eq_left hZero, ite_eq_left hZero]
  · rw [ite_eq_right hZero, ite_eq_right hZero, hMark,
      SubdivisionArithmetic.splitStep_mark_zero]
    congr 1
    simp only [DegSpec.markRiseOut, hValue, hTail, hHead]
    ring

theorem slotHeadTerm_of_unmarked (hMark : mark e = 0)
    (hValue : markValue e = potential (d.rep (d.core.tail e)))
    (hTail : potential (d.rep (d.core.tail e)) = -(hu : ℤ))
    (hHead : potential (d.rep (d.core.head e)) = -(hv : ℤ)) :
    slotHeadTerm d potential mark markValue e = headContribution (d.length e) hu hv := by
  unfold slotHeadTerm headContribution
  by_cases hZero : d.length e = 0
  · rw [ite_eq_left hZero, ite_eq_left hZero]
  · rw [ite_eq_right hZero, ite_eq_right hZero, hMark,
      SubdivisionArithmetic.splitStep_mark_zero]
    congr 2
    simp only [DegSpec.markRiseOut, hValue, hTail, hHead]
    ring

/-- A marked slot whose **head** carries height zero: its tail sees an ordinary
arm of the *near* half length, and its head sees nothing unless the mark has
reached the head. -/
theorem slotTailTerm_of_markedTail
    (hMarks : d.MarksAdmissible potential mark markValue)
    (hValue : markValue e = 0)
    (hTail : potential (d.rep (d.core.tail e)) = -(hu : ℤ))
    (hHead : potential (d.rep (d.core.head e)) = 0) :
    slotTailTerm d potential mark markValue e = tailContribution (mark e) hu 0 := by
  have hIn : d.markRiseIn potential markValue e = (hu : ℤ) := by
    simp [DegSpec.markRiseIn, hValue, hTail]
  have hOut : d.markRiseOut potential markValue e = 0 := by
    simp [DegSpec.markRiseOut, hValue, hHead]
  unfold slotTailTerm
  by_cases hMark : 0 < mark e
  · have hLen : d.length e ≠ 0 := by have := (hMarks e).le; omega
    rw [ite_eq_right hLen, SubdivisionArithmetic.splitStep_first (hMarks e),
      ite_eq_left hMark, hIn]
    unfold tailContribution
    rw [ite_eq_right (by omega)]
    norm_num
  · have hMark0 : mark e = 0 := by omega
    have hu0 : hu = 0 := by
      have := (hMarks e).first_zero hMark0
      rw [hIn] at this
      exact_mod_cast this
    rw [hMark0, hu0, tailContribution_zero_zero]
    by_cases hZero : d.length e = 0
    · rw [ite_eq_left hZero]
    · rw [ite_eq_right hZero, SubdivisionArithmetic.splitStep_mark_zero, hOut]
      exact SubdivisionArithmetic.step_zero_of_lt (by omega)

theorem slotHeadTerm_of_markedTail
    (hMarks : d.MarksAdmissible potential mark markValue)
    (hValue : markValue e = 0)
    (hTail : potential (d.rep (d.core.tail e)) = -(hu : ℤ))
    (hHead : potential (d.rep (d.core.head e)) = 0) :
    slotHeadTerm d potential mark markValue e =
      if mark e < d.length e then 0 else headContribution (d.length e) hu 0 := by
  have hIn : d.markRiseIn potential markValue e = (hu : ℤ) := by
    simp [DegSpec.markRiseIn, hValue, hTail]
  have hOut : d.markRiseOut potential markValue e = 0 := by
    simp [DegSpec.markRiseOut, hValue, hHead]
  unfold slotHeadTerm
  by_cases hZero : d.length e = 0
  · have hMark0 : mark e = 0 := by have := (hMarks e).le; omega
    rw [ite_eq_left hZero, ite_eq_right (by omega)]
    simp [headContribution, hZero]
  · rw [ite_eq_right hZero, SubdivisionArithmetic.splitStep_last (hMarks e) (by omega)]
    by_cases hLt : mark e < d.length e
    · rw [ite_eq_left hLt, ite_eq_left hLt, hOut,
        SubdivisionArithmetic.step_zero_of_lt (by omega)]
      norm_num
    · rw [ite_eq_right hLt, ite_eq_right hLt, hIn]
      unfold headContribution
      rw [ite_eq_right hZero]
      norm_num

/-- A marked slot whose **tail** carries height zero: its head sees an ordinary
arm of the *far* half length, and its tail sees nothing unless the mark is still
at the tail. -/
theorem slotTailTerm_of_markedHead
    (hMarks : d.MarksAdmissible potential mark markValue)
    (hValue : markValue e = 0)
    (hTail : potential (d.rep (d.core.tail e)) = 0)
    (hHead : potential (d.rep (d.core.head e)) = -(hv : ℤ)) :
    slotTailTerm d potential mark markValue e =
      if 0 < mark e then 0 else tailContribution (d.length e) 0 hv := by
  have hIn : d.markRiseIn potential markValue e = 0 := by
    simp [DegSpec.markRiseIn, hValue, hTail]
  have hOut : d.markRiseOut potential markValue e = -(hv : ℤ) := by
    simp [DegSpec.markRiseOut, hValue, hHead]
  unfold slotTailTerm
  by_cases hZero : d.length e = 0
  · have hMark0 : mark e = 0 := by have := (hMarks e).le; omega
    rw [ite_eq_left hZero, ite_eq_right (by omega)]
    simp [tailContribution, hZero]
  · rw [ite_eq_right hZero, SubdivisionArithmetic.splitStep_first (hMarks e)]
    by_cases hMark : 0 < mark e
    · rw [ite_eq_left hMark, ite_eq_left hMark, hIn]
      exact SubdivisionArithmetic.step_zero_of_lt hMark
    · rw [ite_eq_right hMark, ite_eq_right hMark, hOut]
      unfold tailContribution
      rw [ite_eq_right hZero]
      norm_num

theorem slotHeadTerm_of_markedHead
    (hMarks : d.MarksAdmissible potential mark markValue)
    (hValue : markValue e = 0)
    (hTail : potential (d.rep (d.core.tail e)) = 0)
    (hHead : potential (d.rep (d.core.head e)) = -(hv : ℤ)) :
    slotHeadTerm d potential mark markValue e =
      headContribution (d.length e - mark e) 0 hv := by
  have hIn : d.markRiseIn potential markValue e = 0 := by
    simp [DegSpec.markRiseIn, hValue, hTail]
  have hOut : d.markRiseOut potential markValue e = -(hv : ℤ) := by
    simp [DegSpec.markRiseOut, hValue, hHead]
  unfold slotHeadTerm
  by_cases hZero : d.length e = 0
  · have hMark0 : mark e = 0 := by have := (hMarks e).le; omega
    rw [ite_eq_left hZero]
    simp [headContribution, hZero, hMark0]
  · rw [ite_eq_right hZero, SubdivisionArithmetic.splitStep_last (hMarks e) (by omega)]
    by_cases hLt : mark e < d.length e
    · rw [ite_eq_left hLt, hOut]
      unfold headContribution
      rw [ite_eq_right (by omega),
        show d.length e - 1 - mark e = d.length e - mark e - 1 from by omega]
      norm_num
    · have hEq : mark e = d.length e := by have := (hMarks e).le; omega
      rw [ite_eq_right hLt, hIn,
        SubdivisionArithmetic.step_zero_of_lt (by omega)]
      simp [headContribution, hEq]

/-! ### The uniform marked reading

In the intended configurations one of the two heights at a marked slot's ends is
zero -- the chip sits where a flat stretch meets a full ramp, which is also the
hypothesis under which the chip pays for the kink.  Under that single assumption
the two readings above collapse into one pair of formulas, valid at either
orientation, and (taking `mark e = 0`) agreeing with the unmarked slot's tail
reading. -/

theorem slotTailTerm_of_marked
    (hMarks : d.MarksAdmissible potential mark markValue)
    (hValue : markValue e = 0)
    (hTail : potential (d.rep (d.core.tail e)) = -(hu : ℤ))
    (hHead : potential (d.rep (d.core.head e)) = -(hv : ℤ))
    (hflat : hu = 0 ∨ hv = 0) :
    slotTailTerm d potential mark markValue e =
      if 0 < mark e then tailContribution (mark e) hu 0
      else tailContribution (d.length e) hu hv := by
  have hInEq : d.markRiseIn potential markValue e = (hu : ℤ) := by
    simp [DegSpec.markRiseIn, hValue, hTail]
  rcases hflat with h0 | h0
  · subst h0
    rw [slotTailTerm_of_markedHead d hMarks hValue (by simpa using hTail) hHead]
    by_cases hm : 0 < mark e
    · rw [ite_eq_left hm, ite_eq_left hm]
      exact (tailContribution_zero_zero _).symm
    · rw [ite_eq_right hm, ite_eq_right hm]
  · subst h0
    rw [slotTailTerm_of_markedTail d hMarks hValue hTail (by simpa using hHead)]
    by_cases hm : 0 < mark e
    · rw [ite_eq_left hm]
    · rw [ite_eq_right hm]
      have hMark0 : mark e = 0 := by omega
      have hu0 : hu = 0 := by
        have hz := (hMarks e).first_zero hMark0
        rw [hInEq] at hz
        omega
      rw [hMark0, hu0, tailContribution_zero_zero, tailContribution_zero_zero]

theorem slotHeadTerm_of_marked
    (hMarks : d.MarksAdmissible potential mark markValue)
    (hValue : markValue e = 0)
    (hTail : potential (d.rep (d.core.tail e)) = -(hu : ℤ))
    (hHead : potential (d.rep (d.core.head e)) = -(hv : ℤ))
    (hflat : hu = 0 ∨ hv = 0) :
    slotHeadTerm d potential mark markValue e =
      if mark e < d.length e then headContribution (d.length e - mark e) 0 hv
      else headContribution (d.length e) hu hv := by
  have hOutEq : d.markRiseOut potential markValue e = -(hv : ℤ) := by
    simp [DegSpec.markRiseOut, hValue, hHead]
  rcases hflat with h0 | h0
  · subst h0
    rw [slotHeadTerm_of_markedHead d hMarks hValue (by simpa using hTail) hHead]
    by_cases hlt : mark e < d.length e
    · rw [ite_eq_left hlt]
    · rw [ite_eq_right hlt]
      have hEq : mark e = d.length e := by have := (hMarks e).le; omega
      have hv0 : hv = 0 := by
        have hz := (hMarks e).second_zero hEq
        rw [hOutEq] at hz
        omega
      rw [hv0, headContribution_zero_zero, headContribution_zero_zero]
  · subst h0
    rw [slotHeadTerm_of_markedTail d hMarks hValue hTail (by simpa using hHead)]
    by_cases hlt : mark e < d.length e
    · rw [ite_eq_left hlt, ite_eq_left hlt]
      exact (headContribution_zero_zero _).symm
    · rw [ite_eq_right hlt, ite_eq_right hlt]

end Readings

/-! ## The chip at a mark, seen from a core class

When the mark degenerates to an end of its slot the interior chip *is* a core
vertex.  Both degeneracies occur on real faces: `mark = 0` when the leg carrying
the chip collapses, `mark = length` on the chamber wall where the figure's
inequality is an equality. -/

/-- Where the chip at the mark of `e` sits, as a weight on core vertices. -/
def markChipWeight (mark : Fin 12 → ℕ) (e : Fin 12) (v : Fin 8) : ℤ :=
  if mark e = 0 then (if v = d.core.tail e then 1 else 0)
  else if d.length e ≤ mark e then (if v = d.core.head e then 1 else 0)
  else 0

theorem markChipWeight_nonneg (mark : Fin 12 → ℕ) (e : Fin 12) (v : Fin 8) :
    0 ≤ markChipWeight d mark e v := by
  unfold markChipWeight
  split_ifs <;> norm_num

theorem markChip_classSum_eq (mark : Fin 12 → ℕ) (e : Fin 12) (r : Fin 8) :
    oneChip (G := d.graph) (d.pathAt e (mark e)) (d.coreVertex r) =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        markChipWeight d mark e v := by
  classical
  have hcore (u : Fin 8) :
      oneChip (G := d.graph) (d.coreVertex u) (d.coreVertex r) =
        ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
          (if v = u then (1 : ℤ) else 0) := by
    rw [Finset.sum_ite_eq' (Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r))]
    simp only [oneChip, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : d.rep u = d.rep r
    · rw [ite_eq_left h, ite_eq_left ((d.coreVertex_eq_iff r u).mpr h.symm)]
    · rw [ite_eq_right h, ite_eq_right (fun hx => h ((d.coreVertex_eq_iff r u).mp hx).symm)]
  by_cases hZero : mark e = 0
  · have h1 : d.pathAt e (mark e) = d.coreVertex (d.core.tail e) := by
      rw [hZero]; exact d.pathAt_zero e
    rw [h1, hcore]
    exact Finset.sum_congr rfl (fun v _ => by simp [markChipWeight, hZero])
  · by_cases hLe : d.length e ≤ mark e
    · rw [d.pathAt_length hLe, hcore]
      exact Finset.sum_congr rfl (fun v _ => by simp [markChipWeight, hZero, hLe])
    · rw [d.pathAt_interior hZero (by omega)]
      have hAll : ∀ v : Fin 8, markChipWeight d mark e v = 0 := by
        intro v
        simp [markChipWeight, hZero, hLe]
      simp only [hAll, Finset.sum_const_zero]
      simp [oneChip, DegSpec.coreVertex, DegSpec.interiorVertex]

/-! ## Redistributing chips inside a contracted class

A chip may be delivered to a vertex of the target's class other than the target
itself, and a collapsed arm may put its chip in the centre's class.  Both are
handled by moving weight *within* a class, which leaves every class sum -- hence
the divisor -- unchanged. -/

export ConfigurationCommon (indicatorWeight transferWeight
  sum_transferWeight_eq_zero sum_indicatorWeight_class)

theorem sum_conditional_transfer_eq_zero (P : Prop) [Decidable P]
    (source target : Fin 8) (hRep : P → d.rep source = d.rep target) (r : Fin 8) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        (if P then transferWeight source target v else 0) = 0 := by
  by_cases hP : P
  · simp only [ite_eq_left hP]
    exact sum_transferWeight_eq_zero d (hRep hP) r
  · simp [hP]

/-! ## The pair profile

An arm of the picture may be a whole slot read from either end, or the half of a
marked slot.  A `PairLedger` names the contribution at the end carrying the
height, so that both the target and the partner statement are proved once. -/

/-- The one-edge facts the pair profile consumes.  `tail L hu hv` is the
contribution at the end carrying height `hu`. -/
structure PairLedger where
  /-- The tail contribution of a paired slot as a function of length and endpoint heights. -/
  tail : ℕ → ℕ → ℕ → ℤ
  tail_nonneg : ∀ {L hu hv : ℕ}, hv ≤ hu → hu ≤ hv + L → 0 ≤ tail L hu hv
  tail_ge_neg_one : ∀ {L hu hv : ℕ}, hv ≤ hu + L → hu ≤ hv + L → -1 ≤ tail L hu hv
  tail_same : ∀ L h : ℕ, tail L h h = 0
  zeroChip_add_tail_full : ∀ L : ℕ, 1 ≤ zeroChip L + tail L L 0
  tail_eq_one_of_full : ∀ {L hu hv : ℕ}, 0 < L → hu = hv + L → tail L hu hv = 1

/-- The slot read from its tail. -/
def fwd : PairLedger where
  tail := tailContribution
  tail_nonneg h hUpper := tailContribution_nonneg h hUpper
  tail_ge_neg_one h hUpper := tailContribution_ge_neg_one h hUpper
  tail_same := tailContribution_same
  zeroChip_add_tail_full := zeroChip_add_tail_full
  tail_eq_one_of_full h hFull := tailContribution_eq_one_of_full h hFull

/-- The same slot read from its head. -/
def rev : PairLedger where
  tail L hu hv := headContribution L hv hu
  tail_nonneg h hUpper := headContribution_nonneg h hUpper
  tail_ge_neg_one h hUpper := headContribution_ge_neg_one hUpper h
  tail_same L h := headContribution_same L h
  zeroChip_add_tail_full := zeroChip_add_head_full
  tail_eq_one_of_full h hFull := headContribution_eq_one_of_full h hFull

@[simp] theorem fwd_tail (L hu hv : ℕ) : fwd.tail L hu hv = tailContribution L hu hv := rfl

@[simp] theorem rev_tail (L hu hv : ℕ) : rev.tail L hu hv = headContribution L hv hu := rfl

/-- **The target of a configuration-3 pair.**  `la`, `lb` are the target's two
arm lengths, `m` the middle slot, `a = min la lb`, `b` the partner's arm minimum,
`g = min a b` the partner height and `o = min a (g + m)` the target height.  `k`
is one exactly when the delivered chip is charged to this vertex. -/
theorem pairTarget_nonneg (SA SB SM : PairLedger) {la lb m a b g o : ℕ} {k : ℤ}
    (ha : a = min la lb) (hg : g = min a b) (ho : o = min a (g + m))
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hk : k = 1 → m = 0 → a ≤ b) :
    0 ≤ zeroChip la + zeroChip lb - k +
      (SA.tail la o 0 + SB.tail lb o 0 + SM.tail m o g) := by
  have hArmA : 0 ≤ SA.tail la o 0 := SA.tail_nonneg (Nat.zero_le _) (by omega)
  have hArmB : 0 ≤ SB.tail lb o 0 := SB.tail_nonneg (Nat.zero_le _) (by omega)
  have hMid : 0 ≤ SM.tail m o g := SM.tail_nonneg (by omega) (by omega)
  have hZa : (0 : ℤ) ≤ zeroChip la := zeroChip_nonneg la
  have hZb : (0 : ℤ) ≤ zeroChip lb := zeroChip_nonneg lb
  rcases eq_or_lt_of_le hk1 with hkOne | hkLt
  · -- the chip is charged here, so some route must be full
    have hkEq : k = 1 := hkOne
    have hcases : o = la ∨ o = lb ∨ (0 < m ∧ o = g + m) := by
      by_cases hm : m = 0
      · have hab := hk hkEq hm
        rcases Nat.le_total la lb with h1 | h1
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
      · rcases Nat.le_total a (g + m) with h2 | h2
        · rcases Nat.le_total la lb with h1 | h1
          · exact Or.inl (by omega)
          · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    rcases hcases with hFull | hFull | ⟨hmPos, hFull⟩
    · have hOne : 1 ≤ zeroChip la + SA.tail la o 0 := by
        rw [hFull]; exact SA.zeroChip_add_tail_full la
      omega
    · have hOne : 1 ≤ zeroChip lb + SB.tail lb o 0 := by
        rw [hFull]; exact SB.zeroChip_add_tail_full lb
      omega
    · have hOne : SM.tail m o g = 1 := SM.tail_eq_one_of_full hmPos (by omega)
      omega
  · omega

/-- **The partner of a configuration-3 pair.**  `lc`, `ld` are the partner's two
arm lengths and `b = min lc ld`; the partner sits at height `g` and reads the
middle slot from below. -/
theorem pairPartner_nonneg (SC SD SM : PairLedger) {lc ld m a b g o : ℕ} {k : ℤ}
    (hb : b = min lc ld) (hg : g = min a b) (ho : o = min a (g + m))
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hk : k = 1 → m = 0 ∧ b < a) :
    0 ≤ zeroChip lc + zeroChip ld - k +
      (SC.tail lc g 0 + SD.tail ld g 0 + SM.tail m g o) := by
  have hArmC : 0 ≤ SC.tail lc g 0 := SC.tail_nonneg (Nat.zero_le _) (by omega)
  have hArmD : 0 ≤ SD.tail ld g 0 := SD.tail_nonneg (Nat.zero_le _) (by omega)
  have hZc : (0 : ℤ) ≤ zeroChip lc := zeroChip_nonneg lc
  have hZd : (0 : ℤ) ≤ zeroChip ld := zeroChip_nonneg ld
  have hArmFull (hFull : g = b) :
      1 ≤ zeroChip lc + zeroChip ld + (SC.tail lc g 0 + SD.tail ld g 0) := by
    rcases Nat.le_total lc ld with h1 | h1
    · have hOne : 1 ≤ zeroChip lc + SC.tail lc g 0 := by
        rw [show g = lc by omega]; exact SC.zeroChip_add_tail_full lc
      omega
    · have hOne : 1 ≤ zeroChip ld + SD.tail ld g 0 := by
        rw [show g = ld by omega]; exact SD.zeroChip_add_tail_full ld
      omega
  by_cases hgo : g = o
  · have hMid : SM.tail m g o = 0 := by rw [hgo]; exact SM.tail_same m o
    rw [hMid]
    rcases eq_or_lt_of_le hk1 with hkOne | hkLt
    · obtain ⟨hm, hba⟩ := hk hkOne
      have hSupply := hArmFull (by omega)
      omega
    · omega
  · have hMid : -1 ≤ SM.tail m g o := SM.tail_ge_neg_one (by omega) (by omega)
    have hmPos : 0 < m := by omega
    have hkZero : k = 0 := by
      rcases eq_or_lt_of_le hk1 with hkOne | hkLt
      · exact absurd (hk hkOne).1 (by omega)
      · omega
    have hSupply := hArmFull (by omega)
    omega

end AtanasovRanganathan.ConfigurationMarkedThree
