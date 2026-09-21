/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationMarkedThree

/-!
# The tripod centre over a marked script

This is Atanasov--Ranganathan's *second* local picture -- a chip-free core
vertex all three of whose slots end on a chip vertex -- read through the marked
arm ledger, i.e. with **one of the three arms the half of a marked slot**:

```
      A          B          C        A, B, C carry chips
       \         |         /         v is chip free
        p        q        r          one of p, q, r is a half-slot,
         \       |       /           the half from v to an interior chip
          -----  v  -----
```

`ConfigurationTwo` states the same picture against `interpolatedScript`, one
canonical ramp per slot.  AR's first and ninth genus-five families (atlas rows
`01` and `10`) need it when one arm is a *half* of a slot, because their figures
put a chip at an interior point whose offset is another leg's length
(`Utilities/Subdivision/SplitRampScript.lean`).

Nothing about the profile changes: the centre still sits at

```
 h v = min p (min q r),   h = 0 everywhere else
```

and *nothing new is proved about ramps here*.  What a marked arm contributes at
its own end is already `ConfigurationMarkedRow.slotTailForm_of_arm` /
`slotHeadForm_of_arm` -- an ordinary arm of the half length -- and the far half
of a marked slot carries rise `0` and moves nothing.  So the one genuinely new
statement is the centre's **ledger**: with `zeroChip` accounting for a collapsed
arm whose chip has merged into the centre's class, the three arm contributions
already deliver a chip.  That is `centre_ge_one` below, stated through
`ConfigurationMarkedThree.PairLedger` so that each of the three arms may be a
whole slot read from either end (`fwd` / `rev`) or the half of a marked slot.

Compared with `ConfigurationMarkedThree`'s pair, a tripod is *less* work, not
more: `h = min` of three arms has no partner bookkeeping, no `k` indicator and
no collapsed-middle-slot case, so the delivered chip is always charged to the
centre itself and a row needs no `owner` indirection at a tripod.
-/

namespace AtanasovRanganathan.ConfigurationMarkedTripod

open Utilities

open ConfigurationFive
open ConfigurationMarkedThree

/-! ## The tripod height -/

/-- The minimum of three naturals is one of them -- which arm is *full*, hence
which arm delivers the chip. -/
theorem min_three_eq_one (a b c : ℕ) :
    min a (min b c) = a ∨ min a (min b c) = b ∨ min a (min b c) = c := by
  rcases le_total a (min b c) with h | h
  · exact Or.inl (Nat.min_eq_left h)
  · rw [Nat.min_eq_right h]
    rcases le_total b c with hbc | hcb
    · exact Or.inr (Or.inl (Nat.min_eq_left hbc))
    · exact Or.inr (Or.inr (Nat.min_eq_right hcb))

theorem le_first {la lb lc o : ℕ} (ho : o = min la (min lb lc)) : o ≤ la := by
  rw [ho]; exact Nat.min_le_left _ _

theorem le_second {la lb lc o : ℕ} (ho : o = min la (min lb lc)) : o ≤ lb := by
  rw [ho]; omega

theorem le_third {la lb lc o : ℕ} (ho : o = min la (min lb lc)) : o ≤ lc := by
  rw [ho]; omega

/-! ## The centre's ledger

`la`, `lb`, `lc` are the three arm lengths -- a whole slot, or the half of a
marked slot -- and `SA`, `SB`, `SC` name which end of each the centre sits at.
`zeroChip l` is the chip of a *collapsed* arm, which the row has transferred
into the centre's class. -/

/-- **The tripod centre is reached.**  Some arm attains the height, hence is a
full ramp, and delivers a chip; the other two never take one away. -/
theorem centre_ge_one (SA SB SC : PairLedger) {la lb lc o : ℕ}
    (ho : o = min la (min lb lc)) :
    1 ≤ zeroChip la + zeroChip lb + zeroChip lc +
      (SA.tail la o 0 + SB.tail lb o 0 + SC.tail lc o 0) := by
  have hA : 0 ≤ SA.tail la o 0 :=
    SA.tail_nonneg (Nat.zero_le _) (by have := le_first ho; omega)
  have hB : 0 ≤ SB.tail lb o 0 :=
    SB.tail_nonneg (Nat.zero_le _) (by have := le_second ho; omega)
  have hC : 0 ≤ SC.tail lc o 0 :=
    SC.tail_nonneg (Nat.zero_le _) (by have := le_third ho; omega)
  have hZa : (0 : ℤ) ≤ zeroChip la := zeroChip_nonneg la
  have hZb : (0 : ℤ) ≤ zeroChip lb := zeroChip_nonneg lb
  have hZc : (0 : ℤ) ≤ zeroChip lc := zeroChip_nonneg lc
  rcases min_three_eq_one la lb lc with hFull | hFull | hFull
  · have hOne : 1 ≤ zeroChip la + SA.tail la o 0 := by
      rw [show o = la from ho.trans hFull]
      exact SA.zeroChip_add_tail_full la
    omega
  · have hOne : 1 ≤ zeroChip lb + SB.tail lb o 0 := by
      rw [show o = lb from ho.trans hFull]
      exact SB.zeroChip_add_tail_full lb
    omega
  · have hOne : 1 ≤ zeroChip lc + SC.tail lc o 0 := by
      rw [show o = lc from ho.trans hFull]
      exact SC.zeroChip_add_tail_full lc
    omega

/-- The same ledger with the delivered chip already removed. -/
theorem centre_nonneg (SA SB SC : PairLedger) {la lb lc o : ℕ} {k : ℤ}
    (ho : o = min la (min lb lc)) (hk : k ≤ 1) :
    0 ≤ zeroChip la + zeroChip lb + zeroChip lc - k +
      (SA.tail la o 0 + SB.tail lb o 0 + SC.tail lc o 0) := by
  have := centre_ge_one SA SB SC ho
  omega

end AtanasovRanganathan.ConfigurationMarkedTripod
