/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.PairingConnectivity

/-!
# The chord data is a function of the pairing

Systems with the same boundary pairing have the same chord-crossing
count, hence the same path sign: `pathSign` telescopes freely along
pairing-preserving blocks, and around any pairing-returning loop of
repairs the crossing count returns — the parity backbone of the
holonomy bookkeeping.
-/

namespace RS

open scoped Classical

variable {α : Type}

namespace EdgeSubset

/-- The crossing relation only sees the pairing. -/
theorem chordCross_of_samePairing
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ κ' : F.RelTransitionSystem}
    (h : SamePairing κ κ')
    (b b' : {x : W.Flag // x ∈ F.boundaryFlags}) :
    ChordCross κ b b' ↔ ChordCross κ' b b' := by
  unfold ChordCross
  rw [h b.val b.prop, h b'.val b'.prop]

/-- **The crossing count is a pairing invariant.** -/
theorem chordCrossingCount_of_samePairing
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ κ' : F.RelTransitionSystem} (h : SamePairing κ κ') :
    chordCrossingCount κ = chordCrossingCount κ' := by
  unfold chordCrossingCount
  exact congrArg Finset.card (Finset.filter_congr
    (fun bb _ => chordCross_of_samePairing h bb.1 bb.2))

/-- **The path sign is a pairing invariant**: around any
pairing-returning block the chord signs cancel. -/
theorem pathSign_of_samePairing
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ κ' : F.RelTransitionSystem}
    (h : SamePairing κ κ') : pathSign κ = pathSign κ' :=
  congrArg (fun n => ((-1 : ℂ)) ^ n)
    (chordCrossingCount_of_samePairing h)

end EdgeSubset

end RS
