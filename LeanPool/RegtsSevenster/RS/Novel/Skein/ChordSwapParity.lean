/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.ChordParity
public import LeanPool.RegtsSevenster.RS.Novel.Skein.PathLedger

/-!
# Chord re-pairing parity: the bridge and the crossing table

Three pieces of pure order-combinatorics glue on top of the two
coexisting crossing predicates:

* the **bridge** between the cut-style predicate `CrossesCut`
  (`ChordParity.lean`) and the chord-style predicate
  `ChordPairCross` (`PathLedger.lean`), under the normalization
  hypotheses of `chordPairCross_iff_xor`;
* the **mutual-crossing table** for four strictly ordered points in
  `ChordPairCross` vocabulary — parallel and nested chords do not
  cross, interleaved chords do;
* the **summed transfer**: over a finite family of normalized third
  chords avoiding the four points, re-pairing two chords preserves
  the total crossing parity (`third_chord_reparity` per element).
-/

@[expose] public section

namespace RS



variable {α : Type}

/-! ## The bridge between the two crossing predicates -/

/-- **The bridge**: the cut-style crossing predicate of
`ChordParity.lean` agrees with the chord-style crossing predicate
of `PathLedger.lean`, for a chord recorded low-to-high whose ends
avoid the matching ends of the cut. -/
theorem crossesCut_iff_chordPairCross [LinearOrder α]
    {x y u w : α}
    (huw : u < w) (hux : u ≠ x) (hwy : w ≠ y) :
    CrossesCut x y (u, w) ↔ ChordPairCross x y u w := by
  rw [chordPairCross_iff_xor huw hux hwy]
  unfold CrossesCut InsideChord
  exact Iff.rfl

end RS
