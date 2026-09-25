/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.CrossingDelta

/-!
# The four-label parity identities

The per-step sign parity of the canonical-route ledger reduces to two
pure order-combinatorics identities on four distinct labels: `x`, `xb`
(old partners) and `y`, `yb` (old partners), the step re-pairing to
the new chords `{x, y}` and `{xb, yb}`.  The canonical direction at a
`u`-end is "`u`'s old partner `< u`", and the step is separated
exactly when the directions at the `x`-end and the `y`-end differ.
In the separated case the two anti-canonicality indicators of the new
chords (each read at its recorded end) plus the step's intrinsic sign
match the crossing change mod 2; in the non-separated case the
`y`-side directions are toggled by the anchor flip, whose own flip
cancels the intrinsic sign, leaving the bare toggled count.

Both identities are pure order case-bashes: six `Ne.lt_or_lt` splits,
transitivity pruning of the intransitive tournaments (a tournament on
four vertices is transitive iff it has no directed triangle), and a
uniform decision of all indicators from the six resolved comparisons.
-/

@[expose] public section

/- the closing `simp` argument list is shared by all 64 order
branches, and each branch uses a different subset of it -/

namespace RS



variable {α : Type}

/-- **The separated four-label parity identity**: when the canonical
directions at the `x`-end and the `y`-end differ, the two
anti-canonicality indicators of the new chords plus the intrinsic
sign of the step match, mod 2, the crossing change of the re-paired
chords. -/
theorem fourLabel_parity_sep [LinearOrder α]
    {x xb y yb : α}
    (hxxb : x ≠ xb) (hyyb : y ≠ yb) (hxy : x ≠ y) (hxyb : x ≠ yb)
    (hxby : xb ≠ y) (hxbyb : xb ≠ yb)
    (hsep : (xb < x) ≠ (yb < y)) :
    ((if (if x < y then xb < x else yb < y) then 1 else 0) +
      (if (if xb < yb then x < xb else y < yb) then 1 else 0) +
      1) % 2 =
    ((if chordPairCrossSym (x, xb) (y, yb) then 1 else 0) +
      (if chordPairCrossSym (x, y) (xb, yb) then 1 else 0)) % 2 := by
  rcases lt_or_gt_of_ne hxxb with h1 | h1 <;>
    rcases lt_or_gt_of_ne hyyb with h2 | h2 <;>
    rcases lt_or_gt_of_ne hxy with h3 | h3 <;>
    rcases lt_or_gt_of_ne hxyb with h4 | h4 <;>
    rcases lt_or_gt_of_ne hxby with h5 | h5 <;>
    rcases lt_or_gt_of_ne hxbyb with h6 | h6 <;>
    first
    | exact absurd (lt_trans h1 h5) (lt_asymm h3)
    | exact absurd (lt_trans h3 h5) (lt_asymm h1)
    | exact absurd (lt_trans h1 h6) (lt_asymm h4)
    | exact absurd (lt_trans h4 h6) (lt_asymm h1)
    | exact absurd (lt_trans h3 h2) (lt_asymm h4)
    | exact absurd (lt_trans h4 h2) (lt_asymm h3)
    | exact absurd (lt_trans h5 h2) (lt_asymm h6)
    | exact absurd (lt_trans h6 h2) (lt_asymm h5)
    | exact absurd (propext (iff_of_false (lt_asymm h1) (lt_asymm h2)))
        hsep
    | exact absurd (propext (iff_of_true h1 h2)) hsep
    | simp [chordPairCrossSym, ChordPairCross,
        gt_iff_lt.mp h1, gt_iff_lt.mp h2, gt_iff_lt.mp h3,
        gt_iff_lt.mp h4, gt_iff_lt.mp h5, gt_iff_lt.mp h6,
        le_of_lt h1, le_of_lt h2, le_of_lt h3,
        le_of_lt h6,
        lt_asymm h1, lt_asymm h2, lt_asymm h3, lt_asymm h4,
        lt_asymm h5, lt_asymm h6]

/-- **The non-separated four-label parity identity**: when the
canonical directions at the `x`-end and the `y`-end agree, the
anchor flip toggles the `y`-side directions and cancels the
intrinsic sign, so the bare toggled anti-canonicality count matches,
mod 2, the crossing change of the re-paired chords. -/
theorem fourLabel_parity_nonsep [LinearOrder α]
    {x xb y yb : α}
    (hxxb : x ≠ xb) (hyyb : y ≠ yb) (hxy : x ≠ y) (hxyb : x ≠ yb)
    (hxby : xb ≠ y) (hxbyb : xb ≠ yb)
    (hsame : (xb < x) = (yb < y)) :
    ((if (if x < y then xb < x else ¬ (yb < y)) then 1 else 0) +
      (if (if xb < yb then x < xb else ¬ (y < yb)) then 1 else 0)) % 2 =
    ((if chordPairCrossSym (x, xb) (y, yb) then 1 else 0) +
      (if chordPairCrossSym (x, y) (xb, yb) then 1 else 0)) % 2 := by
  rcases lt_or_gt_of_ne hxxb with h1 | h1 <;>
    rcases lt_or_gt_of_ne hyyb with h2 | h2 <;>
    rcases lt_or_gt_of_ne hxy with h3 | h3 <;>
    rcases lt_or_gt_of_ne hxyb with h4 | h4 <;>
    rcases lt_or_gt_of_ne hxby with h5 | h5 <;>
    rcases lt_or_gt_of_ne hxbyb with h6 | h6 <;>
    first
    | exact absurd (lt_trans h1 h5) (lt_asymm h3)
    | exact absurd (lt_trans h3 h5) (lt_asymm h1)
    | exact absurd (lt_trans h1 h6) (lt_asymm h4)
    | exact absurd (lt_trans h4 h6) (lt_asymm h1)
    | exact absurd (lt_trans h3 h2) (lt_asymm h4)
    | exact absurd (lt_trans h4 h2) (lt_asymm h3)
    | exact absurd (lt_trans h5 h2) (lt_asymm h6)
    | exact absurd (lt_trans h6 h2) (lt_asymm h5)
    | exact absurd (cast hsame.symm h2) (lt_asymm h1)
    | exact absurd (cast hsame h1) (lt_asymm h2)
    | simp [chordPairCrossSym, ChordPairCross,
        gt_iff_lt.mp h1, gt_iff_lt.mp h2, gt_iff_lt.mp h3,
        gt_iff_lt.mp h4, gt_iff_lt.mp h5, gt_iff_lt.mp h6,
        le_of_lt h1, le_of_lt h2, le_of_lt h3,
        le_of_lt h6,
        lt_asymm h1, lt_asymm h2, lt_asymm h3, lt_asymm h4,
        lt_asymm h5, lt_asymm h6]

end RS
