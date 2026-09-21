/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.MultiStar

/-!
# The slot pairing

The flag enumeration sends the fragment pairing to the straight
cap matching: the two flags of the `i`-th canonical edge sit at
slots `i` and `edgeCount + i`.  The general-flag glue for the
Eulerian reindex.
-/

namespace RS

variable {α : Type} (W : ClosedFragment)

/-- The rep slot carries the canonical representative. -/
theorem starFlagEnum_symm_castAdd (i : Fin (edgeCount W)) :
    (starFlagEnum W).symm (Fin.castAdd (edgeCount W) i) =
      (canonicalReps W)[i.val]'(i.isLt) := by
  rw [_root_.Equiv.symm_apply_eq]
  exact (starEnum_rep W i.val i.isLt).symm

/-- The partner slot carries the paired flag. -/
theorem starFlagEnum_symm_natAdd (i : Fin (edgeCount W)) :
    (starFlagEnum W).symm (Fin.natAdd (edgeCount W) i) =
      W.pairing ((canonicalReps W)[i.val]'(i.isLt)) := by
  rw [_root_.Equiv.symm_apply_eq]
  exact (starEnum_partner W i.val i.isLt).symm

/-- **The slot pairing**: the fragment pairing links slot `i`
to slot `edgeCount + i`. -/
theorem pairing_starFlagEnum_symm (i : Fin (edgeCount W)) :
    W.pairing ((starFlagEnum W).symm
        (Fin.castAdd (edgeCount W) i)) =
      (starFlagEnum W).symm (Fin.natAdd (edgeCount W) i) := by
  rw [starFlagEnum_symm_castAdd, starFlagEnum_symm_natAdd]

end RS
