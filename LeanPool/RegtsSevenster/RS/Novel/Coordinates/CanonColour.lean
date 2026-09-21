/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.StarSymm

/-!
# The canonical colouring of multiset data

A multiset of even colours and a set of odd colours assemble
into a canonical colouring: sorted even colours first, sorted
odd colours after.  This is the representative through which the
vertex functional of Definition 5 evaluates the symmetric star
coordinates.
-/

namespace RS

variable {k ℓ : ℕ}

/-- The canonical colouring: sorted even colours, then sorted
odd colours. -/
noncomputable def canonColouring (μm : Multiset (Fin k))
    (F : Finset (Fin (2 * ℓ))) :
    MixedColouring k ℓ (μm.card + F.card) := fun i =>
  if h : i.val < μm.card then
    Sum.inl ((μm.sort (· ≤ ·)).get ⟨i.val, by
      rw [Multiset.length_sort]; exact h⟩)
  else
    Sum.inr ((F.sort (· ≤ ·)).get ⟨i.val - μm.card, by
      rw [Finset.length_sort]
      have := i.isLt
      omega⟩)

/-- Low positions are even colours. -/
theorem canonColouring_isRight_low (μm : Multiset (Fin k))
    (F : Finset (Fin (2 * ℓ)))
    (i : Fin (μm.card + F.card)) (h : i.val < μm.card) :
    (canonColouring μm F i).isRight = false := by
  unfold canonColouring
  rw [dif_pos h]
  rfl

/-- High positions are odd colours. -/
theorem canonColouring_isRight_high (μm : Multiset (Fin k))
    (F : Finset (Fin (2 * ℓ)))
    (i : Fin (μm.card + F.card)) (h : ¬ i.val < μm.card) :
    (canonColouring μm F i).isRight = true := by
  unfold canonColouring
  rw [dif_neg h]
  rfl

end RS
