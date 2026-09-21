/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Super.ColourConjTop
import LeanPool.RegtsSevenster.RS.Classical.Super.ColourConjStep

/-!
# The colour action of the model braidings

Assembling the three conjugation laws: the adjacent model
braiding acts on the colouring model as the Koszul-signed
adjacent swap, positionwise and wordwise.
-/

namespace RS

open CategoryTheory MonoidalCategory

variable {k ℓ : ℕ}

/-- **The colour action**: conjugating the adjacent braiding into
the colouring model is the Koszul-signed adjacent swap. -/
theorem toColour_powBraid :
    ∀ (n i : ℕ) (h : i + 2 ≤ n),
      toColour (k := k) (ℓ := ℓ) n
          (powBraid (stdSuperPair k ℓ) n i h) =
        colourSwap k ℓ n i h
  | 0, _, h => absurd h (by omega)
  | 1, _, h => absurd h (by omega)
  | n + 2, i, h => by
    by_cases hi : i = n
    · rw [show powBraid (stdSuperPair k ℓ) (n + 2) i h =
          topBraid (stdSuperPair k ℓ) n from dif_pos hi]
      rw [toColour_topBraid]
      subst hi
      rfl
    · have hle : i + 2 ≤ n + 1 := by omega
      rw [show powBraid (stdSuperPair k ℓ) (n + 2) i h =
          (powBraid (stdSuperPair k ℓ) (n + 1) i hle) ▷
            stdSuperPair k ℓ from dif_neg hi]
      rw [toColour_whisker]
      rw [toColour_powBraid (n + 1) i hle]
      rw [colourExtend_colourSwap]

/-- **The wordwise colour action.** -/
theorem toColour_powBraidWord {n : ℕ} (w : List (Fin n)) :
    toColour (k := k) (ℓ := ℓ) (n + 1)
        (powBraidWord (stdSuperPair k ℓ) w) =
      colourSwapWord k ℓ w := by
  induction w with
  | nil => exact toColour_id (n + 1)
  | cons i w ih =>
    show toColour (n + 1) (powBraidWord (stdSuperPair k ℓ) w ≫
      powBraid (stdSuperPair k ℓ) (n + 1) i.val (by omega)) = _
    rw [toColour_comp, ih, toColour_powBraid]
    rfl

end RS
