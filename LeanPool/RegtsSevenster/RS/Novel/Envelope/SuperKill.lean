/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Envelope.SkeinDimBound
import LeanPool.RegtsSevenster.RS.Classical.Interfaces.OmegaTensorPower

/-!
# Square death at the super level

The kill chain: vanishing under the skein representation
propagates through the fibre functor to the conjugated super
permutation action, and in particular the square block idempotent
at any side `s > 2eR` dies at the super level — the unconditional
half of the sector dichotomy.
-/

namespace RS

variable {R : ℕ} (f : EdgeRankParameter R)
  (P : DelignePackage (SkeinObj f))

/-- **The kill chain**: vanishing under the skein representation
propagates to the super permutation action. -/
theorem skeinRep_zero_imp_superPermAction_zero (n : ℕ)
    (x : SymGroupAlgebra n) (hx : skeinRep f n x = 0) :
    superPermAction f P n x = 0 := by
  letI := P.additive
  letI := P.linear
  rw [superPermAction_eq_zero_iff, omegaSkeinRep_eq, hx]
  exact P.ω.map_zero _ _

/-- **Square death at the super level**: at any side `s > 2eR` the
super permutation action kills the square block idempotent. -/
theorem superPermAction_square_dead {s : ℕ}
    (hs : 2 * Real.exp 1 * R < s) :
    superPermAction f P (squareDiagram s).card
      (charIdempotent (nDim (jtSimple (squareDiagram s)))
        (jtChar (squareDiagram s))) = 0 :=
  skeinRep_zero_imp_superPermAction_zero f P _ _
    (skeinRep_square_dead f hs)

end RS
