/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BraidWord

/-!
# Towards the matching cap

Left composition with a bundle-map class relabels the incoming
boundary: the class-level mirror of `bundleMapCompose`.  This is
the absorption step for permuted caps — composing a braiding word
into the strand-bundle cap yields the cap of the permuted
matching.
-/

namespace RS

variable {R : ℕ} (f : EdgeRankParameter R)

/-- Left composition with a bundle-map class relabels the
fragment along the incoming transport. -/
theorem bundleMapClass_comp_left {n m u : ℕ}
    (e : Fin n ≃ Fin m) (X : Fragment (Fin (m + u))) :
    HomSpace.comp f n m u (bundleMapClass f e)
        (HomSpace.ofFragment f.val X) =
      HomSpace.ofFragment f.val (X.relabel
        (finSumFinEquiv.symm.trans
          ((_root_.Equiv.sumCongr e.symm
            (_root_.Equiv.refl (Fin u))).trans
            finSumFinEquiv))) := by
  rw [bundleMapClass, HomSpace.comp_ofFragment]
  exact HomSpace.ofFragment_congr f (bundleMapCompose e X)

end RS
