/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.EvLeaf

/-!
# The cap value in coordinates

The cap value of an even vector is the coordinate-weighted sum of
the cap values of the colour basis vectors: linearity through the
coordinate expansion.
-/

@[expose] public section

namespace RS

variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}
variable (e : stdSuperPair k ℓ ⟶ P.ω.obj (SkeinObj.mk 1))

/-- **The cap value in coordinates.** -/
theorem capVal_expansion (m : ℕ)
    (v : (superPow (stdSuperPair k ℓ) (m + m)).even) :
    capVal f P e m v =
      ∑ c : {c : MixedColouring k ℓ (m + m) // c.IsEven},
        coordOf v c.val * capVal f P e m (evenBasisVec c) := by
  conv_lhs => rw [coord_expansion v]
  rw [capVal_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [capVal_smul]
  rw [show coordOf v c.val =
      (colourPowerEquiv k ℓ (m + m)).evenEquiv v c from by
    unfold coordOf
    rw [dite_eq_left c.prop]]
  rfl

end RS
