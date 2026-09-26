/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CoordOf
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BasisSplit

/-!
# Coordinates of basis vectors

The coordinate of a colour basis vector is the equality
indicator: the coordinate calculus closes on basis input.
-/

@[expose] public section

namespace RS

variable {k ℓ : ℕ}

/-- **The basis coordinate indicator.** -/
theorem coordOf_evenBasisVec {n : ℕ}
    (c : MixedColouring k ℓ n) (hc : c.IsEven)
    (c' : MixedColouring k ℓ n) :
    coordOf (evenBasisVec (⟨c, hc⟩ :
        {c : MixedColouring k ℓ n // c.IsEven})) c' =
      if c' = c then 1 else 0 := by
  by_cases hc' : c'.IsEven
  · rw [show coordOf (evenBasisVec (⟨c, hc⟩ :
        {c : MixedColouring k ℓ n // c.IsEven})) c' =
      (colourPowerEquiv k ℓ n).evenEquiv
        (evenBasisVec ⟨c, hc⟩) ⟨c', hc'⟩ from by
      unfold coordOf; rw [dite_eq_left hc']]
    rw [show (colourPowerEquiv k ℓ n).evenEquiv
        (evenBasisVec (⟨c, hc⟩ :
          {c : MixedColouring k ℓ n // c.IsEven})) =
      Pi.single ⟨c, hc⟩ 1 from
      (colourPowerEquiv k ℓ n).evenEquiv.apply_symm_apply _]
    by_cases he : c' = c
    · subst he
      rw [ite_eq_left rfl]
      exact Pi.single_eq_same _ _
    · rw [ite_eq_right he]
      exact Pi.single_eq_of_ne
        (fun h => he (congrArg Subtype.val h)) _
  · rw [coordOf_odd _ _ hc']
    rw [ite_eq_right (fun he : c' = c => hc' (he ▸ hc))]

/-- The arity-zero basis vector is the unit scalar. -/
theorem evenBasisVec_zeroArity
    (x : {c : MixedColouring k ℓ 0 // c.IsEven}) :
    evenBasisVec x = (1 : ℂ) := by
  apply (colourPowerEquiv k ℓ 0).evenEquiv.injective
  rw [show (colourPowerEquiv k ℓ 0).evenEquiv
      (evenBasisVec x) = Pi.single x 1 from
    (colourPowerEquiv k ℓ 0).evenEquiv.apply_symm_apply _]
  funext y
  rw [Subsingleton.elim y x, Pi.single_eq_same]
  rfl

end RS
