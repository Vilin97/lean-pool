/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OneBasis

/-!
# Two-position basis vectors, raw form

The colour-model basis vectors at two positions in the raw tensor
structure `(superPow V 1) ⊗ V`: nested unit-padded standard basis
vectors, one lemma per parity pattern.
-/

namespace RS

open scoped TensorProduct

variable {k ℓ : ℕ}

/-- The forward even split, even last colour. -/
theorem evenSplitD_inl {d : ℕ}
    (c : MixedColouring k ℓ (d + 1)) (hc : c.IsEven) (i : Fin k)
    (hi : c (Fin.last d) = Sum.inl i) :
    evenSplitEquiv k ℓ d ⟨c, hc⟩ =
      Sum.inl (⟨MixedColouring.tail c,
        (c.isEven_succ_left i hi).mp hc⟩, i) := by
  have inv : (evenSplitEquiv k ℓ d).symm
      (Sum.inl (⟨MixedColouring.tail c,
        (c.isEven_succ_left i hi).mp hc⟩, i)) = ⟨c, hc⟩ := by
    apply Subtype.ext
    rw [evenSplitEquiv_symm_inl]
    funext j
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · exact (colouringSplit_symm_last _ _).trans hi.symm
    · exact colouringSplit_symm_castSucc _ _ j'
  rw [← inv, Equiv.apply_symm_apply]

/-- The forward even split, odd last colour. -/
theorem evenSplitD_inr {d : ℕ}
    (c : MixedColouring k ℓ (d + 1)) (hc : c.IsEven)
    (b : Fin (2 * ℓ)) (hb : c (Fin.last d) = Sum.inr b) :
    evenSplitEquiv k ℓ d ⟨c, hc⟩ =
      Sum.inr (⟨MixedColouring.tail c, by
        by_contra hcontra
        exact ((c.isEven_succ_right b hb).mp hc) hcontra⟩,
        b) := by
  have inv : (evenSplitEquiv k ℓ d).symm
      (Sum.inr (⟨MixedColouring.tail c, by
        by_contra hcontra
        exact ((c.isEven_succ_right b hb).mp hc) hcontra⟩,
        b)) = ⟨c, hc⟩ := by
    apply Subtype.ext
    rw [evenSplitEquiv_symm_inr]
    funext j
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · exact (colouringSplit_symm_last _ _).trans hb.symm
    · exact colouringSplit_symm_castSucc _ _ j'
  rw [← inv, Equiv.apply_symm_apply]

/-- The forward odd split, odd last colour. -/
theorem oddSplitD_inr {d : ℕ}
    (c : MixedColouring k ℓ (d + 1)) (hc : ¬ c.IsEven)
    (b : Fin (2 * ℓ)) (hb : c (Fin.last d) = Sum.inr b) :
    oddSplitEquiv k ℓ d ⟨c, hc⟩ =
      Sum.inr (⟨MixedColouring.tail c, by
        by_contra hcontra
        exact hc ((c.isEven_succ_right b hb).mpr hcontra)⟩,
        b) := by
  have inv : (oddSplitEquiv k ℓ d).symm
      (Sum.inr (⟨MixedColouring.tail c, by
        by_contra hcontra
        exact hc ((c.isEven_succ_right b hb).mpr hcontra)⟩,
        b)) = ⟨c, hc⟩ := by
    apply Subtype.ext
    rw [oddSplitEquiv_symm_inr]
    funext j
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · exact (colouringSplit_symm_last _ _).trans hb.symm
    · exact colouringSplit_symm_castSucc _ _ j'
  rw [← inv, Equiv.apply_symm_apply]

/-- The forward odd split, even last colour. -/
theorem oddSplitD_inl {d : ℕ}
    (c : MixedColouring k ℓ (d + 1)) (hc : ¬ c.IsEven)
    (i : Fin k) (hi : c (Fin.last d) = Sum.inl i) :
    oddSplitEquiv k ℓ d ⟨c, hc⟩ =
      Sum.inl (⟨MixedColouring.tail c, by
        intro hcontra
        exact hc ((c.isEven_succ_left i hi).mpr hcontra)⟩,
        i) := by
  have inv : (oddSplitEquiv k ℓ d).symm
      (Sum.inl (⟨MixedColouring.tail c, by
        intro hcontra
        exact hc ((c.isEven_succ_left i hi).mpr hcontra)⟩,
        i)) = ⟨c, hc⟩ := by
    apply Subtype.ext
    rw [oddSplitEquiv_symm_inl]
    funext j
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · exact (colouringSplit_symm_last _ _).trans hi.symm
    · exact colouringSplit_symm_castSucc _ _ j'
  rw [← inv, Equiv.apply_symm_apply]

end RS
