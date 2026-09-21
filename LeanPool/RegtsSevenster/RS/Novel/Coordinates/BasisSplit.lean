/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Super.ColourMergeOdd

/-!
# Basis vectors split over the merge

Coordinate basis vectors of a merged power decompose as merges
of half-basis pairs: even halves through the even pair, odd
halves through the odd pair.  The coordinate product rules of
both parities identify the coordinates; injectivity does the
rest.
-/

namespace RS

open scoped TensorProduct

variable {k ℓ : ℕ}

/-- The even coordinate basis vector at a colouring. -/
noncomputable def evenBasisVec {n : ℕ}
    (c : {c : MixedColouring k ℓ n // c.IsEven}) :
    (superPow (stdSuperPair k ℓ) n).even :=
  (colourPowerEquiv k ℓ n).evenEquiv.symm (Pi.single c 1)

/-- The odd coordinate basis vector at a colouring. -/
noncomputable def oddBasisVec {n : ℕ}
    (c : {c : MixedColouring k ℓ n // ¬ c.IsEven}) :
    (superPow (stdSuperPair k ℓ) n).odd :=
  (colourPowerEquiv k ℓ n).oddEquiv.symm (Pi.single c 1)

/-- Colourings are determined by their halves. -/
theorem MixedColouring.ext_halves {a b : ℕ}
    {c₁ c₂ : MixedColouring k ℓ (a + b)}
    (h1 : c₁.firstHalf = c₂.firstHalf)
    (h2 : c₁.secondHalf = c₂.secondHalf) : c₁ = c₂ :=
  funext (fun i => Fin.addCases
    (fun j => congrFun h1 j) (fun j => congrFun h2 j) i)

-- Raised budget: the basis vector is expanded through the merge on
-- both halves, so the colouring equivalence at three arities enters
-- the elaborated term.
/-- **Basis vectors split over the merge.** -/
theorem evenBasisVec_split {a b : ℕ}
    (c : MixedColouring k ℓ (a + b)) (hc : c.IsEven) :
    evenBasisVec (⟨c, hc⟩ :
      {c : MixedColouring k ℓ (a + b) // c.IsEven}) =
      if h : MixedColouring.IsEven c.firstHalf then
        ((powMerge (stdSuperPair k ℓ) a b) :
          SuperVect.Hom _ _).evenMap
          (evenPair (evenBasisVec ⟨c.firstHalf, h⟩)
            (evenBasisVec ⟨c.secondHalf,
              c.secondHalf_isEven hc h⟩))
      else
        ((powMerge (stdSuperPair k ℓ) a b) :
          SuperVect.Hom _ _).evenMap
          (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
              (superPow (stdSuperPair k ℓ) b).even),
            oddBasisVec ⟨c.firstHalf, h⟩ ⊗ₜ[ℂ]
              oddBasisVec ⟨c.secondHalf,
                c.secondHalf_not_isEven' hc h⟩) :
            (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
              (superPow (stdSuperPair k ℓ) b)).even) := by
  apply (colourPowerEquiv k ℓ (a + b)).evenEquiv.injective
  rw [show (colourPowerEquiv k ℓ (a + b)).evenEquiv
      (evenBasisVec (⟨c, hc⟩ :
        {c : MixedColouring k ℓ (a + b) // c.IsEven})) =
    Pi.single ⟨c, hc⟩ 1 from
    (colourPowerEquiv k ℓ (a + b)).evenEquiv.apply_symm_apply _]
  funext ⟨c', hc'⟩
  -- ═══════ THE FIRST HALF'S PARITY ═══════
  -- An even first half puts both halves in the even blocks, an odd
  -- one in the odd blocks; each is then checked coordinatewise.
  by_cases h : MixedColouring.IsEven c.firstHalf
  · rw [dif_pos h]
    rw [show ((colourPowerEquiv k ℓ (a + b)).evenEquiv
        (((powMerge (stdSuperPair k ℓ) a b) :
          SuperVect.Hom _ _).evenMap
          (evenPair (evenBasisVec ⟨c.firstHalf, h⟩)
            (evenBasisVec ⟨c.secondHalf,
              c.secondHalf_isEven hc h⟩)))) ⟨c', hc'⟩ =
      (if h' : MixedColouring.IsEven c'.firstHalf then
        (colourPowerEquiv k ℓ a).evenEquiv
          (evenBasisVec ⟨c.firstHalf, h⟩)
          ⟨c'.firstHalf, h'⟩ *
        (colourPowerEquiv k ℓ b).evenEquiv
          (evenBasisVec ⟨c.secondHalf,
            c.secondHalf_isEven hc h⟩)
          ⟨c'.secondHalf, c'.secondHalf_isEven hc' h'⟩
      else 0) from colourMerge_coord a b _ _ c' hc']
    by_cases h' : MixedColouring.IsEven c'.firstHalf
    · rw [dif_pos h']
      rw [show (colourPowerEquiv k ℓ a).evenEquiv
          (evenBasisVec ⟨c.firstHalf, h⟩) =
        Pi.single ⟨c.firstHalf, h⟩ 1 from
        (colourPowerEquiv k ℓ a).evenEquiv.apply_symm_apply _]
      rw [show (colourPowerEquiv k ℓ b).evenEquiv
          (evenBasisVec ⟨c.secondHalf,
            c.secondHalf_isEven hc h⟩) =
        Pi.single ⟨c.secondHalf,
          c.secondHalf_isEven hc h⟩ 1 from
        (colourPowerEquiv k ℓ b).evenEquiv.apply_symm_apply _]
      by_cases he : c' = c
      · subst he
        rw [single_val_same ⟨c', hc⟩ ⟨c', hc'⟩ rfl,
          single_val_same ⟨c'.firstHalf, h⟩
            ⟨c'.firstHalf, h'⟩ rfl,
          single_val_same ⟨c'.secondHalf,
              c'.secondHalf_isEven hc h⟩
            ⟨c'.secondHalf, c'.secondHalf_isEven hc' h'⟩ rfl]
        norm_num
      · rw [single_val_ne ⟨c, hc⟩ ⟨c', hc'⟩ he]
        by_cases hf : c'.firstHalf = c.firstHalf
        · have hs : c'.secondHalf ≠ c.secondHalf := fun hs2 =>
            he (MixedColouring.ext_halves hf hs2)
          rw [single_val_ne ⟨c.secondHalf,
              c.secondHalf_isEven hc h⟩
            ⟨c'.secondHalf, c'.secondHalf_isEven hc' h'⟩ hs]
          rw [mul_zero]
        · rw [single_val_ne ⟨c.firstHalf, h⟩
            ⟨c'.firstHalf, h'⟩ hf]
          rw [zero_mul]
    · rw [dif_neg h']
      have hne : c' ≠ c := fun he => h' (he ▸ h)
      rw [single_val_ne ⟨c, hc⟩ ⟨c', hc'⟩ hne]
  · rw [dif_neg h]
    rw [show ((colourPowerEquiv k ℓ (a + b)).evenEquiv
        (((powMerge (stdSuperPair k ℓ) a b) :
          SuperVect.Hom _ _).evenMap
          (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
              (superPow (stdSuperPair k ℓ) b).even),
            oddBasisVec ⟨c.firstHalf, h⟩ ⊗ₜ[ℂ]
              oddBasisVec ⟨c.secondHalf,
                c.secondHalf_not_isEven' hc h⟩) :
            (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
              (superPow (stdSuperPair k ℓ) b)).even))) ⟨c', hc'⟩ =
      (if h' : MixedColouring.IsEven c'.firstHalf then 0
      else
        (colourPowerEquiv k ℓ a).oddEquiv
          (oddBasisVec ⟨c.firstHalf, h⟩)
          ⟨c'.firstHalf, h'⟩ *
        (colourPowerEquiv k ℓ b).oddEquiv
          (oddBasisVec ⟨c.secondHalf,
            c.secondHalf_not_isEven' hc h⟩)
          ⟨c'.secondHalf,
            c'.secondHalf_not_isEven' hc' h'⟩) from
      colourMerge_coord_oddPair a b _ _ c' hc']
    by_cases h' : MixedColouring.IsEven c'.firstHalf
    · rw [dif_pos h']
      have hne : c' ≠ c := fun he => h (he ▸ h')
      rw [single_val_ne ⟨c, hc⟩ ⟨c', hc'⟩ hne]
    · rw [dif_neg h']
      rw [show (colourPowerEquiv k ℓ a).oddEquiv
          (oddBasisVec ⟨c.firstHalf, h⟩) =
        Pi.single ⟨c.firstHalf, h⟩ 1 from
        (colourPowerEquiv k ℓ a).oddEquiv.apply_symm_apply _]
      rw [show (colourPowerEquiv k ℓ b).oddEquiv
          (oddBasisVec ⟨c.secondHalf,
            c.secondHalf_not_isEven' hc h⟩) =
        Pi.single ⟨c.secondHalf,
          c.secondHalf_not_isEven' hc h⟩ 1 from
        (colourPowerEquiv k ℓ b).oddEquiv.apply_symm_apply _]
      by_cases he : c' = c
      · subst he
        rw [single_val_same ⟨c', hc⟩ ⟨c', hc'⟩ rfl,
          single_val_same ⟨c'.firstHalf, h⟩
            ⟨c'.firstHalf, h'⟩ rfl,
          single_val_same ⟨c'.secondHalf,
              c'.secondHalf_not_isEven' hc h⟩
            ⟨c'.secondHalf,
              c'.secondHalf_not_isEven' hc' h'⟩ rfl]
        norm_num
      · rw [single_val_ne ⟨c, hc⟩ ⟨c', hc'⟩ he]
        by_cases hf : c'.firstHalf = c.firstHalf
        · have hs : c'.secondHalf ≠ c.secondHalf := fun hs2 =>
            he (MixedColouring.ext_halves hf hs2)
          rw [single_val_ne ⟨c.secondHalf,
              c.secondHalf_not_isEven' hc h⟩
            ⟨c'.secondHalf,
              c'.secondHalf_not_isEven' hc' h'⟩ hs]
          rw [mul_zero]
        · rw [single_val_ne ⟨c.firstHalf, h⟩
            ⟨c'.firstHalf, h'⟩ hf]
          rw [zero_mul]

end RS
