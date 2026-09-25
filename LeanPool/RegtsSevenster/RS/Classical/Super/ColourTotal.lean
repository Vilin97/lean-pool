/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Super.TotalSpace
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ModelPermCoord

/-!
# The total colouring coordinates

Combining the even and odd coordinate functions identifies the total
tensor space with all functions on colour words. The model permutation
acts there by reindexing and its odd-inversion sign.
-/

@[expose] public section

namespace RS

open CategoryTheory

noncomputable section

variable {k ℓ n : ℕ}

/-- Splitting a colour function into its even and odd restrictions. -/
def colourSplit (k ℓ n : ℕ) :
    (MixedColouring k ℓ n → ℂ) ≃ₗ[ℂ] Tot (colourPower k ℓ n) where
  __ := Equiv.piEquivPiSubtypeProd MixedColouring.IsEven (fun _ => ℂ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The total tensor space in coordinates indexed by all colour words. -/
def colourTotalEquiv (k ℓ n : ℕ) :
    Tot (superPow (stdSuperPair k ℓ) n) ≃ₗ[ℂ]
      (MixedColouring k ℓ n → ℂ) :=
  ((colourPowerEquiv k ℓ n).evenEquiv.prodCongr
    (colourPowerEquiv k ℓ n).oddEquiv).trans (colourSplit k ℓ n).symm

private theorem colourSplit_symm_apply
    (v : Tot (colourPower k ℓ n)) (c : MixedColouring k ℓ n) :
    (colourSplit k ℓ n).symm v c =
      if hc : c.IsEven then v.1 ⟨c, hc⟩ else v.2 ⟨c, hc⟩ := rfl

private theorem colourTotalEquiv_conj
    (g : superPow (stdSuperPair k ℓ) n ⟶
      superPow (stdSuperPair k ℓ) n)
    (v : MixedColouring k ℓ n → ℂ) :
    colourTotalEquiv k ℓ n
      (tot g ((colourTotalEquiv k ℓ n).symm v)) =
    (colourSplit k ℓ n).symm
      (tot (toColour n g) (colourSplit k ℓ n v)) := rfl

/-- The total model action has the Koszul monomial coordinates at
every arity, including arity zero. -/
theorem colourTotalEquiv_modelPermMap
    (σ : _root_.Equiv.Perm (Fin n))
    (v : MixedColouring k ℓ n → ℂ) (c : MixedColouring k ℓ n) :
    colourTotalEquiv k ℓ n
      (tot (modelPermMap σ) ((colourTotalEquiv k ℓ n).symm v)) c =
      (-1 : ℂ) ^ oddInversions σ c * v (c ∘ σ) := by
  cases n with
  | zero =>
    have hσ : σ = 1 := Subsingleton.elim _ _
    subst σ
    rw [show modelPermMap (1 : _root_.Equiv.Perm (Fin 0)) =
      𝟙 (superPow (stdSuperPair k ℓ) 0) from rfl, tot_id]
    simp [oddInversions]
  | succ n =>
    rw [colourTotalEquiv_conj]
    change (colourSplit k ℓ (n + 1)).symm
      (tot (toColour (n + 1)
        (powBraidWord (stdSuperPair k ℓ) (adjWord σ)))
          (colourSplit k ℓ (n + 1) v)) c = _
    rw [toColour_powBraidWord, colourSplit_symm_apply]
    by_cases hc : c.IsEven
    · rw [dite_eq_left hc]
      change (colourSwapWord k ℓ (adjWord σ)).evenMap
        (fun a => v a.val) ⟨c, hc⟩ = _
      erw [colourSwapWord_evenMap, wordSign_eq_oddInversions,
        wordPerm_adjWord]
    · rw [dite_eq_right hc]
      change (colourSwapWord k ℓ (adjWord σ)).oddMap
        (fun a => v a.val) ⟨c, hc⟩ = _
      erw [colourSwapWord_oddMap, wordSign_eq_oddInversions,
        wordPerm_adjWord]

end

end RS
