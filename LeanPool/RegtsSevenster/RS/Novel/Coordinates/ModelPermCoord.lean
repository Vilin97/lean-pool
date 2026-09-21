/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Super.ColourAction
import LeanPool.RegtsSevenster.RS.Classical.Super.WordSignPerm

/-!
# The permutation transport in coordinates

The model permutation map acts on coordinates by the adjacent-word
sign and the permutation reindex.
-/

open CategoryTheory

namespace RS

variable {k ℓ : ℕ}

/-- The word of adjacent transpositions composes to its
permutation. -/
theorem wordPerm_eq_prod {n : ℕ} (w : List (Fin n)) :
    wordPerm w = (w.map adjTrans).prod := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    show _root_.Equiv.swap _ _ * wordPerm w = _
    rw [List.map_cons, List.prod_cons, ih]
    rfl

/-- The adjacent word composes to its permutation. -/
theorem wordPerm_adjWord {n : ℕ}
    (σ : _root_.Equiv.Perm (Fin (n + 1))) :
    wordPerm (adjWord σ) = σ := by
  rw [wordPerm_eq_prod]
  exact adjWord_spec σ

/-- **The permutation transport in coordinates.** -/
theorem coordOf_modelPermMap {n : ℕ}
    (σ : _root_.Equiv.Perm (Fin (n + 1)))
    (v : (superPow (stdSuperPair k ℓ) (n + 1)).even)
    (c : MixedColouring k ℓ (n + 1)) :
    coordOf (((modelPermMap σ) :
        SuperVect.Hom _ _).evenMap v) c =
      wordSign (adjWord σ) c * coordOf v (c ∘ σ) := by
  by_cases hc : c.IsEven
  · rw [show coordOf (((modelPermMap σ) :
        SuperVect.Hom _ _).evenMap v) c =
      (colourPowerEquiv k ℓ (n + 1)).evenEquiv
        (((modelPermMap σ) :
          SuperVect.Hom _ _).evenMap v) ⟨c, hc⟩ from by
      unfold coordOf; rw [dif_pos hc]]
    rw [← toColour_apply]
    rw [show modelPermMap σ =
      powBraidWord (stdSuperPair k ℓ) (adjWord σ) from rfl]
    rw [toColour_powBraidWord]
    rw [colourSwapWord_evenMap]
    rw [wordPerm_adjWord]
    rw [show coordOf v (c ∘ σ) =
      (colourPowerEquiv k ℓ (n + 1)).evenEquiv v
        ⟨c ∘ σ, hc.comp σ⟩ from by
      unfold coordOf; rw [dif_pos (hc.comp σ)]]
  · rw [coordOf_odd _ _ hc]
    have hcσ : ¬ MixedColouring.IsEven (c ∘ σ) := fun he => hc
      (by
        have hcomp := he.comp σ⁻¹
        rw [show (c ∘ σ) ∘ (σ⁻¹ :
            _root_.Equiv.Perm (Fin (n + 1))) = c from
          funext (fun x => congrArg c
            (_root_.Equiv.apply_symm_apply σ x))] at hcomp
        exact hcomp)
    rw [coordOf_odd _ _ hcσ, mul_zero]

/-- **The permutation transport in coordinates, arity-uniform
form**: the sign is the odd-inversion sign, valid at every arity
including zero. -/
theorem coordOf_modelPermMap' {n : ℕ}
    (σ : _root_.Equiv.Perm (Fin n))
    (v : (superPow (stdSuperPair k ℓ) n).even)
    (c : MixedColouring k ℓ n) :
    coordOf (((modelPermMap σ) :
        SuperVect.Hom _ _).evenMap v) c =
      (-1 : ℂ) ^ oddInversions σ c * coordOf v (c ∘ σ) := by
  match n, σ with
  | 0, σ =>
    rw [show σ = (1 : _root_.Equiv.Perm (Fin 0)) from
      Subsingleton.elim _ _]
    rw [show modelPermMap (1 : _root_.Equiv.Perm (Fin 0)) =
      𝟙 (superPow (stdSuperPair k ℓ) 0) from rfl]
    rw [show (((𝟙 (superPow (stdSuperPair k ℓ) 0) :
        superPow (stdSuperPair k ℓ) 0 ⟶ _)) :
      SuperVect.Hom _ _).evenMap v = v from rfl]
    rw [show oddInversions (1 : _root_.Equiv.Perm (Fin 0)) c =
      0 from by simp [oddInversions]]
    rw [pow_zero, one_mul]
    exact congrArg (coordOf v) (funext (fun x => x.elim0))
  | n + 1, σ =>
    rw [coordOf_modelPermMap σ v c]
    rw [wordSign_eq_oddInversions]
    rw [wordPerm_adjWord]

end RS
