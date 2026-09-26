/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Super.ColourMerge

/-!
# The merge coordinate product rule, odd input

Coordinates of a merged odd-even pair multiply over the halves,
vanishing when the first half has even parity — the odd-input
counterpart of `ColourMerge.lean`, whose split-equivalence,
tensor-step and right-hand-side helpers it shares.

The four chain reductions run on the four parity patterns of a
pure tensor, and the two parts of `colourMerge_pair_odd` are
proved by one mutual induction on the second arity.
-/

@[expose] public section

open scoped TensorProduct

namespace RS

open CategoryTheory MonoidalCategory

/-! ### Parity helpers for the odd input -/

/-- When the whole is even and the first half is odd,
the second half is odd. -/
theorem MixedColouring.secondHalf_not_isEven' {k ℓ a b : ℕ}
    (c : MixedColouring k ℓ (a + b)) (hc : c.IsEven)
    (h : ¬ c.firstHalf.IsEven) : ¬ c.secondHalf.IsEven :=
  mt (c.isEven_half_iff hc).mpr h

private theorem MixedColouring.secondHalf_isEven_of_not {k ℓ a b : ℕ}
    (c : MixedColouring k ℓ (a + b)) (hc : ¬ c.IsEven)
    (h : ¬ c.firstHalf.IsEven) : c.secondHalf.IsEven := by
  by_contra hs
  apply hc
  unfold MixedColouring.IsEven
  rw [MixedColouring.oddSet_card_split]
  exact Nat.even_add.mpr (Iff.intro (fun hf => absurd hf h) (fun hs' => absurd
    hs' hs))

private theorem assoc_inv_odd_oe_ee_tmul {k ℓ a b : ℕ}
    (x : (superPow (stdSuperPair k ℓ) a).odd)
    (w₁ : (superPow (stdSuperPair k ℓ) b).even)
    (x₁ : (stdSuperPair k ℓ).even) :
    (((α_ (superPow (stdSuperPair k ℓ) a) (superPow (stdSuperPair k ℓ) b)
        (stdSuperPair k ℓ)).inv : SuperVect.Hom _ _).oddMap
      (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
            (stdSuperPair k ℓ)).odd),
        x ⊗ₜ[ℂ] ((w₁ ⊗ₜ[ℂ] x₁,
          (0 : (superPow (stdSuperPair k ℓ) b).odd ⊗[ℂ]
            (stdSuperPair k ℓ).odd)) :
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b) (stdSuperPair k
            ℓ)).even)) :
        (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b) (stdSuperPair k
            ℓ))).odd)) =
    (((0 : (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
        (superPow (stdSuperPair k ℓ) b)).even ⊗[ℂ] (stdSuperPair k ℓ).odd),
      (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
          (superPow (stdSuperPair k ℓ) b).odd),
        x ⊗ₜ[ℂ] w₁) ⊗ₜ[ℂ] x₁)) :
      (SuperVect.tensorObj (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
        (superPow (stdSuperPair k ℓ) b)) (stdSuperPair k ℓ)).odd) := by
  change (SuperVect.assocAux _ _ _ _ _ _).symm
      (((0 : _), x ⊗ₜ[ℂ] ((w₁ ⊗ₜ[ℂ] x₁, (0 : _)) : _)) : _) = _
  exact SuperVect.assocAux_symm_oe x w₁ x₁

/-- The associator inverse oddMap on an oe-oo tensor:
`α⁻¹.oddMap (0, x ⊗ₜ (0, w₂ ⊗ₜ x₂))`. -/
private theorem assoc_inv_odd_oe_oo_tmul {k ℓ a b : ℕ}
    (x : (superPow (stdSuperPair k ℓ) a).odd)
    (w₂ : (superPow (stdSuperPair k ℓ) b).odd)
    (x₂ : (stdSuperPair k ℓ).odd) :
    (((α_ (superPow (stdSuperPair k ℓ) a) (superPow (stdSuperPair k ℓ) b)
        (stdSuperPair k ℓ)).inv : SuperVect.Hom _ _).oddMap
      (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
            (stdSuperPair k ℓ)).odd),
        x ⊗ₜ[ℂ] (((0 : (superPow (stdSuperPair k ℓ) b).even ⊗[ℂ]
            (stdSuperPair k ℓ).even),
          w₂ ⊗ₜ[ℂ] x₂) :
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b) (stdSuperPair k
            ℓ)).even)) :
        (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b) (stdSuperPair k
            ℓ))).odd)) =
    ((((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
          (superPow (stdSuperPair k ℓ) b).even),
        x ⊗ₜ[ℂ] w₂) ⊗ₜ[ℂ] x₂,
      (0 : (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
        (superPow (stdSuperPair k ℓ) b)).odd ⊗[ℂ] (stdSuperPair k ℓ).even)) :
      (SuperVect.tensorObj (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
        (superPow (stdSuperPair k ℓ) b)) (stdSuperPair k ℓ)).odd) := by
  change (SuperVect.assocAux _ _ _ _ _ _).symm
      (((0 : _), x ⊗ₜ[ℂ] (((0 : _), w₂ ⊗ₜ[ℂ] x₂) : _)) : _) = _
  exact SuperVect.assocAux_symm_oo x w₂ x₂

/-- The associator inverse evenMap on an oe-eo tensor:
`α⁻¹.evenMap (0, x ⊗ₜ (w₁ ⊗ₜ x₂, 0))`. -/
private theorem assoc_inv_even_oe_eo_tmul {k ℓ a b : ℕ}
    (x : (superPow (stdSuperPair k ℓ) a).odd)
    (w₁ : (superPow (stdSuperPair k ℓ) b).even)
    (x₂ : (stdSuperPair k ℓ).odd) :
    (((α_ (superPow (stdSuperPair k ℓ) a) (superPow (stdSuperPair k ℓ) b)
        (stdSuperPair k ℓ)).inv : SuperVect.Hom _ _).evenMap
      (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b) (stdSuperPair k
            ℓ)).even),
        x ⊗ₜ[ℂ] ((w₁ ⊗ₜ[ℂ] x₂,
          (0 : (superPow (stdSuperPair k ℓ) b).odd ⊗[ℂ]
            (stdSuperPair k ℓ).even)) :
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
            (stdSuperPair k ℓ)).odd))
            :
        (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b) (stdSuperPair k
            ℓ))).even)) =
    (((0 : (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
        (superPow (stdSuperPair k ℓ) b)).even ⊗[ℂ] (stdSuperPair k ℓ).even),
      (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
          (superPow (stdSuperPair k ℓ) b).odd),
        x ⊗ₜ[ℂ] w₁) ⊗ₜ[ℂ] x₂)) :
      (SuperVect.tensorObj (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
        (superPow (stdSuperPair k ℓ) b)) (stdSuperPair k ℓ)).even) := by
  change (SuperVect.assocAux _ _ _ _ _ _).symm
      (((0 : _), x ⊗ₜ[ℂ] ((w₁ ⊗ₜ[ℂ] x₂, (0 : _)) : _)) : _) = _
  exact SuperVect.assocAux_symm_oe x w₁ x₂

/-- The associator inverse evenMap on an oe-oe tensor:
`α⁻¹.evenMap (0, x ⊗ₜ (0, w₂ ⊗ₜ x₁))`. -/
private theorem assoc_inv_even_oe_oe_tmul {k ℓ a b : ℕ}
    (x : (superPow (stdSuperPair k ℓ) a).odd)
    (w₂ : (superPow (stdSuperPair k ℓ) b).odd)
    (x₁ : (stdSuperPair k ℓ).even) :
    (((α_ (superPow (stdSuperPair k ℓ) a) (superPow (stdSuperPair k ℓ) b)
        (stdSuperPair k ℓ)).inv : SuperVect.Hom _ _).evenMap
      (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b) (stdSuperPair k
            ℓ)).even),
        x ⊗ₜ[ℂ] (((0 : (superPow (stdSuperPair k ℓ) b).even ⊗[ℂ]
            (stdSuperPair k ℓ).odd),
          w₂ ⊗ₜ[ℂ] x₁) :
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
            (stdSuperPair k ℓ)).odd))
            :
        (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b) (stdSuperPair k
            ℓ))).even)) =
    ((((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
          (superPow (stdSuperPair k ℓ) b).even),
        x ⊗ₜ[ℂ] w₂) ⊗ₜ[ℂ] x₁,
      (0 : (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
        (superPow (stdSuperPair k ℓ) b)).odd ⊗[ℂ] (stdSuperPair k ℓ).odd)) :
      (SuperVect.tensorObj (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
        (superPow (stdSuperPair k ℓ) b)) (stdSuperPair k ℓ)).even) := by
  change (SuperVect.assocAux _ _ _ _ _ _).symm
      (((0 : _), x ⊗ₜ[ℂ] (((0 : _), w₂ ⊗ₜ[ℂ] x₁) : _)) : _) = _
  exact SuperVect.assocAux_symm_oo x w₂ x₁

/-! ### Full chain reduction on pure tensor generators (odd input) -/

-- As in `ColourMerge`, the merge and the colouring
-- equivalence unfold on one pure tensor; four chains, one per
-- parity pattern, now with an odd first factor.
/-- Chain for part 1, ee generator: `cpe(a+(b+1)).oddEquiv` on
`pm.oddMap (0, x ⊗ₜ (w₁⊗ₜx₁, 0))` reduces to
`cps ∘ cpe ∘ pm` on the odd pair. -/
private theorem chain_odd_oe_ee {k ℓ a b : ℕ}
    (x : (superPow (stdSuperPair k ℓ) a).odd)
    (w₁ : (superPow (stdSuperPair k ℓ) b).even)
    (x₁ : (stdSuperPair k ℓ).even) :
    (colourPowerEquiv k ℓ (a + (b + 1))).oddEquiv
        (((powMerge (stdSuperPair k ℓ) a (b + 1) :
          SuperVect.Hom _ _).oddMap
          (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
              (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
                (stdSuperPair k ℓ)).odd),
            x ⊗ₜ[ℂ] ((w₁ ⊗ₜ[ℂ] x₁,
              (0 : (superPow (stdSuperPair k ℓ) b).odd ⊗[ℂ]
                (stdSuperPair k ℓ).odd)) :
              (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
                (stdSuperPair k ℓ)).even)) :
            (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
              (superPow (stdSuperPair k ℓ) (b + 1))).odd))) =
      (colourPowerStep k ℓ (a + b)).oddEquiv
        (((0 : ({c : MixedColouring k ℓ (a + b) // c.IsEven} → ℂ)
            ⊗[ℂ] (Fin (2 * ℓ) → ℂ)),
          (colourPowerEquiv k ℓ (a + b)).oddEquiv
            (((powMerge (stdSuperPair k ℓ) a b :
              SuperVect.Hom _ _).oddMap
              (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
                  (superPow (stdSuperPair k ℓ) b).odd),
                x ⊗ₜ[ℂ] w₁) :
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
                  (superPow (stdSuperPair k ℓ) b)).odd)))
            ⊗ₜ[ℂ] x₁)) := by
  change (colourPowerStep k ℓ (a + b)).oddEquiv
      ((SuperLinearEquiv.tensorCongr (colourPowerEquiv k ℓ (a + b))
          (SuperLinearEquiv.refl (stdSuperPair k ℓ))).oddEquiv
        ((powMerge (stdSuperPair k ℓ) a b ▷ stdSuperPair k ℓ :
          SuperVect.Hom _ _).oddMap
          (((α_ (superPow (stdSuperPair k ℓ) a) (superPow (stdSuperPair k ℓ) b)
            (stdSuperPair k ℓ)).inv : SuperVect.Hom _ _).oddMap
            (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
                  (stdSuperPair k ℓ)).odd),
              x ⊗ₜ[ℂ] ((w₁ ⊗ₜ[ℂ] x₁,
                (0 : (superPow (stdSuperPair k ℓ) b).odd ⊗[ℂ]
                  (stdSuperPair k ℓ).odd)) :
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
                  (stdSuperPair k ℓ)).even)) :
              (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
                  (stdSuperPair k ℓ))).odd)))) = _
  refine congr_arg (colourPowerStep k ℓ (a + b)).oddEquiv ?_
  erw [assoc_inv_odd_oe_ee_tmul x w₁ x₁]
  have hid_o : (SuperVect.Hom.id (stdSuperPair k ℓ)).oddMap =
      LinearMap.id := rfl
  have hid_e : (SuperVect.Hom.id (stdSuperPair k ℓ)).evenMap =
      LinearMap.id := rfl
  simp only [MonoidalCategoryStruct.whiskerRight,
    SuperVect.tensorHom_oddMap, hid_o, hid_e]
  change LinearEquiv.prodCongr
    (TensorProduct.congr (colourPowerEquiv k ℓ (a + b)).evenEquiv
      (LinearEquiv.refl ℂ _))
    (TensorProduct.congr (colourPowerEquiv k ℓ (a + b)).oddEquiv
      (LinearEquiv.refl ℂ _))
    (((0 : _),
      ((powMerge (stdSuperPair k ℓ) a b : SuperVect.Hom _ _).oddMap
        (((0 : _), x ⊗ₜ[ℂ] w₁) : _)) ⊗ₜ[ℂ] x₁)) = _
  simp only [LinearEquiv.prodCongr_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, map_zero]
  rfl

-- As for the ee generator, with both factors odd.
/-- Chain for part 1, oo generator: `cpe(a+(b+1)).oddEquiv` on
`pm.oddMap (0, x ⊗ₜ (0, w₂⊗ₜx₂))` reduces to
`cps ∘ cpe ∘ pm` on the even pair. -/
private theorem chain_odd_oe_oo {k ℓ a b : ℕ}
    (x : (superPow (stdSuperPair k ℓ) a).odd)
    (w₂ : (superPow (stdSuperPair k ℓ) b).odd)
    (x₂ : (stdSuperPair k ℓ).odd) :
    (colourPowerEquiv k ℓ (a + (b + 1))).oddEquiv
        (((powMerge (stdSuperPair k ℓ) a (b + 1) :
          SuperVect.Hom _ _).oddMap
          (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
              (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
                (stdSuperPair k ℓ)).odd),
            x ⊗ₜ[ℂ] (((0 : (superPow (stdSuperPair k ℓ) b).even ⊗[ℂ]
                (stdSuperPair k ℓ).even),
              w₂ ⊗ₜ[ℂ] x₂) :
              (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
                (stdSuperPair k ℓ)).even)) :
            (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
              (superPow (stdSuperPair k ℓ) (b + 1))).odd))) =
      (colourPowerStep k ℓ (a + b)).oddEquiv
        (((colourPowerEquiv k ℓ (a + b)).evenEquiv
            (((powMerge (stdSuperPair k ℓ) a b :
              SuperVect.Hom _ _).evenMap
              (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
                  (superPow (stdSuperPair k ℓ) b).even),
                x ⊗ₜ[ℂ] w₂) :
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
                  (superPow (stdSuperPair k ℓ) b)).even)))
            ⊗ₜ[ℂ] x₂,
          (0 : ({c : MixedColouring k ℓ (a + b) // ¬ c.IsEven} → ℂ)
            ⊗[ℂ] (Fin k → ℂ)))) := by
  change (colourPowerStep k ℓ (a + b)).oddEquiv
      ((SuperLinearEquiv.tensorCongr (colourPowerEquiv k ℓ (a + b))
          (SuperLinearEquiv.refl (stdSuperPair k ℓ))).oddEquiv
        ((powMerge (stdSuperPair k ℓ) a b ▷ stdSuperPair k ℓ :
          SuperVect.Hom _ _).oddMap
          (((α_ (superPow (stdSuperPair k ℓ) a) (superPow (stdSuperPair k ℓ) b)
            (stdSuperPair k ℓ)).inv : SuperVect.Hom _ _).oddMap
            (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
                  (stdSuperPair k ℓ)).odd),
              x ⊗ₜ[ℂ] (((0 : (superPow (stdSuperPair k ℓ) b).even ⊗[ℂ]
                  (stdSuperPair k ℓ).even),
                w₂ ⊗ₜ[ℂ] x₂) :
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
                  (stdSuperPair k ℓ)).even)) :
              (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
                  (stdSuperPair k ℓ))).odd)))) = _
  refine congr_arg (colourPowerStep k ℓ (a + b)).oddEquiv ?_
  erw [assoc_inv_odd_oe_oo_tmul x w₂ x₂]
  have hid_o : (SuperVect.Hom.id (stdSuperPair k ℓ)).oddMap =
      LinearMap.id := rfl
  have hid_e : (SuperVect.Hom.id (stdSuperPair k ℓ)).evenMap =
      LinearMap.id := rfl
  simp only [MonoidalCategoryStruct.whiskerRight,
    SuperVect.tensorHom_oddMap, hid_o, hid_e]
  change LinearEquiv.prodCongr
    (TensorProduct.congr (colourPowerEquiv k ℓ (a + b)).evenEquiv
      (LinearEquiv.refl ℂ _))
    (TensorProduct.congr (colourPowerEquiv k ℓ (a + b)).oddEquiv
      (LinearEquiv.refl ℂ _))
    ((((powMerge (stdSuperPair k ℓ) a b : SuperVect.Hom _ _).evenMap
        (((0 : _), x ⊗ₜ[ℂ] w₂) : _)) ⊗ₜ[ℂ] x₂, (0 : _))) = _
  simp only [LinearEquiv.prodCongr_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, map_zero]
  rfl

-- As for part 1, on the even component.
/-- Chain for part 2, eo generator: `cpe(a+(b+1)).evenEquiv` on
`pm.evenMap (0, x ⊗ₜ (w₁⊗ₜx₂, 0))` reduces to
`cps ∘ cpe ∘ pm` on the odd pair. -/
private theorem chain_even_oe_eo {k ℓ a b : ℕ}
    (x : (superPow (stdSuperPair k ℓ) a).odd)
    (w₁ : (superPow (stdSuperPair k ℓ) b).even)
    (x₂ : (stdSuperPair k ℓ).odd) :
    (colourPowerEquiv k ℓ (a + (b + 1))).evenEquiv
        (((powMerge (stdSuperPair k ℓ) a (b + 1) :
          SuperVect.Hom _ _).evenMap
          (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
              (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
                (stdSuperPair k ℓ)).even),
            x ⊗ₜ[ℂ] ((w₁ ⊗ₜ[ℂ] x₂,
              (0 : (superPow (stdSuperPair k ℓ) b).odd ⊗[ℂ]
                (stdSuperPair k ℓ).even)) :
              (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
                (stdSuperPair k ℓ)).odd)) :
            (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
              (superPow (stdSuperPair k ℓ) (b + 1))).even))) =
      (colourPowerStep k ℓ (a + b)).evenEquiv
        (((0 : ({c : MixedColouring k ℓ (a + b) // c.IsEven} → ℂ)
            ⊗[ℂ] (Fin k → ℂ)),
          (colourPowerEquiv k ℓ (a + b)).oddEquiv
            (((powMerge (stdSuperPair k ℓ) a b :
              SuperVect.Hom _ _).oddMap
              (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
                  (superPow (stdSuperPair k ℓ) b).odd),
                x ⊗ₜ[ℂ] w₁) :
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
                  (superPow (stdSuperPair k ℓ) b)).odd)))
            ⊗ₜ[ℂ] x₂)) := by
  change (colourPowerStep k ℓ (a + b)).evenEquiv
      ((SuperLinearEquiv.tensorCongr (colourPowerEquiv k ℓ (a + b))
          (SuperLinearEquiv.refl (stdSuperPair k ℓ))).evenEquiv
        ((powMerge (stdSuperPair k ℓ) a b ▷ stdSuperPair k ℓ :
          SuperVect.Hom _ _).evenMap
          (((α_ (superPow (stdSuperPair k ℓ) a) (superPow (stdSuperPair k ℓ) b)
            (stdSuperPair k ℓ)).inv : SuperVect.Hom _ _).evenMap
            (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
                  (stdSuperPair k ℓ)).even),
              x ⊗ₜ[ℂ] ((w₁ ⊗ₜ[ℂ] x₂,
                (0 : (superPow (stdSuperPair k ℓ) b).odd ⊗[ℂ]
                  (stdSuperPair k ℓ).even)) :
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
                  (stdSuperPair k ℓ)).odd)) :
              (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
                  (stdSuperPair k ℓ))).even)))) = _
  refine congr_arg (colourPowerStep k ℓ (a + b)).evenEquiv ?_
  erw [assoc_inv_even_oe_eo_tmul x w₁ x₂]
  have hid_o : (SuperVect.Hom.id (stdSuperPair k ℓ)).oddMap =
      LinearMap.id := rfl
  simp only [MonoidalCategoryStruct.whiskerRight,
    SuperVect.tensorHom_evenMap, hid_o]
  change LinearEquiv.prodCongr
    (TensorProduct.congr (colourPowerEquiv k ℓ (a + b)).evenEquiv
      (LinearEquiv.refl ℂ _))
    (TensorProduct.congr (colourPowerEquiv k ℓ (a + b)).oddEquiv
      (LinearEquiv.refl ℂ _))
    (((0 : _),
      ((powMerge (stdSuperPair k ℓ) a b : SuperVect.Hom _ _).oddMap
        (((0 : _), x ⊗ₜ[ℂ] w₁) : _)) ⊗ₜ[ℂ] x₂)) = _
  simp only [LinearEquiv.prodCongr_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, map_zero]
  rfl

-- As for part 1, on the even component.
/-- Chain for part 2, oe generator: `cpe(a+(b+1)).evenEquiv` on
`pm.evenMap (0, x ⊗ₜ (0, w₂⊗ₜx₁))` reduces to
`cps ∘ cpe ∘ pm` on the even pair. -/
private theorem chain_even_oe_oe {k ℓ a b : ℕ}
    (x : (superPow (stdSuperPair k ℓ) a).odd)
    (w₂ : (superPow (stdSuperPair k ℓ) b).odd)
    (x₁ : (stdSuperPair k ℓ).even) :
    (colourPowerEquiv k ℓ (a + (b + 1))).evenEquiv
        (((powMerge (stdSuperPair k ℓ) a (b + 1) :
          SuperVect.Hom _ _).evenMap
          (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
              (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
                (stdSuperPair k ℓ)).even),
            x ⊗ₜ[ℂ] (((0 : (superPow (stdSuperPair k ℓ) b).even ⊗[ℂ]
                (stdSuperPair k ℓ).odd),
              w₂ ⊗ₜ[ℂ] x₁) :
              (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
                (stdSuperPair k ℓ)).odd)) :
            (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
              (superPow (stdSuperPair k ℓ) (b + 1))).even))) =
      (colourPowerStep k ℓ (a + b)).evenEquiv
        (((colourPowerEquiv k ℓ (a + b)).evenEquiv
            (((powMerge (stdSuperPair k ℓ) a b :
              SuperVect.Hom _ _).evenMap
              (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
                  (superPow (stdSuperPair k ℓ) b).even),
                x ⊗ₜ[ℂ] w₂) :
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
                  (superPow (stdSuperPair k ℓ) b)).even)))
            ⊗ₜ[ℂ] x₁,
          (0 : ({c : MixedColouring k ℓ (a + b) // ¬ c.IsEven} → ℂ)
            ⊗[ℂ] (Fin (2 * ℓ) → ℂ)))) := by
  change (colourPowerStep k ℓ (a + b)).evenEquiv
      ((SuperLinearEquiv.tensorCongr (colourPowerEquiv k ℓ (a + b))
          (SuperLinearEquiv.refl (stdSuperPair k ℓ))).evenEquiv
        ((powMerge (stdSuperPair k ℓ) a b ▷ stdSuperPair k ℓ :
          SuperVect.Hom _ _).evenMap
          (((α_ (superPow (stdSuperPair k ℓ) a) (superPow (stdSuperPair k ℓ) b)
            (stdSuperPair k ℓ)).inv : SuperVect.Hom _ _).evenMap
            (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
                  (stdSuperPair k ℓ)).even),
              x ⊗ₜ[ℂ] (((0 : (superPow (stdSuperPair k ℓ) b).even ⊗[ℂ]
                  (stdSuperPair k ℓ).odd),
                w₂ ⊗ₜ[ℂ] x₁) :
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
                  (stdSuperPair k ℓ)).odd)) :
              (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
                  (stdSuperPair k ℓ))).even)))) = _
  refine congr_arg (colourPowerStep k ℓ (a + b)).evenEquiv ?_
  erw [assoc_inv_even_oe_oe_tmul x w₂ x₁]
  have hid_e : (SuperVect.Hom.id (stdSuperPair k ℓ)).evenMap =
      LinearMap.id := rfl
  simp only [MonoidalCategoryStruct.whiskerRight,
    SuperVect.tensorHom_evenMap, hid_e]
  change LinearEquiv.prodCongr
    (TensorProduct.congr (colourPowerEquiv k ℓ (a + b)).evenEquiv
      (LinearEquiv.refl ℂ _))
    (TensorProduct.congr (colourPowerEquiv k ℓ (a + b)).oddEquiv
      (LinearEquiv.refl ℂ _))
    ((((powMerge (stdSuperPair k ℓ) a b : SuperVect.Hom _ _).evenMap
        (((0 : _), x ⊗ₜ[ℂ] w₂) : _)) ⊗ₜ[ℂ] x₁, (0 : _))) = _
  simp only [LinearEquiv.prodCongr_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, map_zero]
  rfl

private theorem colourMerge_pair_odd_odd_step {k ℓ : ℕ} (a : ℕ)
    (x : (superPow (stdSuperPair k ℓ) a).odd) (b : ℕ)
    (ih_odd : ∀ (w : (superPow (stdSuperPair k ℓ) b).even)
        (c : MixedColouring k ℓ (a + b)) (hc : ¬ c.IsEven),
        (colourPowerEquiv k ℓ (a + b)).oddEquiv
            (((powMerge (stdSuperPair k ℓ) a b) :
              SuperVect.Hom _ _).oddMap
              (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
                  (superPow (stdSuperPair k ℓ) b).odd),
                x ⊗ₜ[ℂ] w) :
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
                  (superPow (stdSuperPair k ℓ) b)).odd))
            ⟨c, hc⟩ =
          if h : MixedColouring.IsEven c.firstHalf then 0
          else
            (colourPowerEquiv k ℓ a).oddEquiv x ⟨c.firstHalf, h⟩ *
            (colourPowerEquiv k ℓ b).evenEquiv w ⟨c.secondHalf,
              c.secondHalf_isEven_of_not hc h⟩)
    (ih_even : ∀ (u : (superPow (stdSuperPair k ℓ) b).odd)
        (c : MixedColouring k ℓ (a + b)) (hc : c.IsEven),
        (colourPowerEquiv k ℓ (a + b)).evenEquiv
            (((powMerge (stdSuperPair k ℓ) a b) :
              SuperVect.Hom _ _).evenMap
              (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
                  (superPow (stdSuperPair k ℓ) b).even),
                x ⊗ₜ[ℂ] u) :
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
                  (superPow (stdSuperPair k ℓ) b)).even))
            ⟨c, hc⟩ =
          if h : MixedColouring.IsEven c.firstHalf then 0
          else
            (colourPowerEquiv k ℓ a).oddEquiv x ⟨c.firstHalf, h⟩ *
            (colourPowerEquiv k ℓ b).oddEquiv u ⟨c.secondHalf,
              c.secondHalf_not_isEven' hc h⟩) :
    ∀ (w : (superPow (stdSuperPair k ℓ) (b + 1)).even)
        (c : MixedColouring k ℓ (a + (b + 1))) (hc : ¬ c.IsEven),
        (colourPowerEquiv k ℓ (a + (b + 1))).oddEquiv
            (((powMerge (stdSuperPair k ℓ) a (b + 1)) :
              SuperVect.Hom _ _).oddMap
              (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
                  (superPow (stdSuperPair k ℓ) (b + 1)).odd),
                x ⊗ₜ[ℂ] w) :
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
                  (superPow (stdSuperPair k ℓ) (b + 1))).odd))
            ⟨c, hc⟩ =
          if h : MixedColouring.IsEven c.firstHalf then 0
          else
            (colourPowerEquiv k ℓ a).oddEquiv x ⟨c.firstHalf, h⟩ *
            (colourPowerEquiv k ℓ (b + 1)).evenEquiv w ⟨c.secondHalf,
              c.secondHalf_isEven_of_not hc h⟩ := by
  intro w c hc
  obtain ⟨w_ee, w_oo⟩ := w
  -- Both sides are additive in w; decompose.
  have op_add : ∀ (w₁ w₂ : (SuperVect.tensorObj
      (superPow (stdSuperPair k ℓ) b) (stdSuperPair k ℓ)).even),
      (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
            (stdSuperPair k ℓ)).odd),
        x ⊗ₜ[ℂ] (w₁ + w₂)) :
        (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
          (superPow (stdSuperPair k ℓ) (b + 1))).odd) =
      (((0 : _), x ⊗ₜ[ℂ] w₁) : _) + (((0 : _), x ⊗ₜ[ℂ] w₂) : _) :=
    fun w₁ w₂ => Prod.ext (add_zero 0).symm (TensorProduct.tmul_add x w₁ w₂)
  have op_zero : (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
      (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
        (stdSuperPair k ℓ)).odd),
    x ⊗ₜ[ℂ] (0 : (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
      (stdSuperPair k ℓ)).even)) :
    (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
      (superPow (stdSuperPair k ℓ) (b + 1))).odd) = (0 : _) :=
    Prod.ext rfl (TensorProduct.tmul_zero _ x)
  set Goal := fun (w : (SuperVect.tensorObj
      (superPow (stdSuperPair k ℓ) b) (stdSuperPair k ℓ)).even) =>
    (colourPowerEquiv k ℓ (a + (b + 1))).oddEquiv
        (((powMerge (stdSuperPair k ℓ) a (b + 1) :
          SuperVect.Hom _ _).oddMap
          (((0 : _), x ⊗ₜ[ℂ] w) :
            (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
              (superPow (stdSuperPair k ℓ) (b + 1))).odd)))
        ⟨c, hc⟩ =
      if h : MixedColouring.IsEven c.firstHalf then 0
      else
        (colourPowerEquiv k ℓ a).oddEquiv x ⟨c.firstHalf, h⟩ *
        (colourPowerEquiv k ℓ (b + 1)).evenEquiv w ⟨c.secondHalf,
          c.secondHalf_isEven_of_not hc h⟩
    with hGoal
  change Goal (w_ee, w_oo)
  have Goal_add : ∀ (w₁ w₂ : _), Goal w₁ → Goal w₂ → Goal (w₁ + w₂) := by
    intro w₁ w₂ h₁ h₂
    simp only [hGoal] at h₁ h₂ ⊢
    erw [op_add w₁ w₂, map_add, LinearEquiv.map_add, Pi.add_apply, h₁, h₂]
    split_ifs with h
    · exact add_zero 0
    · erw [← mul_add]; congr 1
      erw [LinearEquiv.map_add, Pi.add_apply]
  -- Prove for (t, 0) by TensorProduct.induction_on
  have h_ee : ∀ t, Goal (t, (0 : (superPow (stdSuperPair k ℓ) b).odd ⊗[ℂ]
      (stdSuperPair k ℓ).odd)) := by
    intro t; induction t using TensorProduct.inductionOn with
    | tmul w₁ x₁ =>
      simp only [hGoal]
      rcases hcl : c (Fin.last (a + b)) with a' | b'
      · -- Last colour even: chain + cps_odd_at_inl on LHS
        erw [(congr_fun (chain_odd_oe_ee x w₁ x₁) ⟨c, hc⟩).trans
          (cps_odd_at_inl _ _ c hc a' hcl), funTensorFun_tmul]
        have hcl_sh : c.secondHalf (Fin.last b) = Sum.inl a' :=
          c.secondHalf_last.symm ▸ hcl
        erw [ih_odd w₁ (MixedColouring.tail c)
          ((c.isEven_succ_left a' hcl).not.mp hc)]
        simp only [MixedColouring.firstHalf_tail,
          MixedColouring.secondHalf_tail]
        split_ifs with h
        · simp [zero_mul]
        · erw [(congr_fun (rhs_even_ee w₁ x₁)
              ⟨c.secondHalf, c.secondHalf_isEven_of_not hc h⟩).trans
            (cps_even_at_inl _ _ c.secondHalf
              (c.secondHalf_isEven_of_not hc h) a' hcl_sh),
            funTensorFun_tmul]
          ring
      · -- Last colour odd: both sides vanish
        erw [(congr_fun (chain_odd_oe_ee x w₁ x₁) ⟨c, hc⟩).trans
          (cps_odd_at_inr _ _ c hc b' hcl)]
        simp only [map_zero, Pi.zero_apply]
        split_ifs with h
        · rfl
        · have hcl_sh : c.secondHalf (Fin.last b) = Sum.inr b' :=
            c.secondHalf_last.symm ▸ hcl
          erw [(congr_fun (rhs_even_ee w₁ x₁)
              ⟨c.secondHalf, c.secondHalf_isEven_of_not hc h⟩).trans
            (cps_even_at_inr _ _ c.secondHalf
              (c.secondHalf_isEven_of_not hc h) b' hcl_sh)]
          simp [map_zero, mul_zero]
    | add t₁ t₂ ih₁ ih₂ =>
      have : ((t₁ + t₂, (0 : _)) : (SuperVect.tensorObj
          (superPow (stdSuperPair k ℓ) b) (stdSuperPair k ℓ)).even) =
        ((t₁, (0 : _)) : _) + ((t₂, (0 : _)) : _) :=
        Prod.ext rfl (add_zero 0).symm
      rw [this]; exact Goal_add _ _ ih₁ ih₂
  -- Prove for (0, s) by TensorProduct.induction_on
  have h_oo : ∀ s, Goal ((0 : (superPow (stdSuperPair k ℓ) b).even ⊗[ℂ]
      (stdSuperPair k ℓ).even), s) := by
    intro s; induction s using TensorProduct.inductionOn with
    | tmul w₂ x₂ =>
      simp only [hGoal]
      rcases hcl : c (Fin.last (a + b)) with a' | b'
      · -- Last colour even: both sides vanish
        erw [(congr_fun (chain_odd_oe_oo x w₂ x₂) ⟨c, hc⟩).trans
          (cps_odd_at_inl _ _ c hc a' hcl)]
        simp only [map_zero, Pi.zero_apply]
        split_ifs with h
        · rfl
        · have hcl_sh : c.secondHalf (Fin.last b) = Sum.inl a' :=
            c.secondHalf_last.symm ▸ hcl
          erw [(congr_fun (rhs_even_oo w₂ x₂)
              ⟨c.secondHalf, c.secondHalf_isEven_of_not hc h⟩).trans
            (cps_even_at_inl _ _ c.secondHalf
              (c.secondHalf_isEven_of_not hc h) a' hcl_sh)]
          simp [map_zero, mul_zero]
      · -- Last colour odd: chain + cps_odd_at_inr + IH
        erw [(congr_fun (chain_odd_oe_oo x w₂ x₂) ⟨c, hc⟩).trans
          (cps_odd_at_inr _ _ c hc b' hcl), funTensorFun_tmul]
        have hcl_sh : c.secondHalf (Fin.last b) = Sum.inr b' :=
          c.secondHalf_last.symm ▸ hcl
        erw [ih_even w₂ (MixedColouring.tail c)
          (Decidable.not_not.mp
            ((c.isEven_succ_right b' hcl).not.mp hc))]
        simp only [MixedColouring.firstHalf_tail,
          MixedColouring.secondHalf_tail]
        split_ifs with h
        · simp [zero_mul]
        · erw [(congr_fun (rhs_even_oo w₂ x₂)
              ⟨c.secondHalf, c.secondHalf_isEven_of_not hc h⟩).trans
            (cps_even_at_inr _ _ c.secondHalf
              (c.secondHalf_isEven_of_not hc h) b' hcl_sh),
            funTensorFun_tmul]
          ring
    | add s₁ s₂ ih₁ ih₂ =>
      have : (((0 : _), s₁ + s₂) : (SuperVect.tensorObj
          (superPow (stdSuperPair k ℓ) b) (stdSuperPair k ℓ)).even) =
        (((0 : _), s₁) : _) + (((0 : _), s₂) : _) :=
        Prod.ext (add_zero 0).symm rfl
      rw [this]; exact Goal_add _ _ ih₁ ih₂
  -- Combine
  have hw : ((w_ee, w_oo) : (SuperVect.tensorObj
      (superPow (stdSuperPair k ℓ) b) (stdSuperPair k ℓ)).even) =
    ((w_ee, (0 : _)) : _) + (((0 : _), w_oo) : _) :=
    Prod.ext (add_zero w_ee).symm (zero_add w_oo).symm
  rw [hw]; exact Goal_add _ _ (h_ee w_ee) (h_oo w_oo)

private theorem colourMerge_pair_odd_even_step {k ℓ : ℕ} (a : ℕ)
    (x : (superPow (stdSuperPair k ℓ) a).odd) (b : ℕ)
    (ih_odd : ∀ (w : (superPow (stdSuperPair k ℓ) b).even)
        (c : MixedColouring k ℓ (a + b)) (hc : ¬ c.IsEven),
        (colourPowerEquiv k ℓ (a + b)).oddEquiv
            (((powMerge (stdSuperPair k ℓ) a b) :
              SuperVect.Hom _ _).oddMap
              (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
                  (superPow (stdSuperPair k ℓ) b).odd),
                x ⊗ₜ[ℂ] w) :
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
                  (superPow (stdSuperPair k ℓ) b)).odd))
            ⟨c, hc⟩ =
          if h : MixedColouring.IsEven c.firstHalf then 0
          else
            (colourPowerEquiv k ℓ a).oddEquiv x ⟨c.firstHalf, h⟩ *
            (colourPowerEquiv k ℓ b).evenEquiv w ⟨c.secondHalf,
              c.secondHalf_isEven_of_not hc h⟩)
    (ih_even : ∀ (u : (superPow (stdSuperPair k ℓ) b).odd)
        (c : MixedColouring k ℓ (a + b)) (hc : c.IsEven),
        (colourPowerEquiv k ℓ (a + b)).evenEquiv
            (((powMerge (stdSuperPair k ℓ) a b) :
              SuperVect.Hom _ _).evenMap
              (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
                  (superPow (stdSuperPair k ℓ) b).even),
                x ⊗ₜ[ℂ] u) :
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
                  (superPow (stdSuperPair k ℓ) b)).even))
            ⟨c, hc⟩ =
          if h : MixedColouring.IsEven c.firstHalf then 0
          else
            (colourPowerEquiv k ℓ a).oddEquiv x ⟨c.firstHalf, h⟩ *
            (colourPowerEquiv k ℓ b).oddEquiv u ⟨c.secondHalf,
              c.secondHalf_not_isEven' hc h⟩) :
    ∀ (u : (superPow (stdSuperPair k ℓ) (b + 1)).odd)
        (c : MixedColouring k ℓ (a + (b + 1))) (hc : c.IsEven),
        (colourPowerEquiv k ℓ (a + (b + 1))).evenEquiv
            (((powMerge (stdSuperPair k ℓ) a (b + 1)) :
              SuperVect.Hom _ _).evenMap
              (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
                  (superPow (stdSuperPair k ℓ) (b + 1)).even),
                x ⊗ₜ[ℂ] u) :
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
                  (superPow (stdSuperPair k ℓ) (b + 1))).even))
            ⟨c, hc⟩ =
          if h : MixedColouring.IsEven c.firstHalf then 0
          else
            (colourPowerEquiv k ℓ a).oddEquiv x ⟨c.firstHalf, h⟩ *
            (colourPowerEquiv k ℓ (b + 1)).oddEquiv u ⟨c.secondHalf,
              c.secondHalf_not_isEven' hc h⟩ := by
  intro u c hc
  obtain ⟨u_eo, u_oe⟩ := u
  -- Both sides are additive in u; decompose.
  have op_add : ∀ (u₁ u₂ : (SuperVect.tensorObj
      (superPow (stdSuperPair k ℓ) b) (stdSuperPair k ℓ)).odd),
      (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
            (stdSuperPair k ℓ)).even),
        x ⊗ₜ[ℂ] (u₁ + u₂)) :
        (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
          (superPow (stdSuperPair k ℓ) (b + 1))).even) =
      (((0 : _), x ⊗ₜ[ℂ] u₁) : _) + (((0 : _), x ⊗ₜ[ℂ] u₂) : _) :=
    fun u₁ u₂ => Prod.ext (add_zero 0).symm (TensorProduct.tmul_add x u₁ u₂)
  have op_zero : (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
      (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
        (stdSuperPair k ℓ)).even),
    x ⊗ₜ[ℂ] (0 : (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
      (stdSuperPair k ℓ)).odd)) :
    (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
      (superPow (stdSuperPair k ℓ) (b + 1))).even) = (0 : _) :=
    Prod.ext rfl (TensorProduct.tmul_zero _ x)
  set Goal := fun (u : (SuperVect.tensorObj
      (superPow (stdSuperPair k ℓ) b) (stdSuperPair k ℓ)).odd) =>
    (colourPowerEquiv k ℓ (a + (b + 1))).evenEquiv
        (((powMerge (stdSuperPair k ℓ) a (b + 1) :
          SuperVect.Hom _ _).evenMap
          (((0 : _), x ⊗ₜ[ℂ] u) :
            (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
              (superPow (stdSuperPair k ℓ) (b + 1))).even)))
        ⟨c, hc⟩ =
      if h : MixedColouring.IsEven c.firstHalf then 0
      else
        (colourPowerEquiv k ℓ a).oddEquiv x ⟨c.firstHalf, h⟩ *
        (colourPowerEquiv k ℓ (b + 1)).oddEquiv u ⟨c.secondHalf,
          c.secondHalf_not_isEven' hc h⟩
    with hGoal
  change Goal (u_eo, u_oe)
  have Goal_add : ∀ (u₁ u₂ : _), Goal u₁ → Goal u₂ → Goal (u₁ + u₂) := by
    intro u₁ u₂ h₁ h₂
    simp only [hGoal] at h₁ h₂ ⊢
    erw [op_add u₁ u₂, map_add, LinearEquiv.map_add, Pi.add_apply, h₁, h₂]
    split_ifs with h
    · exact add_zero 0
    · erw [← mul_add]; congr 1
      erw [LinearEquiv.map_add, Pi.add_apply]
  -- Prove for (t, 0) by TensorProduct.induction_on
  have h_eo : ∀ t, Goal (t, (0 : (superPow (stdSuperPair k ℓ) b).odd ⊗[ℂ]
      (stdSuperPair k ℓ).even)) := by
    intro t; induction t using TensorProduct.inductionOn with
    | tmul w₁ x₂ =>
      simp only [hGoal]
      rcases hcl : c (Fin.last (a + b)) with a' | b'
      · -- Last colour even: both sides vanish
        erw [(congr_fun (chain_even_oe_eo x w₁ x₂) ⟨c, hc⟩).trans
          (cps_even_at_inl _ _ c hc a' hcl)]
        simp only [map_zero, Pi.zero_apply]
        split_ifs with h
        · rfl
        · have hcl_sh : c.secondHalf (Fin.last b) = Sum.inl a' :=
            c.secondHalf_last.symm ▸ hcl
          erw [(congr_fun (rhs_odd_eo w₁ x₂)
              ⟨c.secondHalf, c.secondHalf_not_isEven' hc h⟩).trans
            (cps_odd_at_inl _ _ c.secondHalf
              (c.secondHalf_not_isEven' hc h) a' hcl_sh)]
          simp [map_zero, mul_zero]
      · -- Last colour odd: chain + cps_even_at_inr + IH
        erw [(congr_fun (chain_even_oe_eo x w₁ x₂) ⟨c, hc⟩).trans
          (cps_even_at_inr _ _ c hc b' hcl), funTensorFun_tmul]
        have hcl_sh : c.secondHalf (Fin.last b) = Sum.inr b' :=
          c.secondHalf_last.symm ▸ hcl
        erw [ih_odd w₁ (MixedColouring.tail c)
          ((c.isEven_succ_right b' hcl).mp hc)]
        simp only [MixedColouring.firstHalf_tail,
          MixedColouring.secondHalf_tail]
        split_ifs with h
        · simp [zero_mul]
        · erw [(congr_fun (rhs_odd_eo w₁ x₂)
              ⟨c.secondHalf, c.secondHalf_not_isEven' hc h⟩).trans
            (cps_odd_at_inr _ _ c.secondHalf
              (c.secondHalf_not_isEven' hc h) b' hcl_sh),
            funTensorFun_tmul]
          ring
    | add t₁ t₂ ih₁ ih₂ =>
      have : ((t₁ + t₂, (0 : _)) : (SuperVect.tensorObj
          (superPow (stdSuperPair k ℓ) b) (stdSuperPair k ℓ)).odd) =
        ((t₁, (0 : _)) : _) + ((t₂, (0 : _)) : _) :=
        Prod.ext rfl (add_zero 0).symm
      rw [this]; exact Goal_add _ _ ih₁ ih₂
  -- Prove for (0, s) by TensorProduct.induction_on
  have h_oe : ∀ s, Goal ((0 : (superPow (stdSuperPair k ℓ) b).even ⊗[ℂ]
      (stdSuperPair k ℓ).odd), s) := by
    intro s; induction s using TensorProduct.inductionOn with
    | tmul w₂ x₁ =>
      simp only [hGoal]
      rcases hcl : c (Fin.last (a + b)) with a' | b'
      · -- Last colour even: chain + cps_even_at_inl + IH
        erw [(congr_fun (chain_even_oe_oe x w₂ x₁) ⟨c, hc⟩).trans
          (cps_even_at_inl _ _ c hc a' hcl), funTensorFun_tmul]
        have hcl_sh : c.secondHalf (Fin.last b) = Sum.inl a' :=
          c.secondHalf_last.symm ▸ hcl
        erw [ih_even w₂ (MixedColouring.tail c)
          ((c.isEven_succ_left a' hcl).mp hc)]
        simp only [MixedColouring.firstHalf_tail,
          MixedColouring.secondHalf_tail]
        split_ifs with h
        · simp [zero_mul]
        · erw [(congr_fun (rhs_odd_oe w₂ x₁)
              ⟨c.secondHalf, c.secondHalf_not_isEven' hc h⟩).trans
            (cps_odd_at_inl _ _ c.secondHalf
              (c.secondHalf_not_isEven' hc h) a' hcl_sh),
            funTensorFun_tmul]
          ring
      · -- Last colour odd: both sides vanish
        erw [(congr_fun (chain_even_oe_oe x w₂ x₁) ⟨c, hc⟩).trans
          (cps_even_at_inr _ _ c hc b' hcl)]
        simp only [map_zero, Pi.zero_apply]
        split_ifs with h
        · rfl
        · have hcl_sh : c.secondHalf (Fin.last b) = Sum.inr b' :=
            c.secondHalf_last.symm ▸ hcl
          erw [(congr_fun (rhs_odd_oe w₂ x₁)
              ⟨c.secondHalf, c.secondHalf_not_isEven' hc h⟩).trans
            (cps_odd_at_inr _ _ c.secondHalf
              (c.secondHalf_not_isEven' hc h) b' hcl_sh)]
          simp [map_zero, mul_zero]
    | add s₁ s₂ ih₁ ih₂ =>
      have : (((0 : _), s₁ + s₂) : (SuperVect.tensorObj
          (superPow (stdSuperPair k ℓ) b) (stdSuperPair k ℓ)).odd) =
        (((0 : _), s₁) : _) + (((0 : _), s₂) : _) :=
        Prod.ext (add_zero 0).symm rfl
      rw [this]; exact Goal_add _ _ ih₁ ih₂
  -- Combine
  have hu : ((u_eo, u_oe) : (SuperVect.tensorObj
      (superPow (stdSuperPair k ℓ) b) (stdSuperPair k ℓ)).odd) =
    ((u_eo, (0 : _)) : _) + (((0 : _), u_oe) : _) :=
    Prod.ext (add_zero u_eo).symm (zero_add u_oe).symm
  rw [hu]; exact Goal_add _ _ (h_eo u_eo) (h_oe u_oe)

-- Specializing the mutual induction re-elaborates
-- the paired statement.

private theorem colourMerge_pair_odd {k ℓ : ℕ} (a : ℕ)
    (x : (superPow (stdSuperPair k ℓ) a).odd) :
    ∀ (b : ℕ),
    -- Part 1: odd coordinates from pm.oddMap (0, x ⊗ₜ w)
    (∀ (w : (superPow (stdSuperPair k ℓ) b).even)
        (c : MixedColouring k ℓ (a + b)) (hc : ¬ c.IsEven),
        (colourPowerEquiv k ℓ (a + b)).oddEquiv
            (((powMerge (stdSuperPair k ℓ) a b) :
              SuperVect.Hom _ _).oddMap
              (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
                  (superPow (stdSuperPair k ℓ) b).odd),
                x ⊗ₜ[ℂ] w) :
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
                  (superPow (stdSuperPair k ℓ) b)).odd))
            ⟨c, hc⟩ =
          if h : MixedColouring.IsEven c.firstHalf then 0
          else
            (colourPowerEquiv k ℓ a).oddEquiv x ⟨c.firstHalf, h⟩ *
            (colourPowerEquiv k ℓ b).evenEquiv w ⟨c.secondHalf,
              c.secondHalf_isEven_of_not hc h⟩)
    ∧
    -- Part 2: even coordinates from pm.evenMap (0, x ⊗ₜ u)
    (∀ (u : (superPow (stdSuperPair k ℓ) b).odd)
        (c : MixedColouring k ℓ (a + b)) (hc : c.IsEven),
        (colourPowerEquiv k ℓ (a + b)).evenEquiv
            (((powMerge (stdSuperPair k ℓ) a b) :
              SuperVect.Hom _ _).evenMap
              (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
                  (superPow (stdSuperPair k ℓ) b).even),
                x ⊗ₜ[ℂ] u) :
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
                  (superPow (stdSuperPair k ℓ) b)).even))
            ⟨c, hc⟩ =
          if h : MixedColouring.IsEven c.firstHalf then 0
          else
            (colourPowerEquiv k ℓ a).oddEquiv x ⟨c.firstHalf, h⟩ *
            (colourPowerEquiv k ℓ b).oddEquiv u ⟨c.secondHalf,
              c.secondHalf_not_isEven' hc h⟩)
  | 0 => by
    constructor
    · -- ═══════ b = 0, ODD COORDINATES ═══════
      intro w c hc
      -- pm(a,0) = right unitor; its oddMap sends (0, x ⊗ₜ w) to ...
      -- Actually w : (superPow _ 0).even = ℂ, and the oddMap of the
      -- right unitor acts on the (snd) component.
      set w' : ℂ := w with hw'
      have hpow : ((powMerge (stdSuperPair k ℓ) a 0 :
          SuperVect.Hom _ _).oddMap
          (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
              (superPow (stdSuperPair k ℓ) 0).odd),
            x ⊗ₜ[ℂ] w') :
            (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
              (superPow (stdSuperPair k ℓ) 0)).odd)) = w' • x := by
        change ((SuperVect.rightUnitor
            (superPow (stdSuperPair k ℓ) a)).hom).oddMap
          ((0 : _), x ⊗ₜ[ℂ] w') = _
        rw [SuperVect.rightUnitor_hom_oddMap]
        change (TensorProduct.rid ℂ _) (x ⊗ₜ[ℂ] w') = w' • x
        exact TensorProduct.rid_tmul x w'
      have hfh : c.firstHalf = c := c.firstHalf_zero
      -- If c.firstHalf.IsEven then c.IsEven, contradicting hc
      have hfe : ¬ c.firstHalf.IsEven := hfh ▸ hc
      have h0 : (colourPowerEquiv k ℓ 0).evenEquiv w
          ⟨c.secondHalf, c.secondHalf_isEven_of_not hc hfe⟩ = w' := by
        change (LinearEquiv.funUnique
          {c : MixedColouring k ℓ 0 // c.IsEven} ℂ ℂ).symm w' _ = w'
        rfl
      simp only [hpow, LinearEquiv.map_smul,
        dite_eq_right hfe,
        show (⟨c.firstHalf, hfe⟩ :
          {c : MixedColouring k ℓ a // ¬ c.IsEven}) = ⟨c, hc⟩ from
          Subtype.ext hfh]
      change w' * (colourPowerEquiv k ℓ (a + 0)).oddEquiv x ⟨c, hc⟩ =
        (colourPowerEquiv k ℓ a).oddEquiv x ⟨c, hc⟩ *
        (colourPowerEquiv k ℓ 0).evenEquiv w' ⟨c.secondHalf,
          c.secondHalf_isEven_of_not hc hfe⟩
      rw [h0, mul_comm]; rfl
    · -- ═══════ b = 0, EVEN COORDINATES ═══════
      -- u : (superPow _ 0).odd = PUnit odd part, which is trivial (0-dim)
      intro u c hc
      have hfe : c.firstHalf.IsEven := c.firstHalf_zero ▸ hc
      simp only [dite_eq_left hfe]
      -- pm(a,0) = right unitor; its evenMap sends (0, x ⊗ₜ u) to 0
      -- because the even part of the right unitor projects to fst,
      -- and fst of (0, x ⊗ₜ u) is 0.
      have hzero : ((powMerge (stdSuperPair k ℓ) a 0 :
          SuperVect.Hom _ _).evenMap
          (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
              (superPow (stdSuperPair k ℓ) 0).even),
            x ⊗ₜ[ℂ] u) :
            (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
              (superPow (stdSuperPair k ℓ) 0)).even)) = 0 := by
        change ((SuperVect.rightUnitor
            (superPow (stdSuperPair k ℓ) a)).hom).evenMap
          ((0 : _), x ⊗ₜ[ℂ] u) = 0
        rw [SuperVect.rightUnitor_hom_evenMap]; rfl
      rw [hzero, map_zero]; rfl
  | b + 1 => by
    obtain ⟨ih_odd, ih_even⟩ := colourMerge_pair_odd a x b
    constructor
    · exact colourMerge_pair_odd_odd_step a x b ih_odd ih_even
    · exact colourMerge_pair_odd_even_step a x b ih_odd ih_even

/-- **The merge coordinate product rule (odd input)**: coordinates
of a merged odd-even pair multiply over the halves, vanishing when
the first half is even. -/
theorem colourMerge_coord_odd {k ℓ : ℕ} (a b : ℕ)
    (x : (superPow (stdSuperPair k ℓ) a).odd)
    (w : (superPow (stdSuperPair k ℓ) b).even)
    (c : MixedColouring k ℓ (a + b)) (hc : ¬ c.IsEven) :
    (colourPowerEquiv k ℓ (a + b)).oddEquiv
        (((powMerge (stdSuperPair k ℓ) a b) :
          SuperVect.Hom _ _).oddMap
          (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
              (superPow (stdSuperPair k ℓ) b).odd),
            x ⊗ₜ[ℂ] w) :
            (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
              (superPow (stdSuperPair k ℓ) b)).odd))
        ⟨c, hc⟩ =
      if h : MixedColouring.IsEven c.firstHalf then 0
      else
        (colourPowerEquiv k ℓ a).oddEquiv x ⟨c.firstHalf, h⟩ *
        (colourPowerEquiv k ℓ b).evenEquiv w ⟨c.secondHalf,
          by exact c.secondHalf_isEven_of_not hc h⟩ :=
  (colourMerge_pair_odd a x b).1 w c hc

/-- **The odd-pair merge coordinate product rule**: even
coordinates of a merged pair of odd vectors multiply over the
halves, supported on odd first halves. -/
theorem colourMerge_coord_oddPair {k ℓ : ℕ} (a b : ℕ)
    (x : (superPow (stdSuperPair k ℓ) a).odd)
    (u : (superPow (stdSuperPair k ℓ) b).odd)
    (c : MixedColouring k ℓ (a + b)) (hc : c.IsEven) :
    (colourPowerEquiv k ℓ (a + b)).evenEquiv
        (((powMerge (stdSuperPair k ℓ) a b) :
          SuperVect.Hom _ _).evenMap
          (((0 : (superPow (stdSuperPair k ℓ) a).even ⊗[ℂ]
              (superPow (stdSuperPair k ℓ) b).even),
            x ⊗ₜ[ℂ] u) :
            (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
              (superPow (stdSuperPair k ℓ) b)).even))
        ⟨c, hc⟩ =
      if h : MixedColouring.IsEven c.firstHalf then 0
      else
        (colourPowerEquiv k ℓ a).oddEquiv x ⟨c.firstHalf, h⟩ *
        (colourPowerEquiv k ℓ b).oddEquiv u ⟨c.secondHalf,
          c.secondHalf_not_isEven' hc h⟩ :=
  (colourMerge_pair_odd a x b).2 u c hc

/-- Subtype coordinate singles evaluate by values: different. -/
theorem single_val_ne {n : ℕ}
    {p : MixedColouring k ℓ n → Prop}
    (x y : {c : MixedColouring k ℓ n // p c})
    (h : y.val ≠ x.val) :
    (Pi.single x (1 : ℂ) :
      {c : MixedColouring k ℓ n // p c} → ℂ) y = 0 :=
  Pi.single_eq_of_ne (fun he => h (congrArg Subtype.val he)) 1

-- The graded single-basis-vector coordinate is
-- computed through the colouring equivalence.
/-- Subtype coordinate singles evaluate by values: same. -/
theorem single_val_same {n : ℕ}
    {p : MixedColouring k ℓ n → Prop}
    (x y : {c : MixedColouring k ℓ n // p c})
    (h : x.val = y.val) :
    (Pi.single x (1 : ℂ) :
      {c : MixedColouring k ℓ n // p c} → ℂ) y = 1 := by
  rw [show y = x from Subtype.ext h.symm]
  exact Pi.single_eq_same x 1

end RS
