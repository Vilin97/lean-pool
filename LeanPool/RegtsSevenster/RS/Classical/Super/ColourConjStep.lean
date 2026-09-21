/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Super.ColourConj

/-!
# Step compatibility of the colouring conjugation

The conjugation of a whiskered endomorphism into the colouring
model equals the colour-extension of the conjugate: unwinding
`colourPowerEquiv (n + 1)` as `tensorCongr.trans step` and
observing that the `tensorCongr`-conjugation of a whisker is
`tensorHom` of the inner conjugation.
-/

open scoped TensorProduct

namespace RS

open CategoryTheory MonoidalCategory

/-- Conjugating `TensorProduct.map f id` by
`TensorProduct.congr E refl` yields
`TensorProduct.map (E . f . E.symm) id`. -/
private lemma congr_refl_map_id {M₁ M₂ N : Type*}
    [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    [AddCommGroup N] [Module ℂ N]
    (E : M₁ ≃ₗ[ℂ] M₂) (f : M₁ →ₗ[ℂ] M₁) (t : M₂ ⊗[ℂ] N) :
    (TensorProduct.congr E (LinearEquiv.refl ℂ N))
      (TensorProduct.map f LinearMap.id
        ((TensorProduct.congr E (LinearEquiv.refl ℂ N)).symm t)) =
    TensorProduct.map (E.toLinearMap ∘ₗ f ∘ₗ E.symm.toLinearMap)
      LinearMap.id t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [TensorProduct.congr_symm_tmul, TensorProduct.map_tmul,
      LinearEquiv.coe_toLinearMap, LinearMap.comp_apply,
      LinearMap.id_apply, LinearEquiv.refl_apply, LinearEquiv.refl_symm,
      TensorProduct.congr_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

-- Raised budget: the colouring equivalence at arity `n+1`
-- is expanded through the tensor step on both components, so the
-- elaborated term carries the whole step equivalence twice.
/-- **The step compatibility**: conjugating a whiskered
endomorphism into the colouring model extends the conjugate. -/
theorem toColour_whisker {k ℓ : ℕ} (n : ℕ)
    (g : superPow (stdSuperPair k ℓ) n ⟶ superPow (stdSuperPair k ℓ) n) :
    toColour (n + 1) (g ▷ stdSuperPair k ℓ) =
      colourExtend n (toColour n g) := by
  refine SuperVect.Hom.ext ?_ ?_
  · -- Even component
    refine LinearMap.ext (fun x => ?_)
    -- Expand colourPowerEquiv (n+1) = (tensorCongr CPE refl).trans step
    show ((SuperLinearEquiv.tensorCongr (colourPowerEquiv k ℓ n)
            (SuperLinearEquiv.refl (stdSuperPair k ℓ))).evenEquiv.trans
          (colourPowerStep k ℓ n).evenEquiv)
        ((g ▷ stdSuperPair k ℓ : SuperVect.Hom _ _).evenMap
          (((SuperLinearEquiv.tensorCongr (colourPowerEquiv k ℓ n)
              (SuperLinearEquiv.refl (stdSuperPair k ℓ))).evenEquiv.trans
            (colourPowerStep k ℓ n).evenEquiv).symm x)) =
      (colourPowerStep k ℓ n).evenEquiv
        ((SuperVect.tensorHom (toColour n g)
            (SuperVect.Hom.id (stdSuperPair k ℓ)) :
          SuperVect.Hom _ _).evenMap
          ((colourPowerStep k ℓ n).evenEquiv.symm x))
    rw [LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply]
    congr 1
    -- tc.ee(whisker.ee(tc.ee.symm y)) = tensorHom(toColour g, id).ee y
    set y := (colourPowerStep k ℓ n).evenEquiv.symm x
    -- Expand prodCongr/prodMap structure and destructure the Prod
    obtain ⟨y₁, y₂⟩ := y
    dsimp only [SuperLinearEquiv.tensorCongr, SuperLinearEquiv.refl,
      SuperVect.Hom.id]
    simp only [SuperVect.tensorHom, toColour]
    exact Prod.ext (congr_refl_map_id _ _ y₁) (congr_refl_map_id _ _ y₂)
  · -- Odd component (symmetric)
    refine LinearMap.ext (fun x => ?_)
    show ((SuperLinearEquiv.tensorCongr (colourPowerEquiv k ℓ n)
            (SuperLinearEquiv.refl (stdSuperPair k ℓ))).oddEquiv.trans
          (colourPowerStep k ℓ n).oddEquiv)
        ((g ▷ stdSuperPair k ℓ : SuperVect.Hom _ _).oddMap
          (((SuperLinearEquiv.tensorCongr (colourPowerEquiv k ℓ n)
              (SuperLinearEquiv.refl (stdSuperPair k ℓ))).oddEquiv.trans
            (colourPowerStep k ℓ n).oddEquiv).symm x)) =
      (colourPowerStep k ℓ n).oddEquiv
        ((SuperVect.tensorHom (toColour n g)
            (SuperVect.Hom.id (stdSuperPair k ℓ)) :
          SuperVect.Hom _ _).oddMap
          ((colourPowerStep k ℓ n).oddEquiv.symm x))
    rw [LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply]
    congr 1
    set y := (colourPowerStep k ℓ n).oddEquiv.symm x
    obtain ⟨y₁, y₂⟩ := y
    dsimp only [SuperLinearEquiv.tensorCongr, SuperLinearEquiv.refl,
      SuperVect.Hom.id]
    simp only [SuperVect.tensorHom, toColour]
    exact Prod.ext (congr_refl_map_id _ _ y₁) (congr_refl_map_id _ _ y₂)

end RS
