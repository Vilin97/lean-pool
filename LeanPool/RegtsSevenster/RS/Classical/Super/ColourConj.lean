/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Super.PowBraid
public import LeanPool.RegtsSevenster.RS.Classical.Super.ColourEval

/-!
# Conjugation into the colouring model

Endomorphisms of the monoidal power conjugate through
`colourPowerEquiv` into the colouring model; extending along one
step is conjugation of the whisker through `colourPowerStep`.
These are the carriers of the braiding-coordinate computation.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory

variable {k ℓ : ℕ}

/-- Conjugating a power endomorphism into the colouring model. -/
noncomputable def toColour (n : ℕ)
    (g : superPow (stdSuperPair k ℓ) n ⟶ superPow (stdSuperPair k ℓ) n) :
    colourPower k ℓ n ⟶ colourPower k ℓ n where
  evenMap := (colourPowerEquiv k ℓ n).evenEquiv.toLinearMap ∘ₗ
    ((g : SuperVect.Hom _ _).evenMap ∘ₗ
      (colourPowerEquiv k ℓ n).evenEquiv.symm.toLinearMap)
  oddMap := (colourPowerEquiv k ℓ n).oddEquiv.toLinearMap ∘ₗ
    ((g : SuperVect.Hom _ _).oddMap ∘ₗ
      (colourPowerEquiv k ℓ n).oddEquiv.symm.toLinearMap)

/-- Extending a colour-model endomorphism by one position:
conjugation of the whisker through the step equivalence. -/
noncomputable def colourExtend (n : ℕ)
    (T : colourPower k ℓ n ⟶ colourPower k ℓ n) :
    colourPower k ℓ (n + 1) ⟶ colourPower k ℓ (n + 1) where
  evenMap := (colourPowerStep k ℓ n).evenEquiv.toLinearMap ∘ₗ
    (((SuperVect.tensorHom T (SuperVect.Hom.id (stdSuperPair k ℓ)) :
        SuperVect.tensorObj (colourPower k ℓ n)
          (stdSuperPair k ℓ) ⟶
        SuperVect.tensorObj (colourPower k ℓ n)
          (stdSuperPair k ℓ)) : SuperVect.Hom _ _).evenMap ∘ₗ
      (colourPowerStep k ℓ n).evenEquiv.symm.toLinearMap)
  oddMap := (colourPowerStep k ℓ n).oddEquiv.toLinearMap ∘ₗ
    (((SuperVect.tensorHom T (SuperVect.Hom.id (stdSuperPair k ℓ)) :
        SuperVect.tensorObj (colourPower k ℓ n)
          (stdSuperPair k ℓ) ⟶
        SuperVect.tensorObj (colourPower k ℓ n)
          (stdSuperPair k ℓ)) : SuperVect.Hom _ _).oddMap ∘ₗ
      (colourPowerStep k ℓ n).oddEquiv.symm.toLinearMap)

/-- Conjugation preserves composition. -/
theorem toColour_comp (n : ℕ)
    (g₁ g₂ : superPow (stdSuperPair k ℓ) n ⟶
      superPow (stdSuperPair k ℓ) n) :
    toColour n (g₁ ≫ g₂) =
      toColour n g₁ ≫ toColour n g₂ := by
  refine SuperVect.Hom.ext ?_ ?_
  · refine LinearMap.ext (fun x => ?_)
    change (colourPowerEquiv k ℓ n).evenEquiv
      ((g₂ : SuperVect.Hom _ _).evenMap
        ((g₁ : SuperVect.Hom _ _).evenMap
          ((colourPowerEquiv k ℓ n).evenEquiv.symm x))) = _
    change _ = (colourPowerEquiv k ℓ n).evenEquiv
      ((g₂ : SuperVect.Hom _ _).evenMap
        ((colourPowerEquiv k ℓ n).evenEquiv.symm
          ((colourPowerEquiv k ℓ n).evenEquiv
            ((g₁ : SuperVect.Hom _ _).evenMap
              ((colourPowerEquiv k ℓ n).evenEquiv.symm x)))))
    rw [(colourPowerEquiv k ℓ n).evenEquiv.symm_apply_apply]
  · refine LinearMap.ext (fun x => ?_)
    change (colourPowerEquiv k ℓ n).oddEquiv
      ((g₂ : SuperVect.Hom _ _).oddMap
        ((g₁ : SuperVect.Hom _ _).oddMap
          ((colourPowerEquiv k ℓ n).oddEquiv.symm x))) = _
    change _ = (colourPowerEquiv k ℓ n).oddEquiv
      ((g₂ : SuperVect.Hom _ _).oddMap
        ((colourPowerEquiv k ℓ n).oddEquiv.symm
          ((colourPowerEquiv k ℓ n).oddEquiv
            ((g₁ : SuperVect.Hom _ _).oddMap
              ((colourPowerEquiv k ℓ n).oddEquiv.symm x)))))
    rw [(colourPowerEquiv k ℓ n).oddEquiv.symm_apply_apply]

/-- Conjugation preserves the identity. -/
theorem toColour_id (n : ℕ) :
    toColour (k := k) (ℓ := ℓ) n (𝟙 _) = 𝟙 _ := by
  refine SuperVect.Hom.ext ?_ ?_
  · refine LinearMap.ext (fun x => ?_)
    change (colourPowerEquiv k ℓ n).evenEquiv
      ((colourPowerEquiv k ℓ n).evenEquiv.symm x) = x
    rw [(colourPowerEquiv k ℓ n).evenEquiv.apply_symm_apply]
  · refine LinearMap.ext (fun x => ?_)
    change (colourPowerEquiv k ℓ n).oddEquiv
      ((colourPowerEquiv k ℓ n).oddEquiv.symm x) = x
    rw [(colourPowerEquiv k ℓ n).oddEquiv.apply_symm_apply]

end RS
