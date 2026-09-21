/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModAssoc
import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModPowDescent
import LeanPool.RegtsSevenster.RS.Classical.Deligne.TwistPow

/-!
# Merging the sandwich tower into a power pair

Each stage of the sandwich tower reassembles, up to associators
and braidings of the module tensor product, into a pair of module
powers: the stage `sandwichTower A M M' (k + 1)` carries `k + 2`
letters `M` interleaved with `k + 1` letters `M'`, and the
shuffle collects them into `modPowMod A M.X (k + 1)` (carrier
`modPow A M.X (k + 2)`, so `k + 2` letters `M`) tensored with
`modPowMod A M'.X k` (carrier `modPow A M'.X (k + 1)`, so `k + 1`
letters `M'`).

* `modTensorSwapModIso`: the braiding as a module isomorphism.
* `leftMergeModIso`: absorb a module into its own power from the
  left.
* `sandwichMergeModIso`: the merge, as modules.
* `sandwichMergeIso`: the merge at the carrier level.
* `isZero_sandwichTower_of_isZero_modPow`: vanishing of the power
  descends to every tower stage.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- The braiding of the module tensor product, as an isomorphism
of modules. -/
noncomputable def modTensorSwapModIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A]
    (P Q : Mod D A) :
    modTensorMod A P Q ≅ modTensorMod A Q P where
  hom := modTensorSwapMod A P Q
  inv := modTensorSwapMod A Q P
  hom_inv_id := modTensorSwapMod_modTensorSwapMod A P Q
  inv_hom_id := modTensorSwapMod_modTensorSwapMod A Q P

/-- **The left absorption**: a module merges into its own power
from the left, through the braiding, the bottom-stage
identification and the adjacent merge. -/
noncomputable def leftMergeModIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A]
    (N : Mod D A) (n : ℕ) :
    modTensorMod A N (modPowMod A N.X n) ≅
      modPowMod A N.X (n + 1) :=
  modTensorSwapModIso A N (modPowMod A N.X n) ≪≫
    modTensorMapIso A (Iso.refl (modPowMod A N.X n))
      (modPowModZeroIso A N).symm ≪≫
    powMergeModIso A N.X n

/-- **The sandwich merge**: the `(k + 1)`-st tower stage carries
`k + 2` letters `M` and `k + 1` letters `M'`, and reassembles as
the module tensor product of the corresponding module powers. -/
noncomputable def sandwichMergeModIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A) :
    (k : ℕ) →
      sandwichTower A M M' (k + 1) ≅
        modTensorMod A (modPowMod A M.X (k + 1))
          (modPowMod A M'.X k)
  | 0 =>
    modTensorSwapModIso A (modTensorMod A M M') M ≪≫
      (modTensorAssocModIso A M M M').symm ≪≫
      modTensorMapIso A
        (modTensorMapIso A (Iso.refl M)
            (modPowModZeroIso A M).symm ≪≫
          leftMergeModIso A M 0)
        (modPowModZeroIso A M').symm
  | (k + 1) =>
    modTensorMapIso A (Iso.refl (modTensorMod A M M'))
        (sandwichMergeModIso A M M' k) ≪≫
      modTensorAssocModIso A M M'
        (modTensorMod A (modPowMod A M.X (k + 1))
          (modPowMod A M'.X k)) ≪≫
      modTensorMapIso A (Iso.refl M)
        ((modTensorAssocModIso A M' (modPowMod A M.X (k + 1))
            (modPowMod A M'.X k)).symm ≪≫
          modTensorMapIso A
            (modTensorSwapModIso A M' (modPowMod A M.X (k + 1)))
            (Iso.refl (modPowMod A M'.X k)) ≪≫
          modTensorAssocModIso A (modPowMod A M.X (k + 1)) M'
            (modPowMod A M'.X k)) ≪≫
      (modTensorAssocModIso A M (modPowMod A M.X (k + 1))
          (modTensorMod A M' (modPowMod A M'.X k))).symm ≪≫
      modTensorMapIso A (leftMergeModIso A M (k + 1))
        (leftMergeModIso A M' k)

/-- **The sandwich merge at the carrier level**: the carrier of
the `(k + 1)`-st tower stage is the relative tensor product of
`modPow A M.X (k + 2)` with `modPow A M'.X (k + 1)`, presented
through the bundled module powers. -/
noncomputable def sandwichMergeIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (k : ℕ) :
    (sandwichTower A M M' (k + 1)).X ≅
      modTensor A (modPowMod A M.X (k + 1))
        (modPowMod A M'.X k) where
  hom := (sandwichMergeModIso A M M' k).hom.hom
  inv := (sandwichMergeModIso A M M' k).inv.hom
  hom_inv_id := congrArg Mod.Hom.hom
    (sandwichMergeModIso A M M' k).hom_inv_id
  inv_hom_id := congrArg Mod.Hom.hom
    (sandwichMergeModIso A M M' k).inv_hom_id

/-- **Vanishing descends the tower**: if the `(k + 2)`-nd relative
power of the module vanishes, so does the carrier of the
`(k + 1)`-st sandwich tower stage. -/
theorem isZero_sandwichTower_of_isZero_modPow
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (k : ℕ)
    (h : IsZero (modPow A M.X (k + 2))) :
    IsZero ((sandwichTower A M M' (k + 1)).X) :=
  (isZero_modTensor_left A (modPowMod A M.X (k + 1))
      (modPowMod A M'.X k) h).of_iso
    (sandwichMergeIso A M M' k)

end RS
