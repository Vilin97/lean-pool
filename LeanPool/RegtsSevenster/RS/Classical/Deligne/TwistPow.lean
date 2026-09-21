/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.PowSuccMod
import LeanPool.RegtsSevenster.RS.Classical.Deligne.PowZigzag
import LeanPool.RegtsSevenster.RS.Classical.Deligne.TwistShuffle

/-!
# Iso builders for the twisted power induction

Functoriality of the relative tensor and of the left twist on
isomorphisms: the two transport devices consumed by the k-fold
twisted power identification.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- The double twist transport: object and module isomorphisms
together. -/
noncomputable def tensorLeftModMapIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A]
    {V V' : D} (e : V ≅ V')
    {M N : Mod D A} (f : M ≅ N) :
    tensorLeftMod A V M ≅ tensorLeftMod A V' N :=
  tensorLeftModContextIso A e M ≪≫
    tensorLeftModWhiskerIso A V' f

section Powers

/-- The bottom power module is the module. -/
noncomputable def modPowModZeroIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D]
    (M : Mod D A) :
    modPowMod A M.X 0 ≅ M where
  hom := fromModPowModZero A M
  inv := toModPowModZero A M
  hom_inv_id := Mod.hom_ext _ _ (modPowOne A M.X).hom_inv_id
  inv_hom_id := Mod.hom_ext _ _ (modPowOne A M.X).inv_hom_id

/-- The merge of adjacent power modules, as a module
isomorphism. -/
noncomputable def powMergeModIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D]
    (X : D) [ModObj A X] (k : ℕ) :
    modTensorMod A (modPowMod A X k) (modPowMod A X 0) ≅
      modPowMod A X (k + 1) where
  hom := powMulMod A X k 0
  inv := powMulModInv A X k 0
  hom_inv_id := powMulMod_powMulModInv A X k 0
  inv_hom_id := powMulModInv_powMulMod A X k 0

/-- **The twisted power identification**: the relative powers of
a twisted module are the twist of the powers by the tensor powers
of the twisting object. -/
noncomputable def twistPowModIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D]
    (V : D) (R : Mod D A) :
    (k : ℕ) →
    (modPowMod A ((tensorLeftMod A V R).X) k ≅
      tensorLeftMod A (tensorPow D V (k + 1)) (modPowMod A R.X k))
  | 0 =>
    modPowModZeroIso A (tensorLeftMod A V R) ≪≫
      tensorLeftModMapIso A (λ_ V).symm
        (modPowModZeroIso A R).symm
  | (k + 1) =>
    (powMergeModIso A ((tensorLeftMod A V R).X) k).symm ≪≫
      modTensorMapIso A (twistPowModIso A V R k)
        (twistPowModIso A V R 0) ≪≫
      twistShuffleModIso A (tensorPow D V (k + 1))
        (tensorPow D V 1) (modPowMod A R.X k)
        (modPowMod A R.X 0) ≪≫
      tensorLeftModMapIso A (tensorPowConcat V (k + 1) 1)
        (powMergeModIso A R.X k)

end Powers

end RS
