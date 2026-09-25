/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SeedIns

/-!
# The pair product on the graded carrier

The descended pair product of the module entries lands two stages
up the degree-zero line of the graded splitting algebra carrier.
Through the component insertions, the transitions are absorbed
and the copair element multiplies to the unit of the carrier —
the section identity of the splitting data of the Key Lemma.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **The pair product on the carrier**: the descended pair
product of the entries, entering the degree-zero component two
stages up. -/
noncomputable def splitPairMul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D] [HasColimitsOfShape (Discrete ℤ) D]
    (d : ModDualityDatum A M M') :
    modTensor A M M' ⟶ chainBGr A M M' d :=
  chainPairMul A M M' d ≫
    chainStage2Cast A M M'
      (by omega : 2 = (-(0 : ℤ)).toNat + 2)
      (by omega : 2 = (0 : ℤ).toNat + 2) ≫
    chainBGrCompι A M M' d 0 2 ≫
    chainBGrι A M M' d 0

/-- **The copair element multiplies to the unit on the carrier**:
the section identity of the splitting data. -/
theorem copairUnit_splitPairMul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D] [HasColimitsOfShape (Discrete ℤ) D]
    (d : ModDualityDatum A M M') :
    copairUnit A M M' d ≫ splitPairMul A M M' d =
      chainBGrUnit A M M' d := by
  have hA : chainStage2Cast A M M'
        (by omega : 2 = (-(0 : ℤ)).toNat + 2)
        (by omega : 2 = (0 : ℤ).toNat + 2) ≫
      chainBGrCompι A M M' d 0 2 =
      chainBGrCompι A M M' d 0 2 :=
    chainStage2Cast_chainBGrCompι A M M' d 0
      (rfl : (2 : ℕ) = 2)
  have hB : chainDelta2 A M M' d 1 1 ≫
      chainBGrCompι A M M' d 0 2 =
      chainBGrCompι A M M' d 0 1 :=
    chainDelta2_chainBGrCompι A M M' d 0 1
  have hC : chainDelta2 A M M' d 0 0 ≫
      chainBGrCompι A M M' d 0 1 =
      chainBGrCompι A M M' d 0 0 :=
    chainDelta2_chainBGrCompι A M M' d 0 0
  have k1 : chainStage2Cast A M M'
        (by omega : 2 = (-(0 : ℤ)).toNat + 2)
        (by omega : 2 = (0 : ℤ).toNat + 2) ≫
      chainBGrCompι A M M' d 0 2 ≫ chainBGrι A M M' d 0 =
      chainBGrCompι A M M' d 0 2 ≫ chainBGrι A M M' d 0 :=
    (Category.assoc _ _ _).symm.trans (eq_whisker hA _)
  have k2 : chainDelta2 A M M' d 1 1 ≫
      chainBGrCompι A M M' d 0 2 ≫ chainBGrι A M M' d 0 =
      chainBGrCompι A M M' d 0 1 ≫ chainBGrι A M M' d 0 :=
    (Category.assoc _ _ _).symm.trans (eq_whisker hB _)
  have k3 : chainDelta2 A M M' d 0 0 ≫
      chainBGrCompι A M M' d 0 1 ≫ chainBGrι A M M' d 0 =
      chainBGrCompι A M M' d 0 0 ≫ chainBGrι A M M' d 0 :=
    (Category.assoc _ _ _).symm.trans (eq_whisker hC _)
  have h2 : chainBGrUnit A M M' d =
      chainSeed A M M' d ≫ chainBGrCompι A M M' d 0 0 ≫
        chainBGrι A M M' d 0 := by
    erw [chainBGrUnit, ← Category.assoc,
      chainBUnit_chainBGrComponentZeroIso_inv, Category.assoc]
  change copairUnit A M M' d ≫ chainPairMul A M M' d ≫
      chainStage2Cast A M M'
        (by omega : 2 = (-(0 : ℤ)).toNat + 2)
        (by omega : 2 = (0 : ℤ).toNat + 2) ≫
      chainBGrCompι A M M' d 0 2 ≫ chainBGrι A M M' d 0 =
    chainBGrUnit A M M' d
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans
    (eq_whisker (copairUnit_chainPairMul A M M' d) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans
    (whisker_eq _ (whisker_eq _ (whisker_eq _ k1))) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ k2)) ?_
  refine Eq.trans (whisker_eq _ k3) ?_
  exact h2.symm

end RS
