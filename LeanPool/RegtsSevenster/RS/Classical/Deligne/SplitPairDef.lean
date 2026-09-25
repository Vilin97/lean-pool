/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SplitAssemble
import LeanPool.RegtsSevenster.RS.Classical.Deligne.PairCarrier

/-!
# Defining equation of the carrier-level pair product

Through the projection onto the relative tensor product, the
carrier-level pair product of the splitting data is computed by
the graded multiplication of the carrier: the two module entries
enter their components at the bottom stage and multiply into the
degree-zero component two stages up.  This is the defining
equation of the pair product field of the splitting data of the
Key Lemma.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- A component insertion followed by the carrier inclusion,
transported along an equality of degrees. -/
private theorem compι_ι_degCast
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D] [HasColimitsOfShape (Discrete ℤ) D]
    (d : ModDualityDatum A M M')
    {x y : ℤ} (h : x = y) (k : ℕ) :
    chainBGrCompι A M M' d x k ≫ chainBGrι A M M' d x =
      chainStage2Cast A M M'
          (by omega : (-x).toNat + k = (-y).toNat + k)
          (by omega : x.toNat + k = y.toNat + k) ≫
        chainBGrCompι A M M' d y k ≫ chainBGrι A M M' d y := by
  refine Eq.trans (whisker_eq _
    (eqToHom_chainBGrι A M M' d h).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (chainBGrCompι_eqToHom A M M' d h k) _) ?_
  exact Category.assoc _ _ _

-- Raised budget: the relative tensor projection unfolds against
-- the pair multiplication on one generator.
/-- **Defining equation of the carrier-level pair product**:
through the projection of the relative tensor product, the pair
product is the graded product of the two module entries. -/
theorem modTensorπ_splitPairMul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D] [HasColimitsOfShape (Discrete ℤ) D]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    [∀ X : D, PreservesColimitsOfShape (Discrete ℤ) (tensorLeft X)]
    (d : ModDualityDatum A M M') :
    modTensorπ A M M' ≫ splitPairMul A M M' d =
      (splitIns A M M' d ⊗ₘ splitIns' A M M' d) ≫
        (letI := chainBGrMonObj A M M' d;
          μ[chainBGr A M M' d]) := by
  change modTensorπ A M M' ≫ splitPairMul A M M' d =
    (splitIns A M M' d ⊗ₘ splitIns' A M M' d) ≫
      chainBGrMul A M M' d
  have hcastL : chainStage2Cast A M M'
        (by omega : 2 = (-(0 : ℤ)).toNat + 2)
        (by omega : 2 = (0 : ℤ).toNat + 2) ≫
      chainBGrCompι A M M' d 0 2 =
      chainBGrCompι A M M' d 0 2 :=
    chainStage2Cast_chainBGrCompι A M M' d 0
      (rfl : (2 : ℕ) = 2)
  have hL : modTensorπ A M M' ≫ splitPairMul A M M' d =
      chainPairRaw A M M' d ≫
        chainBGrCompι A M M' d 0 2 ≫ chainBGrι A M M' d 0 := by
    change modTensorπ A M M' ≫ chainPairMul A M M' d ≫
        chainStage2Cast A M M'
          (by omega : 2 = (-(0 : ℤ)).toNat + 2)
          (by omega : 2 = (0 : ℤ).toNat + 2) ≫
        chainBGrCompι A M M' d 0 2 ≫ chainBGrι A M M' d 0 =
      chainPairRaw A M M' d ≫
        chainBGrCompι A M M' d 0 2 ≫ chainBGrι A M M' d 0
    rw [modTensorπ_chainPairMul_assoc A M M' d,
      reassoc_of% hcastL]
  have h1 : (chainSeedQ A M M' d ⊗ₘ
        (chainSeedP A M M' d ≫ chainStage2Cast A M M'
          (by omega : 1 = (-(-1 : ℤ)).toNat + 0)
          (by omega : 0 = ((-1 : ℤ)).toNat + 0))) ≫
      (chainBGrCompι A M M' d 1 0 ⊗ₘ
        chainBGrCompι A M M' d (-1) 0) ≫
      (chainBGrι A M M' d 1 ⊗ₘ chainBGrι A M M' d (-1)) =
      splitIns A M M' d ⊗ₘ splitIns' A M M' d := by
    refine Eq.trans (whisker_eq _
      (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _)) ?_
    refine Eq.trans
      (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _) ?_
    rw [splitIns, splitIns']
    simp only [Category.assoc]
  have hw : chainSeedQ A M M' d ⊗ₘ
        (chainSeedP A M M' d ≫ chainStage2Cast A M M'
          (by omega : 1 = (-(-1 : ℤ)).toNat + 0)
          (by omega : 0 = ((-1 : ℤ)).toNat + 0)) =
      (chainSeedQ A M M' d ⊗ₘ chainSeedP A M M' d) ≫
        (chainStage2 A M M' 0 1 ◁ chainStage2Cast A M M'
          (by omega : 1 = (-(-1 : ℤ)).toNat + 0)
          (by omega : 0 = ((-1 : ℤ)).toNat + 0)) := by
    rw [← MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom,
      Category.comp_id]
  have h4 := whiskerLeft_chainStage2Cast_chainMul2 A M M' 0 1
    (by omega : 1 = (-(-1 : ℤ)).toNat + 0)
    (by omega : 0 = ((-1 : ℤ)).toNat + 0)
  have hfront : (chainSeedQ A M M' d ⊗ₘ
        (chainSeedP A M M' d ≫ chainStage2Cast A M M'
          (by omega : 1 = (-(-1 : ℤ)).toNat + 0)
          (by omega : 0 = ((-1 : ℤ)).toNat + 0))) ≫
      chainMul2 A M M' ((-(1 : ℤ)).toNat + 0)
        ((1 : ℤ).toNat + 0) ((-(-1 : ℤ)).toNat + 0)
        (((-1 : ℤ)).toNat + 0) =
      chainPairRaw A M M' d ≫ chainStage2Cast A M M'
        (by omega : 0 + 1 + 1 =
          0 + 1 + ((-(-1 : ℤ)).toNat + 0))
        (by omega : 1 + 1 + 0 =
          1 + 1 + (((-1 : ℤ)).toNat + 0)) := by
    refine Eq.trans (eq_whisker hw _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ h4) ?_
    exact (Category.assoc _ _ _).symm
  have hS : (2 : ℕ) = 0 + 1 + 0 +
      ((1 : ℤ).toNat + (-1 : ℤ).toNat -
        ((1 : ℤ) + -1).toNat) := by omega
  have habs := chainStage2Cast_chainBGrCompι A M M' d 0 hS
  have hR : (splitIns A M M' d ⊗ₘ splitIns' A M M' d) ≫
      chainBGrMul A M M' d =
      chainPairRaw A M M' d ≫
        chainBGrCompι A M M' d 0 2 ≫ chainBGrι A M M' d 0 := by
    refine Eq.trans
      (eq_whisker h1.symm (chainBGrMul A M M' d)) ?_
    simp only [Category.assoc]
    refine Eq.trans (whisker_eq _ (whisker_eq _
      (ι_tensorHom_chainBGrMul A M M' d 1 (-1)))) ?_
    refine Eq.trans (whisker_eq _
      (Category.assoc _ _ _).symm) ?_
    refine Eq.trans (whisker_eq _ (eq_whisker
      (ι_tensorHom_chainBGrCompMul A M M' d 1 (-1) 0 0) _)) ?_
    refine Eq.trans (whisker_eq _ ((Category.assoc _ _ _).trans
      (Category.assoc _ _ _))) ?_
    refine Eq.trans (whisker_eq _ (whisker_eq _ (whisker_eq _
      (compι_ι_degCast A M M' d
        (by omega : (1 : ℤ) + -1 = 0) _)))) ?_
    refine Eq.trans (whisker_eq _ (whisker_eq _
      (chainStage2Cast_trans_assoc A M M' _ _ _ _ _))) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker hfront _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (chainStage2Cast_trans_assoc A M M' _ _ _ _ _)) ?_
    exact whisker_eq _ ((Category.assoc _ _ _).symm.trans
      (eq_whisker habs _))
  exact hL.trans hR.symm

end RS
