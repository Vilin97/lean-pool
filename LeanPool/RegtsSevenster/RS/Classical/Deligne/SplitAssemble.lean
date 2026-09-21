/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SeedIns

/-!
# Assembly of the splitting-data entries on the graded carrier

The stage-level entries of the splitting algebra — the base
algebra, the module and the dual module — are lifted from the
two-index chain stages to the graded splitting algebra carrier:
the base enters the degree-zero component at the bottom stage,
the module the degree `+1` component and the dual module the
degree `−1` component.  The base entry carries the unit to the
unit, and both module entries are linear over the base through
the base entry, in the exact shape of the splitting data of the
Key Lemma.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **The base entry on the carrier**: the base algebra enters
the degree-zero component at the bottom stage. -/
noncomputable def splitOfBase
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D] [HasColimitsOfShape (Discrete ℤ) D]
    (d : ModDualityDatum A M M') :
    A ⟶ chainBGr A M M' d :=
  chainBaseStage A M M' d ≫ chainBGrCompι A M M' d 0 0 ≫
    chainBGrι A M M' d 0

/-- **The module entry on the carrier**: the module enters the
degree `+1` component at the bottom stage. -/
noncomputable def splitIns
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D] [HasColimitsOfShape (Discrete ℤ) D]
    (d : ModDualityDatum A M M') :
    M.X ⟶ chainBGr A M M' d :=
  chainSeedQ A M M' d ≫ chainBGrCompι A M M' d 1 0 ≫
    chainBGrι A M M' d 1

/-- **The dual entry on the carrier**: the dual module enters the
degree `−1` component at the bottom stage, through the arity
transport identifying the bottom stage of the `−1` line. -/
noncomputable def splitIns'
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D] [HasColimitsOfShape (Discrete ℤ) D]
    (d : ModDualityDatum A M M') :
    M'.X ⟶ chainBGr A M M' d :=
  chainSeedP A M M' d ≫
    chainStage2Cast A M M'
      (by omega : 1 = (-(-1 : ℤ)).toNat + 0)
      (by omega : 0 = ((-1 : ℤ)).toNat + 0) ≫
    chainBGrCompι A M M' d (-1) 0 ≫
    chainBGrι A M M' d (-1)

/-- **The base entry carries the unit to the unit**: the carrier
entry of the base algebra is unital. -/
theorem splitOfBase_unit
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D] [HasColimitsOfShape (Discrete ℤ) D]
    (d : ModDualityDatum A M M') :
    η[A] ≫ splitOfBase A M M' d = chainBGrUnit A M M' d := by
  have h1 : η[A] ≫ splitOfBase A M M' d =
      chainSeed A M M' d ≫ chainBGrCompι A M M' d 0 0 ≫
        chainBGrι A M M' d 0 := by
    rw [splitOfBase, reassoc_of% unit_chainBaseStage A M M' d]
    rfl
  have h2 : chainBGrUnit A M M' d =
      chainSeed A M M' d ≫ chainBGrCompι A M M' d 0 0 ≫
        chainBGrι A M M' d 0 := by
    rw [chainBGrUnit, ← Category.assoc,
      chainBUnit_chainBGrComponentZeroIso_inv, Category.assoc]
  exact h1.trans h2.symm

section Linear

-- Raised budget: linearity of the insertion unfolds the module
-- action through the duality datum on one generator.
/-- **The module entry is linear over the base**, through the
carrier entry of the base algebra: the splitting-data shape of
the linearity law. -/
theorem splitIns_linear
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
    actLeft A M.X ≫ splitIns A M M' d =
      (A ◁ splitIns A M M' d) ≫
        (splitOfBase A M M' d ▷ chainBGr A M M' d) ≫
        (letI := chainBGrMonObj A M M' d;
          μ[chainBGr A M M' d]) := by
  show actLeft A M.X ≫ splitIns A M M' d =
    (A ◁ splitIns A M M' d) ≫
      (splitOfBase A M M' d ▷ chainBGr A M M' d) ≫
      chainBGrMul A M M' d
  refine Eq.symm ?_
  rw [← Category.assoc, ← MonoidalCategory.tensorHom_def',
    splitOfBase, splitIns,
    ← MonoidalCategory.tensorHom_comp_tensorHom,
    ← MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [ι_tensorHom_chainBGrMul A M M' d 0 1]
  show (chainBaseStage A M M' d ⊗ₘ chainSeedQ A M M' d) ≫
      (chainBGrCompι A M M' d 0 0 ⊗ₘ
        chainBGrCompι A M M' d 1 0) ≫
      chainBGrCompMul A M M' d 0 1 ≫
      chainBGrι A M M' d (0 + 1) =
    actLeft A M.X ≫ chainSeedQ A M M' d ≫
      chainBGrCompι A M M' d 1 0 ≫ chainBGrι A M M' d 1
  have hz : (chainBGrCompι A M M' d 0 0 ⊗ₘ
        chainBGrCompι A M M' d 1 0 :
        chainStage2 A M M' 0 0 ⊗ chainStage2 A M M' 0 1 ⟶
          chainBGrComponent A M M' d 0 ⊗
            chainBGrComponent A M M' d 1) ≫
      chainBGrCompMul A M M' d 0 1 =
      (chainMul2 A M M' 0 0 0 1 ≫
        chainStage2Cast A M M'
          (by omega : 0 + 1 + 0 =
            (-((0 : ℤ) + 1)).toNat + (0 + 1))
          (by omega : 0 + 1 + 1 =
            ((0 : ℤ) + 1).toNat + (0 + 1))) ≫
      chainBGrCompι A M M' d (0 + 1) (0 + 1) :=
    ι_tensorHom_chainBGrCompMul_zero_left A M M' d 1 0
  rw [reassoc_of% hz]
  rw [MonoidalCategory.tensorHom_def' (chainBaseStage A M M' d)
    (chainSeedQ A M M' d)]
  simp only [Category.assoc]
  have e1 : chainBGrCompι A M M' d (0 + 1) (0 + 1) ≫
      chainBGrι A M M' d (0 + 1) =
      chainStage2Cast A M M'
          (by omega : (-((0 : ℤ) + 1)).toNat + (0 + 1) =
            (-(1 : ℤ)).toNat + (0 + 1))
          (by omega : ((0 : ℤ) + 1).toNat + (0 + 1) =
            (1 : ℤ).toNat + (0 + 1)) ≫
        chainBGrCompι A M M' d 1 (0 + 1) ≫
        chainBGrι A M M' d 1 := by
    refine Eq.trans (whisker_eq _
      (eqToHom_chainBGrι A M M' d (Int.zero_add 1)).symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker (chainBGrCompι_eqToHom
      A M M' d (Int.zero_add 1) (0 + 1)) _) ?_
    exact Category.assoc _ _ _
  have e2 : chainStage2Cast A M M'
        (by omega : 0 + 1 = 0 + 1 + 0)
        (by omega : 1 + 1 = 0 + 1 + 1) ≫
      chainStage2Cast A M M'
        (by omega : 0 + 1 + 0 =
          (-((0 : ℤ) + 1)).toNat + (0 + 1))
        (by omega : 0 + 1 + 1 =
          ((0 : ℤ) + 1).toNat + (0 + 1)) ≫
      chainStage2Cast A M M'
        (by omega : (-((0 : ℤ) + 1)).toNat + (0 + 1) =
          (-(1 : ℤ)).toNat + (0 + 1))
        (by omega : ((0 : ℤ) + 1).toNat + (0 + 1) =
          (1 : ℤ).toNat + (0 + 1)) ≫
      chainBGrCompι A M M' d 1 (0 + 1) ≫
      chainBGrι A M M' d 1 =
      chainStage2Cast A M M'
        (by omega : 0 + 1 = (-(1 : ℤ)).toNat + (0 + 1))
        (by omega : 1 + 1 = (1 : ℤ).toNat + (0 + 1)) ≫
      chainBGrCompι A M M' d 1 (0 + 1) ≫
      chainBGrι A M M' d 1 := by
    refine Eq.trans (chainStage2Cast_trans_assoc
      A M M' _ _ _ _ _) ?_
    exact chainStage2Cast_trans_assoc A M M' _ _ _ _ _
  have e3 : chainStage2Cast A M M'
        (by omega : 0 + 1 = (-(1 : ℤ)).toNat + (0 + 1))
        (by omega : 1 + 1 = (1 : ℤ).toNat + (0 + 1)) ≫
      chainBGrCompι A M M' d 1 (0 + 1) ≫
      chainBGrι A M M' d 1 =
      chainBGrCompι A M M' d 1 (0 + 1) ≫
      chainBGrι A M M' d 1 := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact eq_whisker (chainStage2Cast_chainBGrCompι A M M' d 1
      (rfl : (0 + 1 : ℕ) = 0 + 1)) _
  have hd : chainDelta2 A M M' d 0 1 ≫
      chainBGrCompι A M M' d 1 (0 + 1) =
      chainBGrCompι A M M' d 1 0 :=
    chainDelta2_chainBGrCompι A M M' d 1 0
  have habs : (chainDelta2 A M M' d 0 1 ≫
        chainStage2Cast A M M'
          (by omega : 0 + 1 = 0 + 1 + 0)
          (by omega : 1 + 1 = 0 + 1 + 1)) ≫
      chainStage2Cast A M M'
          (by omega : 0 + 1 + 0 =
            (-((0 : ℤ) + 1)).toNat + (0 + 1))
          (by omega : 0 + 1 + 1 =
            ((0 : ℤ) + 1).toNat + (0 + 1)) ≫
        chainBGrCompι A M M' d (0 + 1) (0 + 1) ≫
        chainBGrι A M M' d (0 + 1) =
      chainBGrCompι A M M' d 1 0 ≫ chainBGrι A M M' d 1 := by
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (whisker_eq _
      (whisker_eq _ e1))) ?_
    refine Eq.trans (whisker_eq _ e2) ?_
    refine Eq.trans (whisker_eq _ e3) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact eq_whisker hd _
  have h1 : (chainBaseStage A M M' d ▷
        chainStage2 A M M' 0 1) ≫
      chainMul2 A M M' 0 0 0 1 ≫
      chainStage2Cast A M M'
        (by omega : 0 + 1 + 0 =
          (-((0 : ℤ) + 1)).toNat + (0 + 1))
        (by omega : 0 + 1 + 1 =
          ((0 : ℤ) + 1).toNat + (0 + 1)) ≫
      chainBGrCompι A M M' d (0 + 1) (0 + 1) ≫
      chainBGrι A M M' d (0 + 1) =
      modTensorAct A (symPowMod A M'.X 0) (symPowMod A M.X 1) ≫
        (chainDelta2 A M M' d 0 1 ≫
          chainStage2Cast A M M'
            (by omega : 0 + 1 = 0 + 1 + 0)
            (by omega : 1 + 1 = 0 + 1 + 1)) ≫
        chainStage2Cast A M M'
            (by omega : 0 + 1 + 0 =
              (-((0 : ℤ) + 1)).toNat + (0 + 1))
            (by omega : 0 + 1 + 1 =
              ((0 : ℤ) + 1).toNat + (0 + 1)) ≫
          chainBGrCompι A M M' d (0 + 1) (0 + 1) ≫
          chainBGrι A M M' d (0 + 1) :=
    (Category.assoc _ _ _).symm.trans
      ((eq_whisker (chainBaseStage_mul2 A M M' d 0 1) _).trans
        (Category.assoc _ _ _))
  refine Eq.trans (whisker_eq _ h1) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (chainSeedQ_linear A M M' d).symm _) ?_
  refine Eq.trans (whisker_eq _ habs) ?_
  exact Category.assoc _ _ _

-- Raised budget: linearity of the insertion unfolds the module
-- action through the duality datum on one generator.
/-- **The dual entry is linear over the base**, through the
carrier entry of the base algebra: the splitting-data shape of
the linearity law for the dual module. -/
theorem splitIns'_linear
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
    actLeft A M'.X ≫ splitIns' A M M' d =
      (A ◁ splitIns' A M M' d) ≫
        (splitOfBase A M M' d ▷ chainBGr A M M' d) ≫
        (letI := chainBGrMonObj A M M' d;
          μ[chainBGr A M M' d]) := by
  show actLeft A M'.X ≫ splitIns' A M M' d =
    (A ◁ splitIns' A M M' d) ≫
      (splitOfBase A M M' d ▷ chainBGr A M M' d) ≫
      chainBGrMul A M M' d
  refine Eq.symm ?_
  rw [← Category.assoc, ← MonoidalCategory.tensorHom_def',
    splitOfBase, splitIns',
    ← Category.assoc (chainSeedP A M M' d),
    ← MonoidalCategory.tensorHom_comp_tensorHom,
    ← MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [ι_tensorHom_chainBGrMul A M M' d 0 (-1)]
  have hzm : (chainBGrCompι A M M' d 0 0 ⊗ₘ
        chainBGrCompι A M M' d (-1) 0 :
        chainStage2 A M M' 0 0 ⊗
          chainStage2 A M M' ((-(-1 : ℤ)).toNat + 0)
            ((-1 : ℤ).toNat + 0) ⟶
          chainBGrComponent A M M' d 0 ⊗
            chainBGrComponent A M M' d (-1)) ≫
      chainBGrCompMul A M M' d 0 (-1) =
      (chainMul2 A M M' 0 0 ((-(-1 : ℤ)).toNat + 0)
          ((-1 : ℤ).toNat + 0) ≫
        chainStage2Cast A M M'
          (by omega : 0 + 1 + ((-(-1 : ℤ)).toNat + 0) =
            (-((0 : ℤ) + -1)).toNat +
              (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
                ((0 : ℤ) + -1).toNat)))
          (by omega : 0 + 1 + ((-1 : ℤ).toNat + 0) =
            ((0 : ℤ) + -1).toNat +
              (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
                ((0 : ℤ) + -1).toNat)))) ≫
      chainBGrCompι A M M' d ((0 : ℤ) + -1)
        (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
          ((0 : ℤ) + -1).toNat)) :=
    ι_tensorHom_chainBGrCompMul_zero_left A M M' d (-1) 0
  rw [reassoc_of% hzm]
  rw [MonoidalCategory.tensorHom_def' (chainBaseStage A M M' d)
    (chainSeedP A M M' d ≫ chainStage2Cast A M M'
      (by omega : 1 = (-(-1 : ℤ)).toNat + 0)
      (by omega : 0 = ((-1 : ℤ)).toNat + 0))]
  simp only [Category.assoc]
  have e1m : chainBGrCompι A M M' d ((0 : ℤ) + -1)
        (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
          ((0 : ℤ) + -1).toNat)) ≫
      chainBGrι A M M' d ((0 : ℤ) + -1) =
      chainStage2Cast A M M'
          (by omega : (-((0 : ℤ) + -1)).toNat +
              (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
                ((0 : ℤ) + -1).toNat)) =
            (-(-1 : ℤ)).toNat +
              (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
                ((0 : ℤ) + -1).toNat)))
          (by omega : ((0 : ℤ) + -1).toNat +
              (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
                ((0 : ℤ) + -1).toNat)) =
            (-1 : ℤ).toNat +
              (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
                ((0 : ℤ) + -1).toNat))) ≫
        chainBGrCompι A M M' d (-1)
          (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
            ((0 : ℤ) + -1).toNat)) ≫
        chainBGrι A M M' d (-1) := by
    refine Eq.trans (whisker_eq _
      (eqToHom_chainBGrι A M M' d (Int.zero_add (-1))).symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker (chainBGrCompι_eqToHom
      A M M' d (Int.zero_add (-1))
      (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
        ((0 : ℤ) + -1).toNat))) _) ?_
    exact Category.assoc _ _ _
  have e2m : chainStage2Cast A M M'
        (by omega : (-(-1 : ℤ)).toNat + 0 + 1 =
          0 + 1 + ((-(-1 : ℤ)).toNat + 0))
        (by omega : (-1 : ℤ).toNat + 0 + 1 =
          0 + 1 + ((-1 : ℤ).toNat + 0)) ≫
      chainStage2Cast A M M'
        (by omega : 0 + 1 + ((-(-1 : ℤ)).toNat + 0) =
          (-((0 : ℤ) + -1)).toNat +
            (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
              ((0 : ℤ) + -1).toNat)))
        (by omega : 0 + 1 + ((-1 : ℤ).toNat + 0) =
          ((0 : ℤ) + -1).toNat +
            (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
              ((0 : ℤ) + -1).toNat))) ≫
      chainStage2Cast A M M'
        (by omega : (-((0 : ℤ) + -1)).toNat +
            (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
              ((0 : ℤ) + -1).toNat)) =
          (-(-1 : ℤ)).toNat +
            (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
              ((0 : ℤ) + -1).toNat)))
        (by omega : ((0 : ℤ) + -1).toNat +
            (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
              ((0 : ℤ) + -1).toNat)) =
          (-1 : ℤ).toNat +
            (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
              ((0 : ℤ) + -1).toNat))) ≫
      chainBGrCompι A M M' d (-1)
        (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
          ((0 : ℤ) + -1).toNat)) ≫
      chainBGrι A M M' d (-1) =
      chainStage2Cast A M M'
        (by omega : (-(-1 : ℤ)).toNat + 0 + 1 =
          (-(-1 : ℤ)).toNat +
            (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
              ((0 : ℤ) + -1).toNat)))
        (by omega : (-1 : ℤ).toNat + 0 + 1 =
          (-1 : ℤ).toNat +
            (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
              ((0 : ℤ) + -1).toNat))) ≫
      chainBGrCompι A M M' d (-1)
        (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
          ((0 : ℤ) + -1).toNat)) ≫
      chainBGrι A M M' d (-1) := by
    refine Eq.trans (chainStage2Cast_trans_assoc
      A M M' _ _ _ _ _) ?_
    exact chainStage2Cast_trans_assoc A M M' _ _ _ _ _
  have e3m : chainStage2Cast A M M'
        (by omega : (-(-1 : ℤ)).toNat + 0 + 1 =
          (-(-1 : ℤ)).toNat +
            (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
              ((0 : ℤ) + -1).toNat)))
        (by omega : (-1 : ℤ).toNat + 0 + 1 =
          (-1 : ℤ).toNat +
            (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
              ((0 : ℤ) + -1).toNat))) ≫
      chainBGrCompι A M M' d (-1)
        (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
          ((0 : ℤ) + -1).toNat)) ≫
      chainBGrι A M M' d (-1) =
      chainBGrCompι A M M' d (-1) (0 + 1) ≫
      chainBGrι A M M' d (-1) := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact eq_whisker (chainStage2Cast_chainBGrCompι A M M' d (-1)
      (by omega : (0 + 1 : ℕ) =
        0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
          ((0 : ℤ) + -1).toNat))) _
  have hdm : chainDelta2 A M M' d ((-(-1 : ℤ)).toNat + 0)
        ((-1 : ℤ).toNat + 0) ≫
      chainBGrCompι A M M' d (-1) (0 + 1) =
      chainBGrCompι A M M' d (-1) 0 :=
    chainDelta2_chainBGrCompι A M M' d (-1) 0
  have habsm : (chainDelta2 A M M' d ((-(-1 : ℤ)).toNat + 0)
          ((-1 : ℤ).toNat + 0) ≫
        chainStage2Cast A M M'
          (by omega : (-(-1 : ℤ)).toNat + 0 + 1 =
            0 + 1 + ((-(-1 : ℤ)).toNat + 0))
          (by omega : (-1 : ℤ).toNat + 0 + 1 =
            0 + 1 + ((-1 : ℤ).toNat + 0))) ≫
      chainStage2Cast A M M'
          (by omega : 0 + 1 + ((-(-1 : ℤ)).toNat + 0) =
            (-((0 : ℤ) + -1)).toNat +
              (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
                ((0 : ℤ) + -1).toNat)))
          (by omega : 0 + 1 + ((-1 : ℤ).toNat + 0) =
            ((0 : ℤ) + -1).toNat +
              (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
                ((0 : ℤ) + -1).toNat))) ≫
        chainBGrCompι A M M' d ((0 : ℤ) + -1)
          (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
            ((0 : ℤ) + -1).toNat)) ≫
        chainBGrι A M M' d ((0 : ℤ) + -1) =
      chainBGrCompι A M M' d (-1) 0 ≫
        chainBGrι A M M' d (-1) := by
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (whisker_eq _
      (whisker_eq _ e1m))) ?_
    refine Eq.trans (whisker_eq _ e2m) ?_
    refine Eq.trans (whisker_eq _ e3m) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact eq_whisker hdm _
  have h1m : (chainBaseStage A M M' d ▷
        chainStage2 A M M' ((-(-1 : ℤ)).toNat + 0)
          ((-1 : ℤ).toNat + 0)) ≫
      chainMul2 A M M' 0 0 ((-(-1 : ℤ)).toNat + 0)
        ((-1 : ℤ).toNat + 0) ≫
      chainStage2Cast A M M'
        (by omega : 0 + 1 + ((-(-1 : ℤ)).toNat + 0) =
          (-((0 : ℤ) + -1)).toNat +
            (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
              ((0 : ℤ) + -1).toNat)))
        (by omega : 0 + 1 + ((-1 : ℤ).toNat + 0) =
          ((0 : ℤ) + -1).toNat +
            (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
              ((0 : ℤ) + -1).toNat))) ≫
      chainBGrCompι A M M' d ((0 : ℤ) + -1)
        (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
          ((0 : ℤ) + -1).toNat)) ≫
      chainBGrι A M M' d ((0 : ℤ) + -1) =
      modTensorAct A (symPowMod A M'.X ((-(-1 : ℤ)).toNat + 0))
          (symPowMod A M.X ((-1 : ℤ).toNat + 0)) ≫
        (chainDelta2 A M M' d ((-(-1 : ℤ)).toNat + 0)
            ((-1 : ℤ).toNat + 0) ≫
          chainStage2Cast A M M'
            (by omega : (-(-1 : ℤ)).toNat + 0 + 1 =
              0 + 1 + ((-(-1 : ℤ)).toNat + 0))
            (by omega : (-1 : ℤ).toNat + 0 + 1 =
              0 + 1 + ((-1 : ℤ).toNat + 0))) ≫
        chainStage2Cast A M M'
            (by omega : 0 + 1 + ((-(-1 : ℤ)).toNat + 0) =
              (-((0 : ℤ) + -1)).toNat +
                (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
                  ((0 : ℤ) + -1).toNat)))
            (by omega : 0 + 1 + ((-1 : ℤ).toNat + 0) =
              ((0 : ℤ) + -1).toNat +
                (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
                  ((0 : ℤ) + -1).toNat))) ≫
          chainBGrCompι A M M' d ((0 : ℤ) + -1)
            (0 + 1 + 0 + ((0 : ℤ).toNat + (-1 : ℤ).toNat -
              ((0 : ℤ) + -1).toNat)) ≫
          chainBGrι A M M' d ((0 : ℤ) + -1) :=
    (Category.assoc _ _ _).symm.trans
      ((eq_whisker (chainBaseStage_mul2 A M M' d
        ((-(-1 : ℤ)).toNat + 0) ((-1 : ℤ).toNat + 0)) _).trans
        (Category.assoc _ _ _))
  have hqm : (A ◁ (chainSeedP A M M' d ≫
        chainStage2Cast A M M'
          (by omega : 1 = (-(-1 : ℤ)).toNat + 0)
          (by omega : 0 = ((-1 : ℤ)).toNat + 0))) ≫
      modTensorAct A (symPowMod A M'.X ((-(-1 : ℤ)).toNat + 0))
        (symPowMod A M.X ((-1 : ℤ).toNat + 0)) =
      (actLeft A M'.X ≫ chainSeedP A M M' d) ≫
        chainStage2Cast A M M'
          (by omega : 1 = (-(-1 : ℤ)).toNat + 0)
          (by omega : 0 = ((-1 : ℤ)).toNat + 0) := by
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp A
        (chainSeedP A M M' d) _) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (chainStage2Cast_actLeft A M M'
        (by omega : 1 = (-(-1 : ℤ)).toNat + 0)
        (by omega : 0 = ((-1 : ℤ)).toNat + 0))) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact eq_whisker (chainSeedP_linear A M M' d).symm _
  refine Eq.trans (whisker_eq _ h1m) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker hqm _) ?_
  refine Eq.trans (whisker_eq _ habsm) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact Category.assoc _ _ _

end Linear

end RS
