/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SplitAssemble

/-!
# The base entry is multiplicative

The carrier entry of the base algebra respects the
multiplication: multiplying in the base and entering the graded
splitting algebra carrier agrees with entering twice and
multiplying on the carrier.  Together with unitality this is the
monoid-morphism property of the base entry of the splitting
data.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **The base entry is multiplicative against the base
action**: multiplying in the base before entering the bottom
stage is entering on the right tensor factor and acting. -/
theorem mul_chainBaseStage
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    μ[A] ≫ chainBaseStage A M M' d =
      (A ◁ chainBaseStage A M M' d) ≫
        modTensorAct A (symPowMod A M'.X 0)
          (symPowMod A M.X 0) := by
  refine Eq.symm ?_
  have ha : (A ◁ modTensorAct A (symPowMod A M'.X 0)
        (symPowMod A M.X 0)) ≫
      modTensorAct A (symPowMod A M'.X 0) (symPowMod A M.X 0) =
      (α_ A A (chainStage2 A M M' 0 0)).inv ≫
        (μ[A] ▷ chainStage2 A M M' 0 0) ≫
        modTensorAct A (symPowMod A M'.X 0)
          (symPowMod A M.X 0) := by
    have h := modTensorAct_mul A (symPowMod A M'.X 0)
      (symPowMod A M.X 0)
    have h' := congrArg (fun t => (α_ A A
        (modTensor A (symPowMod A M'.X 0)
          (symPowMod A M.X 0))).inv ≫ t) h
    exact (h'.trans (Iso.inv_hom_id_assoc _ _)).symm
  have hc : (A ◁ MonoidalCategory.whiskerLeft A
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
      (α_ A A (chainStage2 A M M' 0 0)).inv =
      (α_ A A (𝟙_ D)).inv ≫
        MonoidalCategory.whiskerLeft (A ⊗ A)
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d) :=
    associator_inv_naturality_right _ _ _
  have hd : MonoidalCategory.whiskerLeft (A ⊗ A)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      (μ[A] ▷ chainStage2 A M M' 0 0) =
      (μ[A] ▷ 𝟙_ D) ≫
        MonoidalCategory.whiskerLeft A
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d) :=
    whisker_exchange _ _
  have he : (A ◁ (ρ_ A).inv) ≫ (α_ A A (𝟙_ D)).inv =
      (ρ_ (A ⊗ A)).inv := by
    monoidal
  have hf : (ρ_ (A ⊗ A)).inv ≫ (μ[A] ▷ 𝟙_ D) =
      μ[A] ≫ (ρ_ A).inv :=
    (rightUnitor_inv_naturality _).symm
  have hsplit : A ◁ chainBaseStage A M M' d =
      (A ◁ (ρ_ A).inv) ≫
        (A ◁ MonoidalCategory.whiskerLeft A
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d)) ≫
        (A ◁ modTensorAct A (symPowMod A M'.X 0)
          (symPowMod A M.X 0)) := by
    rw [chainBaseStage, MonoidalCategory.whiskerLeft_comp,
      MonoidalCategory.whiskerLeft_comp]
    rfl
  refine Eq.trans (eq_whisker hsplit
    (modTensorAct A (symPowMod A M'.X 0)
      (symPowMod A M.X 0))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ ha)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker hc _)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (Category.assoc _ _ _).symm)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (eq_whisker hd _))) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (Category.assoc _ _ _))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker he _) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker hf _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact whisker_eq _ (by rw [chainBaseStage]; rfl)

-- Raised budget: the multiplication of the split algebra unfolds
-- through both stage inclusions and the duality datum.
/-- **The base entry is multiplicative**: the carrier entry of
the base algebra respects the multiplication, the multiplicative
half of the monoid-morphism property of the base entry. -/
theorem splitOfBase_mul
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
    μ[A] ≫ splitOfBase A M M' d =
      (splitOfBase A M M' d ⊗ₘ splitOfBase A M M' d) ≫
        (letI := chainBGrMonObj A M M' d;
          μ[chainBGr A M M' d]) := by
  show μ[A] ≫ splitOfBase A M M' d =
    (splitOfBase A M M' d ⊗ₘ splitOfBase A M M' d) ≫
      chainBGrMul A M M' d
  refine Eq.symm ?_
  rw [splitOfBase,
    ← MonoidalCategory.tensorHom_comp_tensorHom,
    ← MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [ι_tensorHom_chainBGrMul A M M' d 0 0]
  have hz : (chainBGrCompι A M M' d 0 0 ⊗ₘ
        chainBGrCompι A M M' d 0 0 :
        chainStage2 A M M' 0 0 ⊗ chainStage2 A M M' 0 0 ⟶
          chainBGrComponent A M M' d 0 ⊗
            chainBGrComponent A M M' d 0) ≫
      chainBGrCompMul A M M' d 0 0 =
      (chainMul2 A M M' 0 0 0 0 ≫
        chainStage2Cast A M M'
          (by omega : 0 + 1 + 0 =
            (-((0 : ℤ) + 0)).toNat + (0 + 1))
          (by omega : 0 + 1 + 0 =
            ((0 : ℤ) + 0).toNat + (0 + 1))) ≫
        chainBGrCompι A M M' d ((0 : ℤ) + 0) (0 + 1) :=
    ι_tensorHom_chainBGrCompMul_zero_left A M M' d 0 0
  rw [reassoc_of% hz]
  rw [MonoidalCategory.tensorHom_def' (chainBaseStage A M M' d)
    (chainBaseStage A M M' d)]
  simp only [Category.assoc]
  have e1 : chainBGrCompι A M M' d ((0 : ℤ) + 0) (0 + 1) ≫
      chainBGrι A M M' d ((0 : ℤ) + 0) =
      chainStage2Cast A M M'
          (by omega : (-((0 : ℤ) + 0)).toNat + (0 + 1) =
            (-(0 : ℤ)).toNat + (0 + 1))
          (by omega : ((0 : ℤ) + 0).toNat + (0 + 1) =
            (0 : ℤ).toNat + (0 + 1)) ≫
        chainBGrCompι A M M' d 0 (0 + 1) ≫
        chainBGrι A M M' d 0 := by
    refine Eq.trans (whisker_eq _
      (eqToHom_chainBGrι A M M' d (Int.add_zero 0)).symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker (chainBGrCompι_eqToHom
      A M M' d (Int.add_zero 0) (0 + 1)) _) ?_
    exact Category.assoc _ _ _
  have e2 : chainStage2Cast A M M'
        (by omega : 0 + 1 = 0 + 1 + 0)
        (by omega : 0 + 1 = 0 + 1 + 0) ≫
      chainStage2Cast A M M'
        (by omega : 0 + 1 + 0 =
          (-((0 : ℤ) + 0)).toNat + (0 + 1))
        (by omega : 0 + 1 + 0 =
          ((0 : ℤ) + 0).toNat + (0 + 1)) ≫
      chainStage2Cast A M M'
        (by omega : (-((0 : ℤ) + 0)).toNat + (0 + 1) =
          (-(0 : ℤ)).toNat + (0 + 1))
        (by omega : ((0 : ℤ) + 0).toNat + (0 + 1) =
          (0 : ℤ).toNat + (0 + 1)) ≫
      chainBGrCompι A M M' d 0 (0 + 1) ≫
      chainBGrι A M M' d 0 =
      chainStage2Cast A M M'
        (by omega : 0 + 1 = (-(0 : ℤ)).toNat + (0 + 1))
        (by omega : 0 + 1 = (0 : ℤ).toNat + (0 + 1)) ≫
      chainBGrCompι A M M' d 0 (0 + 1) ≫
      chainBGrι A M M' d 0 := by
    refine Eq.trans (chainStage2Cast_trans_assoc
      A M M' _ _ _ _ _) ?_
    exact chainStage2Cast_trans_assoc A M M' _ _ _ _ _
  have e3 : chainStage2Cast A M M'
        (by omega : 0 + 1 = (-(0 : ℤ)).toNat + (0 + 1))
        (by omega : 0 + 1 = (0 : ℤ).toNat + (0 + 1)) ≫
      chainBGrCompι A M M' d 0 (0 + 1) ≫
      chainBGrι A M M' d 0 =
      chainBGrCompι A M M' d 0 (0 + 1) ≫
      chainBGrι A M M' d 0 := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact eq_whisker (chainStage2Cast_chainBGrCompι A M M' d 0
      (rfl : (0 + 1 : ℕ) = 0 + 1)) _
  have hd : chainDelta2 A M M' d 0 0 ≫
      chainBGrCompι A M M' d 0 (0 + 1) =
      chainBGrCompι A M M' d 0 0 :=
    chainDelta2_chainBGrCompι A M M' d 0 0
  have habs : (chainDelta2 A M M' d 0 0 ≫
        chainStage2Cast A M M'
          (by omega : 0 + 1 = 0 + 1 + 0)
          (by omega : 0 + 1 = 0 + 1 + 0)) ≫
      chainStage2Cast A M M'
          (by omega : 0 + 1 + 0 =
            (-((0 : ℤ) + 0)).toNat + (0 + 1))
          (by omega : 0 + 1 + 0 =
            ((0 : ℤ) + 0).toNat + (0 + 1)) ≫
        chainBGrCompι A M M' d ((0 : ℤ) + 0) (0 + 1) ≫
        chainBGrι A M M' d ((0 : ℤ) + 0) =
      chainBGrCompι A M M' d 0 0 ≫ chainBGrι A M M' d 0 := by
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (whisker_eq _
      (whisker_eq _ e1))) ?_
    refine Eq.trans (whisker_eq _ e2) ?_
    refine Eq.trans (whisker_eq _ e3) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact eq_whisker hd _
  have h1 : (chainBaseStage A M M' d ▷
        chainStage2 A M M' 0 0) ≫
      chainMul2 A M M' 0 0 0 0 ≫
      chainStage2Cast A M M'
        (by omega : 0 + 1 + 0 =
          (-((0 : ℤ) + 0)).toNat + (0 + 1))
        (by omega : 0 + 1 + 0 =
          ((0 : ℤ) + 0).toNat + (0 + 1)) ≫
      chainBGrCompι A M M' d ((0 : ℤ) + 0) (0 + 1) ≫
      chainBGrι A M M' d ((0 : ℤ) + 0) =
      modTensorAct A (symPowMod A M'.X 0) (symPowMod A M.X 0) ≫
        (chainDelta2 A M M' d 0 0 ≫
          chainStage2Cast A M M'
            (by omega : 0 + 1 = 0 + 1 + 0)
            (by omega : 0 + 1 = 0 + 1 + 0)) ≫
        chainStage2Cast A M M'
            (by omega : 0 + 1 + 0 =
              (-((0 : ℤ) + 0)).toNat + (0 + 1))
            (by omega : 0 + 1 + 0 =
              ((0 : ℤ) + 0).toNat + (0 + 1)) ≫
          chainBGrCompι A M M' d ((0 : ℤ) + 0) (0 + 1) ≫
          chainBGrι A M M' d ((0 : ℤ) + 0) :=
    (Category.assoc _ _ _).symm.trans
      ((eq_whisker (chainBaseStage_mul2 A M M' d 0 0) _).trans
        (Category.assoc _ _ _))
  refine Eq.trans (whisker_eq _ h1) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (mul_chainBaseStage A M M' d).symm _) ?_
  refine Eq.trans (whisker_eq _ habs) ?_
  exact Category.assoc _ _ _

end RS
