/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainMul
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.PowCopairing

/-!
# The transitions of the splitting chain

The copairing of a duality datum seeds the bottom stage of the
splitting chain, and multiplication by the seed is the chain
transition.  The stage units ride along the transitions by
construction; their nonvanishing is the pairing side's business.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- Acting across the unit context is acting after the unitor. -/
theorem powTailAct_zero_lambda
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] :
    powTailAct A X 0 ≫ (λ_ X).hom =
      (A ◁ (λ_ X).hom) ≫ actLeft A X := by
  change actAcross A (𝟙_ D) X ≫ (λ_ X).hom = _
  rw [actAcross]
  simp only [Category.assoc]
  rw [MonoidalCategory.leftUnitor_naturality]
  suffices h : (α_ A (𝟙_ D) X).inv ≫
      ((β_ A (𝟙_ D)).hom ▷ X) ≫ (α_ (𝟙_ D) A X).hom ≫
      (λ_ (A ⊗ X)).hom = A ◁ (λ_ X).hom by
    rw [reassoc_of% h]
  rw [braiding_tensorUnit_right]
  monoidal

/-- The singleton projection of the module power carries the
descended action to the action of the module. -/
theorem modPowAct_modPowOne
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X] :
    modPowAct A X 0 ≫ (modPowOne A X).hom =
      (A ◁ (modPowOne A X).hom) ≫ actLeft A X := by
  apply modPow_whiskerLeft_hom_ext A X A 1
  have hπ : modPowπ A X 1 ≫ (modPowOne A X).hom =
      (λ_ X).hom := by
    erw [modPowOne, Iso.trans_hom, ← Category.assoc]
    rw [show modPowπ A X 1 ≫ (modPowTriv A X (by omega)).hom =
      𝟙 (tensorPow D X 1) from (modPowTriv A X (by omega)).inv_hom_id]
    rw [Category.id_comp]
  rw [whiskerLeft_modPowπ_modPowAct_assoc, hπ,
    ← MonoidalCategory.whiskerLeft_comp_assoc, hπ,
    powTailAct_zero_lambda]
  rfl

/-- The singleton symmetric power carries the descended action to
the action of the module. -/
theorem symPowAct_symPowOne
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X] :
    symPowAct A X 0 ≫ (symPowOne A X).hom =
      (A ◁ (symPowOne A X).hom) ≫ actLeft A X := by
  rw [symPowAct, symPowOne]
  change ((A ◁ symPowσ A X 1) ≫ modPowAct A X 0 ≫
      symPowπ A X 1) ≫ symPowσ A X 1 ≫ (modPowOne A X).hom =
    (A ◁ (symPowσ A X 1 ≫ (modPowOne A X).hom)) ≫ actLeft A X
  rw [MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [symPowπ_symPowσ_assoc, symPowIdem_one, Category.id_comp,
    modPowAct_modPowOne]

/-- The inverse of the singleton iso carries the module action to
the descended action. -/
theorem actLeft_symPowOne_inv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X] :
    actLeft A X ≫ (symPowOne A X).inv =
      (A ◁ (symPowOne A X).inv) ≫ symPowAct A X 0 := by
  calc actLeft A X ≫ (symPowOne A X).inv
      = (A ◁ (symPowOne A X).inv) ≫
          (A ◁ (symPowOne A X).hom) ≫ actLeft A X ≫
          (symPowOne A X).inv := by
        rw [← MonoidalCategory.whiskerLeft_comp_assoc,
          Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id,
          Category.id_comp]
    _ = (A ◁ (symPowOne A X).inv) ≫ symPowAct A X 0 := by
        rw [← reassoc_of% (symPowAct_symPowOne A X)]
        simp only [Iso.hom_inv_id, Category.comp_id]

/-- A module maps into the singleton stage of its symmetric-power
tower. -/
noncomputable def toSymPowModZero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) :
    M ⟶ symPowMod A M.X 0 :=
  Mod.Hom.mk' ((symPowOne A M.X).inv)
    (actLeft_symPowOne_inv A M.X)

/-- **The seed of the splitting chain**: the copairing lands in
the bottom stage. -/
noncomputable def chainSeed
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    𝟙_ D ⟶ chainStage A M M' 0 :=
  copairUnit A M M' d ≫ modTensorSwap A M M' ≫
    modTensorMap A (toSymPowModZero A M') (toSymPowModZero A M)

/-- **The chain transition**: multiplication by the seed. -/
noncomputable def chainDelta
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (k : ℕ) : chainStage A M M' k ⟶ chainStage A M M' (k + 1) :=
  (ρ_ (chainStage A M M' k)).inv ≫
    (chainStage A M M' k ◁ chainSeed A M M' d) ≫
    chainMul A M M' k 0

/-- The stage units of the splitting chain. -/
noncomputable def chainUnitStage
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    (k : ℕ) → (𝟙_ D ⟶ chainStage A M M' k)
  | 0 => chainSeed A M M' d
  | (k + 1) => chainUnitStage A M M' d k ≫ chainDelta A M M' d k

/-- The stage units ride along the transitions. -/
theorem chainUnitStage_succ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (k : ℕ) :
    chainUnitStage A M M' d k ≫ chainDelta A M M' d k =
      chainUnitStage A M M' d (k + 1) :=
  rfl

end RS
