/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainStage2
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.PowChain

/-!
# The interchange is linear over the base

The action compatibility of the interchange: acting on the first
tensor factor and interchanging is reassociating, interchanging,
and acting on the nested module tensor product.  Together with
the functoriality of the module tensor product this makes the
chain multiplication bilinear over the base, which is what the
structure morphism of the splitting-chain algebra multiplies
through.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **The interchange is linear over the base**: the action on
the first factor interchanges to the action on the nested module
tensor product. -/
theorem interchange_actLeft
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (N₁ : Mod D A) (N₂ : Mod D A)
    (P₁ : Mod D A) (P₂ : Mod D A) :
    (modTensorAct A N₁ N₂ ▷ modTensor A P₁ P₂) ≫
        interchange A N₁ N₂ P₁ P₂ =
      (α_ A (modTensor A N₁ N₂) (modTensor A P₁ P₂)).hom ≫
        (A ◁ interchange A N₁ N₂ P₁ P₂) ≫
        modTensorAct A (modTensorMod A N₁ P₁)
          (modTensorMod A N₂ P₂) := by
  refine (cancel_epi
    ((A ◁ modTensorπ A N₁ N₂) ▷ modTensor A P₁ P₂)).mp ?_
  refine (cancel_epi
    ((A ⊗ (N₁.X ⊗ N₂.X)) ◁ modTensorπ A P₁ P₂)).mp ?_
  -- The left side: unfold the source action and the interchange
  -- to the raw crossing.
  conv_lhs => rw [← comp_whiskerRight_assoc,
    whiskerLeft_modTensorπ_act, comp_whiskerRight,
    Category.assoc, whisker_exchange_assoc,
    ← tensorHom_def'_assoc, tensorHom_π_interchange,
    rawInterchangeπ, rawInterchange]
  -- The right side: pass the projections through the associator,
  -- unfold the interchange, and descend the nested action.
  have hT : (A ◁ modTensorπ A (modTensorMod A N₁ P₁)
        (modTensorMod A N₂ P₂)) ≫
      modTensorAct A (modTensorMod A N₁ P₁)
        (modTensorMod A N₂ P₂) =
      ((α_ A (modTensor A N₁ P₁) (modTensor A N₂ P₂)).inv ≫
        modTensorAct A N₁ P₁ ▷ modTensor A N₂ P₂) ≫
      modTensorπ A (modTensorMod A N₁ P₁)
        (modTensorMod A N₂ P₂) :=
    whiskerLeft_modTensorπ_act A
      (modTensorMod A N₁ P₁) (modTensorMod A N₂ P₂)
  have hT' : (A ◁ ((modTensorπ A N₁ P₁ ⊗ₘ modTensorπ A N₂ P₂) ≫
        modTensorπ A (modTensorMod A N₁ P₁)
          (modTensorMod A N₂ P₂))) ≫
      modTensorAct A (modTensorMod A N₁ P₁)
        (modTensorMod A N₂ P₂) =
      (A ◁ (modTensorπ A N₁ P₁ ⊗ₘ modTensorπ A N₂ P₂)) ≫
        (α_ A (modTensor A N₁ P₁) (modTensor A N₂ P₂)).inv ≫
        (modTensorAct A N₁ P₁ ▷ modTensor A N₂ P₂) ≫
        modTensorπ A (modTensorMod A N₁ P₁)
          (modTensorMod A N₂ P₂) := by
    have hTpin : (MonoidalCategory.whiskerLeft A
        (Y₁ := modTensor A N₁ P₁ ⊗ modTensor A N₂ P₂)
        (modTensorπ A (modTensorMod A N₁ P₁)
          (modTensorMod A N₂ P₂))) ≫
        modTensorAct A (modTensorMod A N₁ P₁)
          (modTensorMod A N₂ P₂) =
        ((α_ A (modTensor A N₁ P₁)
            (modTensor A N₂ P₂)).inv ≫
          modTensorAct A N₁ P₁ ▷ modTensor A N₂ P₂) ≫
        modTensorπ A (modTensorMod A N₁ P₁)
          (modTensorMod A N₂ P₂) :=
      whiskerLeft_modTensorπ_act A
        (modTensorMod A N₁ P₁) (modTensorMod A N₂ P₂)
    erw [MonoidalCategory.whiskerLeft_comp, Category.assoc, hTpin]
    repeat' erw [Category.assoc]
  conv_rhs => rw [associator_naturality_middle_assoc,
    associator_naturality_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← tensorHom_def', tensorHom_π_interchange,
    rawInterchangeπ, rawInterchange,
    MonoidalCategory.whiskerLeft_comp, Category.assoc, hT']
  -- Pass the pair projection through the inverse associator.
  have hnat : (A ◁ (modTensorπ A N₁ P₁ ⊗ₘ modTensorπ A N₂ P₂)) ≫
      (α_ A (modTensor A N₁ P₁) (modTensor A N₂ P₂)).inv =
      (α_ A (N₁.X ⊗ P₁.X) (N₂.X ⊗ P₂.X)).inv ≫
        ((A ◁ modTensorπ A N₁ P₁) ⊗ₘ modTensorπ A N₂ P₂) := by
    simpa using associator_inv_naturality (𝟙 A)
      (modTensorπ A N₁ P₁) (modTensorπ A N₂ P₂)
  rw [reassoc_of% hnat]
  -- Merge the nested action into the first pair slot and descend.
  have hmerge : ((A ◁ modTensorπ A N₁ P₁) ⊗ₘ modTensorπ A N₂ P₂) ≫
      (modTensorAct A N₁ P₁ ▷ modTensor A N₂ P₂) =
      ((α_ A N₁.X P₁.X).inv ⊗ₘ 𝟙 (N₂.X ⊗ P₂.X)) ≫
        ((actLeft A N₁.X ▷ P₁.X) ⊗ₘ 𝟙 (N₂.X ⊗ P₂.X)) ≫
        (modTensorπ A N₁ P₁ ⊗ₘ modTensorπ A N₂ P₂) := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom,
      whiskerLeft_modTensorπ_act, Category.comp_id,
      tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    simp
  erw [reassoc_of% hmerge]
  -- Extract the action from the crossing.
  have htm : ((actLeft A N₁.X ▷ N₂.X) ▷ (P₁.X ⊗ P₂.X)) ≫
      tensorμ N₁.X N₂.X P₁.X P₂.X =
      tensorμ (A ⊗ N₁.X) N₂.X P₁.X P₂.X ≫
        ((actLeft A N₁.X ▷ P₁.X) ⊗ₘ 𝟙 (N₂.X ⊗ P₂.X)) := by
    simpa using tensorμ_natural (actLeft A N₁.X) (𝟙 N₂.X)
      (𝟙 P₁.X) (𝟙 P₂.X)
  conv_lhs => rw [comp_whiskerRight, Category.assoc,
    reassoc_of% htm]
  -- The remaining prefixes agree by coherence.
  have hcoh : ((α_ A N₁.X N₂.X).inv ▷ (P₁.X ⊗ P₂.X)) ≫
      tensorμ (A ⊗ N₁.X) N₂.X P₁.X P₂.X =
      (α_ A (N₁.X ⊗ N₂.X) (P₁.X ⊗ P₂.X)).hom ≫
        (A ◁ tensorμ N₁.X N₂.X P₁.X P₂.X) ≫
        (α_ A (N₁.X ⊗ P₁.X) (N₂.X ⊗ P₂.X)).inv ≫
        ((α_ A N₁.X P₁.X).inv ⊗ₘ 𝟙 (N₂.X ⊗ P₂.X)) := by
    simp only [tensorμ]
    monoidal
  rw [reassoc_of% hcoh]

/-- **Commutativity of the interchange**: the block braiding
interchanges to the nested braidings, by the braiding law of the
crossing. -/
theorem interchange_comm
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (N₁ : Mod D A) (N₂ : Mod D A)
    (P₁ : Mod D A) (P₂ : Mod D A) :
    (β_ (modTensor A N₁ N₂) (modTensor A P₁ P₂)).hom ≫
        interchange A P₁ P₂ N₁ N₂ =
      interchange A N₁ N₂ P₁ P₂ ≫
        modTensorMap A (modTensorSwapMod A N₁ P₁)
          (modTensorSwapMod A N₂ P₂) := by
  refine (cancel_epi
    (modTensorπ A N₁ N₂ ⊗ₘ modTensorπ A P₁ P₂)).mp ?_
  conv_lhs => rw [BraidedCategory.braiding_naturality_assoc,
    tensorHom_π_interchange, rawInterchangeπ, rawInterchange]
  conv_rhs => erw [tensorHom_π_interchange_assoc,
    rawInterchangeπ, rawInterchange, Category.assoc,
    Category.assoc]
  have hswap : modTensorπ A
      (modTensorMod A N₁ P₁) (modTensorMod A N₂ P₂) ≫
      modTensorMap A (modTensorSwapMod A N₁ P₁)
        (modTensorSwapMod A N₂ P₂) =
      (modTensorSwap A N₁ P₁ ⊗ₘ modTensorSwap A N₂ P₂) ≫
        modTensorπ A (modTensorMod A P₁ N₁)
          (modTensorMod A P₂ N₂) :=
    modTensorπ_map A (modTensorSwapMod A N₁ P₁)
      (modTensorSwapMod A N₂ P₂)
  have hπswap : (modTensorπ A N₁ P₁ ⊗ₘ modTensorπ A N₂ P₂) ≫
      (modTensorSwap A N₁ P₁ ⊗ₘ modTensorSwap A N₂ P₂) =
      ((β_ N₁.X P₁.X).hom ⊗ₘ (β_ N₂.X P₂.X).hom) ≫
        (modTensorπ A P₁ N₁ ⊗ₘ modTensorπ A P₂ N₂) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom,
      modTensorπ_swap, modTensorπ_swap,
      ← MonoidalCategory.tensorHom_comp_tensorHom]
  have hR : (modTensorπ A N₁ P₁ ⊗ₘ modTensorπ A N₂ P₂) ≫
      modTensorπ A (modTensorMod A N₁ P₁)
        (modTensorMod A N₂ P₂) ≫
      modTensorMap A (modTensorSwapMod A N₁ P₁)
        (modTensorSwapMod A N₂ P₂) =
      ((β_ N₁.X P₁.X).hom ⊗ₘ (β_ N₂.X P₂.X).hom) ≫
        (modTensorπ A P₁ N₁ ⊗ₘ modTensorπ A P₂ N₂) ≫
        modTensorπ A (modTensorMod A P₁ N₁)
          (modTensorMod A P₂ N₂) := by
    refine (congrArg (fun t : (modTensorMod A N₁ P₁).X ⊗
          (modTensorMod A N₂ P₂).X ⟶
          modTensor A (modTensorMod A P₁ N₁)
            (modTensorMod A P₂ N₂) =>
        (modTensorπ A N₁ P₁ ⊗ₘ modTensorπ A N₂ P₂) ≫ t)
      hswap).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun t : (N₁.X ⊗ P₁.X) ⊗ (N₂.X ⊗ P₂.X) ⟶
          modTensor A P₁ N₁ ⊗ modTensor A P₂ N₂ =>
        t ≫ modTensorπ A (modTensorMod A P₁ N₁)
          (modTensorMod A P₂ N₂)) hπswap).trans ?_
    exact Category.assoc _ _ _
  conv_lhs => rw [← Category.assoc,
    tensorμ_braiding N₁.X N₂.X P₁.X P₂.X, Category.assoc]
  conv_rhs => erw [← Category.assoc]
  change _ = tensorμ N₁.X N₂.X P₁.X P₂.X ≫
      (((modTensorπ A N₁ P₁ ⊗ₘ modTensorπ A N₂ P₂) ≫
        modTensorπ A (modTensorMod A N₁ P₁) (modTensorMod A N₂ P₂)) ≫
      modTensorMap A (modTensorSwapMod A N₁ P₁) (modTensorSwapMod A N₂ P₂))
  refine congrArg (fun t : (N₁.X ⊗ P₁.X) ⊗ (N₂.X ⊗ P₂.X) ⟶
      modTensor A (modTensorMod A P₁ N₁)
        (modTensorMod A P₂ N₂) =>
    tensorμ N₁.X N₂.X P₁.X P₂.X ≫ t) ?_
  erw [Category.assoc]
  exact hR.symm

/-- **The interchange is linear in the second factor**: the
middle action braids to the front and the first-factor linearity
applies through commutativity. -/
theorem interchange_actMid
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (N₁ : Mod D A) (N₂ : Mod D A)
    (P₁ : Mod D A) (P₂ : Mod D A) :
    (modTensor A N₁ N₂ ◁ modTensorAct A P₁ P₂) ≫
        interchange A N₁ N₂ P₁ P₂ =
      (α_ (modTensor A N₁ N₂) A (modTensor A P₁ P₂)).inv ≫
        ((β_ (modTensor A N₁ N₂) A).hom ▷ modTensor A P₁ P₂) ≫
        (α_ A (modTensor A N₁ N₂) (modTensor A P₁ P₂)).hom ≫
        (A ◁ interchange A N₁ N₂ P₁ P₂) ≫
        modTensorAct A (modTensorMod A N₁ P₁)
          (modTensorMod A N₂ P₂) := by
  have hcomm : interchange A N₁ N₂ P₁ P₂ =
      (β_ (modTensor A N₁ N₂) (modTensor A P₁ P₂)).hom ≫
        interchange A P₁ P₂ N₁ N₂ ≫
        modTensorMap A (modTensorSwapMod A P₁ N₁)
          (modTensorSwapMod A P₂ N₂) := by
    conv_rhs => rw [← interchange_comm A P₁ P₂ N₁ N₂,
      ← Category.assoc, SymmetricCategory.symmetry,
      Category.id_comp]
  have hcoh : (β_ (modTensor A N₁ N₂)
        (A ⊗ modTensor A P₁ P₂)).hom ≫
      (α_ A (modTensor A P₁ P₂) (modTensor A N₁ N₂)).hom ≫
      (A ◁ (β_ (modTensor A P₁ P₂)
        (modTensor A N₁ N₂)).hom) =
      (α_ (modTensor A N₁ N₂) A (modTensor A P₁ P₂)).inv ≫
        ((β_ (modTensor A N₁ N₂) A).hom ▷ modTensor A P₁ P₂) ≫
        (α_ A (modTensor A N₁ N₂) (modTensor A P₁ P₂)).hom := by
    rw [BraidedCategory.braiding_tensor_right_hom]
    simp only [Category.assoc, Iso.inv_hom_id_assoc,
      ← MonoidalCategory.whiskerLeft_comp]
    rw [SymmetricCategory.symmetry]
    simp
  conv_lhs => rw [hcomm,
    BraidedCategory.braiding_naturality_right_assoc,
    reassoc_of% (interchange_actLeft A P₁ P₂ N₁ N₂),
    modTensorAct_map,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    (show interchange A P₁ P₂ N₁ N₂ ≫
        modTensorMap A (modTensorSwapMod A P₁ N₁)
          (modTensorSwapMod A P₂ N₂) =
      (β_ (modTensor A P₁ P₂) (modTensor A N₁ N₂)).hom ≫
        interchange A N₁ N₂ P₁ P₂
      from (interchange_comm A P₁ P₂ N₁ N₂).symm),
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    reassoc_of% hcoh]

section ChainMulAct

/-- **The chain multiplication is linear over the base in the
first stage**: the interchange linearity composed with the
functoriality of the module tensor product.  Stated at the
unwrapped module tensor products; the stage forms follow by
definitional unfolding. -/
theorem chainMul_actLeft
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [CategoryTheory.Linear ℂ D] [MonoidalLinear ℂ D] (M : Mod D A)
    (M' : Mod D A)
    (m n : ℕ) :
    (modTensorAct A (symPowMod A M'.X m) (symPowMod A M.X m) ▷
        modTensor A (symPowMod A M'.X n) (symPowMod A M.X n)) ≫
      chainMul A M M' m n =
      (α_ A (modTensor A (symPowMod A M'.X m) (symPowMod A M.X m))
          (modTensor A (symPowMod A M'.X n)
            (symPowMod A M.X n))).hom ≫
        (A ◁ chainMul A M M' m n) ≫
        modTensorAct A (symPowMod A M'.X (m + 1 + n))
          (symPowMod A M.X (m + 1 + n)) := by
  change (modTensorAct A (symPowMod A M'.X m) (symPowMod A M.X m) ▷
      modTensor A (symPowMod A M'.X n) (symPowMod A M.X n)) ≫
      (interchange A (symPowMod A M'.X m) (symPowMod A M.X m)
          (symPowMod A M'.X n) (symPowMod A M.X n) ≫
        modTensorMap A (symMulMod A M'.X m n)
          (symMulMod A M.X m n)) =
    (α_ A (modTensor A (symPowMod A M'.X m) (symPowMod A M.X m))
        (modTensor A (symPowMod A M'.X n)
          (symPowMod A M.X n))).hom ≫
      (A ◁ (interchange A (symPowMod A M'.X m)
          (symPowMod A M.X m) (symPowMod A M'.X n)
          (symPowMod A M.X n) ≫
        modTensorMap A (symMulMod A M'.X m n)
          (symMulMod A M.X m n))) ≫
      modTensorAct A (symPowMod A M'.X (m + 1 + n))
        (symPowMod A M.X (m + 1 + n))
  rw [reassoc_of% (interchange_actLeft A
      (symPowMod A M'.X m) (symPowMod A M.X m)
      (symPowMod A M'.X n) (symPowMod A M.X n)),
    modTensorAct_map,
    ← MonoidalCategory.whiskerLeft_comp_assoc]

/-- **The two-index chain multiplication is linear over the base
in the first stage**: the interchange linearity composed with the
functoriality of the module tensor product, at four independent
symmetric-power arities.  Stated at the unwrapped module tensor
products; the two-index stage forms follow by definitional
unfolding.  The diagonal `p = q`, `r = s` is `chainMul_actLeft`. -/
theorem chainMul2_actLeft
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [CategoryTheory.Linear ℂ D] [MonoidalLinear ℂ D] (M : Mod D A)
    (M' : Mod D A)
    (p q r s : ℕ) :
    (modTensorAct A (symPowMod A M'.X p) (symPowMod A M.X q) ▷
        modTensor A (symPowMod A M'.X r) (symPowMod A M.X s)) ≫
      chainMul2 A M M' p q r s =
      (α_ A (modTensor A (symPowMod A M'.X p)
          (symPowMod A M.X q))
          (modTensor A (symPowMod A M'.X r)
            (symPowMod A M.X s))).hom ≫
        (A ◁ chainMul2 A M M' p q r s) ≫
        modTensorAct A (symPowMod A M'.X (p + 1 + r))
          (symPowMod A M.X (q + 1 + s)) := by
  change (modTensorAct A (symPowMod A M'.X p) (symPowMod A M.X q) ▷
      modTensor A (symPowMod A M'.X r) (symPowMod A M.X s)) ≫
      (interchange A (symPowMod A M'.X p) (symPowMod A M.X q)
          (symPowMod A M'.X r) (symPowMod A M.X s) ≫
        modTensorMap A (symMulMod A M'.X p r)
          (symMulMod A M.X q s)) =
    (α_ A (modTensor A (symPowMod A M'.X p) (symPowMod A M.X q))
        (modTensor A (symPowMod A M'.X r)
          (symPowMod A M.X s))).hom ≫
      (A ◁ (interchange A (symPowMod A M'.X p)
          (symPowMod A M.X q) (symPowMod A M'.X r)
          (symPowMod A M.X s) ≫
        modTensorMap A (symMulMod A M'.X p r)
          (symMulMod A M.X q s))) ≫
      modTensorAct A (symPowMod A M'.X (p + 1 + r))
        (symPowMod A M.X (q + 1 + s))
  rw [reassoc_of% (interchange_actLeft A
      (symPowMod A M'.X p) (symPowMod A M.X q)
      (symPowMod A M'.X r) (symPowMod A M.X s)),
    modTensorAct_map,
    ← MonoidalCategory.whiskerLeft_comp_assoc]

/-- **The two-index chain multiplication is linear over the base
in the second factor**: the middle action braids to the front and
the interchange linearity applies.  Stated at the unwrapped module
tensor products; the stage forms follow by definitional
unfolding. -/
theorem chainMul2_actMid
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [CategoryTheory.Linear ℂ D] [MonoidalLinear ℂ D] (M : Mod D A)
    (M' : Mod D A)
    (p q r s : ℕ) :
    (modTensor A (symPowMod A M'.X p) (symPowMod A M.X q) ◁
        modTensorAct A (symPowMod A M'.X r)
          (symPowMod A M.X s)) ≫
      chainMul2 A M M' p q r s =
      (α_ (modTensor A (symPowMod A M'.X p)
          (symPowMod A M.X q)) A
          (modTensor A (symPowMod A M'.X r)
            (symPowMod A M.X s))).inv ≫
        ((β_ (modTensor A (symPowMod A M'.X p)
          (symPowMod A M.X q)) A).hom ▷
          modTensor A (symPowMod A M'.X r)
            (symPowMod A M.X s)) ≫
        (α_ A (modTensor A (symPowMod A M'.X p)
          (symPowMod A M.X q))
          (modTensor A (symPowMod A M'.X r)
            (symPowMod A M.X s))).hom ≫
        (A ◁ chainMul2 A M M' p q r s) ≫
        modTensorAct A (symPowMod A M'.X (p + 1 + r))
          (symPowMod A M.X (q + 1 + s)) := by
  change (modTensor A (symPowMod A M'.X p) (symPowMod A M.X q) ◁
      modTensorAct A (symPowMod A M'.X r) (symPowMod A M.X s)) ≫
      (interchange A (symPowMod A M'.X p) (symPowMod A M.X q)
          (symPowMod A M'.X r) (symPowMod A M.X s) ≫
        modTensorMap A (symMulMod A M'.X p r)
          (symMulMod A M.X q s)) =
    (α_ (modTensor A (symPowMod A M'.X p)
        (symPowMod A M.X q)) A
        (modTensor A (symPowMod A M'.X r)
          (symPowMod A M.X s))).inv ≫
      ((β_ (modTensor A (symPowMod A M'.X p)
        (symPowMod A M.X q)) A).hom ▷
        modTensor A (symPowMod A M'.X r)
          (symPowMod A M.X s)) ≫
      (α_ A (modTensor A (symPowMod A M'.X p)
        (symPowMod A M.X q))
        (modTensor A (symPowMod A M'.X r)
          (symPowMod A M.X s))).hom ≫
      (A ◁ (interchange A (symPowMod A M'.X p)
          (symPowMod A M.X q) (symPowMod A M'.X r)
          (symPowMod A M.X s) ≫
        modTensorMap A (symMulMod A M'.X p r)
          (symMulMod A M.X q s))) ≫
      modTensorAct A (symPowMod A M'.X (p + 1 + r))
        (symPowMod A M.X (q + 1 + s))
  rw [reassoc_of% (interchange_actMid A
      (symPowMod A M'.X p) (symPowMod A M.X q)
      (symPowMod A M'.X r) (symPowMod A M.X s)),
    modTensorAct_map,
    ← MonoidalCategory.whiskerLeft_comp_assoc]

end ChainMulAct

end RS
