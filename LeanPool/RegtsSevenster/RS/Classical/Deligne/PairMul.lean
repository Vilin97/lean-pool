/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.PowActMul

/-!
# The interchange of module tensor products

The pair-multiplication device of the Key Lemma's chain algebra:
over a symmetric base, the tensor product of two module tensor
products interchanges into the module tensor product of the
crossed pairs.  The chain transitions and the stage products of
the splitting algebra factor through it.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- The raw interchange: cross the middle factors. -/
def rawInterchange
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (N₁ : Mod D A) (N₂ : Mod D A) (P₁ : Mod D A) (P₂ : Mod D A) :
    (N₁.X ⊗ N₂.X) ⊗ (P₁.X ⊗ P₂.X) ⟶
      (N₁.X ⊗ P₁.X) ⊗ (N₂.X ⊗ P₂.X) :=
  tensorμ N₁.X N₂.X P₁.X P₂.X

/-- The raw interchange followed by the projections. -/
noncomputable def rawInterchangeπ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (N₁ : Mod D A) (N₂ : Mod D A)
    (P₁ : Mod D A) (P₂ : Mod D A) :
    (N₁.X ⊗ N₂.X) ⊗ (P₁.X ⊗ P₂.X) ⟶
      modTensor A (modTensorMod A N₁ P₁) (modTensorMod A N₂ P₂) :=
  rawInterchange A N₁ N₂ P₁ P₂ ≫
    (modTensorπ A N₁ P₁ ⊗ₘ modTensorπ A N₂ P₂) ≫
    modTensorπ A (modTensorMod A N₁ P₁) (modTensorMod A N₂ P₂)

/-- The scalar-carrying rearrangement: the interchange at the
scalar-extended first block, the scalar crossing to the block
boundary. -/
noncomputable def midArrange
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (N₁ : Mod D A) (N₂ : Mod D A) (P₁ : Mod D A) (P₂ : Mod D A) :
    ((N₁.X ⊗ A) ⊗ N₂.X) ⊗ (P₁.X ⊗ P₂.X) ⟶
      ((N₁.X ⊗ P₁.X) ⊗ A) ⊗ (N₂.X ⊗ P₂.X) :=
  tensorμ (N₁.X ⊗ A) N₂.X P₁.X P₂.X ≫
    (((α_ N₁.X A P₁.X).hom ≫ (N₁.X ◁ (β_ A P₁.X).hom) ≫
      (α_ N₁.X P₁.X A).inv) ▷ (N₂.X ⊗ P₂.X))

/-- The coherence core of the left leg identification. -/
private theorem legM_core
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    {V₁ W₁ U Q₁ Q₂ Z : D}
    (act : A ⊗ V₁ ⟶ V₁) (q₁ : V₁ ⊗ W₁ ⟶ Q₁) (q₂ : U ⟶ Q₂)
    (out : Q₁ ⊗ Q₂ ⟶ Z) :
    ((((β_ V₁ A).hom ≫ act) ▷ W₁) ▷ U) ≫
        (q₁ ⊗ₘ q₂) ≫ out =
      (((α_ V₁ A W₁).hom ≫ (V₁ ◁ (β_ A W₁).hom) ≫
        (α_ V₁ W₁ A).inv) ▷ U) ≫
      ((((β_ (V₁ ⊗ W₁) A).hom ≫ (α_ A V₁ W₁).inv ≫
        (act ▷ W₁)) ≫ q₁) ⊗ₘ q₂) ≫ out := by
  have hq : ∀ {Y : D} (x : Y ⟶ V₁ ⊗ W₁),
      ((x ≫ q₁) ⊗ₘ q₂) = (x ▷ U) ≫ (q₁ ⊗ₘ q₂) := by
    intro Y x
    rw [MonoidalCategory.tensorHom_def,
      MonoidalCategory.tensorHom_def, comp_whiskerRight,
      Category.assoc]
  rw [hq]
  simp only [Category.assoc]
  rw [← comp_whiskerRight_assoc]
  suffices h : ((β_ V₁ A).hom ≫ act) ▷ W₁ =
      ((α_ V₁ A W₁).hom ≫ (V₁ ◁ (β_ A W₁).hom) ≫
        (α_ V₁ W₁ A).inv) ≫
      ((β_ (V₁ ⊗ W₁) A).hom ≫ (α_ A V₁ W₁).inv ≫
        (act ▷ W₁)) by rw [h]
  rw [BraidedCategory.braiding_tensor_left_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc,
    SymmetricCategory.symmetry, MonoidalCategory.whiskerLeft_id,
    Category.id_comp, Iso.hom_inv_id_assoc,
    comp_whiskerRight]
  simp only [Iso.hom_inv_id_assoc]

/-- The coherence core of the right leg identification. -/
private theorem legN_core
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    {V₁ V₂ W₁ W₂ Q₁ Q₂ Z : D}
    (act : A ⊗ V₂ ⟶ V₂) (q₁ : V₁ ⊗ W₁ ⟶ Q₁)
    (q₂ : V₂ ⊗ W₂ ⟶ Q₂) (out : Q₁ ⊗ Q₂ ⟶ Z) :
    ((α_ V₁ A V₂).hom ▷ (W₁ ⊗ W₂)) ≫
        tensorμ V₁ (A ⊗ V₂) W₁ W₂ ≫
        (q₁ ⊗ₘ ((act ▷ W₂) ≫ q₂)) ≫ out =
      tensorμ (V₁ ⊗ A) V₂ W₁ W₂ ≫
        (((α_ V₁ A W₁).hom ≫ (V₁ ◁ (β_ A W₁).hom) ≫
          (α_ V₁ W₁ A).inv) ▷ (V₂ ⊗ W₂)) ≫
        (α_ (V₁ ⊗ W₁) A (V₂ ⊗ W₂)).hom ≫
        ((V₁ ⊗ W₁) ◁ (α_ A V₂ W₂).inv) ≫
        (q₁ ⊗ₘ ((act ▷ W₂) ≫ q₂)) ≫ out := by
  suffices h : ((α_ V₁ A V₂).hom ▷ (W₁ ⊗ W₂)) ≫
      tensorμ V₁ (A ⊗ V₂) W₁ W₂ =
    tensorμ (V₁ ⊗ A) V₂ W₁ W₂ ≫
      (((α_ V₁ A W₁).hom ≫ (V₁ ◁ (β_ A W₁).hom) ≫
        (α_ V₁ W₁ A).inv) ▷ (V₂ ⊗ W₂)) ≫
      (α_ (V₁ ⊗ W₁) A (V₂ ⊗ W₂)).hom ≫
      ((V₁ ⊗ W₁) ◁ (α_ A V₂ W₂).inv) by
    rw [reassoc_of% h]
  simp only [tensorμ]
  rw [BraidedCategory.braiding_tensor_left_hom A V₂ W₁]
  monoidal

/-- The left slide of the first factors becomes the outer left
slide of the target. -/
theorem interchange_legM
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (N₁ : Mod D A) (N₂ : Mod D A)
    (P₁ : Mod D A) (P₂ : Mod D A) :
    (modTensorLegM A N₁ N₂ ▷ (P₁.X ⊗ P₂.X)) ≫
        rawInterchangeπ A N₁ N₂ P₁ P₂ =
      midArrange A N₁ N₂ P₁ P₂ ≫
        ((modTensorπ A N₁ P₁ ▷ A) ⊗ₘ modTensorπ A N₂ P₂) ≫
        modTensorLegM A (modTensorMod A N₁ P₁)
          (modTensorMod A N₂ P₂) ≫
        modTensorπ A (modTensorMod A N₁ P₁)
          (modTensorMod A N₂ P₂) := by
  have h1 := tensorμ_natural (actRight A N₁.X) (𝟙 N₂.X)
    (𝟙 P₁.X) (𝟙 P₂.X)
  simp only [MonoidalCategory.id_whiskerRight,
    MonoidalCategory.tensorHom_id] at h1
  conv_lhs => rw [modTensorLegM, rawInterchangeπ,
    rawInterchange, reassoc_of% h1]
  have hslot : (modTensorπ A N₁ P₁ ▷ A) ≫
      (β_ (modTensor A N₁ P₁) A).hom ≫ modTensorAct A N₁ P₁ =
    (β_ (N₁.X ⊗ P₁.X) A).hom ≫ (α_ A N₁.X P₁.X).inv ≫
      (actLeft A N₁.X ▷ P₁.X) ≫ modTensorπ A N₁ P₁ := by
    rw [BraidedCategory.braiding_naturality_left_assoc,
      whiskerLeft_modTensorπ_act]
    simp only [Category.assoc]
  have hcov : ((modTensorπ A N₁ P₁ ▷ A) ⊗ₘ
      modTensorπ A N₂ P₂) ≫
      modTensorLegM A (modTensorMod A N₁ P₁)
        (modTensorMod A N₂ P₂) =
    ((((β_ (N₁.X ⊗ P₁.X) A).hom ≫ (α_ A N₁.X P₁.X).inv ≫
      (actLeft A N₁.X ▷ P₁.X)) ≫ modTensorπ A N₁ P₁) ⊗ₘ
      modTensorπ A N₂ P₂) := by
    have hmw : ∀ {X₁ X₂ Y₁ Y₂ Z₁ : D} (a : X₁ ⟶ Y₁)
        (b : X₂ ⟶ Y₂) (f : Y₁ ⟶ Z₁),
        (a ⊗ₘ b) ≫ (f ▷ Y₂) = (a ≫ f) ⊗ₘ b := by
      intros
      rw [← MonoidalCategory.tensorHom_id,
        MonoidalCategory.tensorHom_comp_tensorHom,
        Category.comp_id]
    rw [modTensorLegM,
      show actRight A (modTensorMod A N₁ P₁).X =
        (β_ (modTensor A N₁ P₁) A).hom ≫
          modTensorAct A N₁ P₁ from rfl]
    show ((modTensorπ A N₁ P₁ ▷ A) ⊗ₘ modTensorπ A N₂ P₂) ≫
      (((β_ (modTensor A N₁ P₁) A).hom ≫
        modTensorAct A N₁ P₁) ▷ modTensor A N₂ P₂) = _
    rw [hmw, hslot]
    simp only [Category.assoc]
  have hcov' := congrArg (fun t => t ≫
    modTensorπ A (modTensorMod A N₁ P₁)
      (modTensorMod A N₂ P₂)) hcov
  repeat' erw [Category.assoc] at hcov'
  conv_rhs => erw [hcov', midArrange]
  conv_rhs => simp only [Category.assoc]
  refine congrArg (CategoryStruct.comp
    (tensorμ (N₁.X ⊗ A) N₂.X P₁.X P₂.X)) ?_
  rw [actRight]
  have hc := legM_core A (actLeft A N₁.X)
    (modTensorπ A N₁ P₁) (modTensorπ A N₂ P₂)
    (modTensorπ A (modTensorMod A N₁ P₁)
      (modTensorMod A N₂ P₂))
  simp only [Category.assoc] at hc
  exact hc

/-- The right slide of the second factors becomes the outer right
slide of the target. -/
theorem interchange_legN
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (N₁ : Mod D A) (N₂ : Mod D A)
    (P₁ : Mod D A) (P₂ : Mod D A) :
    (modTensorLegN A N₁ N₂ ▷ (P₁.X ⊗ P₂.X)) ≫
        rawInterchangeπ A N₁ N₂ P₁ P₂ =
      midArrange A N₁ N₂ P₁ P₂ ≫
        ((modTensorπ A N₁ P₁ ▷ A) ⊗ₘ modTensorπ A N₂ P₂) ≫
        modTensorLegN A (modTensorMod A N₁ P₁)
          (modTensorMod A N₂ P₂) ≫
        modTensorπ A (modTensorMod A N₁ P₁)
          (modTensorMod A N₂ P₂) := by
  have hml : ∀ {X₁ X₂ Y₂ Z₁ Z₂ : D} (b : X₂ ⟶ Y₂)
      (a : X₁ ⟶ Z₁) (c : Y₂ ⟶ Z₂),
      (X₁ ◁ b) ≫ (a ⊗ₘ c) = a ⊗ₘ (b ≫ c) := by
    intros
    rw [← MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom,
      Category.id_comp]
  have hmr : ∀ {X₁ X₂ Z₁ Y₂ Z₂ : D} (a : X₁ ⟶ Z₁)
      (b : X₂ ⟶ Y₂) (f : Y₂ ⟶ Z₂),
      (a ⊗ₘ b) ≫ (Z₁ ◁ f) = a ⊗ₘ (b ≫ f) := by
    intros
    rw [← MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom,
      Category.comp_id]
  have h1 := tensorμ_natural (𝟙 N₁.X) (actLeft A N₂.X)
    (𝟙 P₁.X) (𝟙 P₂.X)
  simp only [MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_id,
    MonoidalCategory.id_whiskerRight] at h1
  conv_lhs => rw [modTensorLegN, rawInterchangeπ,
    rawInterchange, comp_whiskerRight, Category.assoc,
    reassoc_of% h1]
  conv_lhs => erw [reassoc_of% hml (actLeft A N₂.X ▷ P₂.X)
    (modTensorπ A N₁ P₁) (modTensorπ A N₂ P₂)]
  have hassoc := associator_naturality (modTensorπ A N₁ P₁)
    (𝟙 A) (modTensorπ A N₂ P₂)
  have hcov : ((modTensorπ A N₁ P₁ ▷ A) ⊗ₘ
      modTensorπ A N₂ P₂) ≫
      modTensorLegN A (modTensorMod A N₁ P₁)
        (modTensorMod A N₂ P₂) =
    (α_ (N₁.X ⊗ P₁.X) A (N₂.X ⊗ P₂.X)).hom ≫
      ((N₁.X ⊗ P₁.X) ◁ (α_ A N₂.X P₂.X).inv) ≫
      (modTensorπ A N₁ P₁ ⊗ₘ
        ((actLeft A N₂.X ▷ P₂.X) ≫ modTensorπ A N₂ P₂)) := by
    rw [modTensorLegN,
      show actLeft A (modTensorMod A N₂ P₂).X =
        modTensorAct A N₂ P₂ from rfl]
    show ((modTensorπ A N₁ P₁ ▷ A) ⊗ₘ modTensorπ A N₂ P₂) ≫
      ((α_ (modTensor A N₁ P₁) A (modTensor A N₂ P₂)).hom ≫
        (modTensor A N₁ P₁ ◁ modTensorAct A N₂ P₂)) = _
    rw [← MonoidalCategory.tensorHom_id]
    rw [reassoc_of% hassoc, hmr,
      MonoidalCategory.id_tensorHom,
      whiskerLeft_modTensorπ_act]
    rw [show ((α_ A N₂.X P₂.X).inv ≫
        (actLeft A N₂.X ▷ P₂.X)) ≫ modTensorπ A N₂ P₂ =
      (α_ A N₂.X P₂.X).inv ≫
        ((actLeft A N₂.X ▷ P₂.X) ≫ modTensorπ A N₂ P₂) from
      Category.assoc _ _ _]
    rw [← hml (α_ A N₂.X P₂.X).inv (modTensorπ A N₁ P₁)
      ((actLeft A N₂.X ▷ P₂.X) ≫ modTensorπ A N₂ P₂)]
  have hcov' : ((modTensorπ A N₁ P₁ ▷ A) ⊗ₘ
      modTensorπ A N₂ P₂) ≫
      modTensorLegN A (modTensorMod A N₁ P₁)
        (modTensorMod A N₂ P₂) ≫
      modTensorπ A (modTensorMod A N₁ P₁)
        (modTensorMod A N₂ P₂) =
    (α_ (N₁.X ⊗ P₁.X) A (N₂.X ⊗ P₂.X)).hom ≫
      ((N₁.X ⊗ P₁.X) ◁ (α_ A N₂.X P₂.X).inv) ≫
      (modTensorπ A N₁ P₁ ⊗ₘ
        ((actLeft A N₂.X ▷ P₂.X) ≫ modTensorπ A N₂ P₂)) ≫
      modTensorπ A (modTensorMod A N₁ P₁)
        (modTensorMod A N₂ P₂) := by
    erw [← Category.assoc, hcov]
    exact (Category.assoc _ _ _).trans
      (congrArg (CategoryStruct.comp _) (Category.assoc _ _ _))
  conv_rhs => erw [hcov', midArrange]
  conv_rhs => rw [Category.assoc]
  have hc := legN_core A (actLeft A N₂.X)
    (modTensorπ A N₁ P₁) (modTensorπ A N₂ P₂)
    (modTensorπ A (modTensorMod A N₁ P₁)
      (modTensorMod A N₂ P₂))
  exact hc

/-- The scalar-carrying rearrangement from the second block: the
interchange at the scalar-extended second block, the scalar
reassociating to the block boundary. -/
noncomputable def midArrangeP
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (N₁ : Mod D A) (N₂ : Mod D A) (P₁ : Mod D A) (P₂ : Mod D A) :
    (N₁.X ⊗ N₂.X) ⊗ ((P₁.X ⊗ A) ⊗ P₂.X) ⟶
      ((N₁.X ⊗ P₁.X) ⊗ A) ⊗ (N₂.X ⊗ P₂.X) :=
  tensorμ N₁.X N₂.X (P₁.X ⊗ A) P₂.X ≫
    ((α_ N₁.X P₁.X A).inv ▷ (N₂.X ⊗ P₂.X))

/-- The coherence core of the second-block left leg
identification: the module condition on the first pair transports
the scalar action across the pair. -/
private theorem legMP_core
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    {V₁ W₁ U Q₁ Q₂ Z : D}
    (actN : A ⊗ V₁ ⟶ V₁) (actW : A ⊗ W₁ ⟶ W₁)
    (q₁ : V₁ ⊗ W₁ ⟶ Q₁) (q₂ : U ⟶ Q₂) (out : Q₁ ⊗ Q₂ ⟶ Z)
    (hcond : (((β_ V₁ A).hom ≫ actN) ▷ W₁) ≫ q₁ =
      (α_ V₁ A W₁).hom ≫ (V₁ ◁ actW) ≫ q₁) :
    ((V₁ ◁ ((β_ W₁ A).hom ≫ actW)) ▷ U) ≫
        (q₁ ⊗ₘ q₂) ≫ out =
      ((α_ V₁ W₁ A).inv ▷ U) ≫
      ((((β_ (V₁ ⊗ W₁) A).hom ≫ (α_ A V₁ W₁).inv ≫
        (actN ▷ W₁)) ≫ q₁) ⊗ₘ q₂) ≫ out := by
  have hq : ∀ {Y : D} (x : Y ⟶ V₁ ⊗ W₁),
      (((x ≫ q₁) ⊗ₘ q₂) ≫ out) =
        (x ▷ U) ≫ (q₁ ⊗ₘ q₂) ≫ out := by
    intro Y x
    rw [MonoidalCategory.tensorHom_def,
      MonoidalCategory.tensorHom_def, comp_whiskerRight]
    simp only [Category.assoc]
  rw [BraidedCategory.braiding_tensor_left_hom V₁ W₁ A]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc (β_ V₁ A).hom actN, hcond,
    Iso.inv_hom_id_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc V₁
      (β_ W₁ A).hom actW]
  rw [show (α_ V₁ W₁ A).hom ≫
      (V₁ ◁ ((β_ W₁ A).hom ≫ actW)) ≫ q₁ =
    ((α_ V₁ W₁ A).hom ≫
      (V₁ ◁ ((β_ W₁ A).hom ≫ actW))) ≫ q₁ from
    (Category.assoc _ _ _).symm]
  rw [hq, comp_whiskerRight]
  simp only [Category.assoc]
  rw [← comp_whiskerRight_assoc (α_ V₁ W₁ A).inv
    (α_ V₁ W₁ A).hom, Iso.inv_hom_id,
    MonoidalCategory.id_whiskerRight, Category.id_comp]

/-- The second-block left slide becomes the outer left slide of
the target. -/
theorem interchange_legMP
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (N₁ : Mod D A) (N₂ : Mod D A)
    (P₁ : Mod D A) (P₂ : Mod D A) :
    ((N₁.X ⊗ N₂.X) ◁ modTensorLegM A P₁ P₂) ≫
        rawInterchangeπ A N₁ N₂ P₁ P₂ =
      midArrangeP A N₁ N₂ P₁ P₂ ≫
        ((modTensorπ A N₁ P₁ ▷ A) ⊗ₘ modTensorπ A N₂ P₂) ≫
        modTensorLegM A (modTensorMod A N₁ P₁)
          (modTensorMod A N₂ P₂) ≫
        modTensorπ A (modTensorMod A N₁ P₁)
          (modTensorMod A N₂ P₂) := by
  have h1 := tensorμ_natural (𝟙 N₁.X) (𝟙 N₂.X)
    (actRight A P₁.X) (𝟙 P₂.X)
  simp only [MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_id,
    MonoidalCategory.id_whiskerRight] at h1
  conv_lhs => rw [modTensorLegM, rawInterchangeπ,
    rawInterchange, reassoc_of% h1]
  have hslot : (modTensorπ A N₁ P₁ ▷ A) ≫
      (β_ (modTensor A N₁ P₁) A).hom ≫ modTensorAct A N₁ P₁ =
    (β_ (N₁.X ⊗ P₁.X) A).hom ≫ (α_ A N₁.X P₁.X).inv ≫
      (actLeft A N₁.X ▷ P₁.X) ≫ modTensorπ A N₁ P₁ := by
    rw [BraidedCategory.braiding_naturality_left_assoc,
      whiskerLeft_modTensorπ_act]
    simp only [Category.assoc]
  have hcov : ((modTensorπ A N₁ P₁ ▷ A) ⊗ₘ
      modTensorπ A N₂ P₂) ≫
      modTensorLegM A (modTensorMod A N₁ P₁)
        (modTensorMod A N₂ P₂) =
    ((((β_ (N₁.X ⊗ P₁.X) A).hom ≫ (α_ A N₁.X P₁.X).inv ≫
      (actLeft A N₁.X ▷ P₁.X)) ≫ modTensorπ A N₁ P₁) ⊗ₘ
      modTensorπ A N₂ P₂) := by
    have hmw : ∀ {X₁ X₂ Y₁ Y₂ Z₁ : D} (a : X₁ ⟶ Y₁)
        (b : X₂ ⟶ Y₂) (f : Y₁ ⟶ Z₁),
        (a ⊗ₘ b) ≫ (f ▷ Y₂) = (a ≫ f) ⊗ₘ b := by
      intros
      rw [← MonoidalCategory.tensorHom_id,
        MonoidalCategory.tensorHom_comp_tensorHom,
        Category.comp_id]
    rw [modTensorLegM,
      show actRight A (modTensorMod A N₁ P₁).X =
        (β_ (modTensor A N₁ P₁) A).hom ≫
          modTensorAct A N₁ P₁ from rfl]
    show ((modTensorπ A N₁ P₁ ▷ A) ⊗ₘ modTensorπ A N₂ P₂) ≫
      (((β_ (modTensor A N₁ P₁) A).hom ≫
        modTensorAct A N₁ P₁) ▷ modTensor A N₂ P₂) = _
    rw [hmw, hslot]
    simp only [Category.assoc]
  have hcov' := congrArg (fun t => t ≫
    modTensorπ A (modTensorMod A N₁ P₁)
      (modTensorMod A N₂ P₂)) hcov
  repeat' erw [Category.assoc] at hcov'
  conv_rhs => erw [hcov', midArrangeP]
  conv_rhs => simp only [Category.assoc]
  refine congrArg (CategoryStruct.comp
    (tensorμ N₁.X N₂.X (P₁.X ⊗ A) P₂.X)) ?_
  rw [actRight]
  have hcond : (((β_ N₁.X A).hom ≫ actLeft A N₁.X) ▷ P₁.X) ≫
      modTensorπ A N₁ P₁ =
    (α_ N₁.X A P₁.X).hom ≫ (N₁.X ◁ actLeft A P₁.X) ≫
      modTensorπ A N₁ P₁ := by
    have hc := modTensor_condition A N₁ P₁
    rw [modTensorLegM, modTensorLegN, actRight] at hc
    simpa only [Category.assoc] using hc
  have hb := legMP_core A (actLeft A N₁.X) (actLeft A P₁.X)
    (modTensorπ A N₁ P₁) (modTensorπ A N₂ P₂)
    (modTensorπ A (modTensorMod A N₁ P₁)
      (modTensorMod A N₂ P₂)) hcond
  simp only [Category.assoc] at hb
  exact hb

/-- The coherence core of the second-block right leg
identification: the module condition on the second pair
transports the scalar action across the pair. -/
private theorem legNP_core
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    {V₁ V₂ W₁ W₂ Q₁ Q₂ Z : D}
    (actN : A ⊗ V₂ ⟶ V₂) (actW : A ⊗ W₂ ⟶ W₂)
    (q₁ : V₁ ⊗ W₁ ⟶ Q₁) (q₂ : V₂ ⊗ W₂ ⟶ Q₂)
    (out : Q₁ ⊗ Q₂ ⟶ Z)
    (hcond : (((β_ V₂ A).hom ≫ actN) ▷ W₂) ≫ q₂ =
      (α_ V₂ A W₂).hom ≫ (V₂ ◁ actW) ≫ q₂) :
    ((V₁ ⊗ V₂) ◁ (α_ W₁ A W₂).hom) ≫
        tensorμ V₁ V₂ W₁ (A ⊗ W₂) ≫
        (q₁ ⊗ₘ ((V₂ ◁ actW) ≫ q₂)) ≫ out =
      tensorμ V₁ V₂ (W₁ ⊗ A) W₂ ≫
        ((α_ V₁ W₁ A).inv ▷ (V₂ ⊗ W₂)) ≫
        (α_ (V₁ ⊗ W₁) A (V₂ ⊗ W₂)).hom ≫
        ((V₁ ⊗ W₁) ◁ (α_ A V₂ W₂).inv) ≫
        (q₁ ⊗ₘ ((actN ▷ W₂) ≫ q₂)) ≫ out := by
  have hml : ∀ {X₁ X₂ Y₂ Z₁ Z₂ : D} (b : X₂ ⟶ Y₂)
      (a : X₁ ⟶ Z₁) (c : Y₂ ⟶ Z₂),
      (X₁ ◁ b) ≫ (a ⊗ₘ c) = a ⊗ₘ (b ≫ c) := by
    intros
    rw [← MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom,
      Category.id_comp]
  have hbridge : (V₂ ◁ actW) ≫ q₂ =
      ((α_ V₂ A W₂).inv ≫ ((β_ V₂ A).hom ▷ W₂)) ≫
        ((actN ▷ W₂) ≫ q₂) := by
    calc (V₂ ◁ actW) ≫ q₂
        = (α_ V₂ A W₂).inv ≫ (α_ V₂ A W₂).hom ≫
            (V₂ ◁ actW) ≫ q₂ := by
          rw [Iso.inv_hom_id_assoc]
      _ = (α_ V₂ A W₂).inv ≫
            (((β_ V₂ A).hom ≫ actN) ▷ W₂) ≫ q₂ := by
          rw [hcond]
      _ = ((α_ V₂ A W₂).inv ≫ ((β_ V₂ A).hom ▷ W₂)) ≫
            ((actN ▷ W₂) ≫ q₂) := by
          rw [comp_whiskerRight]
          simp only [Category.assoc]
  rw [hbridge, ← hml ((α_ V₂ A W₂).inv ≫
    ((β_ V₂ A).hom ▷ W₂)) q₁ ((actN ▷ W₂) ≫ q₂)]
  suffices h : ((V₁ ⊗ V₂) ◁ (α_ W₁ A W₂).hom) ≫
      tensorμ V₁ V₂ W₁ (A ⊗ W₂) ≫
      ((V₁ ⊗ W₁) ◁ ((α_ V₂ A W₂).inv ≫
        ((β_ V₂ A).hom ▷ W₂))) =
    tensorμ V₁ V₂ (W₁ ⊗ A) W₂ ≫
      ((α_ V₁ W₁ A).inv ▷ (V₂ ⊗ W₂)) ≫
      (α_ (V₁ ⊗ W₁) A (V₂ ⊗ W₂)).hom ≫
      ((V₁ ⊗ W₁) ◁ (α_ A V₂ W₂).inv) by
    simp only [Category.assoc]
    conv_lhs => rw [reassoc_of% h]
  simp only [tensorμ]
  rw [BraidedCategory.braiding_tensor_right_hom V₂ W₁ A]
  monoidal

/-- The second-block right slide becomes the outer right slide of
the target. -/
theorem interchange_legNP
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (N₁ : Mod D A) (N₂ : Mod D A)
    (P₁ : Mod D A) (P₂ : Mod D A) :
    ((N₁.X ⊗ N₂.X) ◁ modTensorLegN A P₁ P₂) ≫
        rawInterchangeπ A N₁ N₂ P₁ P₂ =
      midArrangeP A N₁ N₂ P₁ P₂ ≫
        ((modTensorπ A N₁ P₁ ▷ A) ⊗ₘ modTensorπ A N₂ P₂) ≫
        modTensorLegN A (modTensorMod A N₁ P₁)
          (modTensorMod A N₂ P₂) ≫
        modTensorπ A (modTensorMod A N₁ P₁)
          (modTensorMod A N₂ P₂) := by
  have hml : ∀ {X₁ X₂ Y₂ Z₁ Z₂ : D} (b : X₂ ⟶ Y₂)
      (a : X₁ ⟶ Z₁) (c : Y₂ ⟶ Z₂),
      (X₁ ◁ b) ≫ (a ⊗ₘ c) = a ⊗ₘ (b ≫ c) := by
    intros
    rw [← MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom,
      Category.id_comp]
  have hmr : ∀ {X₁ X₂ Z₁ Y₂ Z₂ : D} (a : X₁ ⟶ Z₁)
      (b : X₂ ⟶ Y₂) (f : Y₂ ⟶ Z₂),
      (a ⊗ₘ b) ≫ (Z₁ ◁ f) = a ⊗ₘ (b ≫ f) := by
    intros
    rw [← MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom,
      Category.comp_id]
  have h1 := tensorμ_natural (𝟙 N₁.X) (𝟙 N₂.X) (𝟙 P₁.X)
    (actLeft A P₂.X)
  simp only [MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_id,
    MonoidalCategory.id_whiskerRight] at h1
  conv_lhs => rw [modTensorLegN, rawInterchangeπ,
    rawInterchange, MonoidalCategory.whiskerLeft_comp,
    Category.assoc, reassoc_of% h1]
  conv_lhs => erw [reassoc_of% hml (N₂.X ◁ actLeft A P₂.X)
    (modTensorπ A N₁ P₁) (modTensorπ A N₂ P₂)]
  have hassoc := associator_naturality (modTensorπ A N₁ P₁)
    (𝟙 A) (modTensorπ A N₂ P₂)
  have hcov : ((modTensorπ A N₁ P₁ ▷ A) ⊗ₘ
      modTensorπ A N₂ P₂) ≫
      modTensorLegN A (modTensorMod A N₁ P₁)
        (modTensorMod A N₂ P₂) =
    (α_ (N₁.X ⊗ P₁.X) A (N₂.X ⊗ P₂.X)).hom ≫
      ((N₁.X ⊗ P₁.X) ◁ (α_ A N₂.X P₂.X).inv) ≫
      (modTensorπ A N₁ P₁ ⊗ₘ
        ((actLeft A N₂.X ▷ P₂.X) ≫ modTensorπ A N₂ P₂)) := by
    rw [modTensorLegN,
      show actLeft A (modTensorMod A N₂ P₂).X =
        modTensorAct A N₂ P₂ from rfl]
    show ((modTensorπ A N₁ P₁ ▷ A) ⊗ₘ modTensorπ A N₂ P₂) ≫
      ((α_ (modTensor A N₁ P₁) A (modTensor A N₂ P₂)).hom ≫
        (modTensor A N₁ P₁ ◁ modTensorAct A N₂ P₂)) = _
    rw [← MonoidalCategory.tensorHom_id]
    rw [reassoc_of% hassoc, hmr,
      MonoidalCategory.id_tensorHom,
      whiskerLeft_modTensorπ_act]
    rw [show ((α_ A N₂.X P₂.X).inv ≫
        (actLeft A N₂.X ▷ P₂.X)) ≫ modTensorπ A N₂ P₂ =
      (α_ A N₂.X P₂.X).inv ≫
        ((actLeft A N₂.X ▷ P₂.X) ≫ modTensorπ A N₂ P₂) from
      Category.assoc _ _ _]
    rw [← hml (α_ A N₂.X P₂.X).inv (modTensorπ A N₁ P₁)
      ((actLeft A N₂.X ▷ P₂.X) ≫ modTensorπ A N₂ P₂)]
  have hcov' : ((modTensorπ A N₁ P₁ ▷ A) ⊗ₘ
      modTensorπ A N₂ P₂) ≫
      modTensorLegN A (modTensorMod A N₁ P₁)
        (modTensorMod A N₂ P₂) ≫
      modTensorπ A (modTensorMod A N₁ P₁)
        (modTensorMod A N₂ P₂) =
    (α_ (N₁.X ⊗ P₁.X) A (N₂.X ⊗ P₂.X)).hom ≫
      ((N₁.X ⊗ P₁.X) ◁ (α_ A N₂.X P₂.X).inv) ≫
      (modTensorπ A N₁ P₁ ⊗ₘ
        ((actLeft A N₂.X ▷ P₂.X) ≫ modTensorπ A N₂ P₂)) ≫
      modTensorπ A (modTensorMod A N₁ P₁)
        (modTensorMod A N₂ P₂) := by
    erw [← Category.assoc, hcov]
    exact (Category.assoc _ _ _).trans
      (congrArg (CategoryStruct.comp _) (Category.assoc _ _ _))
  conv_rhs => rw [hcov', midArrangeP]
  conv_rhs => rw [Category.assoc]
  have hcond : (((β_ N₂.X A).hom ≫ actLeft A N₂.X) ▷ P₂.X) ≫
      modTensorπ A N₂ P₂ =
    (α_ N₂.X A P₂.X).hom ≫ (N₂.X ◁ actLeft A P₂.X) ≫
      modTensorπ A N₂ P₂ := by
    have hc := modTensor_condition A N₂ P₂
    rw [modTensorLegM, modTensorLegN, actRight] at hc
    simpa only [Category.assoc] using hc
  have hb := legNP_core A (actLeft A N₂.X) (actLeft A P₂.X)
    (modTensorπ A N₁ P₁) (modTensorπ A N₂ P₂)
    (modTensorπ A (modTensorMod A N₁ P₁)
      (modTensorMod A N₂ P₂)) hcond
  exact hb

/-- The two first-block legs agree after the raw interchange
projection. -/
theorem rawInterchangeπ_condN
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (N₁ : Mod D A) (N₂ : Mod D A)
    (P₁ : Mod D A) (P₂ : Mod D A) :
    (modTensorLegM A N₁ N₂ ▷ (P₁.X ⊗ P₂.X)) ≫
        rawInterchangeπ A N₁ N₂ P₁ P₂ =
      (modTensorLegN A N₁ N₂ ▷ (P₁.X ⊗ P₂.X)) ≫
        rawInterchangeπ A N₁ N₂ P₁ P₂ := by
  rw [interchange_legM, interchange_legN]
  exact congrArg (CategoryStruct.comp _)
    (congrArg (CategoryStruct.comp _) (modTensor_condition A
      (modTensorMod A N₁ P₁) (modTensorMod A N₂ P₂)))

/-- The two second-block legs agree after the raw interchange
projection. -/
theorem rawInterchangeπ_condP
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (N₁ : Mod D A) (N₂ : Mod D A)
    (P₁ : Mod D A) (P₂ : Mod D A) :
    ((N₁.X ⊗ N₂.X) ◁ modTensorLegM A P₁ P₂) ≫
        rawInterchangeπ A N₁ N₂ P₁ P₂ =
      ((N₁.X ⊗ N₂.X) ◁ modTensorLegN A P₁ P₂) ≫
        rawInterchangeπ A N₁ N₂ P₁ P₂ := by
  rw [interchange_legMP, interchange_legNP]
  exact congrArg (CategoryStruct.comp _)
    (congrArg (CategoryStruct.comp _) (modTensor_condition A
      (modTensorMod A N₁ P₁) (modTensorMod A N₂ P₂)))

/-- First-stage descent of the interchange, through the
coequalizer of the first block. -/
noncomputable def interchangeStage1
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (N₁ : Mod D A) (N₂ : Mod D A)
    (P₁ : Mod D A) (P₂ : Mod D A) :
    modTensor A N₁ N₂ ⊗ (P₁.X ⊗ P₂.X) ⟶
      modTensor A (modTensorMod A N₁ P₁) (modTensorMod A N₂ P₂) :=
  modTensorWhiskerRDesc A N₁ N₂ (P₁.X ⊗ P₂.X)
    (rawInterchangeπ A N₁ N₂ P₁ P₂)
    (rawInterchangeπ_condN A N₁ N₂ P₁ P₂)

/-- Defining equation of the first-stage descent. -/
@[reassoc]
theorem whiskerRight_π_interchangeStage1
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (N₁ : Mod D A) (N₂ : Mod D A)
    (P₁ : Mod D A) (P₂ : Mod D A) :
    (modTensorπ A N₁ N₂ ▷ (P₁.X ⊗ P₂.X)) ≫
        interchangeStage1 A N₁ N₂ P₁ P₂ =
      rawInterchangeπ A N₁ N₂ P₁ P₂ :=
  whiskerRight_modTensorπ_whiskerRDesc A N₁ N₂ _ _ _

/-- The second-block legs agree after the first-stage descent. -/
theorem interchangeStage1_condP
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (N₁ : Mod D A) (N₂ : Mod D A)
    (P₁ : Mod D A) (P₂ : Mod D A) :
    (modTensor A N₁ N₂ ◁ modTensorLegM A P₁ P₂) ≫
        interchangeStage1 A N₁ N₂ P₁ P₂ =
      (modTensor A N₁ N₂ ◁ modTensorLegN A P₁ P₂) ≫
        interchangeStage1 A N₁ N₂ P₁ P₂ := by
  apply modTensor_whiskerR_hom_ext A N₁ N₂
    ((P₁.X ⊗ A) ⊗ P₂.X)
  rw [← whisker_exchange_assoc, ← whisker_exchange_assoc,
    whiskerRight_π_interchangeStage1]
  exact rawInterchangeπ_condP A N₁ N₂ P₁ P₂

/-- The interchange of module tensor products: the tensor product
of two module tensor products maps to the module tensor product
of the crossed pairs. -/
noncomputable def interchange
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (N₁ : Mod D A) (N₂ : Mod D A)
    (P₁ : Mod D A) (P₂ : Mod D A) :
    modTensor A N₁ N₂ ⊗ modTensor A P₁ P₂ ⟶
      modTensor A (modTensorMod A N₁ P₁) (modTensorMod A N₂ P₂) :=
  modTensorWhiskerDesc A P₁ P₂ (modTensor A N₁ N₂)
    (interchangeStage1 A N₁ N₂ P₁ P₂)
    (interchangeStage1_condP A N₁ N₂ P₁ P₂)

/-- Defining equation of the interchange. -/
@[reassoc (attr := simp)]
theorem tensorHom_π_interchange
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (N₁ : Mod D A) (N₂ : Mod D A)
    (P₁ : Mod D A) (P₂ : Mod D A) :
    (modTensorπ A N₁ N₂ ⊗ₘ modTensorπ A P₁ P₂) ≫
        interchange A N₁ N₂ P₁ P₂ =
      rawInterchangeπ A N₁ N₂ P₁ P₂ := by
  rw [interchange, MonoidalCategory.tensorHom_def,
    Category.assoc, whiskerLeft_modTensorπ_whiskerDesc,
    whiskerRight_π_interchangeStage1]

end RS
