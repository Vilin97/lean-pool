/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModTensor

/-!
# Base change of a free module

Base change along a morphism of commutative monoid objects sends
the free module on an object to the free module over the new base:
`B ⊗[A] (A ⊗ V) ≅ B ⊗ V` as `B`-modules.

* `baseChangeFreeHom`/`baseChangeFreeInv`: the two carrier maps,
  descending multiplication through `φ` and inserting the unit of
  `A` respectively.
* `baseChangeFreeIso`: the isomorphism `baseChangeMod φ (freeMod
  A V) ≅ freeMod B V` in the category of `B`-modules.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- Multiplying through `φ` twice is multiplying through `φ` once
after multiplying in `A`. -/
lemma pushMul_pushMul
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (B : D)
    [MonObj B] (φ : A ⟶ B) [IsMonHom φ] :
    ((B ◁ φ ≫ μ[B]) ▷ A) ≫ (B ◁ φ ≫ μ[B]) =
      (α_ B A A).hom ≫ B ◁ (μ[A] ≫ φ) ≫ μ[B] := by
  rw [IsMonHom.mul_hom φ, tensorHom_def]
  simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp,
    Category.assoc]
  rw [← whisker_exchange_assoc, MonObj.mul_assoc,
    associator_naturality_right_assoc,
    associator_naturality_middle_assoc]

/-- Multiplying in `B` before pushing through `φ` is multiplying
in `B` after. -/
lemma mul_pushMul
    [Category.{v} D] [MonoidalCategory D] (A : D) (B : D) [MonObj B]
    (φ : A ⟶ B) :
    (μ[B] ▷ A) ≫ (B ◁ φ ≫ μ[B]) =
      (α_ B B A).hom ≫ B ◁ (B ◁ φ ≫ μ[B]) ≫ μ[B] := by
  rw [← whisker_exchange_assoc, MonObj.mul_assoc,
    associator_naturality_right_assoc]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]

/-- The first module-tensor leg of the base change of a free
module, at carrier atoms. -/
lemma legM_restrictRegular_freeMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    (V : D) :
    modTensorLegM A (restrictRegular φ) (freeMod A V) =
      (B ◁ φ ≫ μ[B]) ▷ (A ⊗ V) :=
  congrArg (fun t : B ⊗ A ⟶ B => t ▷ (A ⊗ V))
    (actRight_restrictRegular φ)

/-- The comparison map coequalizes the two module-tensor legs,
stated at carrier atoms. -/
lemma baseChangeFree_condition_atoms
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (B : D)
    [MonObj B] (φ : A ⟶ B) [IsMonHom φ]
    (V : D) :
    ((B ◁ φ ≫ μ[B]) ▷ (A ⊗ V)) ≫
        ((α_ B A V).inv ≫ (B ◁ φ ≫ μ[B]) ▷ V) =
      ((α_ B A (A ⊗ V)).hom ≫
          B ◁ ((α_ A A V).inv ≫ μ[A] ▷ V)) ≫
        ((α_ B A V).inv ≫ (B ◁ φ ≫ μ[B]) ▷ V) := by
  have hstruct :
      (α_ B A (A ⊗ V)).hom ≫ B ◁ (α_ A A V).inv ≫
          (α_ B (A ⊗ A) V).inv =
        (α_ (B ⊗ A) A V).inv ≫ (α_ B A A).hom ▷ V := by
    monoidal
  rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight,
    pushMul_pushMul]
  simp only [MonoidalCategory.whiskerLeft_comp, comp_whiskerRight,
    Category.assoc]
  rw [associator_inv_naturality_middle_assoc, reassoc_of% hstruct]

/-- The comparison map coequalizes the two module-tensor legs. -/
lemma baseChangeFree_condition
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    (V : D) :
    modTensorLegM A (restrictRegular φ) (freeMod A V) ≫
        ((α_ B A V).inv ≫ (B ◁ φ ≫ μ[B]) ▷ V) =
      modTensorLegN A (restrictRegular φ) (freeMod A V) ≫
        ((α_ B A V).inv ≫ (B ◁ φ ≫ μ[B]) ▷ V) :=
  (congrArg
    (fun t => t ≫ ((α_ B A V).inv ≫ (B ◁ φ ≫ μ[B]) ▷ V))
    (legM_restrictRegular_freeMod A B φ V)).trans
    (baseChangeFree_condition_atoms A B φ V)

/-- The comparison map from the base change of a free module to
the free module over the new base. -/
noncomputable def baseChangeFreeHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (B : D) [MonObj B]
    [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    (V : D) :
    baseChange φ (freeMod A V) ⟶ B ⊗ V :=
  modTensorDesc A (restrictRegular φ) (freeMod A V)
    ((α_ B A V).inv ≫ (B ◁ φ ≫ μ[B]) ▷ V)
    (baseChangeFree_condition A B φ V)

/-- Defining equation of the comparison map. -/
@[reassoc]
lemma modTensorπ_baseChangeFreeHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (B : D) [MonObj B]
    [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    (V : D) :
    modTensorπ A (restrictRegular φ) (freeMod A V) ≫
        baseChangeFreeHom A B φ V =
      (α_ B A V).inv ≫ (B ◁ φ ≫ μ[B]) ▷ V :=
  modTensorπ_desc A (restrictRegular φ) (freeMod A V) _ _

/-- The inverse comparison map: insert the unit of `A`. -/
noncomputable def baseChangeFreeInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (B : D) [MonObj B] (φ : A ⟶ B)
    [IsMonHom φ]
    (V : D) :
    B ⊗ V ⟶ baseChange φ (freeMod A V) :=
  B ◁ ((λ_ V).inv ≫ η[A] ▷ V) ≫
    modTensorπ A (restrictRegular φ) (freeMod A V)

/-- The balance relation of the base-change projection on a free
module, at carrier atoms. -/
@[reassoc]
lemma baseChangeFree_balance
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (B : D) [MonObj B]
    [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    (V : D) :
    ((B ◁ φ ≫ μ[B]) ▷ (A ⊗ V)) ≫
        modTensorπ A (restrictRegular φ) (freeMod A V) =
      ((α_ B A (A ⊗ V)).hom ≫
          B ◁ ((α_ A A V).inv ≫ μ[A] ▷ V)) ≫
        modTensorπ A (restrictRegular φ) (freeMod A V) :=
  (congrArg
    (fun t =>
      t ≫ modTensorπ A (restrictRegular φ) (freeMod A V))
    (legM_restrictRegular_freeMod A B φ V)).symm.trans
    (modTensor_condition A (restrictRegular φ) (freeMod A V))

/-- Multiplying out and reinserting the unit of `A` returns the
projection: the retract identity behind `hom ≫ inv = 𝟙`. -/
lemma baseChangeFree_retract
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (B : D) [MonObj B]
    [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    (V : D) :
    ((α_ B A V).inv ≫ (B ◁ φ ≫ μ[B]) ▷ V) ≫
        (B ◁ ((λ_ V).inv ≫ η[A] ▷ V) ≫
          modTensorπ A (restrictRegular φ) (freeMod A V)) =
      modTensorπ A (restrictRegular φ) (freeMod A V) := by
  simp only [Category.assoc]
  erw [← whisker_exchange_assoc, baseChangeFree_balance]
  repeat' erw [Category.assoc]
  erw [associator_naturality_right_assoc, Iso.inv_hom_id_assoc,
    ← whiskerLeft_comp_assoc, whiskerLeft_one_mul,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- The two comparison maps compose to the identity of the base
change. -/
lemma baseChangeFree_hom_inv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (B : D) [MonObj B]
    [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    (V : D) :
    baseChangeFreeHom A B φ V ≫ baseChangeFreeInv A B φ V =
      𝟙 (baseChange φ (freeMod A V)) := by
  apply modTensor_hom_ext A (restrictRegular φ) (freeMod A V)
  exact (Category.assoc _ _ _).symm.trans
    (((congrArg (fun t => t ≫ baseChangeFreeInv A B φ V)
      (modTensorπ_baseChangeFreeHom A B φ V)).trans
      (baseChangeFree_retract A B φ V)).trans
      (Category.comp_id _).symm)

/-- Inserting the unit of `A` and multiplying out through `φ` is
the identity of `B ⊗ V`. -/
lemma baseChangeFree_section_atoms
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (B : D)
    [MonObj B] (φ : A ⟶ B) [IsMonHom φ]
    (V : D) :
    B ◁ ((λ_ V).inv ≫ η[A] ▷ V) ≫
        ((α_ B A V).inv ≫ (B ◁ φ ≫ μ[B]) ▷ V) =
      𝟙 (B ⊗ V) := by
  rw [MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight, ← whiskerLeft_comp_assoc,
    IsMonHom.one_hom φ, MonObj.mul_one]
  monoidal

/-- The two comparison maps compose to the identity of the free
module over the new base. -/
lemma baseChangeFree_inv_hom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (B : D) [MonObj B]
    [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    (V : D) :
    baseChangeFreeInv A B φ V ≫ baseChangeFreeHom A B φ V =
      𝟙 (B ⊗ V) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun t => B ◁ ((λ_ V).inv ≫ η[A] ▷ V) ≫ t)
      (modTensorπ_baseChangeFreeHom A B φ V)).trans
      (baseChangeFree_section_atoms A B φ V))

/-- The comparison map intertwines the two `B`-actions, at carrier
atoms. -/
lemma baseChangeFree_linear_atoms
    [Category.{v} D] [MonoidalCategory D] (A : D) (B : D) [MonObj B]
    (φ : A ⟶ B)
    (V : D) :
    ((α_ B B (A ⊗ V)).inv ≫ μ[B] ▷ (A ⊗ V)) ≫
        ((α_ B A V).inv ≫ (B ◁ φ ≫ μ[B]) ▷ V) =
      B ◁ ((α_ B A V).inv ≫ (B ◁ φ ≫ μ[B]) ▷ V) ≫
        ((α_ B B V).inv ≫ μ[B] ▷ V) := by
  have hstruct :
      (α_ B B (A ⊗ V)).inv ≫ (α_ (B ⊗ B) A V).inv ≫
          (α_ B B A).hom ▷ V =
        B ◁ (α_ B A V).inv ≫ (α_ B (B ⊗ A) V).inv := by
    monoidal
  simp only [Category.assoc]
  rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight,
    mul_pushMul]
  simp only [MonoidalCategory.whiskerLeft_comp, comp_whiskerRight,
    Category.assoc]
  rw [associator_inv_naturality_middle_assoc,
    associator_inv_naturality_middle_assoc, reassoc_of% hstruct]

/-- Defining equation of the `B`-action on the base change of a
free module, at carrier atoms. -/
lemma whiskerLeft_π_baseChangeAct_free
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (B : D) [MonObj B]
    [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (V : D) :
    B ◁ modTensorπ A (restrictRegular φ) (freeMod A V) ≫
        baseChangeAct φ (freeMod A V) =
      ((α_ B B (A ⊗ V)).inv ≫ μ[B] ▷ (A ⊗ V)) ≫
        modTensorπ A (restrictRegular φ) (freeMod A V) :=
  whiskerLeft_modTensorπ_baseChangeAct φ (freeMod A V)

/-- The comparison map is `B`-linear. -/
@[reassoc]
lemma baseChangeAct_baseChangeFreeHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (B : D) [MonObj B]
    [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (V : D) :
    baseChangeAct φ (freeMod A V) ≫ baseChangeFreeHom A B φ V =
      B ◁ baseChangeFreeHom A B φ V ≫
        ((α_ B B V).inv ≫ μ[B] ▷ V) := by
  apply modTensor_whisker_hom_ext A (restrictRegular φ)
    (freeMod A V) B
  have h1 :
      B ◁ modTensorπ A (restrictRegular φ) (freeMod A V) ≫
          (baseChangeAct φ (freeMod A V) ≫
            baseChangeFreeHom A B φ V) =
        ((α_ B B (A ⊗ V)).inv ≫ μ[B] ▷ (A ⊗ V)) ≫
          (modTensorπ A (restrictRegular φ) (freeMod A V) ≫
            baseChangeFreeHom A B φ V) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ baseChangeFreeHom A B φ V)
        (whiskerLeft_π_baseChangeAct_free A B φ V)).trans
        (Category.assoc _ _ _))
  have h2 :
      ((α_ B B (A ⊗ V)).inv ≫ μ[B] ▷ (A ⊗ V)) ≫
          (modTensorπ A (restrictRegular φ) (freeMod A V) ≫
            baseChangeFreeHom A B φ V) =
        ((α_ B B (A ⊗ V)).inv ≫ μ[B] ▷ (A ⊗ V)) ≫
          ((α_ B A V).inv ≫ (B ◁ φ ≫ μ[B]) ▷ V) :=
    congrArg
      (fun t => ((α_ B B (A ⊗ V)).inv ≫ μ[B] ▷ (A ⊗ V)) ≫ t)
      (modTensorπ_baseChangeFreeHom A B φ V)
  have h4 :
      B ◁ modTensorπ A (restrictRegular φ) (freeMod A V) ≫
          (B ◁ baseChangeFreeHom A B φ V ≫
            ((α_ B B V).inv ≫ μ[B] ▷ V)) =
        B ◁ (modTensorπ A (restrictRegular φ) (freeMod A V) ≫
            baseChangeFreeHom A B φ V) ≫
          ((α_ B B V).inv ≫ μ[B] ▷ V) :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun t => t ≫ ((α_ B B V).inv ≫ μ[B] ▷ V))
        (MonoidalCategory.whiskerLeft_comp B
          (modTensorπ A (restrictRegular φ) (freeMod A V))
          (baseChangeFreeHom A B φ V)).symm)
  have h5 :
      B ◁ (modTensorπ A (restrictRegular φ) (freeMod A V) ≫
          baseChangeFreeHom A B φ V) ≫
          ((α_ B B V).inv ≫ μ[B] ▷ V) =
        B ◁ ((α_ B A V).inv ≫ (B ◁ φ ≫ μ[B]) ▷ V) ≫
          ((α_ B B V).inv ≫ μ[B] ▷ V) :=
    congrArg (fun t => B ◁ t ≫ ((α_ B B V).inv ≫ μ[B] ▷ V))
      (modTensorπ_baseChangeFreeHom A B φ V)
  exact ((h1.trans h2).trans
    (baseChangeFree_linear_atoms A B φ V)).trans
    ((h4.trans h5).symm)

/-- The inverse comparison map is `B`-linear. -/
lemma freeAct_baseChangeFreeInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (B : D) [MonObj B]
    [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (V : D) :
    ((α_ B B V).inv ≫ μ[B] ▷ V) ≫ baseChangeFreeInv A B φ V =
      B ◁ baseChangeFreeInv A B φ V ≫
        baseChangeAct φ (freeMod A V) := by
  conv_rhs =>
    rw [← Category.comp_id (baseChangeAct φ (freeMod A V)),
      ← baseChangeFree_hom_inv A B φ V,
      baseChangeAct_baseChangeFreeHom_assoc A B φ V,
      ← whiskerLeft_comp_assoc, baseChangeFree_inv_hom A B φ V,
      MonoidalCategory.whiskerLeft_id, Category.id_comp]
  simp only [Category.assoc]

/-- **Base change of a free module**: the base change along `φ` of
the free `A`-module on `V` is the free `B`-module on `V`, as an
isomorphism of `B`-modules. -/
noncomputable def baseChangeFreeIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (B : D) [MonObj B]
    [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (V : D) :
    baseChangeMod φ (freeMod A V) ≅ freeMod B V where
  hom := Mod.Hom.mk' (baseChangeFreeHom A B φ V)
    (by exact baseChangeAct_baseChangeFreeHom A B φ V)
  inv := Mod.Hom.mk' (baseChangeFreeInv A B φ V)
    (by exact freeAct_baseChangeFreeInv A B φ V)
  hom_inv_id := by
    apply Mod.hom_ext
    exact baseChangeFree_hom_inv A B φ V
  inv_hom_id := by
    apply Mod.hom_ext
    exact baseChangeFree_inv_hom A B φ V

end RS
