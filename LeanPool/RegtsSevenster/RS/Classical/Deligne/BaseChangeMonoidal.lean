/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.BaseChangeCoherence
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.StepATransport

/-!
# Base change as a monoidal functor

Base change along a morphism of commutative algebras carries
modules to modules, morphisms to morphisms, and the relative
tensor to the relative tensor: the projection formula is the
structure map, the collapse of the regular module is the unit.
This file bundles the structure map as an isomorphism of modules
over the new base and proves it natural in both slots.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **The structure map of base change, as an isomorphism of
modules over the new base.** -/
noncomputable def projFormulaMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ]
    (M N : Mod D A) :
    modTensorMod B (baseChangeMod φ M) (baseChangeMod φ N) ≅
      baseChangeMod φ (modTensorMod A M N) where
  hom := Mod.Hom.mk' (projFormula A B φ M N).hom (by
    exact projFormula_linear A B φ M N)
  inv := Mod.Hom.mk' (projFormula A B φ M N).inv (by
    exact act_inv_of_act_hom B (projFormula A B φ M N)
      (projFormula_linear A B φ M N))
  hom_inv_id := by
    apply Mod.Hom.ext
    exact (projFormula A B φ M N).hom_inv_id
  inv_hom_id := by
    apply Mod.Hom.ext
    exact (projFormula A B φ M N).inv_hom_id

/-- **The structure map is natural in the second slot.** -/
theorem projFormula_natural_right
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ]
    (M : Mod D A)
    {N N' : Mod D A} (g : N ⟶ N') :
    modTensorMap B (𝟙 (baseChangeMod φ M))
        (baseChangeMapMod A B φ g) ≫
        (projFormula A B φ M N').hom =
      (projFormula A B φ M N).hom ≫
        modTensorMap A (𝟙 (restrictRegular φ))
          (modTensorMapMod A (𝟙 M) g) := by
  have hmapB : modTensorπ B (baseChangeMod φ M)
      (baseChangeMod φ N) ≫
      modTensorMap B (𝟙 (baseChangeMod φ M))
        (baseChangeMapMod A B φ g) =
    ((baseChangeMod φ M).X ◁
        modTensorMap A (𝟙 (restrictRegular φ)) g) ≫
      modTensorπ B (baseChangeMod φ M)
        (baseChangeMod φ N') := by
    rw [modTensorπ_map, Mod.id_hom',
      MonoidalCategory.id_tensorHom]
    rfl
  have hmapA : modTensorπ A (restrictRegular φ) N ≫
      modTensorMap A (𝟙 (restrictRegular φ)) g =
    (B ◁ g.hom) ≫ modTensorπ A (restrictRegular φ) N' := by
    rw [modTensorπ_map, Mod.id_hom',
      MonoidalCategory.id_tensorHom]
  have hL : ((baseChangeMod φ M).X ◁
      modTensorπ A (restrictRegular φ) N) ≫
      modTensorπ B (baseChangeMod φ M)
        (baseChangeMod φ N) ≫
      modTensorMap B (𝟙 (baseChangeMod φ M))
        (baseChangeMapMod A B φ g) ≫
      (projFormula A B φ M N').hom =
    ((baseChangeMod φ M).X ◁ (B ◁ g.hom)) ≫
      (α_ (baseChangeMod φ M).X B N'.X).inv ≫
      (actRight B (baseChangeMod φ M).X ▷ N'.X) ≫
      modTensorAssocMid A (restrictRegular φ) M N' := by
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
    refine Eq.trans (whisker_eq _ (eq_whisker hmapB _)) ?_
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      ((MonoidalCategory.whiskerLeft_comp _ _ _).symm.trans
        (congrArg (fun t =>
          (baseChangeMod φ M).X ◁ t) hmapA)) _) ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp _ _ _) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact whisker_eq _ (projFormula_cover A B φ M N')
  have hR : ((baseChangeMod φ M).X ◁
      modTensorπ A (restrictRegular φ) N) ≫
      modTensorπ B (baseChangeMod φ M)
        (baseChangeMod φ N) ≫
      (projFormula A B φ M N).hom ≫
      modTensorMap A (𝟙 (restrictRegular φ))
        (modTensorMapMod A (𝟙 M) g) =
    (α_ (baseChangeMod φ M).X B N.X).inv ≫
      (actRight B (baseChangeMod φ M).X ▷ N.X) ≫
      ((modTensorMod A (restrictRegular φ) M).X ◁ g.hom) ≫
      modTensorAssocMid A (restrictRegular φ) M N' := by
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (projFormula_cover A B φ M N) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
    exact whisker_eq _ (whisker_eq _
      (modTensorAssocMid_natural_right A
        (restrictRegular φ) M g))
  have hend : ∀ (Y : D) (r : Y ⊗ B ⟶ Y),
      (Y ◁ (B ◁ g.hom)) ≫ (α_ Y B N'.X).inv ≫ (r ▷ N'.X) =
        (α_ Y B N.X).inv ≫ (r ▷ N.X) ≫ (Y ◁ g.hom) := by
    intro Y r
    rw [associator_inv_naturality_right_assoc, whisker_exchange]
  apply modTensor_hom_ext
  apply modTensor_whisker_hom_ext A (restrictRegular φ) N
    (baseChangeMod φ M).X
  refine Eq.trans hL (Eq.trans ?_ hR.symm)
  refine Eq.trans (whisker_eq _
    (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (hend _ _) _) ?_
  simp only []
  conv_lhs => erw [Category.assoc]; arg 2; erw [Category.assoc]
  rfl

/-- **The structure map is natural in the first slot.** -/
theorem projFormula_natural_left
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ]
    {M M' : Mod D A} (f : M ⟶ M')
    (N : Mod D A) :
    modTensorMap B (baseChangeMapMod A B φ f)
        (𝟙 (baseChangeMod φ N)) ≫
        (projFormula A B φ M' N).hom =
      (projFormula A B φ M N).hom ≫
        modTensorMap A (𝟙 (restrictRegular φ))
          (modTensorMapMod A f (𝟙 N)) := by
  have hmapB : modTensorπ B (baseChangeMod φ M)
      (baseChangeMod φ N) ≫
      modTensorMap B (baseChangeMapMod A B φ f)
        (𝟙 (baseChangeMod φ N)) =
    (modTensorMap A (𝟙 (restrictRegular φ)) f ▷
        (baseChangeMod φ N).X) ≫
      modTensorπ B (baseChangeMod φ M')
        (baseChangeMod φ N) := by
    rw [modTensorπ_map, Mod.id_hom',
      MonoidalCategory.tensorHom_id]
    rfl
  have hact : actRight B (baseChangeMod φ M).X ≫
      modTensorMap A (𝟙 (restrictRegular φ)) f =
    (modTensorMap A (𝟙 (restrictRegular φ)) f ▷ B) ≫
      actRight B (baseChangeMod φ M').X :=
    actRight_natural_mod B (baseChangeMapMod A B φ f)
  have hL : ((baseChangeMod φ M).X ◁
      modTensorπ A (restrictRegular φ) N) ≫
      modTensorπ B (baseChangeMod φ M)
        (baseChangeMod φ N) ≫
      modTensorMap B (baseChangeMapMod A B φ f)
        (𝟙 (baseChangeMod φ N)) ≫
      (projFormula A B φ M' N).hom =
    (modTensorMap A (𝟙 (restrictRegular φ)) f ▷
        (B ⊗ N.X)) ≫
      (α_ (baseChangeMod φ M').X B N.X).inv ≫
      (actRight B (baseChangeMod φ M').X ▷ N.X) ≫
      modTensorAssocMid A (restrictRegular φ) M' N := by
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
    refine Eq.trans (whisker_eq _ (eq_whisker hmapB _)) ?_
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker (whisker_exchange _ _) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact whisker_eq _ (projFormula_cover A B φ M' N)
  have hR : ((baseChangeMod φ M).X ◁
      modTensorπ A (restrictRegular φ) N) ≫
      modTensorπ B (baseChangeMod φ M)
        (baseChangeMod φ N) ≫
      (projFormula A B φ M N).hom ≫
      modTensorMap A (𝟙 (restrictRegular φ))
        (modTensorMapMod A f (𝟙 N)) =
    (α_ (baseChangeMod φ M).X B N.X).inv ≫
      (actRight B (baseChangeMod φ M).X ▷ N.X) ≫
      (modTensorMap A (𝟙 (restrictRegular φ)) f ▷ N.X) ≫
      modTensorAssocMid A (restrictRegular φ) M' N := by
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (projFormula_cover A B φ M N) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
    exact whisker_eq _ (whisker_eq _
      (modTensorAssocMid_natural_mid A
        (restrictRegular φ) f N))
  have hend : ∀ (Y Y' : D) (r : Y ⊗ B ⟶ Y) (r' : Y' ⊗ B ⟶ Y')
      (k : Y ⟶ Y'), r ≫ k = (k ▷ B) ≫ r' →
      (k ▷ (B ⊗ N.X)) ≫ (α_ Y' B N.X).inv ≫ (r' ▷ N.X) =
        (α_ Y B N.X).inv ≫ (r ▷ N.X) ≫ (k ▷ N.X) := by
    intro Y Y' r r' k hk
    rw [associator_inv_naturality_left_assoc,
      ← MonoidalCategory.comp_whiskerRight, ← hk,
      MonoidalCategory.comp_whiskerRight]
  apply modTensor_hom_ext
  apply modTensor_whisker_hom_ext A (restrictRegular φ) N
    (baseChangeMod φ M).X
  refine Eq.trans hL (Eq.trans ?_ hR.symm)
  refine Eq.trans (whisker_eq _
    (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (hend _ _ _ _ _ hact) _) ?_
  simp only [Category.assoc]
  rfl

section Assoc

/-- The left-nested side of the associator square, evaluated on
the triple cover. -/
theorem projFormula_assoc_leftCover
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] (M : Mod D A) (N : Mod D A) (P : Mod D A) :
    ((modTensorπ A (restrictRegular φ) M ▷ (B ⊗ N.X)) ▷
        (B ⊗ P.X)) ≫
      (((baseChangeMod φ M).X ◁
        modTensorπ A (restrictRegular φ) N) ▷ (B ⊗ P.X)) ≫
      (modTensorπ B (baseChangeMod φ M) (baseChangeMod φ N) ▷
        (B ⊗ P.X)) ≫
      (modTensor B (baseChangeMod φ M) (baseChangeMod φ N) ◁
        modTensorπ A (restrictRegular φ) P) ≫
      modTensorπ B
        (modTensorMod B (baseChangeMod φ M) (baseChangeMod φ N))
        (baseChangeMod φ P) ≫
      modTensorMap B (projFormulaMod A B φ M N).hom
        (𝟙 (baseChangeMod φ P)) ≫
      (projFormula A B φ (modTensorMod A M N) P).hom ≫
      modTensorMap A (𝟙 (restrictRegular φ))
        (modTensorAssocModIso A M N P).hom =
    (((tensorμ B M.X B N.X ≫ (μ[B] ▷ (M.X ⊗ N.X))) ≫
        (B ◁ modTensorπ A M N)) ▷ (B ⊗ P.X)) ≫
      (tensorμ B (modTensor A M N) B P.X ≫
        (μ[B] ▷ (modTensor A M N ⊗ P.X))) ≫
      (B ◁ modTensorAssocMid A M N P) ≫
      modTensorπ A (restrictRegular φ)
        (modTensorMod A M (modTensorMod A N P)) := by
  have h1 : modTensorπ B
      (modTensorMod B (baseChangeMod φ M) (baseChangeMod φ N))
      (baseChangeMod φ P) ≫
      modTensorMap B (projFormulaMod A B φ M N).hom
        (𝟙 (baseChangeMod φ P)) =
    ((projFormula A B φ M N).hom ▷
        (baseChangeMod φ P).X) ≫
      modTensorπ B (baseChangeMod φ (modTensorMod A M N))
        (baseChangeMod φ P) := by
    rw [modTensorπ_map, Mod.id_hom',
      MonoidalCategory.tensorHom_id]
    rfl
  have h5 : modTensorπ A (restrictRegular φ)
      (modTensorMod A (modTensorMod A M N) P) ≫
      modTensorMap A (𝟙 (restrictRegular φ))
        (modTensorAssocModIso A M N P).hom =
    (B ◁ modTensorAssocHom A M N P) ≫
      modTensorπ A (restrictRegular φ)
        (modTensorMod A M (modTensorMod A N P)) := by
    rw [modTensorπ_map, Mod.id_hom',
      MonoidalCategory.id_tensorHom]
    rfl
  have hcore1 : (modTensor B (baseChangeMod φ M)
        (baseChangeMod φ N) ◁
      modTensorπ A (restrictRegular φ) P) ≫
      modTensorπ B
        (modTensorMod B (baseChangeMod φ M)
          (baseChangeMod φ N)) (baseChangeMod φ P) ≫
      modTensorMap B (projFormulaMod A B φ M N).hom
        (𝟙 (baseChangeMod φ P)) ≫
      (projFormula A B φ (modTensorMod A M N) P).hom ≫
      modTensorMap A (𝟙 (restrictRegular φ))
        (modTensorAssocModIso A M N P).hom =
    ((projFormula A B φ M N).hom ▷ (B ⊗ P.X)) ≫
      ((baseChangeMod φ (modTensorMod A M N)).X ◁
        modTensorπ A (restrictRegular φ) P) ≫
      modTensorπ B (baseChangeMod φ (modTensorMod A M N))
        (baseChangeMod φ P) ≫
      (projFormula A B φ (modTensorMod A M N) P).hom ≫
      modTensorMap A (𝟙 (restrictRegular φ))
        (modTensorAssocModIso A M N P).hom := by
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
    refine Eq.trans (whisker_eq _ (eq_whisker h1 _)) ?_
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker (whisker_exchange
      (projFormula A B φ M N).hom
      (modTensorπ A (restrictRegular φ) P)) _) ?_
    simp only []
    erw [Category.assoc]
    rfl
  have hcore2 : ∀ {Z : D}
      (h : (baseChangeMod φ (modTensorMod A M N)).X ⊗
        (B ⊗ P.X) ⟶ Z),
      ((modTensorπ A (restrictRegular φ) M ▷ (B ⊗ N.X)) ▷
          (B ⊗ P.X)) ≫
        (((baseChangeMod φ M).X ◁
          modTensorπ A (restrictRegular φ) N) ▷ (B ⊗ P.X)) ≫
        (modTensorπ B (baseChangeMod φ M) (baseChangeMod φ N) ▷
          (B ⊗ P.X)) ≫
        ((projFormula A B φ M N).hom ▷ (B ⊗ P.X)) ≫ h =
      (((tensorμ B M.X B N.X ≫ (μ[B] ▷ (M.X ⊗ N.X))) ≫
          (B ◁ modTensorπ A M N)) ▷ (B ⊗ P.X)) ≫
        (modTensorπ A (restrictRegular φ)
          (modTensorMod A M N) ▷ (B ⊗ P.X)) ≫ h := by
    intro Z h
    have hfold : (((modTensorπ A (restrictRegular φ) M ▷
          (B ⊗ N.X)) ≫
        ((baseChangeMod φ M).X ◁
          modTensorπ A (restrictRegular φ) N)) ≫
        modTensorπ B (baseChangeMod φ M) (baseChangeMod φ N)) ≫
        (projFormula A B φ M N).hom =
      ((tensorμ B M.X B N.X ≫ (μ[B] ▷ (M.X ⊗ N.X))) ≫
          (B ◁ modTensorπ A M N)) ≫
        modTensorπ A (restrictRegular φ)
          (modTensorMod A M N) := by
      simp only [Category.assoc]
      conv_lhs => erw [Category.assoc, Category.assoc]
      conv_rhs => erw [Category.assoc]; arg 2; erw [Category.assoc]
      exact projFormula_tensorμ_cover A B φ M N
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.comp_whiskerRight _ _ _).symm _) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.comp_whiskerRight _ _ _).symm _) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.comp_whiskerRight _ _ _).symm _) ?_
    refine Eq.trans (eq_whisker
      (congrArg (fun t => t ▷ (B ⊗ P.X)) hfold) _) ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.comp_whiskerRight _ _ _) _) ?_
    exact Category.assoc _ _ _
  have hcore3 : (modTensorπ A (restrictRegular φ)
        (modTensorMod A M N) ▷ (B ⊗ P.X)) ≫
      ((baseChangeMod φ (modTensorMod A M N)).X ◁
        modTensorπ A (restrictRegular φ) P) ≫
      modTensorπ B (baseChangeMod φ (modTensorMod A M N))
        (baseChangeMod φ P) ≫
      (projFormula A B φ (modTensorMod A M N) P).hom ≫
      modTensorMap A (𝟙 (restrictRegular φ))
        (modTensorAssocModIso A M N P).hom =
    (tensorμ B (modTensor A M N) B P.X ≫
        (μ[B] ▷ (modTensor A M N ⊗ P.X))) ≫
      (B ◁ modTensorAssocMid A M N P) ≫
      modTensorπ A (restrictRegular φ)
        (modTensorMod A M (modTensorMod A N P)) := by
    have hcover := congrArg (fun t => t ≫
        modTensorMap A (𝟙 (restrictRegular φ))
          (modTensorAssocModIso A M N P).hom)
      (projFormula_tensorμ_cover A B φ (modTensorMod A M N) P)
    conv at hcover =>
      lhs
      erw [Category.assoc]
      arg 2
      erw [Category.assoc]
      arg 2
      erw [Category.assoc]
    refine Eq.trans hcover ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
    refine Eq.trans (whisker_eq _ (whisker_eq _
      (Category.assoc _ _ _))) ?_
    refine Eq.trans (whisker_eq _ (whisker_eq _
      (whisker_eq _ h5))) ?_
    refine Eq.trans (whisker_eq _ (whisker_eq _
      ((Category.assoc _ _ _).symm.trans (eq_whisker
        ((MonoidalCategory.whiskerLeft_comp _ _ _).symm.trans
          (congrArg (fun t => B ◁ t)
            (modTensorπ_assocHom A M N P))) _)))) ?_
    exact (Category.assoc _ _ _).symm
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (whisker_eq _ hcore1))) ?_
  refine Eq.trans (hcore2 _) ?_
  exact whisker_eq _ hcore3

/-- The right-nested side of the associator square, evaluated on
the triple cover. -/
theorem projFormula_assoc_rightCover
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] (M : Mod D A) (N : Mod D A) (P : Mod D A) :
    ((modTensorπ A (restrictRegular φ) M ▷ (B ⊗ N.X)) ▷
        (B ⊗ P.X)) ≫
      (((baseChangeMod φ M).X ◁
        modTensorπ A (restrictRegular φ) N) ▷ (B ⊗ P.X)) ≫
      (modTensorπ B (baseChangeMod φ M) (baseChangeMod φ N) ▷
        (B ⊗ P.X)) ≫
      (modTensor B (baseChangeMod φ M) (baseChangeMod φ N) ◁
        modTensorπ A (restrictRegular φ) P) ≫
      modTensorπ B
        (modTensorMod B (baseChangeMod φ M) (baseChangeMod φ N))
        (baseChangeMod φ P) ≫
      modTensorAssocHom B (baseChangeMod φ M)
        (baseChangeMod φ N) (baseChangeMod φ P) ≫
      modTensorMap B (𝟙 (baseChangeMod φ M))
        (projFormulaMod A B φ N P).hom ≫
      (projFormula A B φ M (modTensorMod A N P)).hom =
    (α_ (B ⊗ M.X) (B ⊗ N.X) (B ⊗ P.X)).hom ≫
      ((B ⊗ M.X) ◁ (tensorμ B N.X B P.X ≫
        (μ[B] ▷ (N.X ⊗ P.X)) ≫ (B ◁ modTensorπ A N P))) ≫
      (tensorμ B M.X B (modTensor A N P) ≫
        (μ[B] ▷ (M.X ⊗ modTensor A N P))) ≫
      (B ◁ modTensorπ A M (modTensorMod A N P)) ≫
      modTensorπ A (restrictRegular φ)
        (modTensorMod A M (modTensorMod A N P)) := by
  have h2 : modTensorπ B (baseChangeMod φ M)
      (modTensorMod B (baseChangeMod φ N)
        (baseChangeMod φ P)) ≫
      modTensorMap B (𝟙 (baseChangeMod φ M))
        (projFormulaMod A B φ N P).hom =
    ((baseChangeMod φ M).X ◁
        (projFormula A B φ N P).hom) ≫
      modTensorπ B (baseChangeMod φ M)
        (baseChangeMod φ (modTensorMod A N P)) := by
    rw [modTensorπ_map, Mod.id_hom',
      MonoidalCategory.id_tensorHom]
    rfl
  have hcov : (modTensorπ B (baseChangeMod φ M)
        (baseChangeMod φ N) ▷ (baseChangeMod φ P).X) ≫
      modTensorAssocMid B (baseChangeMod φ M)
        (baseChangeMod φ N) (baseChangeMod φ P) =
    (α_ (baseChangeMod φ M).X (baseChangeMod φ N).X
        (baseChangeMod φ P).X).hom ≫
      ((baseChangeMod φ M).X ◁
        modTensorπ B (baseChangeMod φ N)
          (baseChangeMod φ P)) ≫
      modTensorπ B (baseChangeMod φ M)
        (modTensorMod B (baseChangeMod φ N)
          (baseChangeMod φ P)) := by
    rw [whiskerRight_modTensorπ_assocMid, modTensorAssocCover]
  have hcore1 : (modTensorπ B (baseChangeMod φ M)
        (baseChangeMod φ N) ▷ (B ⊗ P.X)) ≫
      (modTensor B (baseChangeMod φ M) (baseChangeMod φ N) ◁
        modTensorπ A (restrictRegular φ) P) ≫
      modTensorπ B
        (modTensorMod B (baseChangeMod φ M)
          (baseChangeMod φ N)) (baseChangeMod φ P) ≫
      modTensorAssocHom B (baseChangeMod φ M)
        (baseChangeMod φ N) (baseChangeMod φ P) ≫
      modTensorMap B (𝟙 (baseChangeMod φ M))
        (projFormulaMod A B φ N P).hom ≫
      (projFormula A B φ M (modTensorMod A N P)).hom =
    (((baseChangeMod φ M).X ⊗ (baseChangeMod φ N).X) ◁
        modTensorπ A (restrictRegular φ) P) ≫
      (α_ (baseChangeMod φ M).X (baseChangeMod φ N).X
        (baseChangeMod φ P).X).hom ≫
      ((baseChangeMod φ M).X ◁
        modTensorπ B (baseChangeMod φ N)
          (baseChangeMod φ P)) ≫
      ((baseChangeMod φ M).X ◁
        (projFormula A B φ N P).hom) ≫
      modTensorπ B (baseChangeMod φ M)
        (baseChangeMod φ (modTensorMod A N P)) ≫
      (projFormula A B φ M (modTensorMod A N P)).hom := by
    refine Eq.trans (whisker_eq _ (whisker_eq _
      (Category.assoc _ _ _).symm)) ?_
    refine Eq.trans (whisker_eq _ (whisker_eq _ (eq_whisker
      (modTensorπ_assocHom B (baseChangeMod φ M)
        (baseChangeMod φ N) (baseChangeMod φ P)) _))) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker (whisker_exchange
      (modTensorπ B (baseChangeMod φ M) (baseChangeMod φ N))
      (modTensorπ A (restrictRegular φ) P)).symm _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
    refine Eq.trans (whisker_eq _ (eq_whisker hcov _)) ?_
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
    refine Eq.trans (whisker_eq _ (whisker_eq _
      (Category.assoc _ _ _))) ?_
    refine Eq.trans (whisker_eq _ (whisker_eq _ (whisker_eq _
      (Category.assoc _ _ _).symm))) ?_
    refine Eq.trans (whisker_eq _ (whisker_eq _ (whisker_eq _
      (eq_whisker h2 _)))) ?_
    exact whisker_eq _ (whisker_eq _ (whisker_eq _
      (Category.assoc _ _ _)))
  have hfoldNP : (modTensorπ A (restrictRegular φ) N ▷
        (B ⊗ P.X)) ≫
      ((baseChangeMod φ N).X ◁
        modTensorπ A (restrictRegular φ) P) ≫
      modTensorπ B (baseChangeMod φ N) (baseChangeMod φ P) ≫
      (projFormula A B φ N P).hom =
    ((tensorμ B N.X B P.X ≫ (μ[B] ▷ (N.X ⊗ P.X))) ≫
        (B ◁ modTensorπ A N P)) ≫
      modTensorπ A (restrictRegular φ)
        (modTensorMod A N P) := by
    simp only [Category.assoc]
    conv_rhs => erw [Category.assoc]; arg 2; erw [Category.assoc]
    exact projFormula_tensorμ_cover A B φ N P
  have hfoldX : ((baseChangeMod φ M).X ◁
        (modTensorπ A (restrictRegular φ) N ▷ (B ⊗ P.X))) ≫
      ((baseChangeMod φ M).X ◁ ((baseChangeMod φ N).X ◁
        modTensorπ A (restrictRegular φ) P)) ≫
      ((baseChangeMod φ M).X ◁
        modTensorπ B (baseChangeMod φ N)
          (baseChangeMod φ P)) ≫
      ((baseChangeMod φ M).X ◁
        (projFormula A B φ N P).hom) =
    ((baseChangeMod φ M).X ◁
        ((tensorμ B N.X B P.X ≫ (μ[B] ▷ (N.X ⊗ P.X))) ≫
          (B ◁ modTensorπ A N P))) ≫
      ((baseChangeMod φ M).X ◁
        modTensorπ A (restrictRegular φ)
          (modTensorMod A N P)) := by
    repeat' erw [← MonoidalCategory.whiskerLeft_comp]
    exact congrArg
      (fun t => (baseChangeMod φ M).X ◁ t) hfoldNP
  have hfoldM : (modTensorπ A (restrictRegular φ) M ▷
        (B ⊗ (modTensorMod A N P).X)) ≫
      ((baseChangeMod φ M).X ◁
        modTensorπ A (restrictRegular φ)
          (modTensorMod A N P)) ≫
      modTensorπ B (baseChangeMod φ M)
        (baseChangeMod φ (modTensorMod A N P)) ≫
      (projFormula A B φ M (modTensorMod A N P)).hom =
    (tensorμ B M.X B (modTensor A N P) ≫
        (μ[B] ▷ (M.X ⊗ modTensor A N P))) ≫
      (B ◁ modTensorπ A M (modTensorMod A N P)) ≫
      modTensorπ A (restrictRegular φ)
        (modTensorMod A M (modTensorMod A N P)) := by
    simp only [Category.assoc]
    exact projFormula_tensorμ_cover A B φ M
      (modTensorMod A N P)
  refine Eq.trans (whisker_eq _ (whisker_eq _ hcore1)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    ((Category.assoc _ _ _).symm.trans (eq_whisker
      (associator_naturality_right (baseChangeMod φ M).X
        (baseChangeMod φ N).X
        (modTensorπ A (restrictRegular φ) P)) _)))) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (Category.assoc _ _ _))) ?_
  refine Eq.trans (whisker_eq _
    ((Category.assoc _ _ _).symm.trans (eq_whisker
      (associator_naturality_middle (baseChangeMod φ M).X
        (modTensorπ A (restrictRegular φ) N)
        (B ⊗ P.X)) _))) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    ((reassoc_of% hfoldX) _))) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (Category.assoc _ _ _))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (associator_naturality_left
    (modTensorπ A (restrictRegular φ) M) (B ⊗ N.X)
    (B ⊗ P.X)) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine whisker_eq _ ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (whisker_exchange
    (modTensorπ A (restrictRegular φ) M)
    (tensorμ B N.X B P.X ≫ (μ[B] ▷ (N.X ⊗ P.X)) ≫
      (B ◁ modTensorπ A N P))).symm _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact whisker_eq _ hfoldM

/-- **The associator coherence of the projection formula**: base
change carries the module associator to the module associator
through the structure map. -/
theorem projFormula_assoc
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] (M : Mod D A) (N : Mod D A) (P : Mod D A) :
    modTensorMap B (projFormulaMod A B φ M N).hom
        (𝟙 (baseChangeMod φ P)) ≫
      (projFormula A B φ (modTensorMod A M N) P).hom ≫
      modTensorMap A (𝟙 (restrictRegular φ))
        (modTensorAssocModIso A M N P).hom =
    modTensorAssocHom B (baseChangeMod φ M) (baseChangeMod φ N)
        (baseChangeMod φ P) ≫
      modTensorMap B (𝟙 (baseChangeMod φ M))
        (projFormulaMod A B φ N P).hom ≫
      (projFormula A B φ M (modTensorMod A N P)).hom := by
  apply modTensor_hom_ext
  apply modTensor_whisker_hom_ext A (restrictRegular φ) P
    (modTensor B (baseChangeMod φ M) (baseChangeMod φ N))
  apply modTensor_whiskerR_hom_ext B (baseChangeMod φ M)
    (baseChangeMod φ N) (B ⊗ P.X)
  apply modTensor_whiskerLR_hom_ext A (restrictRegular φ) N
    (baseChangeMod φ M).X (B ⊗ P.X)
  apply modTensor_whiskerRR_hom_ext A (restrictRegular φ) M
    (B ⊗ N.X) (B ⊗ P.X)
  refine Eq.trans (projFormula_assoc_leftCover A B φ M N P)
    (Eq.trans ?_
      (projFormula_assoc_rightCover A B φ M N P).symm)
  have hc := eq_whisker (projFormula_assoc_core A B M N P)
    (modTensorπ A (restrictRegular φ)
      (modTensorMod A M (modTensorMod A N P)))
  conv at hc =>
    lhs
    erw [Category.assoc]
    arg 2
    erw [Category.assoc]
  conv at hc =>
    rhs
    erw [Category.assoc]
    arg 2
    erw [Category.assoc]
    arg 2
    erw [Category.assoc]
  conv at hc =>
    rhs
    arg 2
    arg 1
    arg 2
    erw [Category.assoc]
  exact hc

end Assoc

end RS
