/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModBiprod

/-!
# Base change distributes over biproducts

Base change along a morphism of commutative monoid objects sends
the biproduct of two modules to the biproduct of their base
changes, as bundled modules over the new base.  The forward map
projects componentwise; the inverse injects componentwise; both
are linear over the new base, and they are mutually inverse.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- Morphisms out of a tensored biproduct are determined by the
two whiskered injections. -/
private theorem whisker_biprod_ext
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasBinaryBiproducts D]
    {P X Y Z : D}
    {f g : P ⊗ (X ⊞ Y) ⟶ Z}
    (h1 : (P ◁ biprod.inl) ≫ f = (P ◁ biprod.inl) ≫ g)
    (h2 : (P ◁ biprod.inr) ≫ f = (P ◁ biprod.inr) ≫ g) :
    f = g := by
  have htot : 𝟙 (P ⊗ (X ⊞ Y)) =
      (P ◁ biprod.fst) ≫ (P ◁ biprod.inl) +
      (P ◁ biprod.snd) ≫ (P ◁ biprod.inr) := by
    rw [← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalPreadditive.whiskerLeft_add, biprod.total,
      MonoidalCategory.whiskerLeft_id]
  calc f = 𝟙 (P ⊗ (X ⊞ Y)) ≫ f := (Category.id_comp f).symm
    _ = ((P ◁ biprod.fst) ≫ (P ◁ biprod.inl) +
        (P ◁ biprod.snd) ≫ (P ◁ biprod.inr)) ≫ f := by
        rw [← htot]
    _ = (P ◁ biprod.fst) ≫ ((P ◁ biprod.inl) ≫ g) +
        (P ◁ biprod.snd) ≫ ((P ◁ biprod.inr) ≫ g) := by
        rw [Preadditive.add_comp]
        simp only [Category.assoc]
        rw [h1, h2]
    _ = ((P ◁ biprod.fst) ≫ (P ◁ biprod.inl) +
        (P ◁ biprod.snd) ≫ (P ◁ biprod.inr)) ≫ g := by
        rw [Preadditive.add_comp]
        simp only [Category.assoc]
    _ = 𝟙 (P ⊗ (X ⊞ Y)) ≫ g := by rw [← htot]
    _ = g := Category.id_comp g

/-- The first injection followed by the first projection is the
identity, at the level of module morphisms. -/
lemma modBiprodInl_fst [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasBinaryBiproducts D] (A : D) [MonObj A]
    (M : Mod D A) (N : Mod D A) :
    modBiprodInl A M N ≫ modBiprodFst A M N = 𝟙 M := by
  apply Mod.hom_ext
  change (biprod.inl : M.X ⟶ M.X ⊞ N.X) ≫ biprod.fst = 𝟙 M.X
  exact biprod.inl_fst

/-- The second injection followed by the second projection is the
identity, at the level of module morphisms. -/
lemma modBiprodInr_snd [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasBinaryBiproducts D] (A : D) [MonObj A]
    (M : Mod D A) (N : Mod D A) :
    modBiprodInr A M N ≫ modBiprodSnd A M N = 𝟙 N := by
  apply Mod.hom_ext
  change (biprod.inr : N.X ⟶ M.X ⊞ N.X) ≫ biprod.snd = 𝟙 N.X
  exact biprod.inr_snd

/-- **The forward map**: the base change of a biproduct projects
componentwise onto the biproduct of the base changes. -/
noncomputable def baseChangeBiprodFwd
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasCoequalizers D] [HasBinaryBiproducts D] (A : D)
    [MonObj A] (B : D) [MonObj B] (φ : A ⟶ B) [IsMonHom φ] (M : Mod D A)
    (N : Mod D A) :
    baseChange φ (modBiprod A M N) ⟶
      baseChange φ M ⊞ baseChange φ N :=
  biprod.lift
    (modTensorMap A (𝟙 (restrictRegular φ)) (modBiprodFst A M N))
    (modTensorMap A (𝟙 (restrictRegular φ)) (modBiprodSnd A M N))

/-- **The backward map**: the biproduct of the base changes
injects componentwise into the base change of the biproduct. -/
noncomputable def baseChangeBiprodBwd
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasCoequalizers D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (B : D) [MonObj B]
    (φ : A ⟶ B) [IsMonHom φ] (M : Mod D A) (N : Mod D A) :
    baseChange φ M ⊞ baseChange φ N ⟶
      baseChange φ (modBiprod A M N) :=
  biprod.desc
    (modTensorMap A (𝟙 (restrictRegular φ)) (modBiprodInl A M N))
    (modTensorMap A (𝟙 (restrictRegular φ)) (modBiprodInr A M N))

/-- Injecting and then projecting the first component is the
identity on the base change. -/
private lemma map_inl_fst
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasCoequalizers D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (B : D) [MonObj B]
    (φ : A ⟶ B) [IsMonHom φ] (M : Mod D A) (N : Mod D A) :
    modTensorMap A (𝟙 (restrictRegular φ)) (modBiprodInl A M N) ≫
      modTensorMap A (𝟙 (restrictRegular φ))
        (modBiprodFst A M N) =
      𝟙 (baseChange φ M) := by
  rw [← modTensorMap_comp, Category.comp_id, modBiprodInl_fst,
    modTensorMap_id]
  rfl

/-- Injecting and then projecting the second component is the
identity on the base change. -/
private lemma map_inr_snd
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasCoequalizers D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (B : D) [MonObj B]
    (φ : A ⟶ B) [IsMonHom φ] (M : Mod D A) (N : Mod D A) :
    modTensorMap A (𝟙 (restrictRegular φ)) (modBiprodInr A M N) ≫
      modTensorMap A (𝟙 (restrictRegular φ))
        (modBiprodSnd A M N) =
      𝟙 (baseChange φ N) := by
  rw [← modTensorMap_comp, Category.comp_id, modBiprodInr_snd,
    modTensorMap_id]
  rfl

/-- Injecting the first and projecting the second component
vanishes. -/
private lemma map_inl_snd
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasCoequalizers D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (B : D) [MonObj B]
    (φ : A ⟶ B) [IsMonHom φ] (M : Mod D A) (N : Mod D A) :
    modTensorMap A (𝟙 (restrictRegular φ)) (modBiprodInl A M N) ≫
      modTensorMap A (𝟙 (restrictRegular φ))
        (modBiprodSnd A M N) = 0 := by
  apply modTensor_hom_ext
  rw [modTensorπ_map_assoc, modTensorπ_map]
  simp only [Mod.id_hom', modBiprodInl_hom, modBiprodSnd_hom]
  repeat' erw [MonoidalCategory.id_tensorHom]
  erw [← MonoidalCategory.whiskerLeft_comp_assoc]
  change B ◁ ((biprod.inl : M.X ⟶ M.X ⊞ N.X) ≫ biprod.snd) ≫
      modTensorπ A (restrictRegular φ) N =
    modTensorπ A (restrictRegular φ) M ≫ 0
  rw [biprod.inl_snd, MonoidalPreadditive.whiskerLeft_zero,
    Limits.zero_comp, Limits.comp_zero]

/-- Injecting the second and projecting the first component
vanishes. -/
private lemma map_inr_fst
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasCoequalizers D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (B : D) [MonObj B]
    (φ : A ⟶ B) [IsMonHom φ] (M : Mod D A) (N : Mod D A) :
    modTensorMap A (𝟙 (restrictRegular φ)) (modBiprodInr A M N) ≫
      modTensorMap A (𝟙 (restrictRegular φ))
        (modBiprodFst A M N) = 0 := by
  apply modTensor_hom_ext
  rw [modTensorπ_map_assoc, modTensorπ_map]
  simp only [Mod.id_hom', modBiprodInr_hom, modBiprodFst_hom]
  repeat' erw [MonoidalCategory.id_tensorHom]
  erw [← MonoidalCategory.whiskerLeft_comp_assoc]
  change B ◁ ((biprod.inr : N.X ⟶ M.X ⊞ N.X) ≫ biprod.fst) ≫
      modTensorπ A (restrictRegular φ) M =
    modTensorπ A (restrictRegular φ) N ≫ 0
  rw [biprod.inr_fst, MonoidalPreadditive.whiskerLeft_zero,
    Limits.zero_comp, Limits.comp_zero]

/-- The backward map followed by the forward map is the
identity. -/
theorem baseChangeBiprodBwd_fwd
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasCoequalizers D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (B : D) [MonObj B]
    (φ : A ⟶ B) [IsMonHom φ] (M : Mod D A) (N : Mod D A) :
    baseChangeBiprodBwd A B φ M N ≫ baseChangeBiprodFwd A B φ M N =
      𝟙 (baseChange φ M ⊞ baseChange φ N) := by
  unfold baseChangeBiprodBwd baseChangeBiprodFwd
  apply biprod.hom_ext'
  · erw [Category.comp_id, biprod.inl_desc_assoc]
    apply biprod.hom_ext
    · erw [Category.assoc, biprod.lift_fst, biprod.inl_fst]
      exact map_inl_fst A B φ M N
    · erw [Category.assoc, biprod.lift_snd, biprod.inl_snd]
      exact map_inl_snd A B φ M N
  · erw [Category.comp_id, biprod.inr_desc_assoc]
    apply biprod.hom_ext
    · erw [Category.assoc, biprod.lift_fst, biprod.inr_fst]
      exact map_inr_fst A B φ M N
    · erw [Category.assoc, biprod.lift_snd, biprod.inr_snd]
      exact map_inr_snd A B φ M N

/-- The forward map followed by the backward map is the
identity. -/
theorem baseChangeBiprodFwd_bwd
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasCoequalizers D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (B : D) [MonObj B]
    (φ : A ⟶ B) [IsMonHom φ] (M : Mod D A) (N : Mod D A) :
    baseChangeBiprodFwd A B φ M N ≫ baseChangeBiprodBwd A B φ M N =
      𝟙 (baseChange φ (modBiprod A M N)) := by
  unfold baseChangeBiprodFwd baseChangeBiprodBwd
  erw [biprod.lift_desc]
  apply modTensor_hom_ext
  change modTensorπ A (restrictRegular φ) (modBiprod A M N) ≫
      (modTensorMap A (𝟙 (restrictRegular φ))
          (modBiprodFst A M N) ≫
        modTensorMap A (𝟙 (restrictRegular φ))
          (modBiprodInl A M N) +
      modTensorMap A (𝟙 (restrictRegular φ))
          (modBiprodSnd A M N) ≫
        modTensorMap A (𝟙 (restrictRegular φ))
          (modBiprodInr A M N)) =
    modTensorπ A (restrictRegular φ) (modBiprod A M N) ≫
      𝟙 (modTensor A (restrictRegular φ) (modBiprod A M N))
  rw [Preadditive.comp_add, Category.comp_id]
  rw [modTensorπ_map_assoc, modTensorπ_map_assoc,
    modTensorπ_map, modTensorπ_map]
  simp only [Mod.id_hom', modBiprodFst_hom, modBiprodInl_hom,
    modBiprodSnd_hom, modBiprodInr_hom]
  repeat' erw [MonoidalCategory.id_tensorHom]
  erw [← MonoidalCategory.whiskerLeft_comp_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← Preadditive.add_comp,
    ← MonoidalPreadditive.whiskerLeft_add]
  have hs : B ◁ ((biprod.fst : M.X ⊞ N.X ⟶ M.X) ≫ biprod.inl +
      (biprod.snd : M.X ⊞ N.X ⟶ N.X) ≫ biprod.inr) =
      𝟙 (B ⊗ (M.X ⊞ N.X)) := by
    rw [biprod.total, MonoidalCategory.whiskerLeft_id]
  exact (eq_whisker hs
    (modTensorπ A (restrictRegular φ) (modBiprod A M N))).trans
    (Category.id_comp _)

/-- Base change of a module morphism is linear over the new
base. -/
lemma baseChangeAct_modTensorMap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (B : D) [MonObj B]
    [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    {P Q : Mod D A} (f : P ⟶ Q) :
    baseChangeAct φ P ≫ modTensorMap A (𝟙 (restrictRegular φ)) f =
      B ◁ modTensorMap A (𝟙 (restrictRegular φ)) f ≫
        baseChangeAct φ Q := by
  apply modTensor_whisker_hom_ext A (restrictRegular φ) P B
  have h2 : modTensorπ A (restrictRegular φ) P ≫
      modTensorMap A (𝟙 (restrictRegular φ)) f =
        B ◁ f.hom ≫ modTensorπ A (restrictRegular φ) Q := by
    rw [modTensorπ_map, Mod.id_hom',
      MonoidalCategory.id_tensorHom]
  have hcore : ((α_ B B P.X).inv ≫ μ[B] ▷ P.X) ≫
      B ◁ f.hom ≫ modTensorπ A (restrictRegular φ) Q =
      B ◁ (B ◁ f.hom) ≫
        ((α_ B B Q.X).inv ≫ μ[B] ▷ Q.X) ≫
          modTensorπ A (restrictRegular φ) Q := by
    simp only [Category.assoc]
    rw [associator_inv_naturality_right_assoc,
      whisker_exchange_assoc]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (whiskerLeft_modTensorπ_baseChangeAct φ P) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ h2) ?_
  refine Eq.trans hcore ?_
  refine Eq.symm ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
  refine Eq.trans (eq_whisker (congrArg (fun t => B ◁ t) h2) _) ?_
  refine Eq.trans (eq_whisker
    (MonoidalCategory.whiskerLeft_comp B _ _) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact whisker_eq _ (whiskerLeft_modTensorπ_baseChangeAct φ Q)

/-- The forward map intertwines the actions. -/
theorem baseChangeAct_baseChangeBiprodFwd
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasCoequalizers D] [HasBinaryBiproducts D] (A : D)
    [MonObj A] (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (M : Mod D A) (N : Mod D A) :
    baseChangeAct φ (modBiprod A M N) ≫
        baseChangeBiprodFwd A B φ M N =
      B ◁ baseChangeBiprodFwd A B φ M N ≫
        modBiprodAct B (baseChangeMod φ M) (baseChangeMod φ N) := by
  apply biprod.hom_ext
  · refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (biprod.lift_fst _ _)) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (modBiprodAct_fst B (baseChangeMod φ M)
        (baseChangeMod φ N))) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    refine Eq.trans (eq_whisker (congrArg (fun t => B ◁ t)
      (biprod.lift_fst _ _)) _) ?_
    exact
      (baseChangeAct_modTensorMap A B φ (modBiprodFst A M N)).symm
  · refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (biprod.lift_snd _ _)) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (modBiprodAct_snd B (baseChangeMod φ M)
        (baseChangeMod φ N))) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    refine Eq.trans (eq_whisker (congrArg (fun t => B ◁ t)
      (biprod.lift_snd _ _)) _) ?_
    exact
      (baseChangeAct_modTensorMap A B φ (modBiprodSnd A M N)).symm

/-- The backward map intertwines the actions. -/
theorem modBiprodAct_baseChangeBiprodBwd
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasCoequalizers D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (B : D) [MonObj B]
    [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (M : Mod D A) (N : Mod D A) :
    modBiprodAct B (baseChangeMod φ M) (baseChangeMod φ N) ≫
        baseChangeBiprodBwd A B φ M N =
      B ◁ baseChangeBiprodBwd A B φ M N ≫
        baseChangeAct φ (modBiprod A M N) := by
  apply whisker_biprod_ext
  · refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (actLeft_modBiprodInl B (baseChangeMod φ M)
        (baseChangeMod φ N)).symm _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (biprod.inl_desc _ _)) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    refine Eq.trans (eq_whisker (congrArg (fun t => B ◁ t)
      (biprod.inl_desc _ _)) _) ?_
    exact
      (baseChangeAct_modTensorMap A B φ (modBiprodInl A M N)).symm
  · refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (actLeft_modBiprodInr B (baseChangeMod φ M)
        (baseChangeMod φ N)).symm _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (biprod.inr_desc _ _)) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    refine Eq.trans (eq_whisker (congrArg (fun t => B ◁ t)
      (biprod.inr_desc _ _)) _) ?_
    exact
      (baseChangeAct_modTensorMap A B φ (modBiprodInr A M N)).symm

/-- **Base change distributes over the biproduct**: the base
change of a biproduct of modules is the biproduct of the base
changes, as bundled modules over the new base. -/
noncomputable def baseChangeBiprodIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasCoequalizers D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (B : D) [MonObj B]
    [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (M : Mod D A) (N : Mod D A) :
    baseChangeMod φ (modBiprod A M N) ≅
      modBiprod B (baseChangeMod φ M) (baseChangeMod φ N) where
  hom := Mod.Hom.mk' (baseChangeBiprodFwd A B φ M N)
    (by exact baseChangeAct_baseChangeBiprodFwd A B φ M N)
  inv := Mod.Hom.mk' (baseChangeBiprodBwd A B φ M N)
    (by exact modBiprodAct_baseChangeBiprodBwd A B φ M N)
  hom_inv_id := by
    apply Mod.hom_ext
    exact baseChangeBiprodFwd_bwd A B φ M N
  inv_hom_id := by
    apply Mod.hom_ext
    exact baseChangeBiprodBwd_fwd A B φ M N

end RS
