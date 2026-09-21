/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.BaseChangeTransport
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SplitExtractDual

/-!
# The base-changed pairing on its cover

The pairing of a base-changed duality datum, evaluated on the
double cover of the relative tensor over the new base: it
multiplies the two base factors and applies the pairing through
the base morphism.  This is the working form for the adjointness
of the split idempotents.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **The base-changed pairing on the cover**: it multiplies the
two base factors and applies the pairing through the base
morphism. -/
theorem baseChangePair_cover
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M') :
    (modTensorπ A (restrictRegular φ) M' ▷ (B ⊗ M.X)) ≫
        ((baseChangeMod φ M').X ◁
          modTensorπ A (restrictRegular φ) M) ≫
        modTensorπ B (baseChangeMod φ M') (baseChangeMod φ M) ≫
        (baseChangeDatum A B φ d).pair =
      tensorμ B M'.X B M.X ≫ (μ[B] ▷ (M'.X ⊗ M.X)) ≫
        (B ◁ (modTensorπ A M' M ≫ d.pair ≫ φ)) ≫ μ[B] := by
  have hpair : (baseChangeDatum A B φ d).pair =
      (projFormula A B φ M' M).hom ≫
        modTensorMap A (𝟙 (restrictRegular φ))
          (d.pairMod) ≫
        (modTensorUnitRight A (restrictRegular φ)).hom := rfl
  have htail : modTensorπ A (restrictRegular φ)
        (modTensorMod A M' M) ≫
      modTensorMap A (𝟙 (restrictRegular φ)) (d.pairMod) ≫
      (modTensorUnitRight A (restrictRegular φ)).hom =
    (B ◁ (d.pair ≫ φ)) ≫ μ[B] := by
    rw [modTensorπ_map_assoc, Mod.id_hom',
      MonoidalCategory.id_tensorHom,
      show (d.pairMod).hom = d.pair from rfl,
      modTensorUnitRight_hom, modTensorπ_desc,
      actRight_restrictRegular,
      MonoidalCategory.whiskerLeft_comp]
    simp only [Category.assoc]
    rfl
  rw [hpair]
  refine Eq.trans ((reassoc_of%
    (projFormula_tensorμ_cover A B φ M' M)) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (Category.assoc _ _ _))) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (whisker_eq _ htail))) ?_
  refine whisker_eq _ (whisker_eq _ ?_)
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]

/-- The interchange followed by braiding the base factor to the
right is a reassociation of the braiding. -/
theorem tensorμ_braid
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (X Y Z W : D) :
    tensorμ X Y Z W ≫ (α_ X Z (Y ⊗ W)).hom ≫
        (X ◁ (β_ Z (Y ⊗ W)).hom) =
      ((X ⊗ Y) ◁ (β_ Z W).hom) ≫ (α_ (X ⊗ Y) W Z).inv ≫
        ((α_ X Y W).hom ▷ Z) ≫ (α_ X (Y ⊗ W) Z).hom := by
  have hin : (α_ Y Z W).inv ≫ ((β_ Y Z).hom ▷ W) ≫
      (α_ Z Y W).hom ≫ (β_ Z (Y ⊗ W)).hom =
    (Y ◁ (β_ Z W).hom) ≫ (α_ Y W Z).inv := by
    rw [BraidedCategory.braiding_tensor_right_hom Z Y W]
    simp only [Iso.hom_inv_id_assoc]
    rw [← MonoidalCategory.comp_whiskerRight_assoc,
      SymmetricCategory.symmetry,
      MonoidalCategory.id_whiskerRight, Category.id_comp,
      Iso.inv_hom_id_assoc]
  rw [tensorμ]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simp only [← MonoidalCategory.whiskerLeft_comp]
  rw [hin]
  simp only [MonoidalCategory.whiskerLeft_comp]
  monoidal

/-- Multiplying two scalars is symmetric. -/
theorem mulSwap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (B : D)
    [MonObj B] [IsCommMonObj B]
    {U V : D} (f : U ⟶ B) (g : V ⟶ B) :
    (f ⊗ₘ g) ≫ μ[B] =
      (β_ U V).hom ≫ (g ⊗ₘ f) ≫ μ[B] := by
  rw [← Category.assoc,
    ← BraidedCategory.braiding_naturality, Category.assoc,
    IsCommMonObj.mul_comm]

/-- Reassociating a product with a base factor on the left. -/
theorem mulLeftAssoc [Category.{v} D] [MonoidalCategory D] (B : D) [MonObj B]
    {U V : D} (f : U ⟶ B) (g : V ⟶ B) :
    ((((B ◁ f) ≫ μ[B]) ⊗ₘ g) ≫ μ[B]) =
      (α_ B U V).hom ≫ (B ◁ ((f ⊗ₘ g) ≫ μ[B])) ≫ μ[B] := by
  rw [show (((B ◁ f) ≫ μ[B]) ⊗ₘ g) =
      ((B ◁ f) ⊗ₘ g) ≫ (μ[B] ⊗ₘ 𝟙 B) from by
    rw [tensorHom_comp_tensorHom, Category.comp_id]]
  rw [Category.assoc, MonoidalCategory.tensorHom_id μ[B] B,
    MonObj.mul_assoc, ← Category.assoc,
    ← MonoidalCategory.id_tensorHom B f,
    associator_naturality, Category.assoc]
  refine whisker_eq _ ?_
  rw [MonoidalCategory.id_tensorHom,
    ← MonoidalCategory.whiskerLeft_comp_assoc]

/-- The interchange, followed by reassociation, is the
braiding of the outer block. -/
theorem tensorμ_shuffle
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (W X Y : D) :
    ((W ⊗ Y) ◁ (β_ X Y).hom) ≫ tensorμ W Y Y X ≫
        (α_ W Y (Y ⊗ X)).hom =
      (α_ W Y (X ⊗ Y)).hom ≫
        (W ◁ ((α_ Y X Y).inv ≫ (β_ (Y ⊗ X) Y).hom)) := by
  have hin : (α_ Y X Y).inv ≫ (β_ (Y ⊗ X) Y).hom =
      (Y ◁ (β_ X Y).hom) ≫ (α_ Y Y X).inv ≫
        ((β_ Y Y).hom ▷ X) ≫ (α_ Y Y X).hom := by
    rw [BraidedCategory.braiding_tensor_left_hom Y X Y,
      Iso.inv_hom_id_assoc]
  rw [hin, tensorμ]
  simp only [Category.assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]
  rw [associator_naturality_right_assoc]
  simp only [← MonoidalCategory.whiskerLeft_comp]

/-- Sliding a base factor across a product of two scalars. -/
theorem mulSlide
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (B : D)
    [MonObj B] [IsCommMonObj B]
    {U V : D} (f : U ⟶ B) (g : V ⟶ B) :
    ((((f ▷ B) ≫ μ[B]) ⊗ₘ g) ≫ μ[B]) =
      (α_ U B V).hom ≫ (U ◁ (β_ B V).hom) ≫
        (f ⊗ₘ ((g ▷ B) ≫ μ[B])) ≫ μ[B] := by
  have hbg : (B ◁ g) ≫ μ[B] =
      (β_ B V).hom ≫ (g ⊗ₘ 𝟙 B) ≫ μ[B] := by
    rw [MonoidalCategory.tensorHom_id,
      ← BraidedCategory.braiding_naturality_right_assoc,
      IsCommMonObj.mul_comm]
  rw [← MonoidalCategory.tensorHom_id f B,
    ← MonoidalCategory.tensorHom_id g B]
  rw [show (((f ⊗ₘ 𝟙 B) ≫ μ[B]) ⊗ₘ g) =
      ((f ⊗ₘ 𝟙 B) ⊗ₘ g) ≫ (μ[B] ⊗ₘ 𝟙 B) from by
    rw [tensorHom_comp_tensorHom, Category.comp_id]]
  rw [Category.assoc, MonoidalCategory.tensorHom_id μ[B] B,
    MonObj.mul_assoc, ← Category.assoc,
    associator_naturality, Category.assoc]
  refine whisker_eq _ ?_
  rw [← Category.assoc,
    ← MonoidalCategory.id_tensorHom B μ[B],
    tensorHom_comp_tensorHom,
    Category.comp_id, MonoidalCategory.id_tensorHom, hbg]
  rw [show (f ⊗ₘ ((β_ B V).hom ≫ (g ⊗ₘ 𝟙 B) ≫ μ[B])) =
      (𝟙 U ⊗ₘ (β_ B V).hom) ≫
        (f ⊗ₘ ((g ⊗ₘ 𝟙 B) ≫ μ[B])) from by
    rw [tensorHom_comp_tensorHom, Category.id_comp]]
  rw [MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_id]
  simp only [Category.assoc]

section Adjoint

/-- A base-linear insertion intertwines the braided right action
with multiplication through the base morphism. -/
theorem actRight_ins
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B) {M : Mod D A}
    (v : M.X ⟶ B)
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B]) :
    actRight A M.X ≫ v = (v ▷ A) ≫ (B ◁ φ) ≫ μ[B] := by
  show ((β_ M.X A).hom ≫ actLeft A M.X) ≫ v = _
  rw [Category.assoc, hv,
    ← BraidedCategory.braiding_naturality_left_assoc,
    ← BraidedCategory.braiding_naturality_right_assoc,
    IsCommMonObj.mul_comm]

/-- **The dual coevaluation core against the base-changed
pairing**: the pairing sees the inserted primal factor through
the zig contraction. -/
theorem splitCoevalCoreDual_cover
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] {M : Mod D A} {M' : Mod D A} (v : M.X ⟶ B)
    (d : ModDualityDatum A M M')
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B]) :
    (splitCoevalCoreDual A B φ v hv ▷ (B ⊗ M.X)) ≫
        ((baseChangeMod φ M').X ◁
          modTensorπ A (restrictRegular φ) M) ≫
        modTensorπ B (baseChangeMod φ M') (baseChangeMod φ M) ≫
        (baseChangeDatum A B φ d).pair =
      (modTensor A M M' ◁ (β_ B M.X).hom) ≫
        (α_ (modTensor A M M') M.X B).inv ≫
        ((zigContract A d.pair d.pair_linear ≫ v) ▷ B) ≫
        μ[B] := by
  apply modTensor_whiskerR_hom_ext A M M' (B ⊗ M.X)
  have hL : (modTensorπ A M M' ▷ (B ⊗ M.X)) ≫
      (splitCoevalCoreDual A B φ v hv ▷ (B ⊗ M.X)) ≫
      ((baseChangeMod φ M').X ◁
        modTensorπ A (restrictRegular φ) M) ≫
      modTensorπ B (baseChangeMod φ M') (baseChangeMod φ M) ≫
      (baseChangeDatum A B φ d).pair =
    ((v ▷ M'.X) ▷ (B ⊗ M.X)) ≫ tensorμ B M'.X B M.X ≫
      (μ[B] ▷ (M'.X ⊗ M.X)) ≫
      (B ◁ (modTensorπ A M' M ≫ d.pair ≫ φ)) ≫ μ[B] := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.comp_whiskerRight _ _ _).symm _) ?_
    refine Eq.trans (eq_whisker (congrArg
      (fun t => t ▷ (B ⊗ M.X))
      (modTensorπ_splitCoevalCoreDual A B φ v hv)) _) ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.comp_whiskerRight _ _ _) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact whisker_eq _ (baseChangePair_cover A B φ d)
  have hR : (modTensorπ A M M' ▷ (B ⊗ M.X)) ≫
      (modTensor A M M' ◁ (β_ B M.X).hom) ≫
      (α_ (modTensor A M M') M.X B).inv ≫
      ((zigContract A d.pair d.pair_linear ≫ v) ▷ B) ≫
      μ[B] =
    ((M.X ⊗ M'.X) ◁ (β_ B M.X).hom) ≫
      (α_ (M.X ⊗ M'.X) M.X B).inv ≫
      (((α_ M.X M'.X M.X).hom ≫ (v ▷ (M'.X ⊗ M.X)) ≫
        (B ◁ (modTensorπ A M' M ≫ d.pair ≫ φ)) ≫ μ[B]) ▷
        B) ≫ μ[B] := by
    rw [← whisker_exchange_assoc,
      associator_inv_naturality_left_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc,
      ← Category.assoc (modTensorπ A M M' ▷ M.X),
      whiskerRight_modTensorπ_zigContract]
    refine congrArg (fun t => ((M.X ⊗ M'.X) ◁
      (β_ B M.X).hom) ≫ (α_ (M.X ⊗ M'.X) M.X B).inv ≫
      (t ▷ B) ≫ μ[B]) ?_
    rw [Category.assoc, Category.assoc,
      actRight_ins A B φ v hv, ← whisker_exchange_assoc]
    simp only [Category.assoc,
      MonoidalCategory.whiskerLeft_comp]
    refine whisker_eq _ ?_
    simp only [← MonoidalCategory.whiskerLeft_comp_assoc]
    rw [whisker_exchange_assoc]
  have hbk : (B ◁ (modTensorπ A M' M ≫ d.pair ≫ φ)) ≫ μ[B] =
      (β_ B (M'.X ⊗ M.X)).hom ≫
        ((modTensorπ A M' M ≫ d.pair ≫ φ) ▷ B) ≫ μ[B] := by
    rw [← BraidedCategory.braiding_naturality_right_assoc,
      IsCommMonObj.mul_comm]
  have hLform : ((v ▷ M'.X) ▷ (B ⊗ M.X)) ≫
      tensorμ B M'.X B M.X ≫ (μ[B] ▷ (M'.X ⊗ M.X)) ≫
      (B ◁ (modTensorπ A M' M ≫ d.pair ≫ φ)) ≫ μ[B] =
    tensorμ M.X M'.X B M.X ≫
      (α_ M.X B (M'.X ⊗ M.X)).hom ≫
      (M.X ◁ (β_ B (M'.X ⊗ M.X)).hom) ≫
      (v ⊗ₘ (((modTensorπ A M' M ≫ d.pair ≫ φ) ▷ B) ≫
        μ[B])) ≫ μ[B] := by
    rw [← MonoidalCategory.tensorHom_id v M'.X,
      tensorμ_natural_left_assoc]
    refine whisker_eq _ ?_
    rw [MonoidalCategory.id_whiskerRight,
      MonoidalCategory.tensorHom_id (v ▷ B) (M'.X ⊗ M.X),
      ← MonoidalCategory.comp_whiskerRight_assoc,
      ← MonoidalCategory.tensorHom_def_assoc,
      mulSlide B v (modTensorπ A M' M ≫ d.pair ≫ φ)]
  have hRform : ((M.X ⊗ M'.X) ◁ (β_ B M.X).hom) ≫
      (α_ (M.X ⊗ M'.X) M.X B).inv ≫
      (((α_ M.X M'.X M.X).hom ≫ (v ▷ (M'.X ⊗ M.X)) ≫
        (B ◁ (modTensorπ A M' M ≫ d.pair ≫ φ)) ≫ μ[B]) ▷
        B) ≫ μ[B] =
    (((M.X ⊗ M'.X) ◁ (β_ B M.X).hom) ≫
        (α_ (M.X ⊗ M'.X) M.X B).inv ≫
        ((α_ M.X M'.X M.X).hom ▷ B) ≫
        (α_ M.X (M'.X ⊗ M.X) B).hom) ≫
      (v ⊗ₘ (((modTensorπ A M' M ≫ d.pair ≫ φ) ▷ B) ≫
        μ[B])) ≫ μ[B] := by
    rw [← MonoidalCategory.tensorHom_def_assoc]
    rw [MonoidalCategory.comp_whiskerRight,
      MonoidalCategory.comp_whiskerRight]
    simp only [Category.assoc]
    rw [MonObj.mul_assoc]
    rw [← MonoidalCategory.tensorHom_id
        (v ⊗ₘ (modTensorπ A M' M ≫ d.pair ≫ φ)) B,
      ← MonoidalCategory.tensorHom_id
        (modTensorπ A M' M ≫ d.pair ≫ φ) B,
      ← Category.assoc
        ((v ⊗ₘ (modTensorπ A M' M ≫ d.pair ≫ φ)) ⊗ₘ 𝟙 B),
      associator_naturality]
    simp only [Category.assoc]
    rw [← MonoidalCategory.id_tensorHom B μ[B],
      ← Category.assoc
        (v ⊗ₘ (modTensorπ A M' M ≫ d.pair ≫ φ) ⊗ₘ 𝟙 B),
      tensorHom_comp_tensorHom, Category.comp_id]
  rw [hL, hR, hLform, hRform]
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact eq_whisker (tensorμ_braid M.X M'.X B M.X) _

/-- **The dual coevaluation point against the base-changed
pairing**: pairing the inserted point with a vector evaluates the
insertion on it. -/
theorem splitCoevalDual_point_pair
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] {M : Mod D A} {M' : Mod D A} (v : M.X ⟶ B)
    (d : ModDualityDatum A M M')
    (hz : ModZigzagDatum A d)
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B]) :
    (λ_ (baseChangeMod φ M).X).inv ≫
        ((η[A] ≫ d.copair ≫
          splitCoevalCoreDual A B φ v hv) ▷
          (baseChangeMod φ M).X) ≫
        modTensorπ B (baseChangeMod φ M') (baseChangeMod φ M) ≫
        (baseChangeDatum A B φ d).pair =
      splitEval A B φ v hv := by
  have hz1 : (η[A] ≫ d.copair ≫
        splitCoevalCoreDual A B φ v hv) ▷
        (baseChangeMod φ M).X =
      ((η[A] ≫ d.copair) ▷ (baseChangeMod φ M).X) ≫
        (splitCoevalCoreDual A B φ v hv ▷
          (baseChangeMod φ M).X) := by
    rw [← Category.assoc, MonoidalCategory.comp_whiskerRight]
  have hpre : (λ_ (B ⊗ M.X)).inv ≫
      (𝟙_ D ◁ (β_ B M.X).hom) ≫
      (α_ (𝟙_ D) M.X B).inv =
    (β_ B M.X).hom ≫ ((λ_ M.X).inv ▷ B) := by
    rw [← leftUnitor_inv_naturality_assoc,
      ← leftUnitor_inv_whiskerRight]
  have hstep : modTensorπ A (restrictRegular φ) M ≫
      (λ_ (baseChangeMod φ M).X).inv ≫
      ((η[A] ≫ d.copair ≫
        splitCoevalCoreDual A B φ v hv) ▷
        (baseChangeMod φ M).X) ≫
      modTensorπ B (baseChangeMod φ M') (baseChangeMod φ M) ≫
      (baseChangeDatum A B φ d).pair =
    (β_ B M.X).hom ≫ (v ▷ B) ≫ μ[B] := by
    have hclean : modTensorπ A (restrictRegular φ) M ≫
        (λ_ (modTensor A (restrictRegular φ) M)).inv ≫
        (((η[A] ≫ d.copair) ▷
          (modTensor A (restrictRegular φ) M)) ≫
          (splitCoevalCoreDual A B φ v hv ▷
            (modTensor A (restrictRegular φ) M))) ≫
        modTensorπ B (baseChangeMod φ M')
          (baseChangeMod φ M) ≫
        (baseChangeDatum A B φ d).pair =
      (λ_ (B ⊗ M.X)).inv ≫
        ((η[A] ≫ d.copair) ▷ (B ⊗ M.X)) ≫
        (splitCoevalCoreDual A B φ v hv ▷ (B ⊗ M.X)) ≫
        ((baseChangeMod φ M').X ◁
          modTensorπ A (restrictRegular φ) M) ≫
        modTensorπ B (baseChangeMod φ M')
          (baseChangeMod φ M) ≫
        (baseChangeDatum A B φ d).pair := by
      rw [leftUnitor_inv_naturality_assoc]
      simp only [Category.assoc]
      rw [whisker_exchange_assoc, whisker_exchange_assoc]
      rfl
    rw [hz1]
    refine Eq.trans hclean ?_
    rw [splitCoevalCoreDual_cover A B φ v d hv]
    rw [← whisker_exchange_assoc,
      associator_inv_naturality_left_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc]
    rw [reassoc_of% hpre]
    rw [← MonoidalCategory.comp_whiskerRight_assoc,
      zigzag_carrier_zig_assoc A hz]
  apply modTensor_hom_ext
  refine Eq.trans hstep ?_
  rw [modTensorπ_splitEval,
    ← BraidedCategory.braiding_naturality_right_assoc,
    IsCommMonObj.mul_comm]

/-- The base-changed pairing is linear over the new base in its
outer variable. -/
theorem baseChangePair_linear_outer
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M') :
    (baseChangeAct φ M' ▷ (baseChangeMod φ M).X) ≫
        modTensorπ B (baseChangeMod φ M') (baseChangeMod φ M) ≫
        (baseChangeDatum A B φ d).pair =
      (α_ B (baseChangeMod φ M').X
        (baseChangeMod φ M).X).hom ≫
        (B ◁ (modTensorπ B (baseChangeMod φ M')
          (baseChangeMod φ M) ≫
          (baseChangeDatum A B φ d).pair)) ≫ μ[B] := by
  letI := modTensorModObj B (baseChangeMod φ M')
    (baseChangeMod φ M)
  have hact : (B ◁ modTensorπ B (baseChangeMod φ M')
        (baseChangeMod φ M)) ≫
      actLeft B (modTensor B (baseChangeMod φ M')
        (baseChangeMod φ M)) =
    ((α_ B (baseChangeMod φ M').X
        (baseChangeMod φ M).X).inv ≫
      (actLeft B (baseChangeMod φ M').X ▷
        (baseChangeMod φ M).X)) ≫
      modTensorπ B (baseChangeMod φ M')
        (baseChangeMod φ M) :=
    whiskerLeft_modTensorπ_act B (baseChangeMod φ M')
      (baseChangeMod φ M)
  have hlin := (baseChangeDatum A B φ d).pair_linear
  rw [MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [← hlin, ← Category.assoc
      (B ◁ modTensorπ B (baseChangeMod φ M')
        (baseChangeMod φ M)),
    hact]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rfl

/-- **The dual coevaluation against the base-changed pairing**:
pairing the dual coevaluation with a vector evaluates the
insertion on it. -/
theorem splitCoevalDual_pair
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] {M : Mod D A} {M' : Mod D A} (v : M.X ⟶ B)
    (d : ModDualityDatum A M M')
    (hz : ModZigzagDatum A d)
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B]) :
    (splitCoevalDual A B φ v d hv ▷
        (baseChangeMod φ M).X) ≫
        modTensorπ B (baseChangeMod φ M') (baseChangeMod φ M) ≫
        (baseChangeDatum A B φ d).pair =
      (B ◁ splitEval A B φ v hv) ≫ μ[B] := by
  have hcoh : ((ρ_ B).inv ▷ (baseChangeMod φ M).X) ≫
      (α_ B (𝟙_ D) (baseChangeMod φ M).X).hom =
    B ◁ (λ_ (baseChangeMod φ M).X).inv := by monoidal
  have hsplit : splitCoevalDual A B φ v d hv =
      (ρ_ B).inv ≫
        (B ◁ (η[A] ≫ d.copair ≫
          splitCoevalCoreDual A B φ v hv)) ≫
        baseChangeAct φ M' := rfl
  rw [hsplit]
  rw [MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.comp_whiskerRight]
  simp only [Category.assoc]
  rw [baseChangePair_linear_outer A B φ d]
  have hmid : ((B ◁ (η[A] ≫ d.copair ≫
      splitCoevalCoreDual A B φ v hv)) ▷
      (modTensor A (restrictRegular φ) M)) ≫
      (α_ B (modTensor A (restrictRegular φ) M')
        (modTensor A (restrictRegular φ) M)).hom =
    (α_ B (𝟙_ D) (modTensor A (restrictRegular φ) M)).hom ≫
      (B ◁ ((η[A] ≫ d.copair ≫
        splitCoevalCoreDual A B φ v hv) ▷
        (modTensor A (restrictRegular φ) M))) :=
    associator_naturality_middle _ _ _
  refine Eq.trans (whisker_eq _ ((reassoc_of% hmid) _)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker hcoh _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (show
      (B ◁ (λ_ (baseChangeMod φ M).X).inv) ≫
        (B ◁ ((η[A] ≫ d.copair ≫
          splitCoevalCoreDual A B φ v hv) ▷
          (baseChangeMod φ M).X)) ≫
        (B ◁ (modTensorπ B (baseChangeMod φ M')
          (baseChangeMod φ M) ≫
          (baseChangeDatum A B φ d).pair)) =
      B ◁ ((λ_ (baseChangeMod φ M).X).inv ≫
        ((η[A] ≫ d.copair ≫
          splitCoevalCoreDual A B φ v hv) ▷
          (baseChangeMod φ M).X) ≫
        modTensorπ B (baseChangeMod φ M')
          (baseChangeMod φ M) ≫
        (baseChangeDatum A B φ d).pair) from by
    simp only [← MonoidalCategory.whiskerLeft_comp]) _) ?_
  rw [splitCoevalDual_point_pair A B φ v d hz hv]
  rfl

/-- The shuffle identity behind the primal cover. -/
theorem mulShuffle
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (B : D)
    [MonObj B] [IsCommMonObj B]
    (X Y : D) (w : Y ⟶ B) (p : Y ⊗ X ⟶ B) :
    ((B ⊗ Y) ◁ ((β_ X Y).hom ≫ (w ▷ X))) ≫
        tensorμ B Y B X ≫ (μ[B] ▷ (Y ⊗ X)) ≫
        (B ◁ p) ≫ μ[B] =
      (α_ B Y (X ⊗ Y)).hom ≫
        (B ◁ ((α_ Y X Y).inv ≫ (p ⊗ₘ w) ≫ μ[B])) ≫
        μ[B] := by
  rw [mulSwap B p w]
  rw [show (α_ Y X Y).inv ≫ (β_ (Y ⊗ X) Y).hom ≫
      (w ⊗ₘ p) ≫ μ[B] =
    ((α_ Y X Y).inv ≫ (β_ (Y ⊗ X) Y).hom) ≫
      ((w ⊗ₘ p) ≫ μ[B]) from by
    simp only [Category.assoc]]
  rw [MonoidalCategory.whiskerLeft_comp]
  rw [MonoidalCategory.whiskerLeft_comp,
    ← MonoidalCategory.tensorHom_id w X]
  simp only [Category.assoc]
  rw [tensorμ_natural_right_assoc]
  rw [MonoidalCategory.whiskerLeft_id,
    MonoidalCategory.tensorHom_id]
  rw [← MonoidalCategory.comp_whiskerRight_assoc,
    ← MonoidalCategory.tensorHom_def_assoc,
    mulLeftAssoc B w p]
  rw [reassoc_of% (tensorμ_shuffle B X Y)]

section Primal

/-- **The coevaluation core against the base-changed pairing**:
the pairing sees the inserted dual factor through the zag
contraction. -/
theorem splitCoevalCore_cover
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] {M : Mod D A} {M' : Mod D A} (w : M'.X ⟶ B)
    (d : ModDualityDatum A M M')
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    ((B ⊗ M'.X) ◁ splitCoevalCore A B φ w hw) ≫
        (modTensorπ A (restrictRegular φ) M' ▷
          (baseChangeMod φ M).X) ≫
        modTensorπ B (baseChangeMod φ M') (baseChangeMod φ M) ≫
        (baseChangeDatum A B φ d).pair =
      (α_ B M'.X (modTensor A M M')).hom ≫
        (B ◁ (zagContract A d.pair d.pair_linear ≫ w)) ≫
        μ[B] := by
  apply modTensor_whisker_hom_ext A M M' (B ⊗ M'.X)
  have hR : ((B ⊗ M'.X) ◁ modTensorπ A M M') ≫
      (α_ B M'.X (modTensor A M M')).hom ≫
      (B ◁ (zagContract A d.pair d.pair_linear ≫ w)) ≫
      μ[B] =
    (α_ B M'.X (M.X ⊗ M'.X)).hom ≫
      (B ◁ ((α_ M'.X M.X M'.X).inv ≫
        ((modTensorπ A M' M ≫ d.pair) ▷ M'.X) ≫
        (A ◁ w) ≫ (φ ▷ B) ≫ μ[B])) ≫ μ[B] := by
    rw [associator_naturality_right_assoc]
    refine whisker_eq _ ?_
    rw [← MonoidalCategory.whiskerLeft_comp_assoc]
    refine eq_whisker (congrArg (fun t => B ◁ t) ?_) _
    rw [← Category.assoc, whiskerLeft_modTensorπ_zagContract]
    simp only [Category.assoc, hw]
  have hL : ((B ⊗ M'.X) ◁ modTensorπ A M M') ≫
      ((B ⊗ M'.X) ◁ splitCoevalCore A B φ w hw) ≫
      (modTensorπ A (restrictRegular φ) M' ▷
        (baseChangeMod φ M).X) ≫
      modTensorπ B (baseChangeMod φ M') (baseChangeMod φ M) ≫
      (baseChangeDatum A B φ d).pair =
    ((B ⊗ M'.X) ◁ ((β_ M.X M'.X).hom ≫ (w ▷ M.X))) ≫
      tensorμ B M'.X B M.X ≫ (μ[B] ▷ (M'.X ⊗ M.X)) ≫
      (B ◁ (modTensorπ A M' M ≫ d.pair ≫ φ)) ≫ μ[B] := by
    rw [← MonoidalCategory.whiskerLeft_comp_assoc,
      modTensorπ_splitCoevalCore]
    refine Eq.trans (eq_whisker (show (B ⊗ M'.X) ◁
        ((β_ M.X M'.X).hom ≫ (w ▷ M.X) ≫
          modTensorπ A (restrictRegular φ) M) =
      ((B ⊗ M'.X) ◁ ((β_ M.X M'.X).hom ≫ (w ▷ M.X))) ≫
        ((B ⊗ M'.X) ◁
          modTensorπ A (restrictRegular φ) M) from by
      rw [← MonoidalCategory.whiskerLeft_comp,
        Category.assoc]) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine whisker_eq _ ?_
    have hex : ((B ⊗ M'.X) ◁
          modTensorπ A (restrictRegular φ) M) ≫
        (modTensorπ A (restrictRegular φ) M' ▷
          (modTensor A (restrictRegular φ) M)) =
      (modTensorπ A (restrictRegular φ) M' ▷ (B ⊗ M.X)) ≫
        ((modTensor A (restrictRegular φ) M') ◁
          modTensorπ A (restrictRegular φ) M) :=
      whisker_exchange _ _
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker hex _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact baseChangePair_cover A B φ d
  rw [hL, hR]
  rw [show ((modTensorπ A M' M ≫ d.pair) ▷ M'.X) ≫
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B] =
    ((modTensorπ A M' M ≫ d.pair ≫ φ) ⊗ₘ w) ≫ μ[B] from by
    rw [← MonoidalCategory.tensorHom_def_assoc,
      ← MonoidalCategory.tensorHom_id φ B,
      ← Category.assoc, tensorHom_comp_tensorHom,
      Category.comp_id, Category.assoc]]
  exact mulShuffle B M.X M'.X w
    (modTensorπ A M' M ≫ d.pair ≫ φ)

/-- **The coevaluation point against the base-changed
pairing**. -/
theorem splitCoeval_point_pair
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] {M : Mod D A} {M' : Mod D A} (w : M'.X ⟶ B)
    (d : ModDualityDatum A M M')
    (hz : ModZigzagDatum A d)
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    (ρ_ (baseChangeMod φ M').X).inv ≫
        ((baseChangeMod φ M').X ◁ (η[A] ≫ d.copair ≫
          splitCoevalCore A B φ w hw)) ≫
        modTensorπ B (baseChangeMod φ M') (baseChangeMod φ M) ≫
        (baseChangeDatum A B φ d).pair =
      splitEval A B φ w hw := by
  have hz1 : ((baseChangeMod φ M').X ◁ (η[A] ≫ d.copair ≫
        splitCoevalCore A B φ w hw)) =
      ((baseChangeMod φ M').X ◁ (η[A] ≫ d.copair)) ≫
        ((baseChangeMod φ M').X ◁
          splitCoevalCore A B φ w hw) := by
    rw [← MonoidalCategory.whiskerLeft_comp, Category.assoc]
  have hpre : (ρ_ (B ⊗ M'.X)).inv ≫
      (α_ B M'.X (𝟙_ D)).hom =
    B ◁ (ρ_ M'.X).inv := by
    rw [← whiskerLeft_rightUnitor_inv]
  have hclean : modTensorπ A (restrictRegular φ) M' ≫
      (ρ_ (modTensor A (restrictRegular φ) M')).inv ≫
      (((modTensor A (restrictRegular φ) M') ◁
        (η[A] ≫ d.copair)) ≫
        ((modTensor A (restrictRegular φ) M') ◁
          splitCoevalCore A B φ w hw)) ≫
      modTensorπ B (baseChangeMod φ M')
        (baseChangeMod φ M) ≫
      (baseChangeDatum A B φ d).pair =
    (ρ_ (B ⊗ M'.X)).inv ≫
      ((B ⊗ M'.X) ◁ (η[A] ≫ d.copair)) ≫
      ((B ⊗ M'.X) ◁ splitCoevalCore A B φ w hw) ≫
      (modTensorπ A (restrictRegular φ) M' ▷
        (baseChangeMod φ M).X) ≫
      modTensorπ B (baseChangeMod φ M')
        (baseChangeMod φ M) ≫
      (baseChangeDatum A B φ d).pair := by
    rw [rightUnitor_inv_naturality_assoc]
    simp only [Category.assoc]
    rw [← whisker_exchange_assoc, ← whisker_exchange_assoc]
    rfl
  have hstep : modTensorπ A (restrictRegular φ) M' ≫
      (ρ_ (baseChangeMod φ M').X).inv ≫
      ((baseChangeMod φ M').X ◁ (η[A] ≫ d.copair ≫
        splitCoevalCore A B φ w hw)) ≫
      modTensorπ B (baseChangeMod φ M')
        (baseChangeMod φ M) ≫
      (baseChangeDatum A B φ d).pair =
    (B ◁ w) ≫ μ[B] := by
    rw [hz1]
    refine Eq.trans hclean ?_
    rw [splitCoevalCore_cover A B φ w d hw]
    rw [associator_naturality_right_assoc]
    rw [← Category.assoc, hpre]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc]
    simp only [Category.assoc]
    rw [zigzag_carrier_zag_assoc A hz]
  apply modTensor_hom_ext
  refine Eq.trans hstep ?_
  rw [modTensorπ_splitEval]

/-- The base-changed pairing is linear over the new base in its
inner variable. -/
theorem baseChangePair_linear_inner
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M') :
    ((baseChangeMod φ M').X ◁ baseChangeAct φ M) ≫
        modTensorπ B (baseChangeMod φ M') (baseChangeMod φ M) ≫
        (baseChangeDatum A B φ d).pair =
      (α_ (baseChangeMod φ M').X B
        (baseChangeMod φ M).X).inv ≫
        ((β_ (baseChangeMod φ M').X B).hom ▷
          (baseChangeMod φ M).X) ≫
        (α_ B (baseChangeMod φ M').X
          (baseChangeMod φ M).X).hom ≫
        (B ◁ (modTensorπ B (baseChangeMod φ M')
          (baseChangeMod φ M) ≫
          (baseChangeDatum A B φ d).pair)) ≫ μ[B] := by
  have hcond : (actRight B (baseChangeMod φ M').X ▷
        (baseChangeMod φ M).X) ≫
      modTensorπ B (baseChangeMod φ M') (baseChangeMod φ M) =
    (α_ (baseChangeMod φ M').X B (baseChangeMod φ M).X).hom ≫
      ((baseChangeMod φ M').X ◁
        actLeft B (baseChangeMod φ M).X) ≫
      modTensorπ B (baseChangeMod φ M')
        (baseChangeMod φ M) := by
    have h := modTensor_condition B (baseChangeMod φ M')
      (baseChangeMod φ M)
    rw [modTensorLegM, modTensorLegN, Category.assoc] at h
    exact h
  have hfold : ((β_ (baseChangeMod φ M').X B).hom ▷
      (baseChangeMod φ M).X) ≫
      (baseChangeAct φ M' ▷ (baseChangeMod φ M).X) =
    (actRight B (baseChangeMod φ M').X ▷
      (baseChangeMod φ M).X) :=
    (MonoidalCategory.comp_whiskerRight _ _ _).symm
  rw [← baseChangePair_linear_outer A B φ d]
  refine Eq.symm ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker hfold _)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker hcond _)) ?_
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- **The coevaluation against the base-changed pairing**. -/
theorem splitCoeval_pair
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] {M : Mod D A} {M' : Mod D A} (w : M'.X ⟶ B)
    (d : ModDualityDatum A M M')
    (hz : ModZigzagDatum A d)
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    ((baseChangeMod φ M').X ◁
        splitCoeval A B φ w d hw) ≫
        modTensorπ B (baseChangeMod φ M') (baseChangeMod φ M) ≫
        (baseChangeDatum A B φ d).pair =
      (splitEval A B φ w hw ▷ B) ≫ μ[B] := by
  have hstruct : ∀ (Y X : D) (z : 𝟙_ D ⟶ X),
      (Y ◁ (ρ_ B).inv) ≫ (Y ◁ (B ◁ z)) ≫
        (α_ Y B X).inv ≫ ((β_ Y B).hom ▷ X) ≫
        (α_ B Y X).hom =
      (β_ Y B).hom ≫ (B ◁ ((ρ_ Y).inv ≫ (Y ◁ z))) := by
    intro Y X z
    rw [associator_inv_naturality_right_assoc,
      whisker_exchange_assoc,
      associator_naturality_right]
    rw [whiskerLeft_rightUnitor_inv]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← rightUnitor_inv_naturality_assoc,
      ← whiskerLeft_rightUnitor_inv_assoc,
      ← MonoidalCategory.whiskerLeft_comp]
  have hsplit : splitCoeval A B φ w d hw =
      (ρ_ B).inv ≫
        (B ◁ (η[A] ≫ d.copair ≫
          splitCoevalCore A B φ w hw)) ≫
        baseChangeAct φ M := rfl
  rw [hsplit]
  rw [MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [baseChangePair_linear_inner A B φ d]
  refine Eq.trans ((reassoc_of% (hstruct
    (baseChangeMod φ M').X (baseChangeMod φ M).X
    (η[A] ≫ d.copair ≫
      splitCoevalCore A B φ w hw))) _) ?_
  have hfold : ∀ {U V W : D} (p : U ⟶ V) (q : V ⟶ W)
      (k : B ⊗ W ⟶ B),
      (B ◁ p) ≫ (B ◁ q) ≫ k = (B ◁ (p ≫ q)) ≫ k := by
    intro U V W p q k
    rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp]
  refine Eq.trans (whisker_eq _ (hfold _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker (congrArg
    (fun t => B ◁ t) (Category.assoc _ _ _)) _)) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker (congrArg
    (fun t => B ◁ t)
    (splitCoeval_point_pair A B φ w d hz hw)) _)) ?_
  rw [← BraidedCategory.braiding_naturality_left_assoc,
    IsCommMonObj.mul_comm]
  rfl

end Primal

end Adjoint

end RS
