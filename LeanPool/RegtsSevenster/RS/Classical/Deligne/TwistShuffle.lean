/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.TensorDatum
import LeanPool.RegtsSevenster.RS.Classical.Deligne.TwistCoherence

/-!
# The twist shuffle

The relative tensor of two twisted modules is the twist of the
relative tensor by the tensor of the twisting objects: the middle
twisting object crosses the first module through the braiding.
The cover-level shuffle is the middle-four interchange, so the
committed interchange toolbox applies; the twisting is fully
general, and the sign phenomena of the odd line enter only at the
symmetriser conjugation downstream.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- The twist of a module by an object on the left, bundled. -/
noncomputable def tensorLeftMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A]
    (V : D) (M : Mod D A) :
    Mod D A :=
  letI := tensorLeftModObj A V M.X
  ⟨V ⊗ M.X⟩

@[simp] lemma tensorLeftMod_X
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A]
    (V : D) (M : Mod D A) :
    (tensorLeftMod A V M).X = V ⊗ M.X :=
  rfl

/-- The cover map of the twist shuffle: the middle-four
interchange followed by the projection under the twists. -/
noncomputable def twistShuffleCover
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (V : D) (W : D) (R : Mod D A)
    (S : Mod D A) :
    (V ⊗ R.X) ⊗ (W ⊗ S.X) ⟶ (V ⊗ W) ⊗ modTensor A R S :=
  tensorμ V R.X W S.X ≫ ((V ⊗ W) ◁ modTensorπ A R S)

/-- The cover map coequalizes the twisted balance relation. -/
theorem twistShuffleCover_cond
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (V : D) (W : D) (R : Mod D A)
    (S : Mod D A) :
    modTensorLegM A (tensorLeftMod A V R) (tensorLeftMod A W S) ≫
        twistShuffleCover A V W R S =
      modTensorLegN A (tensorLeftMod A V R)
          (tensorLeftMod A W S) ≫
        twistShuffleCover A V W R S := by
  rw [modTensorLegM, modTensorLegN, twistShuffleCover]
  rw [show actLeft A (tensorLeftMod A W S).X =
      actAcross A W S.X from rfl,
    show actRight A (tensorLeftMod A V R).X =
      (β_ (V ⊗ R.X) A).hom ≫ actAcross A V R.X from rfl]
  have hN : ((V ⊗ R.X) ◁ (W ◁ actLeft A S.X)) ≫
      tensorμ V R.X W S.X =
      tensorμ V R.X W (A ⊗ S.X) ≫
        ((V ⊗ W) ◁ (R.X ◁ actLeft A S.X)) := by
    simpa using tensorμ_natural (𝟙 V) (𝟙 R.X) (𝟙 W)
      (actLeft A S.X)
  have hM : ((V ◁ actLeft A R.X) ▷ (W ⊗ S.X)) ≫
      tensorμ V R.X W S.X =
      tensorμ V (A ⊗ R.X) W S.X ≫
        ((V ⊗ W) ◁ (actLeft A R.X ▷ S.X)) := by
    simpa using tensorμ_natural (𝟙 V) (actLeft A R.X) (𝟙 W)
      (𝟙 S.X)
  have hswap : (actLeft A R.X ▷ S.X) ≫ modTensorπ A R S =
      ((β_ R.X A).inv ▷ S.X) ≫ (α_ R.X A S.X).hom ≫
        (R.X ◁ actLeft A S.X) ≫ modTensorπ A R S := by
    have h := modTensor_condition A R S
    rw [modTensorLegM, modTensorLegN] at h
    rw [show actLeft A R.X ▷ S.X =
        ((β_ R.X A).inv ▷ S.X) ≫ (actRight A R.X ▷ S.X) from by
      rw [← comp_whiskerRight,
        show actRight A R.X =
          (β_ R.X A).hom ≫ actLeft A R.X from rfl,
        Iso.inv_hom_id_assoc],
      Category.assoc, h]
    simp only [Category.assoc]
  rw [actAcross, actAcross]
  show ((β_ (V ⊗ R.X) A).hom ≫ (α_ A V R.X).inv ≫
      ((β_ A V).hom ▷ R.X) ≫ (α_ V A R.X).hom ≫
      (V ◁ actLeft A R.X)) ▷ (W ⊗ S.X) ≫
      tensorμ V R.X W S.X ≫ ((V ⊗ W) ◁ modTensorπ A R S) =
    ((α_ (V ⊗ R.X) A (W ⊗ S.X)).hom ≫
      ((V ⊗ R.X) ◁ ((α_ A W S.X).inv ≫
        ((β_ A W).hom ▷ S.X) ≫ (α_ W A S.X).hom ≫
        (W ◁ actLeft A S.X)))) ≫
      tensorμ V R.X W S.X ≫ ((V ⊗ W) ◁ modTensorπ A R S)
  simp only [MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% hM, reassoc_of% hN]
  rw [← MonoidalCategory.whiskerLeft_comp
      (V ⊗ W) (actLeft A R.X ▷ S.X) (modTensorπ A R S),
    hswap]
  simp only [MonoidalCategory.whiskerLeft_comp]
  have hpure : (β_ (V ⊗ R.X) A).hom ▷ (W ⊗ S.X) ≫
      (α_ A V R.X).inv ▷ (W ⊗ S.X) ≫
      (β_ A V).hom ▷ R.X ▷ (W ⊗ S.X) ≫
      (α_ V A R.X).hom ▷ (W ⊗ S.X) ≫
      tensorμ V (A ⊗ R.X) W S.X ≫
      ((V ⊗ W) ◁ ((β_ R.X A).inv ▷ S.X)) ≫
      ((V ⊗ W) ◁ (α_ R.X A S.X).hom) =
      (α_ (V ⊗ R.X) A (W ⊗ S.X)).hom ≫
      ((V ⊗ R.X) ◁ (α_ A W S.X).inv) ≫
      ((V ⊗ R.X) ◁ ((β_ A W).hom ▷ S.X)) ≫
      ((V ⊗ R.X) ◁ (α_ W A S.X).hom) ≫
      tensorμ V R.X W (A ⊗ S.X) :=
    twist_shuffle_coherence V R.X A W S.X
  rw [reassoc_of% hpure]

/-- **The twist shuffle**: the relative tensor of two twisted
modules maps to the twist of the relative tensor. -/
noncomputable def twistShuffleHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (V : D) (W : D) (R : Mod D A)
    (S : Mod D A) :
    modTensor A (tensorLeftMod A V R) (tensorLeftMod A W S) ⟶
      (V ⊗ W) ⊗ modTensor A R S :=
  modTensorDesc A (tensorLeftMod A V R) (tensorLeftMod A W S)
    (twistShuffleCover A V W R S)
    (twistShuffleCover_cond A V W R S)

/-- Defining equation of the twist shuffle. -/
@[reassoc (attr := simp)]
theorem modTensorπ_twistShuffleHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (V : D) (W : D) (R : Mod D A)
    (S : Mod D A) :
    modTensorπ A (tensorLeftMod A V R) (tensorLeftMod A W S) ≫
        twistShuffleHom A V W R S =
      twistShuffleCover A V W R S :=
  modTensorπ_desc A _ _ _ _

/-- The cover map of the inverse twist shuffle: split into the
twisted pairs and project. -/
noncomputable def twistShuffleInvCover
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (V : D) (W : D) (R : Mod D A)
    (S : Mod D A) :
    (V ⊗ W) ⊗ (R.X ⊗ S.X) ⟶
      modTensor A (tensorLeftMod A V R) (tensorLeftMod A W S) :=
  tensorδ V R.X W S.X ≫
    modTensorπ A (tensorLeftMod A V R) (tensorLeftMod A W S)

/-- The interchange splitting is invertible. -/
instance isIso_tensorμ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (X₁ X₂ Y₁ Y₂ : D) :
    IsIso (tensorμ X₁ X₂ Y₁ Y₂) :=
  ⟨tensorδ X₁ X₂ Y₁ Y₂,
    tensorμ_tensorδ X₁ X₂ Y₁ Y₂, tensorδ_tensorμ X₁ X₂ Y₁ Y₂⟩

/-- The second-slot action slides through the splitting. -/
theorem tensorδ_slide_snd
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (V : D) (W : D) (R : Mod D A) (S : Mod D A) :
    ((V ⊗ W) ◁ (R.X ◁ actLeft A S.X)) ≫
        tensorδ V R.X W S.X =
      tensorδ V R.X W (A ⊗ S.X) ≫
        ((V ⊗ R.X) ◁ (W ◁ actLeft A S.X)) := by
  have hN : ((V ⊗ R.X) ◁ (W ◁ actLeft A S.X)) ≫
      tensorμ V R.X W S.X =
      tensorμ V R.X W (A ⊗ S.X) ≫
        ((V ⊗ W) ◁ (R.X ◁ actLeft A S.X)) := by
    simpa using tensorμ_natural (𝟙 V) (𝟙 R.X) (𝟙 W)
      (actLeft A S.X)
  rw [← cancel_mono (tensorμ V R.X W S.X), Category.assoc,
    Category.assoc, tensorδ_tensorμ, Category.comp_id, hN,
    ← Category.assoc, tensorδ_tensorμ, Category.id_comp]

/-- The first-slot action slides through the splitting. -/
theorem tensorδ_slide_fst
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (V : D) (W : D) (R : Mod D A) (S : Mod D A) :
    ((V ⊗ W) ◁ (actLeft A R.X ▷ S.X)) ≫
        tensorδ V R.X W S.X =
      tensorδ V (A ⊗ R.X) W S.X ≫
        ((V ◁ actLeft A R.X) ▷ (W ⊗ S.X)) := by
  have hM : ((V ◁ actLeft A R.X) ▷ (W ⊗ S.X)) ≫
      tensorμ V R.X W S.X =
      tensorμ V (A ⊗ R.X) W S.X ≫
        ((V ⊗ W) ◁ (actLeft A R.X ▷ S.X)) := by
    simpa using tensorμ_natural (𝟙 V) (actLeft A R.X) (𝟙 W)
      (𝟙 S.X)
  rw [← cancel_mono (tensorμ V R.X W S.X), Category.assoc,
    Category.assoc, tensorδ_tensorμ, Category.comp_id, hM,
    ← Category.assoc, tensorδ_tensorμ, Category.id_comp]

/-- The inverse cover coequalizes the whiskered balance
relation. -/
theorem twistShuffleInvCover_cond
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (V : D) (W : D) (R : Mod D A)
    (S : Mod D A) :
    ((V ⊗ W) ◁ modTensorLegM A R S) ≫
        twistShuffleInvCover A V W R S =
      ((V ⊗ W) ◁ modTensorLegN A R S) ≫
        twistShuffleInvCover A V W R S := by
  rw [modTensorLegM, modTensorLegN, twistShuffleInvCover,
    show actRight A R.X = (β_ R.X A).hom ≫ actLeft A R.X
      from rfl]
  simp only [MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  erw [reassoc_of% (tensorδ_slide_fst A V W R S),
    reassoc_of% (tensorδ_slide_snd A V W R S)]
  have hcond := modTensor_condition A (tensorLeftMod A V R)
    (tensorLeftMod A W S)
  rw [modTensorLegM, modTensorLegN,
    show actLeft A (tensorLeftMod A W S).X =
      actAcross A W S.X from rfl,
    show actRight A (tensorLeftMod A V R).X =
      (β_ (V ⊗ R.X) A).hom ≫ actAcross A V R.X from rfl,
    actAcross, actAcross] at hcond
  have hbig : (β_ (V ⊗ R.X) A).hom ▷ (W ⊗ S.X) ≫
      (α_ A V R.X).inv ▷ (W ⊗ S.X) ≫
      (β_ A V).hom ▷ R.X ▷ (W ⊗ S.X) ≫
      (α_ V A R.X).hom ▷ (W ⊗ S.X) ≫
      (V ◁ actLeft A R.X) ▷ (W ⊗ S.X) ≫
      modTensorπ A (tensorLeftMod A V R)
        (tensorLeftMod A W S) =
      (α_ (V ⊗ R.X) A (W ⊗ S.X)).hom ≫
      ((V ⊗ R.X) ◁ (α_ A W S.X).inv) ≫
      ((V ⊗ R.X) ◁ ((β_ A W).hom ▷ S.X)) ≫
      ((V ⊗ R.X) ◁ (α_ W A S.X).hom) ≫
      ((V ⊗ R.X) ◁ (W ◁ actLeft A S.X)) ≫
      modTensorπ A (tensorLeftMod A V R)
        (tensorLeftMod A W S) := by
    have h' : ((β_ (V ⊗ R.X) A).hom ≫ (α_ A V R.X).inv ≫
        ((β_ A V).hom ▷ R.X) ≫ (α_ V A R.X).hom ≫
        (V ◁ actLeft A R.X)) ▷ (W ⊗ S.X) ≫
        modTensorπ A (tensorLeftMod A V R)
          (tensorLeftMod A W S) =
        ((α_ (V ⊗ R.X) A (W ⊗ S.X)).hom ≫
          ((V ⊗ R.X) ◁ ((α_ A W S.X).inv ≫
            ((β_ A W).hom ▷ S.X) ≫ (α_ W A S.X).hom ≫
            (W ◁ actLeft A S.X)))) ≫
          modTensorπ A (tensorLeftMod A V R)
            (tensorLeftMod A W S) := hcond
    simp only [MonoidalCategory.comp_whiskerRight,
      MonoidalCategory.whiskerLeft_comp] at h'
    repeat' erw [Category.assoc] at h'
    exact h'
  have htail : (V ◁ actLeft A R.X) ▷ (W ⊗ S.X) ≫
      modTensorπ A (tensorLeftMod A V R)
        (tensorLeftMod A W S) =
      (α_ V A R.X).inv ▷ (W ⊗ S.X) ≫
      ((β_ A V).inv ▷ R.X) ▷ (W ⊗ S.X) ≫
      (α_ A V R.X).hom ▷ (W ⊗ S.X) ≫
      (β_ (V ⊗ R.X) A).inv ▷ (W ⊗ S.X) ≫
      (α_ (V ⊗ R.X) A (W ⊗ S.X)).hom ≫
      ((V ⊗ R.X) ◁ (α_ A W S.X).inv) ≫
      ((V ⊗ R.X) ◁ ((β_ A W).hom ▷ S.X)) ≫
      ((V ⊗ R.X) ◁ (α_ W A S.X).hom) ≫
      ((V ⊗ R.X) ◁ (W ◁ actLeft A S.X)) ≫
      modTensorπ A (tensorLeftMod A V R)
        (tensorLeftMod A W S) := by
    rw [← hbig]
    simp only [← MonoidalCategory.comp_whiskerRight_assoc,
      Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
      Iso.inv_hom_id, MonoidalCategory.id_whiskerRight,
      Category.id_comp]
  have hmirror : (V ⊗ W) ◁ ((β_ R.X A).hom ▷ S.X) ≫
      tensorδ V (A ⊗ R.X) W S.X ≫
      (α_ V A R.X).inv ▷ (W ⊗ S.X) ≫
      ((β_ A V).inv ▷ R.X) ▷ (W ⊗ S.X) ≫
      (α_ A V R.X).hom ▷ (W ⊗ S.X) ≫
      (β_ (V ⊗ R.X) A).inv ▷ (W ⊗ S.X) ≫
      (α_ (V ⊗ R.X) A (W ⊗ S.X)).hom ≫
      ((V ⊗ R.X) ◁ (α_ A W S.X).inv) ≫
      ((V ⊗ R.X) ◁ ((β_ A W).hom ▷ S.X)) ≫
      ((V ⊗ R.X) ◁ (α_ W A S.X).hom) =
      (V ⊗ W) ◁ (α_ R.X A S.X).hom ≫
      tensorδ V R.X W (A ⊗ S.X) := by
    rw [← cancel_mono (tensorμ V R.X W (A ⊗ S.X))]
    simp only [Category.assoc]
    rw [← twist_shuffle_coherence V R.X A W S.X]
    simp only [← MonoidalCategory.comp_whiskerRight_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
      MonoidalCategory.hom_inv_whiskerRight,
      Iso.inv_hom_id, MonoidalCategory.id_whiskerRight,
      MonoidalCategory.whiskerLeft_id,
      Category.id_comp, Category.comp_id,
      tensorδ_tensorμ, tensorδ_tensorμ_assoc]
  rw [htail, reassoc_of% hmirror]

/-- **The inverse twist shuffle.** -/
noncomputable def twistShuffleInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (V : D) (W : D) (R : Mod D A) (S : Mod D A) :
    (V ⊗ W) ⊗ modTensor A R S ⟶
      modTensor A (tensorLeftMod A V R) (tensorLeftMod A W S) :=
  modTensorWhiskerDesc A R S (V ⊗ W)
    (twistShuffleInvCover A V W R S)
    (twistShuffleInvCover_cond A V W R S)

/-- Defining equation of the inverse twist shuffle. -/
@[reassoc]
theorem whiskerLeft_π_twistShuffleInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (V : D) (W : D) (R : Mod D A) (S : Mod D A) :
    ((V ⊗ W) ◁ modTensorπ A R S) ≫ twistShuffleInv A V W R S =
      twistShuffleInvCover A V W R S :=
  whiskerLeft_modTensorπ_whiskerDesc A R S (V ⊗ W) _ _

/-- The twist shuffle retracts the inverse shuffle. -/
@[reassoc (attr := simp)]
theorem twistShuffleHom_twistShuffleInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (V : D) (W : D) (R : Mod D A) (S : Mod D A) :
    twistShuffleHom A V W R S ≫ twistShuffleInv A V W R S =
      𝟙 (modTensor A (tensorLeftMod A V R)
        (tensorLeftMod A W S)) := by
  apply modTensor_hom_ext A (tensorLeftMod A V R)
    (tensorLeftMod A W S)
  rw [modTensorπ_twistShuffleHom_assoc, Category.comp_id,
    twistShuffleCover]
  show (tensorμ V R.X W S.X ≫
      ((V ⊗ W) ◁ modTensorπ A R S)) ≫
      twistShuffleInv A V W R S =
    modTensorπ A (tensorLeftMod A V R) (tensorLeftMod A W S)
  erw [Category.assoc, whiskerLeft_π_twistShuffleInv,
    twistShuffleInvCover, ← Category.assoc, tensorμ_tensorδ,
    Category.id_comp]

/-- The inverse shuffle retracts the twist shuffle. -/
@[reassoc (attr := simp)]
theorem twistShuffleInv_twistShuffleHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (V : D) (W : D) (R : Mod D A) (S : Mod D A) :
    twistShuffleInv A V W R S ≫ twistShuffleHom A V W R S =
      𝟙 ((V ⊗ W) ⊗ modTensor A R S) := by
  apply modTensor_whisker_hom_ext A R S (V ⊗ W)
  rw [whiskerLeft_π_twistShuffleInv_assoc, Category.comp_id,
    twistShuffleInvCover]
  show (tensorδ V R.X W S.X ≫
      modTensorπ A (tensorLeftMod A V R)
        (tensorLeftMod A W S)) ≫
      twistShuffleHom A V W R S =
    (V ⊗ W) ◁ modTensorπ A R S
  erw [Category.assoc]
  erw [modTensorπ_twistShuffleHom]
  rw [twistShuffleCover, ← Category.assoc, tensorδ_tensorμ,
    Category.id_comp]

/-- **The twist shuffle is a module map**: it intertwines the
descended action of the twisted pair with the twist action of
the shuffled pair. -/
theorem twistShuffleHom_act
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (V : D) (W : D) (R : Mod D A)
    (S : Mod D A) :
    letI := modTensorModObj A R S
    modTensorAct A (tensorLeftMod A V R) (tensorLeftMod A W S) ≫
        twistShuffleHom A V W R S =
      (A ◁ twistShuffleHom A V W R S) ≫
        actAcross A (V ⊗ W) (modTensor A R S) := by
  letI := modTensorModObj A R S
  apply modTensor_whisker_hom_ext A (tensorLeftMod A V R)
    (tensorLeftMod A W S) A
  conv_lhs => rw [whiskerLeft_modTensorπ_act_assoc]
  rw [show actLeft A (tensorLeftMod A V R).X =
    actAcross A V R.X from rfl]
  conv_rhs => rw [← MonoidalCategory.whiskerLeft_comp_assoc,
    modTensorπ_twistShuffleHom]
  conv_lhs => rw [modTensorπ_twistShuffleHom]
  rw [twistShuffleCover,
    show actAcross A (V ⊗ W) (modTensor A R S) =
      (braidPast A (V ⊗ W) (modTensor A R S)).hom ≫
        ((V ⊗ W) ◁ modTensorAct A R S) from by
      rw [actAcross_eq_braidPast]
      rfl]
  show (α_ A (V ⊗ R.X) (W ⊗ S.X)).inv ≫
      (actAcross A V R.X ▷ (W ⊗ S.X)) ≫
      (tensorμ V R.X W S.X ≫ ((V ⊗ W) ◁ modTensorπ A R S)) =
    (A ◁ (tensorμ V R.X W S.X ≫
      ((V ⊗ W) ◁ modTensorπ A R S))) ≫
      ((braidPast A (V ⊗ W) (modTensor A R S)).hom ≫
        ((V ⊗ W) ◁ modTensorAct A R S))
  conv_rhs => rw [MonoidalCategory.whiskerLeft_comp,
    Category.assoc,
    ← Category.assoc (A ◁ ((V ⊗ W) ◁ modTensorπ A R S)),
    braidPast_natural_tail A (V ⊗ W) (modTensorπ A R S),
    Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp
      (V ⊗ W) (A ◁ modTensorπ A R S) (modTensorAct A R S),
    whiskerLeft_modTensorπ_act]
  rw [actAcross]
  show (α_ A (V ⊗ R.X) (W ⊗ S.X)).inv ≫
      ((α_ A V R.X).inv ≫ ((β_ A V).hom ▷ R.X) ≫
        (α_ V A R.X).hom ≫ (V ◁ actLeft A R.X)) ▷ (W ⊗ S.X) ≫
      tensorμ V R.X W S.X ≫ ((V ⊗ W) ◁ modTensorπ A R S) =
    A ◁ tensorμ V R.X W S.X ≫
      (braidPast A (V ⊗ W) (R.X ⊗ S.X)).hom ≫
      (V ⊗ W) ◁ (((α_ A R.X S.X).inv ≫
        (actLeft A R.X ▷ S.X)) ≫ modTensorπ A R S)
  have hM : ((V ◁ actLeft A R.X) ▷ (W ⊗ S.X)) ≫
      tensorμ V R.X W S.X =
      tensorμ V (A ⊗ R.X) W S.X ≫
        ((V ⊗ W) ◁ (actLeft A R.X ▷ S.X)) := by
    simpa using tensorμ_natural (𝟙 V) (actLeft A R.X) (𝟙 W)
      (𝟙 S.X)
  simp only [MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% hM]
  have hpure2 : (α_ A (V ⊗ R.X) (W ⊗ S.X)).inv ≫
      (α_ A V R.X).inv ▷ (W ⊗ S.X) ≫
      ((β_ A V).hom ▷ R.X) ▷ (W ⊗ S.X) ≫
      (α_ V A R.X).hom ▷ (W ⊗ S.X) ≫
      tensorμ V (A ⊗ R.X) W S.X =
      A ◁ tensorμ V R.X W S.X ≫
      (braidPast A (V ⊗ W) (R.X ⊗ S.X)).hom ≫
      ((V ⊗ W) ◁ (α_ A R.X S.X).inv) := by
    simp only [braidPast_hom, Category.assoc]
    exact twist_act_coherence A V R.X W S.X
  rw [reassoc_of% hpure2]

/-- **The twist shuffle as a module map**: the shuffled pair maps
to the twist of the relative tensor. -/
noncomputable def twistShuffleModHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (V : D) (W : D) (R : Mod D A)
    (S : Mod D A) :
    modTensorMod A (tensorLeftMod A V R) (tensorLeftMod A W S) ⟶
      tensorLeftMod A (V ⊗ W) (modTensorMod A R S) :=
  Mod.Hom.mk' (twistShuffleHom A V W R S)
    (twistShuffleHom_act A V W R S)

/-- The inverse twist shuffle intertwines the actions. -/
theorem twistShuffleInv_act
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (V : D) (W : D) (R : Mod D A)
    (S : Mod D A) :
    letI := modTensorModObj A R S
    actAcross A (V ⊗ W) (modTensor A R S) ≫
        twistShuffleInv A V W R S =
      (A ◁ twistShuffleInv A V W R S) ≫
        modTensorAct A (tensorLeftMod A V R)
          (tensorLeftMod A W S) := by
  letI := modTensorModObj A R S
  haveI : IsIso (twistShuffleHom A V W R S) :=
    ⟨twistShuffleInv A V W R S,
      twistShuffleHom_twistShuffleInv A V W R S,
      twistShuffleInv_twistShuffleHom A V W R S⟩
  rw [← cancel_mono (twistShuffleHom A V W R S)]
  have h := twistShuffleHom_act A V W R S
  rw [Category.assoc, Category.assoc,
    twistShuffleInv_twistShuffleHom, Category.comp_id, h,
    ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
    twistShuffleInv_twistShuffleHom,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- The inverse twist shuffle as a module map. -/
noncomputable def twistShuffleModInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (V : D) (W : D) (R : Mod D A)
    (S : Mod D A) :
    tensorLeftMod A (V ⊗ W) (modTensorMod A R S) ⟶
      modTensorMod A (tensorLeftMod A V R) (tensorLeftMod A W S) :=
  Mod.Hom.mk' (twistShuffleInv A V W R S)
    (twistShuffleInv_act A V W R S)

/-- The module-level twist shuffle is an isomorphism. -/
noncomputable def twistShuffleModIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (V : D) (W : D) (R : Mod D A)
    (S : Mod D A) :
    modTensorMod A (tensorLeftMod A V R) (tensorLeftMod A W S) ≅
      tensorLeftMod A (V ⊗ W) (modTensorMod A R S) where
  hom := twistShuffleModHom A V W R S
  inv := twistShuffleModInv A V W R S
  hom_inv_id := Mod.hom_ext _ _
    (twistShuffleHom_twistShuffleInv A V W R S)
  inv_hom_id := Mod.hom_ext _ _
    (twistShuffleInv_twistShuffleHom A V W R S)

/-- An object map in the twist slot, as a module map: the twist
action carries past the context naturally. -/
noncomputable def tensorLeftModContextHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A]
    {V V' : D}
    (f : V ⟶ V') (M : Mod D A) :
    tensorLeftMod A V M ⟶ tensorLeftMod A V' M :=
  Mod.Hom.mk' (f ▷ M.X)
    (by
      show actAcross A V M.X ≫ (f ▷ M.X) =
        (A ◁ (f ▷ M.X)) ≫ actAcross A V' M.X
      exact (actAcross_natural A f M.X).symm)

/-- A module map under the twist, as a module map. -/
noncomputable def tensorLeftModWhiskerHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A]
    (V : D)
    {M N : Mod D A} (g : M ⟶ N) :
    tensorLeftMod A V M ⟶ tensorLeftMod A V N :=
  Mod.Hom.mk' (V ◁ g.hom)
    (by
      show actAcross A V M.X ≫ (V ◁ g.hom) =
        (A ◁ (V ◁ g.hom)) ≫ actAcross A V N.X
      have hg : actLeft A M.X ≫ g.hom =
          (A ◁ g.hom) ≫ actLeft A N.X := IsModHom.smul_hom
      rw [actAcross_eq_braidPast, actAcross_eq_braidPast,
        Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
        hg, MonoidalCategory.whiskerLeft_comp, ← Category.assoc,
        ← braidPast_natural_tail, Category.assoc])

/-- The twist-slot transport of an object isomorphism. -/
noncomputable def tensorLeftModContextIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A]
    {V V' : D}
    (e : V ≅ V') (M : Mod D A) :
    tensorLeftMod A V M ≅ tensorLeftMod A V' M where
  hom := tensorLeftModContextHom A e.hom M
  inv := tensorLeftModContextHom A e.inv M
  hom_inv_id := Mod.hom_ext _ _ (by
    show (e.hom ▷ M.X) ≫ (e.inv ▷ M.X) = 𝟙 _
    rw [← MonoidalCategory.comp_whiskerRight, Iso.hom_inv_id,
      MonoidalCategory.id_whiskerRight])
  inv_hom_id := Mod.hom_ext _ _ (by
    show (e.inv ▷ M.X) ≫ (e.hom ▷ M.X) = 𝟙 _
    rw [← MonoidalCategory.comp_whiskerRight, Iso.inv_hom_id,
      MonoidalCategory.id_whiskerRight])

/-- The twist of a module isomorphism. -/
noncomputable def tensorLeftModWhiskerIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A]
    (V : D)
    {M N : Mod D A} (f : M ≅ N) :
    tensorLeftMod A V M ≅ tensorLeftMod A V N where
  hom := tensorLeftModWhiskerHom A V f.hom
  inv := tensorLeftModWhiskerHom A V f.inv
  hom_inv_id := Mod.hom_ext _ _ (by
    show (V ◁ f.hom.hom) ≫ (V ◁ f.inv.hom) = 𝟙 _
    rw [← MonoidalCategory.whiskerLeft_comp,
      show f.hom.hom ≫ f.inv.hom = 𝟙 M.X from
        congrArg Mod.Hom.hom f.hom_inv_id,
      MonoidalCategory.whiskerLeft_id])
  inv_hom_id := Mod.hom_ext _ _ (by
    show (V ◁ f.inv.hom) ≫ (V ◁ f.hom.hom) = 𝟙 _
    rw [← MonoidalCategory.whiskerLeft_comp,
      show f.inv.hom ≫ f.hom.hom = 𝟙 N.X from
        congrArg Mod.Hom.hom f.inv_hom_id,
      MonoidalCategory.whiskerLeft_id])

end RS
