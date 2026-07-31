/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument

universe w v v' u u'

local instance Cardinal.aleph0_isRegular : Fact Cardinal.aleph0.{w}.IsRegular where
  out := Cardinal.isRegular_aleph0

noncomputable local instance Cardinal.orderbot_aleph0_ord_to_type :
    OrderBot Cardinal.aleph0.ord.ToType :=
  Cardinal.orderBotAleph0OrdToType

namespace CategoryTheory.MorphismProperty

attribute [local instance] Cardinal.orderbot_aleph0_ord_to_type

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

lemma monotone_coproducts {W₁ W₂ : MorphismProperty C} (h : W₁ ≤ W₂) :
    coproducts.{w} W₁ ≤ coproducts.{w} W₂ := by
  intro A B f hf
  rw [coproducts_iff] at hf ⊢
  obtain ⟨J, hf⟩ := hf
  exact ⟨J, colimitsOfShape_monotone h _ _ hf⟩

@[simp]
lemma min_iff (W₁ W₂ : MorphismProperty C) {X Y : C} (f : X ⟶ Y) :
    (W₁ ⊓ W₂) f ↔ W₁ f ∧ W₂ f := Iff.rfl

@[simp]
lemma max_iff (W₁ W₂ : MorphismProperty C) {X Y : C} (f : X ⟶ Y) :
    (W₁ ⊔ W₂) f ↔ W₁ f ∨ W₂ f := Iff.rfl

section

variable {ι : Type*} (W : ι → MorphismProperty C)

instance [∀ i, (W i).ContainsIdentities] : (⨅ (i : ι), W i).ContainsIdentities where
  id_mem X := by
    simp only [iInf_iff]
    intro i
    apply id_mem

instance [∀ i, (W i).IsStableUnderComposition] : (⨅ (i : ι), W i).IsStableUnderComposition where
  comp_mem f g hf hg := by
    simp only [iInf_iff] at hf hg ⊢
    intro i
    exact comp_mem _ _ _ (hf i) (hg i)

instance [∀ i, (W i).IsMultiplicative] : (⨅ (i : ι), W i).IsMultiplicative where

instance [∀ i, (W i).IsStableUnderRetracts] : (⨅ (i : ι), W i).IsStableUnderRetracts where
  of_retract hfg hg := by
    simp only [iInf_iff] at hg ⊢
    intro i
    exact of_retract hfg (hg i)

instance [∀ i, (W i).HasTwoOutOfThreeProperty] : (⨅ (i : ι), W i).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg := by
    simp only [iInf_iff] at hg hfg ⊢
    intro i
    exact (W i).of_postcomp f g (hg i) (hfg i)
  of_precomp f g hf hfg := by
    simp only [iInf_iff] at hf hfg ⊢
    intro i
    exact (W i).of_precomp f g (hf i) (hfg i)

end

section

variable (W₁ W₂ : MorphismProperty C)

instance [W₁.IsStableUnderRetracts] [W₂.IsStableUnderRetracts] :
    (W₁ ⊓ W₂).IsStableUnderRetracts where
  of_retract hfg hg := ⟨of_retract hfg hg.1, of_retract hfg hg.2⟩

instance [W₁.HasTwoOutOfThreeProperty] [W₂.HasTwoOutOfThreeProperty] :
    (W₁ ⊓ W₂).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg := ⟨W₁.of_postcomp f g hg.1 hfg.1, W₂.of_postcomp f g hg.2 hfg.2⟩
  of_precomp f g hf hfg := ⟨W₁.of_precomp f g hf.1 hfg.1, W₂.of_precomp f g hf.2 hfg.2⟩

end

instance (W : MorphismProperty C) :
    IsStableUnderTransfiniteComposition.{w} W.llp where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ :=
    isStableUnderTransfiniteCompositionOfShape_llp W J

instance (W : MorphismProperty C) :
    IsStableUnderCoproducts.{w} W.llp where
  isStableUnderCoproductsOfShape J :=
    llp_isStableUnderCoproductsOfShape W J

open Limits

lemma map_pushouts (W : MorphismProperty C) {X Y : C} {f : X ⟶ Y}
    (hf : W.pushouts f) (F : C ⥤ D) [PreservesColimitsOfShape WalkingSpan F] :
    (W.map F).pushouts (F.map f) := by
  obtain ⟨_, _, l, _, _, hl, sq⟩ := hf
  exact ⟨_, _, _, _, _, W.map_mem_map F l hl, sq.map F⟩

lemma map_pushouts_le (W : MorphismProperty C) (F : C ⥤ D)
    [PreservesColimitsOfShape WalkingSpan F] :
    W.pushouts.map F ≤ (W.map F).pushouts := by
  rw [map_le_iff]
  intro _ _ _ hf
  exact W.map_pushouts hf F

lemma map_colimitsOfShape (W : MorphismProperty C)
    {J : Type*} [Category J]
    {X Y : C} {f : X ⟶ Y} (hf : W.colimitsOfShape J f) (F : C ⥤ D)
    [PreservesColimitsOfShape J F] :
    (W.map F).colimitsOfShape J (F.map f) := by
  obtain ⟨_, _, c₁, c₂, hc₁, hc₂, φ, hφ⟩ := hf
  have : F.map (hc₁.desc (Cocone.mk _ (φ ≫ c₂.ι))) =
      (isColimitOfPreserves F hc₁).desc
        (Cocone.mk _ (Functor.whiskerRight φ F ≫ (F.mapCocone c₂).ι)) := by
    refine (isColimitOfPreserves F hc₁).hom_ext (fun j ↦ ?_)
    erw [(isColimitOfPreserves F hc₁).fac, ← F.map_comp, hc₁.fac]
    exact F.map_comp _ _
  rw [this]
  exact ⟨_, _, _, _, _, isColimitOfPreserves F hc₂, _,
    fun j ↦ W.map_mem_map F (φ.app j) (hφ j)⟩

lemma map_coproducts (W : MorphismProperty C) {X Y : C} {f : X ⟶ Y}
    (hf : coproducts.{w} W f) (F : C ⥤ D)
    [∀ (J : Type w), PreservesColimitsOfShape (Discrete J) F] :
    coproducts.{w} (W.map F) (F.map f) := by
  rw [coproducts_iff] at hf ⊢
  obtain ⟨J, hf⟩ := hf
  exact ⟨J, W.map_colimitsOfShape hf F⟩

instance (W : MorphismProperty C) : (coproducts.{w} W).RespectsIso :=
  RespectsIso.of_respects_arrow_iso _ (fun f g e hf ↦ by
    rw [coproducts_iff] at hf ⊢
    obtain ⟨J, hf⟩ := hf
    exact ⟨J, (MorphismProperty.arrow_mk_iso_iff _ e).1 hf⟩)

lemma map_coproducts_le (W : MorphismProperty C) (F : C ⥤ D)
    [∀ (J : Type w), PreservesColimitsOfShape (Discrete J) F] :
    (coproducts.{w} W).map F ≤ coproducts.{w} (W.map F) := by
  rw [map_le_iff]
  intro _ _ _ hf
  exact W.map_coproducts hf F

end CategoryTheory.MorphismProperty
