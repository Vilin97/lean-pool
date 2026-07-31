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
    OrderBot Cardinal.aleph0.ord.toType :=
  toTypeOrderBot Cardinal.isRegular_aleph0.ne_zero

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
lemma sInf_iff (S : Set (MorphismProperty C)) {X Y : C} (f : X ⟶ Y) :
    sInf S f ↔ ∀ (W : S), W.1 f := by
  dsimp [sInf, iInf]
  aesop

@[simp]
lemma max_iff (W₁ W₂ : MorphismProperty C) {X Y : C} (f : X ⟶ Y) :
    (W₁ ⊔ W₂) f ↔ W₁ f ∨ W₂ f := Iff.rfl

instance isSmall_iSup {ι : Type w'} (W : ι → MorphismProperty C) [∀ i, IsSmall.{w} (W i)]
    [Small.{w} ι] :
    IsSmall.{w} (⨆ i, W i) := by
  have : ⨆ i, W i = .ofHoms (fun (j : Σ (i : ι), (W i).toSet) ↦ j.2.1.hom) := by
    ext
    simp [ofHoms_iff]
  rw [this]
  infer_instance

section

variable {ι : Sort*} (W : ι → MorphismProperty C)

@[simp]
lemma iInf_iff {X Y : C} (f : X ⟶ Y) :
    iInf W f ↔ ∀ i, W i f := by
  dsimp [sInf, iInf]
  aesop

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

section

variable (W : MorphismProperty D) (F : C ⥤ D)

instance [W.IsStableUnderRetracts] : (W.inverseImage F).IsStableUnderRetracts where
  of_retract r h := W.of_retract (r.map F.mapArrow) h

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
  let hc₁' := isColimitOfPreserves F hc₁
  have : F.map (hc₁.desc { ι := φ ≫ c₂.ι }) =
    hc₁'.desc { ι := whiskerRight φ F ≫ (F.mapCocone c₂).ι } :=
      hc₁'.hom_ext (fun j ↦ by
        rw [IsColimit.fac]
        dsimp
        rw [← F.map_comp, IsColimit.fac, NatTrans.comp_app, Functor.map_comp] )
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
