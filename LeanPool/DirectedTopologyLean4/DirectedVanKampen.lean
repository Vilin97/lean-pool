/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import LeanPool.DirectedTopologyLean4.DihomotopyCover
import LeanPool.DirectedTopologyLean4.PushoutAlternative
import LeanPool.DirectedTopologyLean4.DihomotopyToPathDihomotopy
import LeanPool.DirectedTopologyLean4.MorphismAux
/-
  This file contains the directed version of the Van Kampen Theorem.
  The statement is as follows:
  Let `X : dTopCat` and `X₁ X₂ : Set X` such that `X₁` and `X₂` are
  both open and `X₁ ∪ X₂ = X`.
  Let `i₁ : X₁ ∩ X₂ → X₁`, `i₂ : X₁ ∩ X₂ → X₂`, `j₁ : X₁ → X`
  and `j₂ : X₂ → X` be the inclusion maps in `dTopCat`.
  Then we have a pushout in `Cat`:
  dπₓ(X₁ ∩ X₂) ------ dπₘ i₁ -----> dπₓ(X₁)
       |                              |
       |                              |
       |                              |
     dπₘ i₂                         dπₘ j₁
       |                              |
       |                              |
       |                              |
    dπₓ(X₂) ------- dπₘ j₂ ------> dπₓ(X)
  The proof we give is constructive and is based on the proof given by
  Marco Grandis, Directed Homotopy Theory I, published in Cahiers de topologie
  et géométrie différentielle catégoriques, 44, no. 4, pages 307-309, 2003.
-/
universe u v
open Set
open scoped unitInterval FundamentalCategory
attribute [local instance] Dipath.Dihomotopic.setoid
noncomputable section
namespace DirectedVanKampen
open FundamentalCategory DiSubtype CategoryTheory
attribute [local instance] Classical.propDecidable
variable {X : dTopCat.{u}} {X₁ X₂ : Set X}
variable (hX : X₁ ∪ X₂ = Set.univ)
variable (X₁_open : IsOpen X₁) (X₂_open : IsOpen X₂)
-- We will use a shorthand notation for the 4 morphisms in dTop:
-- i₁ : X₁ ∩ X₂ ⟶ X₁
local notation "i₁" => dTopCat.DirectedSubsetHom <| Set.inter_subset_left (s := X₁) (t := X₂)
-- i₂ : X₁ ∩ X₂ ⟶ X₂
local notation "i₂" => dTopCat.DirectedSubsetHom <| Set.inter_subset_right (s := X₁) (t := X₂)
-- j₁ : X₁ ⟶ X
local notation "j₁" => dTopCat.DirectedSubtypeHom X₁
-- j₂ : X₂ ⟶ X
local notation "j₂" => dTopCat.DirectedSubtypeHom X₂
namespace PushoutFunctor
open Dipath Dipath.covered Dipath.covered_partwise
variable {x y : X} {C : CategoryTheory.Cat.{u, u}}
variable (F₁ : (dπₓ (dTopCat.of X₁) ⥤ C)) (F₂ : (dπₓ (dTopCat.of X₂) ⥤ C))
variable (h_comm : (dπₘ (dTopCat.DirectedSubsetHom <|
    Set.inter_subset_left (s := X₁) (t := X₂))) ⋙ F₁ =
  ((dπₘ (dTopCat.DirectedSubsetHom <|
    Set.inter_subset_right (s := X₁) (t := X₂))) ⋙ F₂))
open CategoryTheory
variable {Y : dTopCat.{u}} {Y₀ : Set Y} {F : dπₓ (dTopCat.of Y₀) ⥤ C}
lemma subset_functor_trans {x y z : Y} {γ₁ : Dipath x y} {γ₂ : Dipath y z}
    (hγ : range (γ₁.trans γ₂) ⊆ Y₀) :
    (F.map ⟦SubtypeDipath γ₁ (subsets_of_trans_subset hγ).1⟧ ≫
      F.map ⟦SubtypeDipath γ₂ (subsets_of_trans_subset hγ).2⟧) =
      F.map ⟦SubtypeDipath (γ₁.trans γ₂) hγ⟧ := by
  rw [←F.map_comp]
  change F.map (Dipath.Dihomotopic.Quotient.comp
    ⟦SubtypeDipath γ₁ (subsets_of_trans_subset hγ).1⟧
    ⟦SubtypeDipath γ₂ (subsets_of_trans_subset hγ).2⟧) =
      F.map ⟦SubtypeDipath (γ₁.trans γ₂) hγ⟧
  rw [←Dipath.Dihomotopic.comp_lift]
  congr 1
  apply Quotient.sound
  exact Eq.ndrec
    (motive := fun p =>
      ((SubtypeDipath γ₁ (subsets_of_trans_subset hγ).1).trans
        (SubtypeDipath γ₂ (subsets_of_trans_subset hγ).2)).Dihomotopic p)
    (Relation.EqvGen.refl _)
    (subtype_trans hγ)
lemma subset_functor_reparam {x y : Y} {γ : Dipath x y} (hγ : range γ ⊆ Y₀)
    {f : D(I,I)} (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    F.map ⟦SubtypeDipath (γ.reparam f hf₀ hf₁)
        (show range (γ.reparam f hf₀ hf₁) ⊆ Y₀ by
          exact (Dipath.range_reparam γ f hf₀ hf₁).symm ▸ hγ)⟧ =
      F.map ⟦SubtypeDipath γ hγ⟧ := by
  congr 1
  rw [subtype_reparam hγ hf₀ hf₁]
  symm
  exact Quotient.eq.mpr (Dipath.Dihomotopic.reparam (SubtypeDipath γ hγ) f hf₀ hf₁)
lemma functor_cast {X : dTopCat} (F : (dπₓ X) ⥤ C) {x y x' y' : X}
    (γ : Dipath x y) (hx : x' = x) (hy : y' = y) :
    F.map ⟦γ.cast hx hy⟧ =
      (eqToHom (congrArg F.obj (congrArg FundamentalCategory.mk hx))) ≫ F.map ⟦γ⟧ ≫
      (eqToHom (congrArg F.obj (congrArg FundamentalCategory.mk hy)).symm) := by
  subst_vars
  simp
  congr 2
@[simp]
lemma functor_cast_heq {X : dTopCat} (F : (dπₓ X) ⥤ C) {x y x' y' : X}
    (γ : Dipath x y) (hx : x' = x) (hy : y' = y) :
    F.map ⟦γ.cast hx hy⟧ ≍ F.map ⟦γ⟧ := by
  cases hx
  cases hy
  rfl
/-
  Given a category `C` and functors `F₁ : dπₓ X₁ ⥤ C` and
  `F₂ : dπₓ X₂ ⥤ C`, construct a functor `F : dπₓ X ⥤ C`.
-/
/- ### Functor on Objects -/
/-
- Define the behaviour on objects
-/
/-- Object map for the pushout functor induced by the covering square. -/
def FunctorOnObj (x : dπₓ X) : C :=
  Or.by_cases
    ((Set.mem_union x.as X₁ X₂).mp (Filter.mem_top.mpr hX x.as))
      (fun hx => F₁.obj ⟨x.as, hx⟩)
      (fun hx => F₂.obj ⟨x.as, hx⟩)
-- We will use the shorhand notation F_obj
local notation "F_obj" => FunctorOnObj hX F₁ F₂
/-
  Under the assumption that the square commutes, we can show how the functor behaves on objects
-/
variable {F₁ F₂}
include h_comm
lemma functorOnObj_apply_one {x : X} (hx : x ∈ X₁) : F₁.obj ⟨x, hx⟩ = F_obj ⟨x⟩ := by
  have := h_comm
  convert (dif_pos hx).symm using 1
  rfl
lemma functorOnObj_apply_two {x : X} (hx₂ : x ∈ X₂) :
    F₂.obj ⟨x, hx₂⟩ = F_obj ⟨x⟩ := by
  by_cases hx₁ : x ∈ X₁
  case pos =>
    have hx₀ : x ∈ X₁ ∩ X₂ := ⟨hx₁, hx₂⟩
    have : F₁.obj ((dπₘ i₁).obj ⟨x, hx₀⟩) =
        F₂.obj ((dπₘ i₂).obj ⟨x, hx₀⟩) :=
      show ((dπₘ i₁) ⋙ F₁).obj ⟨x, hx₀⟩ =
          ((dπₘ i₂) ⋙ F₂).obj ⟨x, hx₀⟩ by
        rw [h_comm]
    have : F₁.obj ⟨x, hx₁⟩ = F₂.obj (⟨x, hx₂⟩) :=
      calc F₁.obj ⟨x, hx₁⟩
        _ = F₁.obj ((dπₘ i₁).obj ⟨x, hx₀⟩) := rfl
        _ = F₂.obj ((dπₘ i₂).obj ⟨x, hx₀⟩) := this
        _ = F₂.obj (⟨x, hx₂⟩) := rfl
    rw [this.symm]
    convert (dif_pos hx₁).symm using 1; rfl
  case neg =>
    convert (dif_neg hx₁).symm using 1; rfl
/- ### Functor on Maps -/
/-
  Define the mapping behaviour on paths that are fully covered by one set
-/
/-- Map assigned to a path whose image lies in the first open subset. -/
def FunctorOnHomOfCoveredAux₁ {γ : Dipath x y} (hγ : range γ ⊆ X₁) :
    F_obj ⟨x⟩ ⟶ F_obj ⟨y⟩ :=
  (eqToHom (functorOnObj_apply_one hX h_comm (source_elt_of_image_subset hγ)).symm) ≫
  (F₁.map ⟦SubtypeDipath γ hγ⟧) ≫
  (eqToHom (functorOnObj_apply_one hX h_comm (target_elt_of_image_subset hγ)))
/-- Map assigned to a path whose image lies in the second open subset. -/
def FunctorOnHomOfCoveredAux₂ {γ : Dipath x y} (hγ : range γ ⊆ X₂) :
    F_obj ⟨x⟩ ⟶ F_obj ⟨y⟩ :=
  (eqToHom (functorOnObj_apply_two hX h_comm (source_elt_of_image_subset hγ)).symm) ≫
  (F₂.map ⟦SubtypeDipath γ hγ⟧) ≫
  (eqToHom (functorOnObj_apply_two hX h_comm (target_elt_of_image_subset hγ)))
/-
  Show that these maps respect composition of paths
-/
lemma functorOnHomOfCoveredAux₁_trans {x y z : X} {γ₁ : Dipath x y}
    {γ₂ : Dipath y z} (hγ : range (γ₁.trans γ₂) ⊆ X₁) :
    FunctorOnHomOfCoveredAux₁ hX h_comm hγ =
      FunctorOnHomOfCoveredAux₁ hX h_comm (subsets_of_trans_subset hγ).1
      ≫ FunctorOnHomOfCoveredAux₁ hX h_comm (subsets_of_trans_subset hγ).2 := by
  unfold FunctorOnHomOfCoveredAux₁
  rw [(subset_functor_trans hγ).symm]
  simp
lemma functorOnHomOfCoveredAux₂_trans {x y z : X} {γ₁ : Dipath x y}
    {γ₂ : Dipath y z} (hγ : range (γ₁.trans γ₂) ⊆ X₂) :
    FunctorOnHomOfCoveredAux₂ hX h_comm hγ =
      FunctorOnHomOfCoveredAux₂ hX h_comm (subsets_of_trans_subset hγ).1
      ≫ FunctorOnHomOfCoveredAux₂ hX h_comm (subsets_of_trans_subset hγ).2 := by
  unfold FunctorOnHomOfCoveredAux₂
  rw [(subset_functor_trans hγ).symm]
  simp
/-
 Show that the maps respect reparametrization of paths
-/
lemma functorOnHomOfCoveredAux₁_reparam {x y : X} {γ : Dipath x y} (hγ : range γ ⊆ X₁)
    {f : D(I,I)} (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    FunctorOnHomOfCoveredAux₁ hX h_comm hγ =
      FunctorOnHomOfCoveredAux₁ hX h_comm (reparam_subset_of_subset hγ hf₀ hf₁) := by
  unfold FunctorOnHomOfCoveredAux₁
  rw [subset_functor_reparam hγ hf₀ hf₁]
lemma functorOnHomOfCoveredAux₂_reparam {x y : X} {γ : Dipath x y} (hγ : range γ ⊆ X₂)
    {f : D(I,I)} (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    FunctorOnHomOfCoveredAux₂ hX h_comm hγ =
      FunctorOnHomOfCoveredAux₂ hX h_comm (reparam_subset_of_subset hγ hf₀ hf₁) := by
  unfold FunctorOnHomOfCoveredAux₂
  rw [subset_functor_reparam hγ hf₀ hf₁]
/-
 Show that the maps respect reparametrization of paths
-/
lemma functorOnHomOfCoveredAux₁_refl {x : X} (hx : x ∈ X₁) :
  FunctorOnHomOfCoveredAux₁ hX h_comm (range_refl_subset_of_mem hx) = 𝟙 (F_obj ⟨x⟩) := by
  unfold FunctorOnHomOfCoveredAux₁
  rw [subtype_refl]
  change eqToHom _ ≫ F₁.map (𝟙 ⟨x, hx⟩) ≫ eqToHom _ = 𝟙 (F_obj ⟨x⟩)
  rw [F₁.map_id]
  simp
lemma functorOnHomOfCoveredAux₂_refl {x : X} (hx : x ∈ X₂) :
  FunctorOnHomOfCoveredAux₂ hX h_comm (range_refl_subset_of_mem hx) = 𝟙 (F_obj ⟨x⟩) := by
  unfold FunctorOnHomOfCoveredAux₂
  rw [subtype_refl]
  change eqToHom _ ≫ F₂.map (𝟙 ⟨x, hx⟩) ≫ eqToHom _ = 𝟙 (F_obj ⟨x⟩)
  rw [F₂.map_id]
  simp
/-
  Show that for any path living in `X₁ ∩ X₂`, either map gives the same result.
-/
lemma functorOnHomOfCoveredAux_equal {γ : Dipath x y} (hγ₁ : range γ ⊆ X₁)
    (hγ₂ : range γ ⊆ X₂) :
    FunctorOnHomOfCoveredAux₁ hX h_comm hγ₁ =
      FunctorOnHomOfCoveredAux₂ hX h_comm hγ₂ := by
  unfold FunctorOnHomOfCoveredAux₁ FunctorOnHomOfCoveredAux₂
  have hγ₀ : range γ ⊆ X₁ ∩ X₂ := subset_inter hγ₁ hγ₂
  apply (eqToHom_comp_iff _ _ _).mpr
  apply (comp_eqToHom_iff _ _ _).mpr
  simp only [dTopCat.coe_of, eqToHom_trans_assoc, Category.assoc, eqToHom_trans]
  exact map_eq_map_of_eq h_comm ⟦SubtypeDipath γ hγ₀⟧
/-
- ### Define the mapping behaviour on covered paths
-/
/-- Map assigned to a path covered by one of the two open subsets. -/
def FunctorOnHomOfCovered {γ : Dipath x y} (hγ : covered hX γ) :
    F_obj ⟨x⟩ ⟶ F_obj ⟨y⟩ :=
  Or.by_cases hγ
    (fun hγ => FunctorOnHomOfCoveredAux₁ hX h_comm hγ)
    (fun hγ => FunctorOnHomOfCoveredAux₂ hX h_comm hγ)
local notation "F₀" => FunctorOnHomOfCovered hX h_comm
lemma functorOnHomOfCovered_apply_left {γ : Dipath x y} (hγ : range γ ⊆ X₁) :
    F₀ (Or.inl hγ) = FunctorOnHomOfCoveredAux₁ hX h_comm hγ := dif_pos hγ
lemma functorOnHomOfCovered_apply_left' {γ : Dipath x y} (hγ : range γ ⊆ X₁) :
    F₀ (covered_partwise_of_covered 0 (Or.inl hγ)) = FunctorOnHomOfCoveredAux₁ hX h_comm hγ :=
  functorOnHomOfCovered_apply_left _ _ _
lemma functorOnHomOfCovered_apply_right {γ : Dipath x y} (hγ : range γ ⊆ X₂) :
    F₀ (Or.inr hγ) = FunctorOnHomOfCoveredAux₂ hX h_comm hγ := by
  by_cases hγ₁ : range γ ⊆ X₁
  · rw [functorOnHomOfCovered_apply_left hX h_comm hγ₁]
    exact functorOnHomOfCoveredAux_equal hX h_comm hγ₁ hγ
  · apply dif_neg hγ₁
lemma functorOnHomOfCovered_equal {γ₁ γ₂ : Dipath x y} (h : γ₁ = γ₂)
    (hγ₁ : covered hX γ₁) (hγ₂ : covered hX γ₂) :
    F₀ hγ₁ = F₀ hγ₂ := by subst_vars; rfl
lemma functorOnHomOfCovered_heq_of_ext {x y x' y' : X} {γ : Dipath x y}
    {γ' : Dipath x' y'} (h : ∀ t, γ t = γ' t) (hγ : covered hX γ)
    (hγ' : covered hX γ') :
    F₀ hγ ≍ F₀ hγ' := by
  have hx : x = x' := by simpa using h 0
  have hy : y = y' := by simpa using h 1
  subst hx
  subst hy
  have hγ_eq : γ = γ' := by
    ext t
    exact h t
  subst hγ_eq
  rfl
lemma functorOnHomOfCovered_refl : F₀ (covered_refl x hX) = 𝟙 (F_obj ⟨x⟩) := by
  cases ((Set.mem_union x X₁ X₂).mp (Filter.mem_top.mpr hX x))
  case inl hx₁ =>
    rw [←functorOnHomOfCoveredAux₁_refl hX h_comm hx₁]
    exact functorOnHomOfCovered_apply_left hX h_comm (DiSubtype.range_refl_subset_of_mem hx₁)
  case inr hx₂ =>
    rw [←functorOnHomOfCoveredAux₂_refl hX h_comm hx₂]
    exact functorOnHomOfCovered_apply_right hX h_comm (DiSubtype.range_refl_subset_of_mem hx₂)
lemma functorOnHomOfCovered_apply_right' {γ : Dipath x y} (hγ : range γ ⊆ X₂) :
    F₀ (covered_partwise_of_covered 0 (Or.inr hγ)) = FunctorOnHomOfCoveredAux₂ hX h_comm hγ :=
  functorOnHomOfCovered_apply_right _ _ _
lemma functorOnHomOfCovered_trans {x y z : X} {γ₁ : Dipath x y} {γ₂ : Dipath y z}
    (hγ : covered hX (γ₁.trans γ₂)) :
    F₀ hγ =
      (F₀ (covered_of_covered_trans hγ).1) ≫ (F₀ (covered_of_covered_trans hγ).2) := by
  cases hγ
  case inl hγ => -- γ is covered by X₁
    rw [functorOnHomOfCovered_apply_left _ _ hγ]
    rw [functorOnHomOfCoveredAux₁_trans]
    congr
    · exact (functorOnHomOfCovered_apply_left _ _ _).symm
    · exact (functorOnHomOfCovered_apply_left _ _ _).symm
  case inr hγ => -- γ is covered by X₂
    rw [functorOnHomOfCovered_apply_right _ _ hγ]
    rw [functorOnHomOfCoveredAux₂_trans]
    congr
    · exact (functorOnHomOfCovered_apply_right _ _ (subsets_of_trans_subset hγ).1).symm
    · exact (functorOnHomOfCovered_apply_right _ _ (subsets_of_trans_subset hγ).2).symm
lemma functorOnHomOfCovered_reparam {x y : X} {γ : Dipath x y} (hγ : covered hX γ)
    {f : D(I,I)} (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    F₀ hγ = F₀ ((covered_reparam_iff γ hX f hf₀ hf₁).mp hγ) := by
  cases hγ
  case inl hγ =>
    have : range (γ.reparam f hf₀ hf₁) ⊆ X₁ := by
      rw [Dipath.range_reparam γ f hf₀ hf₁]
      exact hγ
    rw [functorOnHomOfCovered_apply_left]
    · rw [functorOnHomOfCoveredAux₁_reparam hX h_comm hγ hf₀ hf₁]
      rw [←functorOnHomOfCovered_apply_left hX h_comm this]
    · exact hγ
  case inr hγ =>
    have : range (γ.reparam f hf₀ hf₁) ⊆ X₂ := by
      rw [Dipath.range_reparam γ f hf₀ hf₁]
      exact hγ
    rw [functorOnHomOfCovered_apply_right]
    · rw [functorOnHomOfCoveredAux₂_reparam hX h_comm hγ hf₀ hf₁]
      rw [←functorOnHomOfCovered_apply_right hX h_comm this]
    · exact hγ
lemma functorOnHomOfCovered_cast {x y x' y' : X} {γ : Dipath x y}
    (hγ : covered hX γ) (hx : x' = x) (hy : y' = y) :
    F₀ ((covered_cast_iff γ hX hx hy).mp hγ) =
      (eqToHom (show F_obj ⟨x'⟩ = F_obj ⟨x⟩ by rw [hx])) ≫
      (F₀ hγ) ≫ (eqToHom (show F_obj ⟨y⟩ = F_obj ⟨y'⟩ by rw [hy])) := by
  subst_vars
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp]
  rfl
lemma functorOnHomOfCovered_cast_left {x y x' : X} {γ : Dipath x y}
    (hγ : covered hX γ) (hx : x' = x) :
    F₀ ((covered_cast_iff γ hX hx rfl).mp hγ) =
      (eqToHom (show F_obj ⟨x'⟩ = F_obj ⟨x⟩ by rw [hx])) ≫ (F₀ hγ) := by
  subst_vars
  rw [eqToHom_refl, Category.id_comp]
  rfl
lemma functorOnHomOfCovered_cast_right {x y y' : X} {γ : Dipath x y}
    (hγ : covered hX γ) (hy : y' = y) :
  F₀ ((covered_cast_iff γ hX rfl hy).mp hγ) =
    (F₀ hγ) ≫ (eqToHom (show F_obj ⟨y⟩ = F_obj ⟨y'⟩ by rw [hy])) := by
  subst_vars
  rw [eqToHom_refl, Category.comp_id]
  rfl
lemma functorOnHomOfCovered_split_comp {x y : X} {γ : Dipath x y}
    (hγ : covered hX γ) {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) :
    F₀ hγ =
      (F₀ (covered_split_path hT₀ hT₁ hγ).1) ≫
        (F₀ (covered_split_path hT₀ hT₁ hγ).2) := by
  have : covered hX ((SplitDipath.FirstPart γ T).trans (SplitDipath.SecondPart γ T)) := by
    rw [SplitDipath.first_trans_second_reparam_eq_self γ hT₀ hT₁] at hγ
    exact (covered_reparam_iff _ hX _ _ _).mpr hγ
  rw [←functorOnHomOfCovered_trans hX h_comm this]
  rw [functorOnHomOfCovered_reparam hX h_comm this
      (SplitDipath.trans_reparam_map_zero hT₀ hT₁)
      (SplitDipath.trans_reparam_map_one hT₀ hT₁)]
  congr
  apply SplitDipath.first_trans_second_reparam_eq_self
lemma functorOnHomOfCovered_dihomotopic {x y : X} {γ γ' : Dipath x y} {F : Dihomotopy γ γ'}
  (hF : Dipath.Dihomotopy.covered hX F) :
    F₀ (Dipath.Dihomotopy.covered_left_of_covered hF) =
      F₀ (Dipath.Dihomotopy.covered_right_of_covered hF) := by
  cases hF
  case inl hF =>
    have hγ := subset_trans (Dipath.Dihomotopy.range_left_subset F) hF
    have hγ' := subset_trans (Dipath.Dihomotopy.range_right_subset F) hF
    rw [functorOnHomOfCovered_equal hX h_comm rfl _ (Or.inl hγ)]
    rw [functorOnHomOfCovered_equal hX h_comm rfl _ (Or.inl hγ')]
    rw [functorOnHomOfCovered_apply_left hX h_comm hγ]
    rw [functorOnHomOfCovered_apply_left hX h_comm hγ']
    unfold FunctorOnHomOfCoveredAux₁
    rw [show F₁.map ⟦SubtypeDipath γ hγ⟧ = F₁.map ⟦SubtypeDipath γ' hγ'⟧ from
      congrArg F₁.map (dihomSubtype_of_dihom_range_subset hγ hγ' hF)]
  case inr hF =>
    have hγ := subset_trans (Dipath.Dihomotopy.range_left_subset F) hF
    have hγ' := subset_trans (Dipath.Dihomotopy.range_right_subset F) hF
    rw [functorOnHomOfCovered_equal hX h_comm rfl _ (Or.inr hγ)]
    rw [functorOnHomOfCovered_equal hX h_comm rfl _ (Or.inr hγ')]
    rw [functorOnHomOfCovered_apply_right hX h_comm hγ]
    rw [functorOnHomOfCovered_apply_right hX h_comm hγ']
    unfold FunctorOnHomOfCoveredAux₂
    rw [show F₂.map ⟦SubtypeDipath γ hγ⟧ = F₂.map ⟦SubtypeDipath γ' hγ'⟧ from
      congrArg F₂.map (dihomSubtype_of_dihom_range_subset hγ hγ' hF)]
/-
-  ### Define the behaviour on partwise covered paths
-/
/-- Recursive map on paths split into finitely many covered pieces. -/
def FunctorOnHomOfCoveredPartwiseAux {n : ℕ} :
    ∀ (x y : X) (γ : Dipath x y) (_ : covered_partwise hX γ n),
      F_obj ⟨x⟩ ⟶ F_obj ⟨y⟩ :=
  Nat.recOn n
    (fun _ _ _ hγ => F₀ hγ)
    (fun _ ih _ _ _ hγ => (F₀ hγ.1) ≫ (ih _ _ _ hγ.2))
/-- Map assigned to a path equipped with a proof that it is piecewise covered. -/
abbrev FunctorOnHomOfCoveredPartwise {n : ℕ} {x y : X} {γ : Dipath x y}
    (hγ : covered_partwise hX γ n) :=
  FunctorOnHomOfCoveredPartwiseAux hX h_comm x y γ hγ
local notation "Fₙ" => FunctorOnHomOfCoveredPartwise hX h_comm
lemma functorOnHomOfCoveredPartwise_apply_0 {x y : X} {γ : Dipath x y}
    (hγ : covered_partwise hX γ 0) :
    Fₙ hγ = F₀ hγ := rfl
lemma functorOnHomOfCoveredPartwise_apply_succ {n : ℕ} {x y : X}
    {γ : Dipath x y} (hγ : covered_partwise hX γ n.succ) :
    Fₙ hγ = (F₀ hγ.left) ≫ (Fₙ hγ.right) := rfl
lemma functorOnHomOfCoveredPartwise_equal {n : ℕ} {γ₁ γ₂ : Dipath x y} (h : γ₁ = γ₂)
  (hγ₁ : covered_partwise hX γ₁ n) (hγ₂ : covered_partwise hX γ₂ n) :
    Fₙ hγ₁ = Fₙ hγ₂ := by subst_vars; rfl
lemma functorOnHomOfCoveredPartwise_equal' {n m : ℕ} {γ₁ γ₂ : Dipath x y}
    (h₁ : γ₁ = γ₂)
  (h₂ : n = m) (hγ₁ : covered_partwise hX γ₁ n) (hγ₂ : covered_partwise hX γ₂ m) :
    Fₙ hγ₁ = Fₙ hγ₂ := by subst_vars; rfl
lemma functorOnHomOfCoveredPartwise_heq_of_ext {n m : ℕ} {x y x' y' : X}
    {γ : Dipath x y} {γ' : Dipath x' y'} (h : ∀ t, γ t = γ' t) (hn : n = m)
    (hγ : covered_partwise hX γ n) (hγ' : covered_partwise hX γ' m) :
    Fₙ hγ ≍ Fₙ hγ' := by
  have hx : x = x' := by simpa using h 0
  have hy : y = y' := by simpa using h 1
  subst hx
  subst hy
  have hγ_eq : γ = γ' := by
    ext t
    exact h t
  subst hγ_eq
  cases hn
  rfl
lemma functorOnHomOfCoveredPartwise_cast_params {n m : ℕ} {γ₁ γ₂ : Dipath x y}
    (h₁ : γ₁ = γ₂)
  (h₂ : n = m) (hγ₁ : covered_partwise hX γ₁ n) :
    Fₙ hγ₁ = Fₙ (covered_partwise_of_equal hX h₁ h₂ hγ₁) := by subst_vars; rfl
lemma functorOnHomOfCoveredPartwise_cast {x y x' y' : X} {n : ℕ} {γ : Dipath x y}
  (hγ : covered_partwise hX γ n) (hx : x' = x) (hy : y' = y) :
    Fₙ ((covered_partwise_cast_iff hX γ hx hy).mp hγ) =
      (eqToHom (by rw [hx])) ≫ (Fₙ hγ) ≫ (eqToHom (by rw [hy])) := by
  subst_vars
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp]
  apply functorOnHomOfCoveredPartwise_equal
  rfl
lemma functorOnHomOfCoveredPartwise_cast_left {x y x' : X} {n : ℕ} {γ : Dipath x y}
  (hγ : covered_partwise hX γ n) (hx : x' = x) :
    Fₙ ((covered_partwise_cast_iff hX γ hx rfl).mp hγ) =
      (eqToHom (by rw [hx])) ≫ (Fₙ hγ) := by
  subst_vars
  rw [eqToHom_refl, Category.id_comp]
  apply functorOnHomOfCoveredPartwise_equal
  rfl
lemma functorOnHomOfCoveredPartwise_cast_right {x y y' : X} {n : ℕ} {γ : Dipath x y}
    (hγ : covered_partwise hX γ n) (hy : y' = y) :
    Fₙ ((covered_partwise_cast_iff hX γ rfl hy).mp hγ) =
      (Fₙ hγ) ≫ (eqToHom (by rw [hy])) := by
  subst_vars
  rw [eqToHom_refl, Category.comp_id]
  apply functorOnHomOfCoveredPartwise_equal
  rfl
lemma functorOnHomOfCoveredPartwise_refine_of_covered (k : ℕ) :
  Π {x y : X} {γ : Dipath x y} (hγ : covered hX γ),
    Fₙ (covered_partwise_of_covered 0 hγ) = Fₙ (covered_partwise_of_covered k hγ) := by
  induction k
  case zero =>
    intro x y γ hγ
    rfl
  case succ k ih =>
    intro x y γ hγ
    rw [functorOnHomOfCoveredPartwise_apply_succ hX h_comm
      (covered_partwise_of_covered k.succ hγ)]
    change (FunctorOnHomOfCovered hX h_comm hγ) = _
    have : 1 < k + 2 := by linarith
    rw [functorOnHomOfCovered_split_comp hX h_comm hγ
      (Fraction.ofPos_pos (lt_trans zero_lt_one this)) (Fraction.ofPos_lt_one this)]
    congr
    apply ih
    exact (covered_split_path (Fraction.ofPos_pos (lt_trans zero_lt_one this))
      (Fraction.ofPos_lt_one this) hγ).2
/--
When a path is partwise covered by `n + 1` paths, applying `Fₙ` to the
two restrictions and composing gives `Fₙ γ`.
-/
lemma functorOnHomOfCoveredPartwise_split {n : ℕ} :
    Π {d : ℕ} (hdn : n > d) {x y : X} {γ : Dipath x y}
      (hγ : covered_partwise hX γ n),
    Fₙ hγ = Fₙ (covered_partwise_first_part_d hX (Nat.succ_lt_succ hdn) hγ) ≫
          Fₙ (covered_partwise_second_part_d hX (Nat.succ_lt_succ hdn) hγ) := by
  induction n
  case zero =>
    intro d hd
    linarith
  case succ n ih_n =>
    intro d hdn
    induction d
    case zero =>
        intro x y γ hγ
        rfl
    case succ d _ =>
      intro x y γ hγ
      rw [functorOnHomOfCoveredPartwise_apply_succ hX h_comm hγ]
      have : n > d := Nat.succ_lt_succ_iff.mp hdn
      rw [ih_n this _]
      rw [functorOnHomOfCoveredPartwise_apply_succ hX h_comm _]
      rw [Category.assoc]
      change F₀ _ ≫ (Fₙ _ ≫ Fₙ _) = F₀ _ ≫ (Fₙ _ ≫ Fₙ _)
      apply eq_of_morphism
      · apply (comp_eqToHom_iff _ _ _).mp
        rw [←functorOnHomOfCovered_cast_right]
        focus
          apply functorOnHomOfCovered_equal
          rw [SplitProperties.firstPart_of_firstPart γ (Nat.succ_lt_succ hdn)
            (Nat.succ_pos d.succ)]
          rfl
      · rw [←Category.assoc]
        apply eq_of_morphism
        · apply (comp_eqToHom_iff _ _ _).mp
          focus
            apply (eqToHom_comp_iff _ _ _).mp
            rw [←functorOnHomOfCoveredPartwise_cast]
            focus
              apply functorOnHomOfCoveredPartwise_equal
              rw [SplitProperties.first_part_of_second_part γ hdn (Nat.succ_pos d)]
              rfl
        · rw [←functorOnHomOfCoveredPartwise_cast_left]
          exact functorOnHomOfCoveredPartwise_equal' hX h_comm
            (SplitProperties.second_part_of_second_part γ (Nat.lt_of_succ_lt_succ hdn))
            (by omega) _ _
/--
If a path can be covered partwise by `(n + 1) ≥ 2` parts, its refinement
to `k * (n + 1)` parts is the composition of covering the first part in
`k` parts and the second part in `k * n` parts.
-/
lemma functorOnHomOfCoveredPartwise_refine_apply (n k : ℕ) {x y : X}
    {γ : Dipath x y} (hγ : covered_partwise hX γ n.succ) :
    Fₙ (covered_partwise_refine hX n.succ k hγ) =
      (Fₙ <| covered_partwise_of_covered k hγ.left) ≫
        (Fₙ <| covered_partwise_refine hX n k hγ.right) := by
  have h₀ : k + 1 < (n+1+1) * (k + 1) := by
    have : n + 1 + 1 > 1 := by linarith
    convert Nat.mul_lt_mul_of_pos_right (this) (Nat.succ_pos k) using 1
    exact (one_mul k.succ).symm
  have h₁ : (n+1+1)*(k+1) - 1 > (k + 1) - 1 :=
    Nat.pred_lt_pred (ne_of_gt (Nat.succ_pos k)) h₀
  have h₂ := FractionEqualities.cancel_common_factor (Nat.succ_pos k)
    (le_of_lt (Nat.succ_lt_succ h₁))
  rw [functorOnHomOfCoveredPartwise_split hX h_comm h₁
    (covered_partwise_refine hX n.succ k hγ)]
  apply eq_of_morphism
  · rw [←functorOnHomOfCoveredPartwise_cast_right hX h_comm _ (congr_arg γ h₂.symm)]
    apply functorOnHomOfCoveredPartwise_equal hX h_comm
    ext t
    rw [Dipath.cast_apply]
    exact SplitProperties.firstPart_eq_of_point_eq _ h₂.symm _
  · rw [←functorOnHomOfCoveredPartwise_cast_left hX h_comm _ (congr_arg γ h₂.symm)]
    apply functorOnHomOfCoveredPartwise_equal' hX h_comm
    · ext t
      rw [Dipath.cast_apply]
      exact SplitProperties.secondPart_eq_of_point_eq _ h₂.symm _
    · simp only [add_tsub_cancel_right, Nat.succ_eq_add_one]
      rw [Nat.succ_mul, Nat.sub_right_comm, Nat.add_sub_cancel]
lemma functorOnHomOfCoveredPartwise_refine {n : ℕ} (k : ℕ) :
    Π {x y : X} {γ : Dipath x y} (hγ_n : covered_partwise hX γ n),
      Fₙ hγ_n = Fₙ (covered_partwise_refine hX n k hγ_n) := by
  induction n
  case zero => apply functorOnHomOfCoveredPartwise_refine_of_covered
  case succ n ih =>
    intros x y γ hγ
    rw [functorOnHomOfCoveredPartwise_refine_apply hX h_comm n k hγ]
    rw [← functorOnHomOfCoveredPartwise_refine_of_covered hX h_comm _ hγ.left]
    rw [functorOnHomOfCoveredPartwise_apply_succ hX h_comm hγ]
    rw [ih hγ.right]
    rfl
lemma functorOnHomOfCoveredPartwise_apply_right_side {x y : X} {γ : Dipath x y}
    {n : ℕ} (hγ : covered_partwise hX γ n.succ) :
    Fₙ hγ = Fₙ (covered_partwise_first_part_end_split hX hγ) ≫
            F₀ (covered_second_part_end_split hX hγ) := by
  rw [functorOnHomOfCoveredPartwise_split hX h_comm (Nat.lt_succ_self n)]
  rw [functorOnHomOfCoveredPartwise_equal' hX h_comm rfl (Nat.sub_self n.succ)]
  rw [functorOnHomOfCoveredPartwise_apply_0]
lemma functorOnHomOfCoveredPartwise_trans_case_0 {x y z : X}
    {γ₁ : Dipath x y} {γ₂ : Dipath y z}
  (hγ₁ : covered_partwise hX γ₁ 0) (hγ₂ : covered_partwise hX γ₂ 0) :
    Fₙ (covered_partwise_trans hγ₁ hγ₂) = (Fₙ hγ₁) ≫ (Fₙ hγ₂) := by
  rw [functorOnHomOfCoveredPartwise_apply_0]
  rw [functorOnHomOfCoveredPartwise_apply_0]
  rw [functorOnHomOfCoveredPartwise_apply_succ]
  rw [functorOnHomOfCoveredPartwise_apply_0]
  rw [functorOnHomOfCovered_equal hX h_comm (SplitProperties.first_part_trans γ₁ γ₂)
    _ ((covered_cast_iff γ₁ hX _ _).mp hγ₁)]
  rw [functorOnHomOfCovered_equal hX h_comm (SplitProperties.second_part_trans γ₁ γ₂)
    _ ((covered_cast_iff γ₂ hX _ _).mp hγ₂)]
  rw [functorOnHomOfCovered_cast_right hX h_comm hγ₁]
  rw [functorOnHomOfCovered_cast_left hX h_comm hγ₂]
  simp
lemma functorOnHomOfCoveredPartwise_trans {n : ℕ} :
    Π {x y z : X} {γ₁ : Dipath x y} {γ₂ : Dipath y z}
      (hγ₁ : covered_partwise hX γ₁ n) (hγ₂ : covered_partwise hX γ₂ n),
      Fₙ (covered_partwise_trans hγ₁ hγ₂) = (Fₙ hγ₁) ≫ (Fₙ hγ₂) := by
  induction n
  case zero =>
    intro x y z γ₁ γ₂ hγ₁ hγ₂
    exact functorOnHomOfCoveredPartwise_trans_case_0 hX h_comm hγ₁ hγ₂
  case succ n ih =>
    intros x y z γ₁ γ₂ hγ₁ hγ₂
    rw [functorOnHomOfCoveredPartwise_apply_succ hX h_comm]
    rw [functorOnHomOfCoveredPartwise_apply_succ hX h_comm hγ₁]
    rw [Category.assoc]
    apply eq_of_morphism
    · rw [←functorOnHomOfCovered_cast_right]
      focus
        apply functorOnHomOfCovered_equal
        ext t
        rw [Dipath.cast_apply]
        exact SplitProperties.trans_first_part γ₁ γ₂ n.succ t
      exact SplitProperties.trans_image_inv_eq_first γ₁ γ₂ n.succ
    · rw [functorOnHomOfCoveredPartwise_apply_right_side hX h_comm hγ₂]
      apply (eqToHom_comp_iff _ _ _).mp
      rw [←functorOnHomOfCoveredPartwise_cast_left hX h_comm _
          (SplitProperties.trans_image_inv_eq_first γ₁ γ₂ n.succ).symm]
      rw [←Category.assoc (Fₙ _) _ _]
      change Fₙ _ =
        (Fₙ hγ₁.right ≫ Fₙ (covered_partwise_first_part_end_split hX hγ₂)) ≫ F₀ _
      rw [←ih hγ₁.right (covered_partwise_first_part_end_split hX hγ₂)]
      have : (n.succ + n.succ).succ - 1 = (n + n).succ.succ := by
        rw [Nat.sub_one]
        rw [Nat.pred_succ (n.succ + n.succ)]
        rw [Nat.succ_add]
        rw [Nat.add_succ]
      erw [functorOnHomOfCoveredPartwise_cast_params hX h_comm rfl this]
      rw [functorOnHomOfCoveredPartwise_apply_right_side hX h_comm _]
      congr 1
      · apply congrArg F_obj
        congr 1
        rw [Dipath.cast_apply]
        exact SplitProperties.second_part_trans_eval_at_end γ₁ γ₂ n
      · apply functorOnHomOfCoveredPartwise_heq_of_ext hX h_comm
        focus
          intro t
          simpa [Dipath.cast_apply] using
            SplitProperties.trans_first_part_of_second_part γ₁ γ₂ n t
        simp
      · apply functorOnHomOfCovered_heq_of_ext hX h_comm
        intro t
        simpa [Dipath.cast_apply] using
          SplitProperties.trans_second_part_second_part γ₁ γ₂ n t
lemma functorOnHomOfCoveredPartwise_unique {n m : ℕ} {γ : Dipath x y}
  (hγ_n : covered_partwise hX γ n) (hγ_m : covered_partwise hX γ m) :
    Fₙ hγ_n = Fₙ hγ_m := by
  rw [functorOnHomOfCoveredPartwise_refine hX h_comm m hγ_n]
  rw [functorOnHomOfCoveredPartwise_refine hX h_comm n hγ_m]
  congr 2
  exact mul_comm _ _

/-
-  ### Define the behaviour on all paths
-/
/-- Map on arbitrary directed paths, choosing a covered subdivision. -/
def FunctorOnHomAux (γ : Dipath x y) : F_obj ⟨x⟩ ⟶ F_obj ⟨y⟩ :=
  Fₙ (Classical.choose_spec (has_subpaths hX X₁_open X₂_open γ))
local notation "Fh_aux" => FunctorOnHomAux hX X₁_open X₂_open h_comm

lemma functorOnHomAux_apply {n : ℕ} {γ : Dipath x y} (hγ : covered_partwise hX γ n) :
    Fh_aux γ = Fₙ hγ := functorOnHomOfCoveredPartwise_unique hX h_comm _ _
lemma functorOnHomAux_refl {x : X} : Fh_aux (Dipath.refl x) = 𝟙 (F_obj ⟨x⟩) := by
  have : covered_partwise hX (Dipath.refl x) 0 := covered_refl x hX
  rw [functorOnHomAux_apply _ _ _ _ this]
  rw [functorOnHomOfCoveredPartwise_apply_0]
  apply functorOnHomOfCovered_refl
lemma functorOnHomAux_cast {x y x' y' : X} (γ : Dipath x y) (hx : x' = x) (hy : y' = y) :
    Fh_aux (γ.cast hx hy) = (eqToHom (by rw [hx])) ≫ Fh_aux γ ≫ (eqToHom (by rw [hy])) := by
  subst_vars
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp]
  apply congr_arg
  ext t
  rfl
@[simp]
lemma functorOnHomAux_cast_heq {x y x' y' : X} (γ : Dipath x y) (hx : x' = x)
    (hy : y' = y) :
    Fh_aux (γ.cast hx hy) ≍ Fh_aux γ := by
  cases hx
  cases hy
  rfl
lemma functorOnHomAux_heq_of_ext {x y x' y' : X} {γ : Dipath x y} {γ' : Dipath x' y'}
    (h : ∀ t, γ t = γ' t) :
    Fh_aux γ ≍ Fh_aux γ' := by
  have hx : x = x' := by simpa using h 0
  have hy : y = y' := by simpa using h 1
  subst hx
  subst hy
  have hγ : γ = γ' := by
    ext t
    exact h t
  subst hγ
  rfl
lemma functorOnHomAux_trans {x y z : X} (γ₁ : Dipath x y) (γ₂ : Dipath y z) :
    Fh_aux (γ₁.trans γ₂) = Fh_aux γ₁ ≫ Fh_aux γ₂ := by
  cases has_subpaths hX X₁_open X₂_open γ₁
  cases has_subpaths hX X₁_open X₂_open γ₂
  rename_i n hn m hm
  have hn' : covered_partwise hX γ₁ ((n + 1) * (m + 1) - 1) := covered_partwise_refine hX n m hn
  have hm' : covered_partwise hX γ₂ ((n + 1) * (m + 1) - 1) :=
    (mul_comm (m + 1) _) ▸ covered_partwise_refine hX m n hm
  rw [functorOnHomAux_apply hX X₁_open X₂_open h_comm hn']
  rw [functorOnHomAux_apply hX X₁_open X₂_open h_comm hm']
  rw [functorOnHomAux_apply hX X₁_open X₂_open h_comm (covered_partwise_trans hn' hm')]
  rw [functorOnHomOfCoveredPartwise_trans]
lemma functorOnHomAux_split_of_covered_partwise {x y : X} {γ : Dipath x y}
    {n : ℕ} (hγ : covered_partwise hX γ n.succ) :
    Fh_aux γ =
      Fh_aux (SplitDipath.FirstPart γ
        (Fraction (Nat.succ_pos _) (Nat.succ_le_succ (Nat.zero_le n.succ)))) ≫
      Fh_aux (SplitDipath.SecondPart γ
        (Fraction (Nat.succ_pos _) (Nat.succ_le_succ (Nat.zero_le n.succ)))) := by
  -- Rewrite L.H.S.
  rw [functorOnHomAux_apply hX _ _ h_comm hγ]
  rw [functorOnHomOfCoveredPartwise_apply_succ hX h_comm hγ]
  --Rewrite R.H.S.
  have : covered_partwise hX (SplitDipath.FirstPart γ _) 0 := hγ.left
  rw [functorOnHomAux_apply hX _ _ h_comm this]
  rw [functorOnHomOfCoveredPartwise_apply_0]
  rw [functorOnHomAux_apply hX _ _ h_comm hγ.right]
lemma functorOnHomAux_of_covered_dihomotopic {x y : X} {γ γ' : Dipath x y} {F : Dihomotopy γ γ'}
  (hF : Dipath.Dihomotopy.covered hX F) :
    Fh_aux γ = Fh_aux γ' := by
  have : covered_partwise hX γ 0 := Dipath.Dihomotopy.covered_left_of_covered hF
  rw [functorOnHomAux_apply _ _ _ _ this]
  rw [functorOnHomOfCoveredPartwise_apply_0]
  have : covered_partwise hX γ' 0 := Dipath.Dihomotopy.covered_right_of_covered hF
  rw [functorOnHomAux_apply _ _ _ _ this]
  rw [functorOnHomOfCoveredPartwise_apply_0]
  exact functorOnHomOfCovered_dihomotopic hX h_comm hF
lemma functorOnHomAux_of_homotopic_dimaps_0 {f g : D(I,X)} {H : DirectedMap.Dihomotopy f g}
  (hcov : DirectedMap.Dihomotopy.coveredPartwise hX H 0 0) :
    Fh_aux (Dipath.of_directedMap f) ≫ Fh_aux (H.eval_at_right 1) =
    Fh_aux (H.eval_at_right 0) ≫ Fh_aux (Dipath.of_directedMap g) := by
  let Γ := DihomToPathDihom.dihom_to_path_dihom H
  have Γ_cov : Dipath.Dihomotopy.covered hX Γ := by
    unfold Dipath.Dihomotopy.covered
    cases DirectedMap.Dihomotopy.covered_of_coveredPartwise hcov
    case inl h =>
      left
      exact subset_trans (DihomToPathDihom.dihom_to_path_dihom_range _) h
    case inr h =>
      right
      exact subset_trans (DihomToPathDihom.dihom_to_path_dihom_range _) h
  calc Fh_aux (Dipath.of_directedMap f) ≫ Fh_aux (H.eval_at_right 1)
    _ = (𝟙 (F_obj ⟨f 0⟩) ≫ Fh_aux (of_directedMap f)) ≫ Fh_aux (H.eval_at_right 1)
          := by rw [Category.id_comp]
    _ = (Fh_aux (Dipath.refl (f 0)) ≫ Fh_aux (of_directedMap f)) ≫ Fh_aux (H.eval_at_right 1)
          := by rw [functorOnHomAux_refl]
    _ = Fh_aux ((Dipath.refl (f 0)).trans (of_directedMap f)) ≫ Fh_aux (H.eval_at_right 1)
          := by rw [functorOnHomAux_trans]
    _ = Fh_aux (((Dipath.refl (f 0)).trans (of_directedMap f)).trans (H.eval_at_right 1))
          := by rw [←functorOnHomAux_trans]
    _ = Fh_aux (((H.eval_at_right 0).trans (of_directedMap g)).trans (refl (g 1)))
          := functorOnHomAux_of_covered_dihomotopic hX X₁_open X₂_open h_comm Γ_cov
    _ = Fh_aux ((H.eval_at_right 0).trans (of_directedMap g)) ≫ Fh_aux (refl (g 1))
          := by rw [functorOnHomAux_trans]
    _ = Fh_aux ((H.eval_at_right 0).trans (of_directedMap g)) ≫ 𝟙 (F_obj ⟨g 1⟩)
          := by rw [functorOnHomAux_refl]
    _ = Fh_aux ((H.eval_at_right 0).trans (of_directedMap g))
          := by rw [Category.comp_id]
    _ = Fh_aux (H.eval_at_right 0) ≫ Fh_aux (Dipath.of_directedMap g)
          := by rw [functorOnHomAux_trans]
lemma functorOnHomAux_of_homotopic_dimaps {m : ℕ} :
    Π {f g : D(I,X)} {H : DirectedMap.Dihomotopy f g}
      (_ : DirectedMap.Dihomotopy.coveredPartwise hX H 0 m),
      Fh_aux (Dipath.of_directedMap f) ≫ Fh_aux (H.eval_at_right 1) =
      Fh_aux (H.eval_at_right 0) ≫ Fh_aux (Dipath.of_directedMap g) := by
  induction m
  case zero => exact fun hcov => functorOnHomAux_of_homotopic_dimaps_0 _ _ _ _ hcov
  case succ m ih =>
    intro f g H hcov
    have f_cov : covered_partwise hX (Dipath.of_directedMap f) m.succ :=
      DirectedMap.Dihomotopy.path_covered_partiwse_of_dihomotopy_coveredPartwise_left hcov
    have g_cov : covered_partwise hX (Dipath.of_directedMap g) m.succ :=
      DirectedMap.Dihomotopy.path_covered_partiwse_of_dihomotopy_coveredPartwise_right hcov
    -- Split at 1/(m.succ + 1)
    let T := Fraction.ofPos (Nat.succ_pos m.succ)
    let f₁ := (SplitDipath.FirstPart (Dipath.of_directedMap f) T)
    let f₂ := (SplitDipath.SecondPart (Dipath.of_directedMap f) T)
    let g₁ := (SplitDipath.FirstPart (Dipath.of_directedMap g) T)
    let g₂ := (SplitDipath.SecondPart (Dipath.of_directedMap g) T)
    have h₁ : Fh_aux f₂ ≫ Fh_aux (H.eval_at_right 1) =
        Fh_aux (H.eval_at_right T) ≫ Fh_aux g₂ := by
      have := ih (DirectedMap.Dihomotopy.coveredPartwise_second_hpart hcov)
      rw [SplitDihomotopy.sph_eval_0] at this
      rw [SplitDihomotopy.sph_eval_1] at this
      rw [Dipath.dipath_of_directed_map_of_to_dimap] at this
      rw [Dipath.dipath_of_directed_map_of_to_dimap] at this
      convert this using 1
      · simp [T]
      · apply heq_comp
        · apply congrArg F_obj
          change (⟨(of_directedMap f) T⟩ : FundamentalCategory X) =
            ⟨(SplitDipath.SecondPart (of_directedMap f)
              (Fraction.ofPos (Nat.succ_pos m.succ))).toDirectedMap 0⟩
          ext
          simp [T, Dipath.of_directedMap]
        · apply congrArg F_obj
          change (⟨f 1⟩ : FundamentalCategory X) =
            ⟨(SplitDipath.SecondPart (of_directedMap f)
              (Fraction.ofPos (Nat.succ_pos m.succ))).toDirectedMap 1⟩
          ext
          simp [Dipath.of_directedMap]
        · apply congrArg F_obj
          change (⟨g 1⟩ : FundamentalCategory X) =
            ⟨(SplitDipath.SecondPart (of_directedMap g)
              (Fraction.ofPos (Nat.succ_pos m.succ))).toDirectedMap 1⟩
          ext
          simp [Dipath.of_directedMap]
        · simpa [f₂, T] using (functorOnHomAux_cast_heq hX X₁_open X₂_open h_comm
            (SplitDipath.SecondPart (Dipath.of_directedMap f)
              (Fraction.ofPos (Nat.succ_pos m.succ))) _ _).symm
        · simpa using (functorOnHomAux_cast_heq hX X₁_open X₂_open h_comm
            (H.eval_at_right 1) _ _).symm
      · apply heq_comp
        · apply congrArg F_obj
          change (⟨f T⟩ : FundamentalCategory X) =
            ⟨(SplitDipath.SecondPart (of_directedMap f)
              (Fraction.ofPos (Nat.succ_pos m.succ))).toDirectedMap 0⟩
          ext
          simp [T, Dipath.of_directedMap]
        · apply congrArg F_obj
          change (⟨g T⟩ : FundamentalCategory X) =
            ⟨(SplitDipath.SecondPart (of_directedMap g)
              (Fraction.ofPos (Nat.succ_pos m.succ))).toDirectedMap 0⟩
          ext
          simp [T, Dipath.of_directedMap]
        · apply congrArg F_obj
          change (⟨g 1⟩ : FundamentalCategory X) =
            ⟨(SplitDipath.SecondPart (of_directedMap g)
              (Fraction.ofPos (Nat.succ_pos m.succ))).toDirectedMap 1⟩
          ext
          simp [Dipath.of_directedMap]
        · simpa [T] using (functorOnHomAux_cast_heq hX X₁_open X₂_open h_comm
            (H.eval_at_right (Fraction.ofPos (Nat.succ_pos m.succ))) _ _).symm
        · simpa [g₂, T] using (functorOnHomAux_cast_heq hX X₁_open X₂_open h_comm
            (SplitDipath.SecondPart (Dipath.of_directedMap g)
              (Fraction.ofPos (Nat.succ_pos m.succ))) _ _).symm
    have h₂ : Fh_aux f₁ ≫ Fh_aux (H.eval_at_right T) =
        Fh_aux (H.eval_at_right 0) ≫ Fh_aux g₁ := by
      have := functorOnHomAux_of_homotopic_dimaps_0 hX X₁_open X₂_open h_comm
            (DirectedMap.Dihomotopy.coveredPartwise_first_hpart hcov)
      rw [SplitDihomotopy.fph_eval_0] at this
      rw [SplitDihomotopy.fph_eval_1] at this
      rw [Dipath.dipath_of_directed_map_of_to_dimap] at this
      rw [Dipath.dipath_of_directed_map_of_to_dimap] at this
      convert this using 1
      · simp [T, Dipath.of_directedMap]
      · apply heq_comp
        · apply congrArg F_obj
          change (⟨f 0⟩ : FundamentalCategory X) =
            ⟨(SplitDipath.FirstPart (of_directedMap f)
              (Fraction.ofPos (Nat.succ_pos m.succ))).toDirectedMap 0⟩
          ext
          simp [Dipath.of_directedMap]
        · apply congrArg F_obj
          change (⟨f T⟩ : FundamentalCategory X) =
            ⟨(SplitDipath.FirstPart (of_directedMap f)
              (Fraction.ofPos (Nat.succ_pos m.succ))).toDirectedMap 1⟩
          ext
          simp [T, Dipath.of_directedMap]
        · apply congrArg F_obj
          change (⟨g T⟩ : FundamentalCategory X) =
            ⟨(SplitDipath.FirstPart (of_directedMap g)
              (Fraction.ofPos (Nat.succ_pos m.succ))).toDirectedMap 1⟩
          ext
          simp [T, Dipath.of_directedMap]
        · apply functorOnHomAux_heq_of_ext hX X₁_open X₂_open h_comm
          intro t
          change (SplitDipath.FirstPart (Dipath.of_directedMap f)
            (Fraction.ofPos (Nat.succ_pos m.succ))) t =
            ((SplitDipath.FirstPart (Dipath.of_directedMap f)
              (Fraction.ofPos (Nat.succ_pos m.succ))).cast _ _) t
          rw [Dipath.cast_apply]
        · apply functorOnHomAux_heq_of_ext hX X₁_open X₂_open h_comm
          intro t
          change (H.eval_at_right (Fraction.ofPos (Nat.succ_pos m.succ))) t =
            ((H.eval_at_right (Fraction.ofPos (Nat.succ_pos m.succ))).cast _ _) t
          rw [Dipath.cast_apply]
      · apply heq_comp
        · apply congrArg F_obj
          change (⟨f 0⟩ : FundamentalCategory X) =
            ⟨(SplitDipath.FirstPart (of_directedMap f)
              (Fraction.ofPos (Nat.succ_pos m.succ))).toDirectedMap 0⟩
          ext
          simp [Dipath.of_directedMap]
        · apply congrArg F_obj
          change (⟨g 0⟩ : FundamentalCategory X) =
            ⟨(SplitDipath.FirstPart (of_directedMap g)
              (Fraction.ofPos (Nat.succ_pos m.succ))).toDirectedMap 0⟩
          ext
          simp [Dipath.of_directedMap]
        · apply congrArg F_obj
          change (⟨g T⟩ : FundamentalCategory X) =
            ⟨(SplitDipath.FirstPart (of_directedMap g)
              (Fraction.ofPos (Nat.succ_pos m.succ))).toDirectedMap 1⟩
          ext
          simp [T, Dipath.of_directedMap]
        · apply functorOnHomAux_heq_of_ext hX X₁_open X₂_open h_comm
          intro t
          change (H.eval_at_right 0) t = ((H.eval_at_right 0).cast _ _) t
          rw [Dipath.cast_apply]
        · apply functorOnHomAux_heq_of_ext hX X₁_open X₂_open h_comm
          intro t
          change (SplitDipath.FirstPart (Dipath.of_directedMap g)
            (Fraction.ofPos (Nat.succ_pos m.succ))) t =
            ((SplitDipath.FirstPart (Dipath.of_directedMap g)
              (Fraction.ofPos (Nat.succ_pos m.succ))).cast _ _) t
          rw [Dipath.cast_apply]
    calc Fh_aux (Dipath.of_directedMap f) ≫ Fh_aux (H.eval_at_right 1)
      _ = (Fh_aux f₁ ≫ Fh_aux f₂) ≫ Fh_aux (H.eval_at_right 1)
            := by rw [functorOnHomAux_split_of_covered_partwise _ _ _ _ f_cov]
      _ = Fh_aux f₁ ≫ (Fh_aux f₂ ≫ Fh_aux (H.eval_at_right 1))
            := by rw [Category.assoc]
      _ = Fh_aux f₁ ≫ (Fh_aux (H.eval_at_right T) ≫ Fh_aux g₂)
            := by simpa only [Category.assoc] using congrArg (fun q => Fh_aux f₁ ≫ q) h₁
      _ = (Fh_aux f₁ ≫ Fh_aux (H.eval_at_right T)) ≫ Fh_aux g₂
            := by rw [Category.assoc]
      _ = (Fh_aux (H.eval_at_right 0) ≫ Fh_aux g₁) ≫ Fh_aux g₂
            := by exact congrArg (fun q => q ≫ Fh_aux g₂) h₂
      _ = Fh_aux (H.eval_at_right 0) ≫ (Fh_aux g₁ ≫ Fh_aux g₂)
            := by rw [Category.assoc]
      _ = Fh_aux (H.eval_at_right 0) ≫ Fh_aux (Dipath.of_directedMap g)
            := by rw [functorOnHomAux_split_of_covered_partwise _ _ _ _ g_cov]
lemma functorOnHomAux_of_covered_dihomotopic_zero_m {m : ℕ} {x y : X} {γ γ' : Dipath x y}
  (h : Dipath.Dihomotopy.dihomotopicCovered hX γ γ' 0 m) :
    Fh_aux γ = Fh_aux γ' := by
  cases h
  rename_i G HG
  have h₁ : Fh_aux ((G.eval_at_right 0)) = (eqToHom (by simp)) ≫
            (𝟙 (F_obj ⟨x⟩)) ≫ (eqToHom (by simp)) := by
      have : G.eval_at_right 0 = (Dipath.refl x).cast γ.source γ'.source := by
        ext t
        change G (t, 0) = x
        simp
      rw [this]
      erw [functorOnHomAux_cast hX X₁_open X₂_open h_comm]
      rw [functorOnHomAux_refl]
  have h₂ : Fh_aux ((G.eval_at_right 1)) = (eqToHom (by simp)) ≫
            (𝟙 (F_obj ⟨y⟩)) ≫ (eqToHom (by simp)) := by
      have : G.eval_at_right 1 = (Dipath.refl y).cast γ.target γ'.target := by
        ext t
        change G (t, 1) = y
        simp
      rw [this]
      erw [functorOnHomAux_cast hX X₁_open X₂_open h_comm]
      rw [functorOnHomAux_refl]
  have := functorOnHomAux_of_homotopic_dimaps hX X₁_open X₂_open h_comm HG
  rw [h₁, h₂] at this
  rw [Dipath.dipath_of_directed_map_of_to_dimap] at this
  rw [Dipath.dipath_of_directed_map_of_to_dimap] at this
  erw [functorOnHomAux_cast hX X₁_open X₂_open h_comm γ] at this
  erw [functorOnHomAux_cast hX X₁_open X₂_open h_comm γ'] at this
  simp only [coe_toDirectedMap, Dipath.target, eqToHom_naturality, Category.comp_id,
    eqToHom_trans, Category.assoc, Dipath.source, eqToHom_trans_assoc] at this
  have := (comp_eqToHom_iff _ _ _).mp ((eqToHom_comp_iff _ _ _).mp this)
  simpa [Category.assoc] using this
lemma functorOnHomAux_of_partwise_covered_dihomotopic :
    Π {n m : ℕ} {x y : X} {γ γ' : Dipath x y}
      (_ : Dipath.Dihomotopy.dihomotopicCovered hX γ γ' n m),
    Fh_aux γ = Fh_aux γ' := by
  intro n m
  induction n
  case zero =>
    intro x y γ γ' h
    exact functorOnHomAux_of_covered_dihomotopic_zero_m hX X₁_open X₂_open h_comm h
  case succ n ih =>
    rintro x y γ γ' ⟨F, hF⟩
    have ⟨h₁, h₂⟩ := Dipath.Dihomotopy.dihomotopicCovered_split hX hF
    rw [functorOnHomAux_of_covered_dihomotopic_zero_m hX X₁_open X₂_open h_comm h₁]
    exact ih h₂
lemma functorOnHomAux_of_pre_dihomotopic {γ γ' : Dipath x y} (h : γ.PreDihomotopic γ') :
    Fh_aux γ = Fh_aux γ' := by
  rcases Dipath.Dihomotopy.dihomotopicCovered_exists_of_preDihomotopic
      hX h X₁_open X₂_open with
    ⟨n, m, h⟩
  exact functorOnHomAux_of_partwise_covered_dihomotopic hX X₁_open X₂_open h_comm h
lemma functorOnHomAux_of_dihomotopic (γ γ' : Dipath x y) (h : γ.Dihomotopic γ') :
    Fh_aux γ = Fh_aux γ' :=
  Relation.EqvGen.rec
    (fun _ _ h => functorOnHomAux_of_pre_dihomotopic _ _ _ _ h)
    (fun _ => rfl)
    (fun _ _ _ h => h.symm)
    (fun _ _ _ _ _ h₁ h₂ => Eq.trans h₁ h₂)
  h

/-
-  ### Define the behaviour on quotient of paths
-/
/-- Map on morphisms of the directed fundamental category. -/
def FunctorOnHom {x y : dπₓ X} (γ : x ⟶ y) : F_obj x ⟶ F_obj y :=
 Quotient.liftOn γ Fh_aux (functorOnHomAux_of_dihomotopic hX X₁_open X₂_open h_comm)
local notation "F_hom" => FunctorOnHom hX X₁_open X₂_open h_comm
lemma functorOnHom_apply (γ : Dipath x y) :
  F_hom ⟦γ⟧ = Fh_aux γ := rfl
lemma functorOnHom_trans {x y z : X} (γ₁ : Dipath x y) (γ₂ : Dipath y z) :
    F_hom ⟦γ₁.trans γ₂⟧ = F_hom ⟦γ₁⟧ ≫ F_hom ⟦γ₂⟧ := by
  change Fh_aux (γ₁.trans γ₂) = Fh_aux γ₁ ≫ Fh_aux γ₂
  exact functorOnHomAux_trans hX X₁_open X₂_open h_comm γ₁ γ₂
lemma functorOnHom_id (x : dπₓ X) : F_hom (𝟙 x) = 𝟙 (F_obj x) := by
  change Fh_aux (Dipath.refl x.as) = 𝟙 (F_obj x)
  apply functorOnHomAux_refl
lemma functorOnHom_comp_path {x y z : X} (γ₁ : Dipath x y) (γ₂ : Dipath y z) :
    F_hom (⟦γ₁⟧ ≫ ⟦γ₂⟧) = F_hom ⟦γ₁⟧ ≫ F_hom ⟦γ₂⟧ := by
  change Fh_aux (γ₁.trans γ₂) = Fh_aux γ₁ ≫ Fh_aux γ₂
  exact functorOnHom_trans hX X₁_open X₂_open h_comm γ₁ γ₂
lemma functorOnHom_comp {x y z : dπₓ X} (γ₁ : x ⟶ y) (γ₂ : y ⟶ z) :
    F_hom (γ₁ ≫ γ₂) = F_hom γ₁ ≫ F_hom γ₂ := by
  have := functorOnHom_comp_path hX X₁_open X₂_open h_comm (γ₁.out) (γ₂.out)
  rw [Quotient.out_eq] at this
  rw [Quotient.out_eq] at this
  exact this
/-
  ## Define the functor F : (dπₓ X) ⟶ C
-/
/-- The pushout functor from the directed fundamental category of `X` to `C`. -/
def Functor : (dπₓ X) ⥤ C where
  obj := F_obj
  map γ := F_hom γ
  map_id x := functorOnHom_id hX X₁_open X₂_open h_comm x
  map_comp γ₁ γ₂ := functorOnHom_comp hX X₁_open X₂_open h_comm γ₁ γ₂
local notation "F" => Functor hX X₁_open X₂_open h_comm
lemma functorObj_def {x : dπₓ X} : (F).obj x = F_obj x := rfl
lemma functorHom_def {x y : dπₓ X} (f : x ⟶ y) : (F).map f = F_hom f := rfl
lemma functor_comp_left_object (x : X₁) :
    (F).obj ((dπₘ j₁).obj ⟨x⟩) = F₁.obj ⟨x⟩ := by
  change F_obj ⟨j₁ _⟩ = _
  rw [←functorOnObj_apply_one hX h_comm]
  · congr 1
  · exact x.property
lemma functor_comp_left_dipath {x y : X₁} (γ : Dipath x y) : F_hom ((dπₘ j₁).map ⟦γ⟧) =
    (eqToHom (functor_comp_left_object hX X₁_open X₂_open h_comm x)) ≫ (F₁.map ⟦γ⟧) ≫
    (eqToHom (functor_comp_left_object hX X₁_open X₂_open h_comm y).symm)
     := by
  rw [subtype_path_class_eq_map]
  change Fh_aux (γ.map (DirectedSubtypeInclusion X₁)) = _
  have h₁ : range (γ.map (DirectedSubtypeInclusion X₁)) ⊆ X₁ :=
    range_dipath_map_inclusion γ
  have h₂ : covered_partwise hX (γ.map (DirectedSubtypeInclusion X₁)) 0 := Or.inl h₁
  rw [functorOnHomAux_apply hX X₁_open X₂_open h_comm h₂]
  rw [functorOnHomOfCoveredPartwise_apply_0]
  rw [functorOnHomOfCovered_apply_left' hX h_comm h₁]
  rw [FunctorOnHomOfCoveredAux₁]
  rw [subtypeDipath_of_included_dipath_eq]
  erw [functor_cast F₁ γ]
  rfl
/- Shpw that the two obtained triangles commute -/
lemma functor_comp_left : (dπₘ j₁) ⋙ F = F₁ := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro x
    exact functor_comp_left_object hX X₁_open X₂_open h_comm x.as
  · intros x y f
    rw [←Quotient.out_eq f]
    simpa using functor_comp_left_dipath hX X₁_open X₂_open h_comm f.out
lemma functor_comp_right_object (x : X₂) :
    (F).obj ((dπₘ j₂).obj ⟨x⟩) = F₂.obj ⟨x⟩ := by
  change F_obj ⟨j₂ _⟩ = _
  rw [←functorOnObj_apply_two hX h_comm]
  · congr 1
  · exact x.property
lemma functor_comp_right_dipath {x y : X₂} (γ : Dipath x y) :
    F_hom ((dπₘ j₂).map ⟦γ⟧) =
    (eqToHom (functor_comp_right_object hX X₁_open X₂_open h_comm x)) ≫
      (F₂.map ⟦γ⟧) ≫
    (eqToHom (functor_comp_right_object hX X₁_open X₂_open h_comm y).symm)
     := by
  rw [subtype_path_class_eq_map]
  change Fh_aux (γ.map (DirectedSubtypeInclusion X₂)) = _
  have h₁ : range (γ.map (DirectedSubtypeInclusion X₂)) ⊆ X₂ :=
    range_dipath_map_inclusion γ
  have h₂ : covered_partwise hX (γ.map (DirectedSubtypeInclusion X₂)) 0 := Or.inr h₁
  rw [functorOnHomAux_apply hX X₁_open X₂_open h_comm h₂]
  rw [functorOnHomOfCoveredPartwise_apply_0]
  rw [functorOnHomOfCovered_apply_right' hX h_comm h₁]
  rw [FunctorOnHomOfCoveredAux₂]
  rw [subtypeDipath_of_included_dipath_eq]
  erw [functor_cast F₂ γ]
  rfl
lemma functor_comp_right : (dπₘ j₂) ⋙ F = F₂ := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro x
    exact functor_comp_right_object hX X₁_open X₂_open h_comm x.as
  · intros x y f
    rw [←Quotient.out_eq f]
    simpa using functor_comp_right_dipath hX X₁_open X₂_open h_comm f.out
lemma functor_uniq_aux_obj (F' : (dπₓ X) ⥤ C) (h₁ : (dπₘ j₁) ⋙ F' = F₁)
    (h₂ : (dπₘ j₂) ⋙ F' = F₂) (x : X) :
    F'.obj ⟨x⟩ = (F).obj ⟨x⟩ := by
  rw [functorObj_def]
  cases ((Set.mem_union x X₁ X₂).mp (Filter.mem_top.mpr hX x))
  case inl hx₁ =>
    rw [←functorOnObj_apply_one hX h_comm hx₁]
    rw [obj_eq_obj_of_eq h₁.symm]
    change F'.obj _ = F'.obj _
    apply congrArg
    rfl
  case inr hx₂ =>
    rw [←functorOnObj_apply_two hX h_comm hx₂]
    rw [obj_eq_obj_of_eq h₂.symm]
    change F'.obj _ = F'.obj _
    apply congrArg
    rfl
lemma functor_uniq_of_covered (F' : (dπₓ X) ⥤ C) (h₁ : (dπₘ j₁) ⋙ F' = F₁)
  (h₂ : (dπₘ j₂) ⋙ F' = F₂)
  {x y : X} {γ : Dipath x y} (hγ : covered hX γ) :
    F'.map ⟦γ⟧ =
      (eqToHom (functor_uniq_aux_obj hX X₁_open X₂_open h_comm F' h₁ h₂ x)) ≫
      (F).map ⟦γ⟧ ≫
      (eqToHom (functor_uniq_aux_obj hX X₁_open X₂_open h_comm F' h₁ h₂ y).symm) := by
  rw [functorHom_def]
  rw [functorOnHom_apply]
  have : covered_partwise hX γ 0 := hγ
  rw [functorOnHomAux_apply _ _ _ _ this]
  rw [functorOnHomOfCoveredPartwise_apply_0 _ _ this]
  cases hγ
  case inl hγ =>
    rw [functorOnHomOfCovered_apply_left' _ _ hγ]
    unfold FunctorOnHomOfCoveredAux₁
    refine Eq.trans (congrArg F'.map (map_subtypeDipath_eq γ hγ)).symm ?_
    change ((dπₘ j₁) ⋙ F').map ⟦SubtypeDipath γ hγ⟧ = _
    rw [map_eq_map_of_eq h₁]
    simp [functorObj_def]
    rfl
  case inr hγ =>
    rw [functorOnHomOfCovered_apply_right' _ _ hγ]
    unfold FunctorOnHomOfCoveredAux₂
    refine Eq.trans (congrArg F'.map (map_subtypeDipath_eq γ hγ)).symm ?_
    change ((dπₘ j₂) ⋙ F').map ⟦SubtypeDipath γ hγ⟧ = _
    rw [map_eq_map_of_eq h₂]
    simp [functorObj_def]
    rfl
lemma functor_uniq_aux_map (F' : (dπₓ X) ⥤ C) (h₁ : (dπₘ j₁) ⋙ F' = F₁)
    (h₂ : (dπₘ j₂) ⋙ F' = F₂) {n : ℕ} :
    Π {x y : X} {γ : Dipath x y} (_ : covered_partwise hX γ n), F'.map ⟦γ⟧ =
      (eqToHom (functor_uniq_aux_obj hX X₁_open X₂_open h_comm F' h₁ h₂ x)) ≫
        (F).map ⟦γ⟧
        ≫ (eqToHom (functor_uniq_aux_obj hX X₁_open X₂_open h_comm F' h₁ h₂ y).symm) := by
  induction n
  case zero =>
    intros x y γ hγ
    exact functor_uniq_of_covered _ _ _ _ F' h₁ h₂ hγ
  case succ n ih =>
    intros x y γ hγ
    let T := Fraction.ofPos (Nat.succ_pos n.succ) -- T = 1/(n+1+1)
    have hT₀ : 0 < T := Fraction.ofPos_pos (Nat.succ_pos n.succ)
    have hT₁ : T < 1 := Fraction.ofPos_lt_one (Nat.succ_lt_succ (Nat.succ_pos n))
    rw [SplitDipath.first_trans_second_reparam_eq_self γ hT₀ hT₁]
    rw [Dipath.Dihomotopic.quot_reparam]
    rw [Dipath.Dihomotopic.comp_lift]
    change F'.map ((⟦SplitDipath.FirstPart γ T⟧ :
        (⟨x⟩ : dπₓ X) ⟶ (⟨γ T⟩ : dπₓ X)) ≫
        ⟦SplitDipath.SecondPart γ T⟧) =
      eqToHom _ ≫ (F).map ((⟦SplitDipath.FirstPart γ T⟧ :
        (⟨x⟩ : dπₓ X) ⟶ (⟨γ T⟩ : dπₓ X)) ≫ ⟦SplitDipath.SecondPart γ T⟧) ≫
      eqToHom _
    rw [CategoryTheory.Functor.map_comp]
    rw [CategoryTheory.Functor.map_comp]
    rw [functor_uniq_of_covered hX X₁_open X₂_open h_comm  F' h₁ h₂ hγ.left]
    rw [ih hγ.right]
    simp [T]
lemma functor_uniq (F' : (dπₓ X) ⥤ C) (h₁ : (dπₘ j₁) ⋙ F' = F₁)
    (h₂ : (dπₘ j₂) ⋙ F' = F₂) : F' = F := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro x
    exact functor_uniq_aux_obj hX X₁_open X₂_open h_comm F' h₁ h₂ x.as
  · intros x y f
    rw [←Quotient.out_eq f]
    cases has_subpaths hX X₁_open X₂_open (Quotient.out f)
    rename_i n hn
    exact functor_uniq_aux_map hX X₁_open X₂_open h_comm F' h₁ h₂ hn
end PushoutFunctor
/--
The Van Kampen Theorem: the fundamental category functor `dπ` induces a
pushout in the category of categories.
-/
theorem directed_van_kampen (X₁_open : IsOpen X₁) (X₂_open : IsOpen X₂)
    (hX : X₁ ∪ X₂ = Set.univ) :
    IsPushout
      (FundamentalCategory.fundamentalCategoryFunctor.map i₁)
      (FundamentalCategory.fundamentalCategoryFunctor.map i₂)
      (FundamentalCategory.fundamentalCategoryFunctor.map j₁)
      (FundamentalCategory.fundamentalCategoryFunctor.map j₂) := by
  apply PushoutAlternative.isPushout_alternative
  · rw [←Functor.map_comp]
    rw [←Functor.map_comp]
    apply congrArg FundamentalCategory.fundamentalCategoryFunctor.map
    ext x
    rfl
  intros C F₁ F₂ h_comm
  have h_comm' : (dπₘ i₁) ⋙ F₁.toFunctor = (dπₘ i₂) ⋙ F₂.toFunctor :=
    congrArg CategoryTheory.Cat.Hom.toFunctor h_comm
  use (PushoutFunctor.Functor hX X₁_open X₂_open h_comm').toCatHom
  constructor
  constructor
  · apply CategoryTheory.Cat.Hom.ext
    exact PushoutFunctor.functor_comp_left hX X₁_open X₂_open h_comm'
  · apply CategoryTheory.Cat.Hom.ext
    exact PushoutFunctor.functor_comp_right hX X₁_open X₂_open h_comm'
  · rintro F' ⟨h₁, h₂⟩
    apply CategoryTheory.Cat.Hom.ext
    exact PushoutFunctor.functor_uniq hX X₁_open X₂_open h_comm' F'.toFunctor
      (congrArg CategoryTheory.Cat.Hom.toFunctor h₁)
      (congrArg CategoryTheory.Cat.Hom.toFunctor h₂)
end DirectedVanKampen
