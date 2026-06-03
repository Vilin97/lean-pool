/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
import LeanPool.DirectedTopologyLean4.FundamentalCategory

/-!
# LeanPool.DirectedTopologyLean4.DipathSubtype
-/

/-
  This file contains properties of dipaths contained in directed subspaces of a directed space.
  In particular, properties about their equivalence classes in the fundamental category.
-/

open Set
open scoped FundamentalCategory unitInterval

attribute [local instance] Dipath.Dihomotopic.setoid

namespace DiSubtype

variable {X : dTopCat} {X₀ : Set X}

lemma subtypeHom_eq_coe (x : X₀) : (dTopCat.DirectedSubtypeHom X₀) x = (x : X) := rfl

lemma range_dipath_map_inclusion {x y : X₀} (γ : Dipath x y)
    : range (γ.map (DirectedSubtypeInclusion X₀)) ⊆ X₀ := by
  rintro z ⟨t, ht⟩
  rw [←ht]
  change (dTopCat.DirectedSubtypeHom X₀) (γ t) ∈ X₀
  rw [subtypeHom_eq_coe]
  exact Subtype.mem (γ t)

lemma subtype_path_class_eq_map {x y : X₀} (γ : Dipath x y) :
    (dπₘ (dTopCat.DirectedSubtypeHom X₀)).map ⟦γ⟧ = ⟦(γ.map (DirectedSubtypeInclusion X₀))⟧ :=
  rfl


variable {x y z : X}

lemma source_elt_of_image_subset {γ : Dipath x y} (hγ : range γ ⊆ X₀) : x ∈ X₀
    := γ.source ▸ (hγ (mem_range_self 0))
lemma target_elt_of_image_subset {γ : Dipath x y} (hγ : range γ ⊆ X₀) : y ∈ X₀
    := γ.target ▸ (hγ (mem_range_self 1))

/-- Lift a path whose range lies inside `X₀` to a path in the subtype `X₀`. -/
def SubtypePath {γ : Dipath x y} (hγ : range γ ⊆ X₀) :
    Path (⟨x, source_elt_of_image_subset hγ⟩ : X₀) ⟨y, target_elt_of_image_subset hγ⟩ where
  toFun := fun t => ⟨γ t, hγ (mem_range_self t)⟩
  source' := by simp
  target' := by simp

/-- Lift a dipath whose range lies inside `X₀` to a dipath in the subtype `X₀`. -/
def SubtypeDipath (γ : Dipath x y) (hγ : range γ ⊆ X₀) :
    Dipath (⟨x, source_elt_of_image_subset hγ⟩ : X₀) ⟨y, target_elt_of_image_subset hγ⟩ where
  toPath := SubtypePath hγ
  dipath_toPath := γ.dipath_toPath

lemma map_subtypeDipath_eq {x y : X} (γ : Dipath x y) (hγ : range γ ⊆ X₀) :
    (dπₘ (dTopCat.DirectedSubtypeHom X₀)).map ⟦SubtypeDipath γ hγ⟧ = ⟦γ⟧ := by
  rw [subtype_path_class_eq_map]
  congr 1

lemma subtypeDipath_of_included_dipath_eq {x y : X₀} (γ : Dipath x y) :
    SubtypeDipath (γ.map (DirectedSubtypeInclusion X₀)) (range_dipath_map_inclusion γ) =
    γ.cast (by ext; rw [←subtypeHom_eq_coe x]; rfl) (by ext; rw [←subtypeHom_eq_coe y]; rfl) := by
  ext t
  rfl

lemma range_refl_subset_of_mem {x : X} (hx : x ∈ X₀) : range (Dipath.refl x) ⊆ X₀ := by
  rw [Dipath.refl_range]
  exact singleton_subset_iff.mpr hx

lemma subtype_refl {x : X} (hx : x ∈ X₀)
    : (SubtypeDipath (Dipath.refl x) (range_refl_subset_of_mem hx)) = Dipath.refl (⟨x, hx⟩ : X₀)
        := rfl

lemma subsets_of_trans_subset {γ₁ : Dipath x y} {γ₂ : Dipath y z} (hγ : range (γ₁.trans γ₂) ⊆ X₀) :
    range γ₁ ⊆ X₀ ∧ range γ₂ ⊆ X₀ := by
  rw [Dipath.trans_range] at hγ
  exact ⟨subset_trans subset_union_left hγ, subset_trans subset_union_right hγ⟩

lemma trans_subset_of_subsets {γ₁ : Dipath x y} {γ₂ : Dipath y z}
    (hγ₁ : range γ₁ ⊆ X₀) (hγ₂ : range γ₂ ⊆ X₀) :
    range (γ₁.trans γ₂) ⊆ X₀ := by
  rw [Dipath.trans_range]
  exact union_subset hγ₁ hγ₂

lemma subtype_trans {γ₁ : Dipath x y} {γ₂ : Dipath y z} (hγ : range (γ₁.trans γ₂) ⊆ X₀) :
    (SubtypeDipath γ₁ (subsets_of_trans_subset hγ).1).trans
        (SubtypeDipath γ₂ (subsets_of_trans_subset hγ).2) =
      SubtypeDipath (γ₁.trans γ₂) hγ := by
  ext t
  change _ = (γ₁.trans γ₂) t
  rw [Dipath.trans_apply, Dipath.trans_apply,]
  split_ifs <;> rfl

lemma subtype_reparam {γ : Dipath x y} (hγ : range γ ⊆ X₀) {f : D(I,I)}
    (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    SubtypeDipath (γ.reparam f hf₀ hf₁) ((Dipath.range_reparam γ f hf₀ hf₁).symm ▸ hγ) =
    (SubtypeDipath γ hγ).reparam f hf₀ hf₁ :=
  rfl

lemma reparam_subset_of_subset {γ : Dipath x y} (hγ : range γ ⊆ X₀) {f : D(I,I)} (hf₀ : f 0 = 0)
    (hf₁ : f 1 = 1) :
    range (γ.reparam f hf₀ hf₁) ⊆ X₀ := by
  rw [Dipath.range_reparam]
  exact hγ

/-- Lift a dihomotopy whose range lies inside `X₀` to a dihomotopy of subtype dipaths. -/
def DihomotopyOfSubtype {γ γ' : Dipath x y} (hγ : range γ ⊆ X₀) (hγ' : range γ' ⊆ X₀)
  {F : Dipath.Dihomotopy γ γ'} (hF : range F ⊆ X₀) :
    Dipath.Dihomotopy (SubtypeDipath γ hγ) (SubtypeDipath γ' hγ') where
  toFun := fun t => ⟨F t, hF (mem_range_self t)⟩
  directed_toFun := fun a b p hp => F.directed_toFun _ hp
  map_zero_left := fun t => by simp; rfl
  map_one_left := fun t => by simp; rfl
  prop' := fun t p hp => by
    have := F.prop' t p hp
    ext
    change _ = (γ.toDirectedMap) p
    rw [←this]
    rfl

lemma dihomSubtype_of_dihom_range_subset {γ γ' : Dipath x y} (hγ : range γ ⊆ X₀)
    (hγ' : range γ' ⊆ X₀)
  {F : Dipath.Dihomotopy γ γ'} (hF : range F ⊆ X₀) :
    @Eq (Dipath.Dihomotopic.Quotient _ _) ⟦SubtypeDipath γ hγ⟧ ⟦SubtypeDipath γ' hγ'⟧ :=
Quotient.eq.mpr (Relation.EqvGen.rel _ _ ⟨DihomotopyOfSubtype hγ hγ' hF⟩)

end DiSubtype
