/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Cat
import LeanPool.DirectedTopologyLean4.DirectedPathHomotopy
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# LeanPool.DirectedTopologyLean4.FundamentalCategory
-/

/-
  This file contains the definition of the fundamental category of a directed space.
  We follow the structure of the undirected version found at:
  https://leanprover-community.github.io/mathlib_docs/algebraic_topology/fundamental_groupoid/basic.html#fundamental_groupoid
-/

open DirectedMap
open CategoryTheory

universe u v
variable {X : Type u} {Y : Type v} [DirectedSpace X] [DirectedSpace Y] {x₀ x₁ : X}

open scoped unitInterval

noncomputable section

namespace Dipath

namespace Dihomotopy

open Path.Homotopy

section assoc

lemma transAssocReparamAux_directed : DirectedMap.Directed
    ({ toFun := fun t => ⟨transAssocReparamAux t, transAssocReparamAux_mem_I t⟩
       continuous_toFun := Continuous.subtype_mk continuous_transAssocReparamAux _ } :
      C(I, I)) := by
  apply DirectedUnitInterval.directed_of_monotone _
  intros x y hxy
  unfold transAssocReparamAux
  simp only [one_div, ContinuousMap.coe_mk, Subtype.mk_le_mk]
  have hxy' : (x : ℝ) ≤ (y : ℝ) := hxy
  split_ifs with h₀ h₁ h₂ h₃ h₄ h₅
  · linarith
  · linarith
  · push Not at h₂
    have hy_pos : 0 ≤ (y : ℝ) := le_trans (by norm_num) (le_of_lt h₂)
    have h₀' : (x : ℝ) ≤ 4⁻¹ := h₀
    nlinarith
  · linarith
  · linarith
  · push Not at h₅
    have h₃' : (x : ℝ) ≤ 2⁻¹ := h₃
    have h₅' : (2⁻¹ : ℝ) < y := h₅
    nlinarith
  · linarith
  · linarith
  · apply (mul_le_mul_iff_of_pos_left (show 0 < (2⁻¹ : ℝ) by norm_num)).mpr
    linarith

/-- The directed self-map of the unit interval used to associate triple concatenations of
dipaths. -/
def transAssocReparamAuxMap : D(I,I) where
  toFun := fun t => ⟨transAssocReparamAux t, transAssocReparamAux_mem_I t⟩
  continuous_toFun := Continuous.subtype_mk continuous_transAssocReparamAux _
  directed_toFun := transAssocReparamAux_directed

lemma trans_assoc_reparam_directed {x₀ x₁ x₂ x₃ : X} (p : Dipath x₀ x₁) (q : Dipath x₁ x₂)
    (r : Dipath x₂ x₃) :
    (p.trans q).trans r = (p.trans (q.trans r)).reparam
      transAssocReparamAuxMap
      (Subtype.ext transAssocReparamAux_zero)
      (Subtype.ext transAssocReparamAux_one) := by
  ext t
  have : (p.trans q).trans r t =  (p.toPath.trans q.toPath).trans r.toPath t := rfl
  rw [this, trans_assoc_reparam p.toPath q.toPath r.toPath]
  rfl

/-- For any three dipaths `p q r`, `(p.trans q).trans r` is dihomotopic with
`p.trans (q.trans r)`. -/
theorem trans_assoc {x₀ x₁ x₂ x₃ : X} (p : Dipath x₀ x₁) (q : Dipath x₁ x₂) (r : Dipath x₂ x₃) :
    ((p.trans q).trans r).Dihomotopic (p.trans (q.trans r)) := by
  have := Dihomotopic.reparam (p.trans (q.trans r)) transAssocReparamAuxMap
    (Subtype.ext transAssocReparamAux_zero)
    (Subtype.ext transAssocReparamAux_one)
  rw [←trans_assoc_reparam_directed] at this
  exact Relation.EqvGen.symm _ _ this

end assoc

end Dihomotopy

end Dipath

/-
 Definition of the fundamental category and of the functor sending a directed space to its
 fundamental category
-/
/-- The fundamental category of a type, wrapping the underlying element as `as`. -/
@[ext]
structure FundamentalCategory (X : Type u) where
  /-- The underlying element of the type. -/
  as : X

namespace FundamentalCategory

/-- The fundamental-category wrapper is type-equivalent to the underlying type. -/
@[simps]
def equiv (X : Type*) : FundamentalCategory X ≃ X where
  toFun x := x.as
  invFun x := .mk x
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma isEmpty_iff (X : Type*) :
    IsEmpty (FundamentalCategory X) ↔ IsEmpty X :=
  equiv _ |>.isEmpty_congr

instance (X : Type*) [IsEmpty X] :
    IsEmpty (FundamentalCategory X) :=
  equiv _ |>.isEmpty

@[simp]
lemma nonempty_iff (X : Type*) :
    Nonempty (FundamentalCategory X) ↔ Nonempty X :=
  equiv _ |>.nonempty_congr

instance (X : Type*) [Nonempty X] :
    Nonempty (FundamentalCategory X) :=
  equiv _ |>.nonempty

@[simp]
lemma subsingleton_iff (X : Type*) :
    Subsingleton (FundamentalCategory X) ↔ Subsingleton X :=
  equiv _ |>.subsingleton_congr

instance (X : Type*) [Subsingleton X] :
    Subsingleton (FundamentalCategory X) :=
  equiv _ |>.subsingleton


instance {X : Type u} [Inhabited X] : Inhabited (FundamentalCategory X) :=
  ⟨⟨default⟩⟩

attribute [local instance] Dipath.Dihomotopic.setoid

instance : CategoryTheory.Category (FundamentalCategory X) where
  Hom x y := Dipath.Dihomotopic.Quotient x.as y.as
  id x := ⟦Dipath.refl x.as⟧
  comp {_ _ _} := Dipath.Dihomotopic.Quotient.comp
  id_comp {x _} f :=
    Quotient.inductionOn f fun a =>
      show ⟦(Dipath.refl x.as).trans a⟧ = ⟦a⟧ from
        Quotient.sound (Relation.EqvGen.rel _ _ ⟨Dipath.Dihomotopy.reflTrans a⟩)
  comp_id {_ y} f :=
    Quotient.inductionOn f fun a =>
      show ⟦a.trans (Dipath.refl y.as)⟧ = ⟦a⟧ from
        Quotient.sound (Relation.EqvGen.symm _ _
          (Relation.EqvGen.rel _ _ ⟨Dipath.Dihomotopy.transRefl a⟩))
  assoc {_ _ _ _} f g h :=
    Quotient.inductionOn₃ f g h fun p q r =>
      show ⟦(p.trans q).trans r⟧ = ⟦p.trans (q.trans r)⟧ from
        Quotient.sound (Dipath.Dihomotopy.trans_assoc p q r)

lemma comp_eq (x y z : FundamentalCategory X) (p : x ⟶ y) (q : y ⟶ z) :
    p ≫ q = p.comp q := rfl

lemma id_eq_path_refl (x : FundamentalCategory X) :
    𝟙 x = ⟦Dipath.refl x.as⟧ := rfl

/-- The functor on fundamental categories induced by a directed map. -/
@[simps]
def mapFunctor {X Y : Type*} [DirectedSpace X] [DirectedSpace Y] (f : D(X,Y)) :
    FundamentalCategory X ⥤ FundamentalCategory Y where
  obj x := ⟨f x.as⟩
  map {_ _} p := p.mapFn f
  map_id _ := rfl
  map_comp {_ _ _} p q := by
    refine Quotient.inductionOn₂ p q fun a b => ?_
    simp only [comp_eq, ←Dipath.Dihomotopic.map_lift, ←Dipath.Dihomotopic.comp_lift,
      Dipath.map_trans]

@[simp]
protected theorem mapFunctor_id (X : Type*) [DirectedSpace X] :
    mapFunctor (DirectedMap.id X) = 𝟭 _ := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intros; rfl
  · intros x y p
    refine Quotient.inductionOn p fun q => ?_
    change (mapFunctor (DirectedMap.id X)).map ⟦q⟧ =
      eqToHom rfl ≫ (𝟭 (FundamentalCategory X)).map ⟦q⟧ ≫ eqToHom rfl
    simp
    rfl

@[simp]
protected theorem mapFunctor_comp {X Y Z : Type*} [DirectedSpace X] [DirectedSpace Y]
    [DirectedSpace Z] (f : D(X,Y)) (g : D(Y,Z)) :
    mapFunctor (g.comp f) = mapFunctor f ⋙ mapFunctor g := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intros; rfl
  · intros x y p
    refine Quotient.inductionOn p fun q => ?_
    change (mapFunctor (g.comp f)).map ⟦q⟧ =
      eqToHom rfl ≫ (mapFunctor f ⋙ mapFunctor g).map ⟦q⟧ ≫ eqToHom rfl
    simp
    rfl

/-- The fundamental-category functor `dTopCat ⥤ Cat` sending a directed space to its
fundamental category. -/
def fundamentalCategoryFunctor : dTopCat ⥤ CategoryTheory.Cat where
  obj X := Cat.of (FundamentalCategory X)
  map f := (mapFunctor f.hom).toCatHom
  map_id X := by
    apply Cat.Hom.ext
    exact FundamentalCategory.mapFunctor_id X
  map_comp f g := by
    apply Cat.Hom.ext
    exact FundamentalCategory.mapFunctor_comp f.hom g.hom

/-- Notation for the fundamental-category functor `dTopCat ⥤ Cat`. -/
scoped notation "dπ" => FundamentalCategory.fundamentalCategoryFunctor
/-- Notation for the object part of the fundamental-category functor. -/
scoped notation "dπₓ" => FundamentalCategory.fundamentalCategoryFunctor.obj

/-- The underlying functor (not just `Cat.Hom`) induced by a `dTopCat` map. -/
@[reducible]
def fundamentalCategoryMap {X Y : dTopCat} (f : X ⟶ Y) :
    (fundamentalCategoryFunctor.obj X) ⥤ (fundamentalCategoryFunctor.obj Y) :=
  (fundamentalCategoryFunctor.map f).toFunctor

/-- Notation for the underlying functor on fundamental categories induced by a `dTopCat` map. -/
scoped notation "dπₘ" => FundamentalCategory.fundamentalCategoryMap

lemma map_eq {X Y : dTopCat} {x₀ x₁ : X} (f : X ⟶ Y) (p : Dipath.Dihomotopic.Quotient x₀ x₁) :
  (dπₘ f).map p = p.mapFn f.hom := rfl

/-- Help the typechecker by converting a point in the fundamental category back to a point in
the underlying directed space. -/
@[reducible]
def toTop {X : dTopCat} (x : dπₓ X) : X := x.as

/-- Help the typechecker by converting a point in a directed space to a
point in the fundamental category of that space -/
@[reducible]
def fromTop {X : dTopCat} (x : X) : dπₓ X := ⟨x⟩

/-- Help the typechecker by converting an arrow in the fundamental category of
a directed space back to a directed path in that space (i.e., `Dipath.Dihomotopic.Quotient`). -/
@[reducible]
def toPath {X : dTopCat} {x₀ x₁ : dπₓ X} (p : x₀ ⟶ x₁) :
  Dipath.Dihomotopic.Quotient (X := X) x₀.as x₁.as := p

/-- Help the typechecker by convering a directed path in a directed space to an arrow in the
fundamental category of that space. -/
@[reducible]
def fromPath {X : dTopCat} {x₀ x₁ : X} (p : Dipath.Dihomotopic.Quotient x₀ x₁) :
  FundamentalCategory.mk x₀ ⟶ FundamentalCategory.mk x₁ := p

end FundamentalCategory
