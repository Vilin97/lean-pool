/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

/-
Copyright (c) 2024 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Category instances for `Field`.
-/

universe u v

open CategoryTheory

/-- The category of fields. -/
structure FieldCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type u
  [field : Field carrier]

attribute [instance] FieldCat.field

initialize_simps_projections FieldCat (-field)

namespace FieldCat

instance : CoeSort (FieldCat) (Type u) :=
  ⟨FieldCat.carrier⟩

attribute [coe] FieldCat.carrier

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `FieldCat`. -/
abbrev of (R : Type u) [Field R] : FieldCat := ⟨R⟩

lemma coe_of (R : Type u) [Field R] : (of R : Type u) = R := rfl

lemma of_carrier (R : FieldCat.{u}) : of R = R := rfl

variable {R} in
/-- The type of morphisms in `FieldCat`. -/
@[ext]
structure Hom (R S : FieldCat) where
  private mk ::
  /-- The underlying ring hom. -/
  hom : R →+* S

instance : Category FieldCat where
  Hom R S := Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom.comp f.hom⟩

instance {R S : FieldCat.{u}} : CoeFun (R ⟶ S) (fun _ ↦ R → S) where
  coe f := f.hom

@[simp]
lemma hom_id {R : FieldCat} : (𝟙 R : R ⟶ R).hom = RingHom.id R := rfl

/- Provided for rewriting. -/
lemma id_apply (R : FieldCat) (r : R) :
    (𝟙 R : R ⟶ R) r = r := by simp

@[simp]
lemma hom_comp {R S T : FieldCat} (f : R ⟶ S) (g : S ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply {R S T : FieldCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) :
    (f ≫ g) r = g (f r) := by simp

@[ext]
lemma hom_ext {R S : FieldCat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

/-- Typecheck a `RingHom` as a morphism in `FieldCat`. -/
abbrev ofHom {R S : Type u} [Field R] [Field S] (f : R →+* S) : of R ⟶ of S :=
  ⟨f⟩

lemma hom_ofHom {R S : Type u} [Field R] [Field S] (f : R →+* S) : (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {R S : FieldCat} (f : R ⟶ S) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {R : Type u} [Field R] : ofHom (RingHom.id R) = 𝟙 (of R) := rfl

@[simp]
lemma ofHom_comp {R S T : Type u} [Field R] [Field S] [Field T]
    (f : R →+* S) (g : S →+* T) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {R S : Type u} [Field R] [Field S]
    (f : R →+* S) (r : R) : ofHom f r = f r := rfl

@[simp]
lemma inv_hom_apply {R S : FieldCat} (e : R ≅ S) (r : R) : e.inv (e.hom r) = r := by
  rw [← comp_apply]
  simp

@[simp]
lemma hom_inv_apply {R S : FieldCat} (e : R ≅ S) (s : S) : e.hom (e.inv s) = s := by
  rw [← comp_apply]
  simp

instance : ConcreteCategory.{u} FieldCat (fun R S ↦ R →+* S) where
  hom := Hom.hom
  ofHom := ofHom

/-- This unification hint helps with problems of the form `(forget ?C).obj R =?= carrier R'`.

An example where this is needed is in applying
`PresheafOfModules.Sheafify.app_eq_of_isLocallyInjective`.
-/
unif_hint forgetObjEqCoe (R R' : FieldCat) where
  R ≟ R' ⊢
  (forget FieldCat).obj R ≟ FieldCat.carrier R'

lemma forget_obj {R : FieldCat} : (forget FieldCat).obj R = R := rfl

lemma forget_map {R S : FieldCat} (f : R ⟶ S) :
    (forget FieldCat).map f = (f.hom : R → S) :=
  rfl

instance {R : FieldCat} : Field ((forget FieldCat).obj R) :=
  (inferInstance : Field R.carrier)

instance hasForgetToSemiRingCat : HasForget₂ FieldCat CommRingCat where
  forget₂ :=
    { obj := fun R ↦ CommRingCat.of R
      map := fun f ↦ CommRingCat.ofHom f.hom }

instance hasForgetToAddCommGrp : HasForget₂ FieldCat RingCat where
  forget₂ :=
    { obj := fun R ↦ RingCat.of R
      map := fun f ↦ RingCat.ofHom f.hom }

/-- Field equivalence are isomorphisms in category of semirings -/
@[simps]
def RingEquiv.toRingCatIso {R S : Type u} [Field R] [Field S] (e : R ≃+* S) :
    of R ≅ of S where
  hom := ⟨e⟩
  inv := ⟨e.symm⟩

instance forgetReflectIsos : (forget FieldCat).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget FieldCat).map f)
    let ff : X →+* Y := f.hom
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact FieldCat.RingEquiv.toRingCatIso e|>.isIso_hom

end FieldCat
