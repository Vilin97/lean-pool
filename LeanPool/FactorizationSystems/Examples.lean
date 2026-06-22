/-
Copyright (c) 2026 Ivan Kobe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Kobe
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.Types.Epimorphisms
import Mathlib.CategoryTheory.Types.Monomorphisms
import LeanPool.FactorizationSystems.Basic

/-!
# LeanPool.FactorizationSystems.Examples
-/

namespace CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C]

/-
We construct an example of factorization system: (Mono,Epi) on Set
-/

/- Every iso is an epi -/
lemma isIsoIsEpi : {X Y : C} → (f : X ⟶ Y) →
      MorphismProperty.isomorphisms _ f → MorphismProperty.epimorphisms _ f := by
  intro X Y f hf
  simp at hf
  exact {left_cancellation := by exact (IsIso.epi_of_iso f).left_cancellation}


/- Iso ⊆ Epi -/
lemma epimorphismsContainsIsos : containsIsos (MorphismProperty.epimorphisms C) := by
    intro X Y isof
    exact isIsoIsEpi isof.hom (Iso.isIso_hom isof)

/- Epimorphisms are closed under composition -/
lemma epimorphismsClosedUnderComp : is_closed_comp (MorphismProperty.epimorphisms C) where
    precomp := by exact epi_comp
    postcomp := by
        intro _ _ _ f hf g hg
        exact epi_comp g f

/- Every iso is a mono -/
lemma isIsoIsMono : {X Y : C} → (f : X ⟶ Y) →
        MorphismProperty.isomorphisms _ f → MorphismProperty.monomorphisms _ f := by
    intro X Y f hf
    simp at hf
    exact {right_cancellation := by exact (IsIso.mono_of_iso f).right_cancellation}

/- Mono ⊆ Iso -/
lemma monomorphismsContainsIsos : containsIsos (MorphismProperty.monomorphisms C) := by
    intro X Y isof
    exact isIsoIsMono isof.hom (Iso.isIso_hom isof)

/- Monomorphisms are closed under composition -/
lemma monomorphismsClosedUnderComp : is_closed_comp (MorphismProperty.monomorphisms C) where
    precomp := by exact mono_comp
    postcomp := by
        intro _ _ _ f hf g hg
        exact mono_comp g f

/- The image of a function of sets -/
/-- Imported FactorizationSystems declaration. -/
def imageSet {X Y : Type u} (f : X ⟶ Y) : Type u := {y : Y // ∃ x : X , f x = y}

/- Left map of the image factorization of a map -/
/-- Imported FactorizationSystems declaration. -/
def leftMapSet {X Y : Type u} (f : X ⟶ Y) : X ⟶ imageSet f :=
  TypeCat.ofHom fun x => ⟨f x, ⟨x, rfl⟩⟩

/- Right map of the image factorization of a map -/
/-- Imported FactorizationSystems declaration. -/
def rightMapSet {X Y : Type u} (f : X ⟶ Y) : imageSet f ⟶ Y :=
  TypeCat.ofHom fun y => y.1

/- The image factorization of a map -/
lemma factorization_set {X Y : Type u} (f : X ⟶ Y) :
    leftMapSet f ≫ rightMapSet f = f := by
  ext x
  rfl

/- The left map of the image factorization of a map is epi -/
lemma left_map_in_left_class_set {X Y : Type u} (f : X ⟶ Y) :
    MorphismProperty.epimorphisms _ (leftMapSet f) := by
  apply (epi_iff_surjective (leftMapSet f)).mpr
  rintro ⟨fx, ⟨x, hx⟩⟩
  use x
  apply Subtype.ext
  exact hx

/- The right map of the image factorization of a map is mono -/
lemma right_map_in_right_class_set {X Y : Type u} (f : X ⟶ Y) :
    MorphismProperty.monomorphisms _ (rightMapSet f) := by
  apply (mono_iff_injective (rightMapSet f)).mpr
  intro x y h
  apply Subtype.ext
  exact h

/- Given another (Epi,Mono) factorization of a map, there
is a unique way solve the corresponding lifting problem -/
lemma factorization_iso_set_hom' {X Y : Type u} (f : X ⟶ Y) (im : Type u)
    (left : X ⟶ im) (_ : MorphismProperty.epimorphisms _ left) (right : im ⟶ Y)
    (q : MorphismProperty.monomorphisms _ right) (fact : left ≫ right = f) (y : imageSet f) :
    ∃! y' : im, right y' = (rightMapSet f) y := by
  let ⟨fx, P⟩ := y
  have injectiveRight : Function.Injective right := by
    exact (mono_iff_injective right).mp q
  obtain ⟨x, hx⟩ := P
  have hfact : right (left x) = f x := by
    simpa using congrArg (fun h : X ⟶ Y => h x) fact
  refine ⟨left x, hfact.trans hx, ?_⟩
  intro y' hy
  apply injectiveRight
  exact hy.trans (hfact.trans hx).symm

/- A (unique) way of solving the lifting problem, i.e. a diagonal filler -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def factorizationIsoSetHom : {X Y : Type u} → (f : X ⟶ Y) → (im : Type u) →
    (left : X ⟶ im) → (MorphismProperty.epimorphisms _ left) → (right : im ⟶ Y) →
    (MorphismProperty.monomorphisms _ right) → (fact : left ≫ right = f) → imageSet f ⟶ im := by
  intro X Y f im left p right q fact
  exact TypeCat.ofHom fun y => (factorization_iso_set_hom' f im left p right q fact y).choose

/- The commutiativity of the right triangle with the diagonal filler -/
lemma factorization_iso_set_hom_comm_right : {X Y : Type u} → (f : X ⟶ Y) → (im : Type u) →
    (left : X ⟶ im) → (p : MorphismProperty.epimorphisms _ left) → (right : im ⟶ Y) →
    (q : MorphismProperty.monomorphisms _ right) → (fact : left ≫ right = f) →
    factorizationIsoSetHom f im left p right q fact ≫ right = rightMapSet f := by
  intro X Y f im left p right q fact
  ext y
  exact (Exists.choose_spec (factorization_iso_set_hom' f im left p right q fact y)).left

/- The commutiativity of the left triangle with the diagonal filler -/
lemma factorization_iso_set_hom_comm_left : {X Y : Type u} → (f : X ⟶ Y) → (im : Type u) →
    (left : X ⟶ im) → (p : MorphismProperty.epimorphisms _ left) → (right : im ⟶ Y) →
    (q : MorphismProperty.monomorphisms _ right) → (fact : left ≫ right = f) →
    leftMapSet f ≫ factorizationIsoSetHom f im left p right q fact = left := by
  intro X Y f im left p right q fact
  apply q.right_cancellation
  rw [Category.assoc, factorization_iso_set_hom_comm_right f im left p right q fact,
    factorization_set f, fact]

/- The inverse of the solution to the lifting problem -/
/-- Imported FactorizationSystems declaration. -/
def factorizationIsoSetInv : {X Y : Type u} → (f : X ⟶ Y) → (im : Type u) → (left : X ⟶ im) →
    (MorphismProperty.epimorphisms _ left) → (right : im ⟶ Y) →
    (fact : left ≫ right = f) → im ⟶ imageSet f := by
  intro X Y f im left p right fact
  exact TypeCat.ofHom fun y =>
  have existence : ∃ x : X, f x = right y := by
    have surjectiveLeft : Function.Surjective left := by
      exact (epi_iff_surjective left).mp p
    obtain ⟨x, hx⟩ := surjectiveLeft y
    use x
    have hfact : right (left x) = f x := by
      simpa using congrArg (fun h : X ⟶ Y => h x) fact
    exact hfact.symm.trans (congrArg right hx)
  ⟨right y, existence⟩

/- The commutiativity of the right triangle with the inverse to the diagonal filler -/
lemma factorization_iso_set_inv_comm_right : {X Y : Type u} → (f : X ⟶ Y) → (im : Type u) →
    (left : X ⟶ im) → (p : MorphismProperty.epimorphisms _ left) → (right : im ⟶ Y) →
    (fact : left ≫ right = f) →
    factorizationIsoSetInv f im left p right fact ≫ rightMapSet f = right := by
  intro X Y f im left p right fact
  ext y
  rfl

/- The commutiativity of the left triangle with the inverse to the diagonal filler -/
lemma factorization_iso_set_inv_comm_left : {X Y : Type u} → (f : X ⟶ Y) → (im : Type u) →
    (left : X ⟶ im) → (p : MorphismProperty.epimorphisms _ left) → (right : im ⟶ Y) →
    (fact : left ≫ right = f) →
    left ≫ factorizationIsoSetInv f im left p right fact = leftMapSet f := by
  intro X Y f im left p right fact
  ext x
  apply Subtype.ext
  exact congrArg (fun h : X ⟶ Y => h x) fact

/- The factorization isomorphism -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def factorizationIsoSet : {X Y : Type u} → (f : X ⟶ Y) → (im : Type u) → (left : X ⟶ im) →
    (MorphismProperty.epimorphisms _ left) → (right : im ⟶ Y) →
    (MorphismProperty.monomorphisms _ right) → (left ≫ right = f) →
    Σ' i : imageSet f ≅ im,
      leftMapSet  f ≫ i.hom = left ∧ i.hom ≫ right = rightMapSet f := by
  intro X Y f im left p right q fact
  exact {
    fst := by exact {
      hom := factorizationIsoSetHom f im left p right q fact
      inv := factorizationIsoSetInv f im left p right fact
      hom_inv_id := by
        ext y
        apply Subtype.ext
        exact (Exists.choose_spec (factorization_iso_set_hom' f im left p right q fact y)).left
      inv_hom_id := by
        ext y
        apply (mono_iff_injective right).mp q
        exact (Exists.choose_spec
          (factorization_iso_set_hom' f im left p right q fact
            (factorizationIsoSetInv f im left p right fact y))).left
    }
    snd := by exact {
      left := factorization_iso_set_hom_comm_left f im left p right q fact
      right := factorization_iso_set_hom_comm_right f im left p right q fact
    }
  }

/- The uniqueness of the factorization isomorphism -/
lemma factorization_iso_is_unique_set : {X Y : Type u} → (f : X ⟶ Y) → (im : Type u) →
    (left : X ⟶ im) → (p : MorphismProperty.epimorphisms _ left) → (right : im ⟶ Y) →
    (q : MorphismProperty.monomorphisms _ right) → (fact : left ≫ right = f) →
    (i : imageSet f ≅ im) → (leftMapSet f ≫ i.hom = left) →
    (_ : i.hom ≫ right = rightMapSet f) →
    i = (factorizationIsoSet f im left p right q fact).fst := by
  intro X Y f im left p right q fact i comm_left _
  apply Iso.ext
  apply (left_map_in_left_class_set f).left_cancellation
  exact comm_left.trans
    (factorization_iso_set_hom_comm_left f im left p right q fact).symm

/- The (Epi,Mono) factorization system on Set -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def EpiMonoSet : FactorizationSystem
    (MorphismProperty.epimorphisms (Type u)) (MorphismProperty.monomorphisms (Type u)) := {
  contains_isos_left_class := epimorphismsContainsIsos
  contains_isos_right_class := monomorphismsContainsIsos
  is_closed_comp_left_class := epimorphismsClosedUnderComp
  is_closed_comp_right_class := monomorphismsClosedUnderComp
  image := imageSet
  leftMap := leftMapSet
  rightMap := rightMapSet
  factorization := factorization_set
  left_map_in_left_class := left_map_in_left_class_set
  right_map_in_right_class := right_map_in_right_class_set
  factorizationIso := factorizationIsoSet
  factorization_iso_is_unique := factorization_iso_is_unique_set }

end CategoryTheory
