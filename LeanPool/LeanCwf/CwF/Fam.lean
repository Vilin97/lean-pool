/-
Copyright (c) 2026 Joseph Eremondi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Eremondi
-/

import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Opposite

namespace LeanPool.LeanCwf

open CategoryTheory

universe u

/-- The category of families of types, realized as the arrow category of `Type u`. -/
abbrev Fam : Type (u + 1) :=
  Arrow (Type u)

namespace Fam

/-- Make a family from an index type and a type indexed by it. -/
def mkFam (A : Type u) (B : A → Type u) : Fam.{u} :=
  Arrow.mk (TypeCat.ofHom (fun ab : (a : A) × B a => ab.1))

/-- The index type of a family. -/
def ixSet (arr : Fam) : Type u :=
  arr.right

/-- The fiber of a family over an index. -/
def famFor (arr : Fam) (a : ixSet arr) : Type u :=
  { ab : arr.left // arr.hom ab = a }

@[simp]
theorem famForIxInv (A : Type u) (B : A → Type u) :
    ixSet (mkFam.{u} A B) = A :=
  rfl

/-- Convert a fiber element of `mkFam A B` over `a` to an element of `B a`. -/
def toFam {A : Type u} {B : A → Type u} {a : A} :
    famFor (mkFam.{u} A B) a → B a
  | ⟨⟨a', b⟩, h⟩ => by
      have h' : a' = a := by
        simpa [mkFam] using h
      subst h'
      exact b

/-- Convert an element of `B a` to a fiber element of `mkFam A B` over `a`. -/
def fromFam {A : Type u} {B : A → Type u} {a : A} (b : B a) :
    famFor (mkFam.{u} A B) a :=
  ⟨⟨a, b⟩, by
    change (fun ab : (a : A) × B a => ab.1) ⟨a, b⟩ = a
    rfl⟩

/-- `fromFam` is a left inverse to `toFam`. -/
theorem toFamLeftInv {A : Type u} {B : A → Type u} {a : A} :
    Function.LeftInverse fromFam.{u} (toFam (A := A) (B := B) (a := a)) := by
  rintro ⟨⟨a', b⟩, h⟩
  have h' : a' = a := by
    simpa [mkFam] using h
  subst h'
  rfl

/-- `fromFam` is a right inverse to `toFam`. -/
theorem toFamRightInv {A : Type u} {B : A → Type u} {a : A} :
    Function.RightInverse (fromFam.{u} (A := A) (B := B) (a := a)) toFam := by
  intro b
  rfl

private def totalEquiv (arr : Fam) : ((a : ixSet arr) × famFor arr a) ≃ arr.left where
  toFun x := x.2.val
  invFun x := ⟨arr.hom x, ⟨x, rfl⟩⟩
  left_inv x := by
    cases x with
    | mk a x =>
      cases x with
      | mk val property =>
        cases property
        rfl
  right_inv x := rfl

/-- Rebuilding a family from its index type and fibers gives an isomorphic family. -/
def mkFamInv (arr : Fam) : mkFam (ixSet arr) (famFor arr) ≅ arr :=
  Arrow.isoMk (totalEquiv arr).toIso (Iso.refl _) (by
    ext x
    exact x.2.property)

/-- A morphism of families maps indices. -/
def mapIx {AB₁ AB₂ : Fam} (f : AB₁ ⟶ AB₂) : ixSet AB₁ → ixSet AB₂ :=
  fun x => f.right x

@[simp]
theorem mapIxId {AB : Fam} {x : ixSet AB} : mapIx (𝟙 AB) x = x :=
  rfl

@[simp]
theorem mapIxComp {AB₁ AB₂ AB₃ : Fam} (f : AB₁ ⟶ AB₂) (g : AB₂ ⟶ AB₃) :
    mapIx (f ≫ g) = mapIx g ∘ mapIx f := by
  rfl

/-- The projection from families to their index types. -/
def projIx : CategoryTheory.Functor Fam (Type u) where
  obj := ixSet
  map f := TypeCat.ofHom (mapIx f)
  map_id _ := by
    ext x
    rfl
  map_comp _ _ := by
    ext x
    rfl

/-- A morphism of families maps elements of fibers. -/
def mapFam {AB₁ AB₂ : Fam} (f : AB₁ ⟶ AB₂) {a : ixSet AB₁}
    (b : famFor AB₁ a) : famFor AB₂ (mapIx f a) :=
  match b with
  | ⟨val, property⟩ => ⟨f.left val, by
    have h :=
      congrArg (fun h : AB₁.left ⟶ AB₂.right => h val) (Arrow.Hom.w f)
    change AB₂.hom (f.left val) = f.right a
    rw [← property]
    exact h⟩

/-- Build a family morphism from a map on indices and a compatible map on fibers. -/
def unmapFam {AB₁ AB₂ : Fam} (ixMap : ixSet AB₁ → ixSet AB₂)
    (famMap : {a : ixSet AB₁} → famFor AB₁ a → famFor AB₂ (ixMap a)) :
    AB₁ ⟶ AB₂ :=
  Arrow.homMk
    (TypeCat.ofHom fun x => (famMap ⟨x, rfl⟩).val)
    (TypeCat.ofHom ixMap)
    (by
      ext x
      exact (famMap ⟨x, rfl⟩).property)

@[simp]
theorem unmapMap {AB₁ AB₂ : Fam} (f : AB₁ ⟶ AB₂) :
    unmapFam (mapIx f) (mapFam f) = f := by
  apply Arrow.hom_ext
  · ext x
    rfl
  · ext x
    rfl

/-- The fiber map of `unmapFam ixMap famMap` is the given fiber map. -/
@[simp]
theorem mapUnmap {AB₁ AB₂ : Fam} (ixMap : ixSet AB₁ → ixSet AB₂)
    (famMap : {a : ixSet AB₁} → famFor AB₁ a → famFor AB₂ (ixMap a))
    (a : ixSet AB₁) :
    mapFam (unmapFam ixMap famMap) (a := a) = famMap (a := a) := by
  funext b
  cases b with
  | mk val property =>
  cases property
  apply Subtype.ext
  rfl

/-- Cast a fiber element along an equality of indices. -/
def castFam {AB : Fam} {a a' : ixSet AB} (b : famFor AB a) (eq : a = a') :
    famFor AB a' :=
  cast (by rw [eq]) b

/-- Mapping along equal family morphisms agrees up to a cast on indices. -/
@[aesop safe]
theorem mapCast {AB₁ AB₂ : Fam} {a : ixSet AB₁} {f g : AB₁ ⟶ AB₂}
    (b : famFor AB₁ a) (eq : g = f) :
    mapFam f b = castFam (mapFam g b) (congrArg₂ mapIx eq (rfl : a = a)) := by
  subst eq
  rfl

/-- Mapping a fiber element along the identity morphism leaves it unchanged. -/
@[simp]
theorem mapFamId {AB : Fam} {a : ixSet AB} (b : famFor AB a) : mapFam (𝟙 AB) b = b := by
  apply Subtype.ext
  rfl

@[simp]
theorem mapFamComp {AB₁ AB₂ AB₃ : Fam} (f : AB₁ ⟶ AB₂) (g : AB₂ ⟶ AB₃)
    {a : ixSet AB₁} (b : famFor AB₁ a) :
    mapFam (f ≫ g) b = castFam (mapFam g (mapFam f b)) (by
      simp [mapIxComp, Function.comp_apply]) := by
  apply Subtype.ext
  rfl

/-- View a family as an object of the slice over its index type. -/
def toSlice (arr : Fam) : Over (ixSet arr) :=
  Over.mk arr.hom

/-- View an object of a slice category as a family. -/
def fromSlice {A : Type u} (arr : Over A) : Fam :=
  Arrow.mk arr.hom

@[simp]
theorem fromToSlice {arr : Fam} : fromSlice (toSlice arr) = arr :=
  rfl

@[simp]
theorem toFromSlice {A : Type u} (arr : Over A) : toSlice (fromSlice arr) = arr := by
  cases arr
  rfl

end Fam

end LeanPool.LeanCwf
