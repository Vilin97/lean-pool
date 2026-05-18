/-
Copyright (c) 2026 Joseph Eremondi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Eremondi
-/

import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Equivalence

open CategoryTheory

namespace LeanPool.LeanCwf

universe u

/-- Families of types, represented as arrows in `Type u`. -/
abbrev Fam : Type (u + 1) :=
  Arrow (Type u)

namespace Fam

/-- Builds a family from an index type and a dependent type over it. -/
def mkFam (A : Type u) (B : A → Type u) : Fam.{u} :=
  { left := Σ x : A , B x
    right := A
    hom := TypeCat.ofHom Sigma.fst }

/-- The index type of a family. -/
def ixSet (arr : Fam) : Type u :=
  arr.right


/-- The fiber of a family over an index. -/
def famFor (arr : Fam) (a : ixSet arr) : Type u :=
  {ab : arr.left // arr.hom ab = a}

--The index projection cancels with the constructor
@[simp]
theorem famForIxInv (A : Type u) (B : A → Type u) : ixSet (mkFam.{u} A B) = A :=
  rfl

/-- Converts an element of the fiber of a constructed family to the original dependent type. -/
def toFam {A : Type u} {B : A → Type u} {a : A}
 : (b : famFor (mkFam.{u} A B) a) → B a := fun
    | .mk ab eq => by
      rw [<- eq]
      exact ab.snd

/-- Converts an element of the original dependent type to the fiber of the constructed family. -/
def fromFam {A : Type u} {B : A → Type u} {a : A}
  (b : B a) : famFor (mkFam.{u} A B) a where
    val := .mk a b
    property := rfl

theorem toFamLeftInv {A : Type u} {B : A → Type u} {a : A}
  : Function.LeftInverse fromFam.{u} (toFam (A := A) (B := B) (a := a)) := by
  intros b
  rcases b with ⟨⟨a', b⟩, h⟩
  cases h
  rfl


theorem toFamRightInv {A : Type u} {B : A → Type u} {a : A}
  : Function.RightInverse (fromFam.{u} (A := A) (B := B) (a := a)) toFam := by
  intro b
  rfl

/-- Reconstructing a family from its index and fibers gives an isomorphic family. -/
def mkFamInv (arr : Fam) : mkFam (ixSet arr) (famFor arr) ≅ arr where
  hom :=
    Arrow.homMk
      (TypeCat.ofHom fun a_ab_pf => a_ab_pf.2.1)
      (𝟙 _)
      (by
        ext a_ab_pf
        exact a_ab_pf.2.2)
  inv :=
    Arrow.homMk
      (TypeCat.ofHom fun b => ⟨arr.hom b, ⟨b, rfl⟩⟩)
      (𝟙 _)
      (by
        ext b
        rfl)
  hom_inv_id := by
    apply Arrow.hom_ext
    · ext a_ab_pf
      rcases a_ab_pf with ⟨a, b, h⟩
      cases h
      rfl
    · ext a
      rfl
  inv_hom_id := by
    apply Arrow.hom_ext
    · ext b
      rfl
    · ext a
      rfl

/-- The function on indices induced by a morphism of families. -/
def mapIx {AB₁ AB₂ : Fam} (f : AB₁ ⟶ AB₂) : ixSet AB₁ → ixSet AB₂ :=
  f.right

-- Mapping the identity morphism over a family's index is the identity
@[simp]
theorem mapIxId {AB : Fam} {x : ixSet AB} : mapIx (𝟙 AB) x = x := by
  rfl

-- Mapping a composite arrow over an index gives the composite
@[simp]
theorem mapIxComp {AB₁ AB₂ AB₃ : Fam} (f : AB₁ ⟶ AB₂) (g : AB₂ ⟶ AB₃) :
    mapIx (f ≫ g) = mapIx g ∘ mapIx f := by
  rfl


/-- The functor sending a family to its index type. -/
def projIx : CategoryTheory.Functor Fam (Type u) where
  obj := ixSet
  map f := TypeCat.ofHom (mapIx f)
  map_id X := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

/-- The function on fibers induced by a morphism of families. -/
def mapFam {AB₁ AB₂ : Fam}
  (f : AB₁ ⟶ AB₂)
  {a : ixSet AB₁}
  (b : famFor AB₁ a)
  : famFor AB₂ (mapIx f a) :=
  ⟨f.left b.val,
    calc
      AB₂.hom (f.left b.val) = f.right (AB₁.hom b.val) := by
        change (f.left ≫ AB₂.hom) b.val = (AB₁.hom ≫ f.right) b.val
        exact ConcreteCategory.congr_hom f.w b.val
      _ = f.right a := by rw [b.property]⟩

/-- Builds a morphism of families from maps on indices and fibers. -/
def unmapFam {AB₁ AB₂ : Fam}
  (ixMap : ixSet AB₁ → ixSet AB₂)
  (famMap : {a : ixSet AB₁} -> famFor AB₁ a -> famFor AB₂ (ixMap a))
  : (AB₁ ⟶ AB₂) :=
  Arrow.homMk
    (TypeCat.ofHom fun x => (famMap ⟨x, rfl⟩).val)
    (TypeCat.ofHom ixMap)
    (by
      ext x
      exact (famMap ⟨x, rfl⟩).property)


@[simp]
theorem unmapMap {AB₁ AB₂ : Fam}
  (f : AB₁ ⟶ AB₂)
  : unmapFam (mapIx f) (mapFam f) = f := by
  apply Arrow.hom_ext
  · ext x
    rfl
  · ext x
    rfl


@[simp]
theorem mapUnmap {AB₁ AB₂ : Fam}
  (ixMap : ixSet AB₁ → ixSet AB₂)
  (famMap : {a : ixSet AB₁} -> famFor AB₁ a -> famFor AB₂ (ixMap a))
  (a : ixSet AB₁)
  : mapFam (unmapFam ixMap famMap) (a := a) = famMap (a := a) := by
    funext b
    cases b with
    | mk x pf =>
      cases pf
      apply Subtype.ext
      rfl

/-- Casts an element of a family along an equality of indices. -/
def castFam {AB : Fam} {a a' : ixSet AB} (b : famFor AB a) (eq : a = a') : famFor AB a' :=
  cast (by aesop) b

@[aesop safe]
theorem mapCast {AB₁ AB₂ : Fam} {a : ixSet AB₁} {f g : AB₁ ⟶ AB₂} (b : famFor AB₁ a) (eq : g = f)
  : mapFam f b = castFam (mapFam g b) (congrArg₂ mapIx eq (refl a)) := by
    subst eq
    rfl

-- Mapping the idenitity over an element of a family is the identity
@[simp]
theorem mapFamId {AB : Fam} {a : ixSet AB} (b : famFor AB a) : mapFam (𝟙 AB) b = b := by
  apply Subtype.ext
  rfl

-- Mapping a composite arrow over an element of a family
-- is the composition of the mappings
@[simp]
theorem mapFamComp {AB₁ AB₂ AB₃ : Fam} (f : AB₁ ⟶ AB₂) (g : AB₂ ⟶ AB₃)
  {a : ixSet AB₁} (b : famFor AB₁ a)
  : (mapFam (f ≫ g) b) = castFam (mapFam g (mapFam f b)) (by aesop) := by
  apply Subtype.ext
  rfl


/-- Views a family as an object in the slice category over its index type. -/
def toSlice (arr : Fam) : Over (ixSet arr) :=
  Over.mk arr.hom

/-- Views an object of a slice category over a type as a family. -/
def fromSlice {A : Type u} (arr : Over A) : Fam :=
  Arrow.mk arr.hom

@[simp]
theorem fromToSlice {arr : Fam} : fromSlice (toSlice arr) = arr :=
  rfl


@[simp]
theorem toFromSlice {A : Type u} (arr : Over A) : toSlice (fromSlice arr) = arr := by
  cases arr with
  | mk left hom => rfl



end Fam

end LeanPool.LeanCwf
