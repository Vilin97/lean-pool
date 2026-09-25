/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.CatTheory.WhiskerAdditive

/-!
# The ℤ/2-graded doubling of a category

Deligne 2.11's device: the category of super-objects over an
ambient category `A`.  An object is a pair of objects of `A`, the
*even* and *odd* components; a morphism is a pair of component
morphisms.  The graded tensor product mixes the components in the
usual super pattern, the braiding carries the Koszul sign `-1` on
the odd⊗odd block, and the odd copy of the unit provides an odd
invertible object — exactly the hypothesis pair of Deligne 2.9 —
to a category that may lack one.

This module mirrors, at the abstract level, the concrete
`SuperVect` construction of `RS/Definitions.lean`: the same
component bookkeeping, with binary biproducts in place of products
of vector spaces.

The monoidal coherences are not proved by hand: the summing
functor `Doubled A ⥤ A`, `X ↦ X.even ⊞ X.odd`, is faithful, and
`CategoryTheory.Monoidal.induced` transports the pentagon and
triangle from `A` along it.  The braiding coherences, which the
Koszul sign prevents from transporting, are discharged by
componentwise matrix checks against the distributor calculus set
up in the `Distributors` section.
-/

@[expose] public section

namespace RS

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

noncomputable section

/-- A super-object over `A`: a pair of objects of `A`, thought of
as the even and odd graded components. -/
structure Doubled (A : Type u) : Type u where
  /-- The even component. -/
  even : A
  /-- The odd component. -/
  odd : A

namespace Doubled

variable {A : Type u}

/-- A morphism of super-objects: a pair of component morphisms,
preserving the grading. -/
@[ext]
structure Hom
    [Category.{v} A]
    (X Y : Doubled A) where
  /-- The even component of the morphism. -/
  even : X.even ⟶ Y.even
  /-- The odd component of the morphism. -/
  odd : X.odd ⟶ Y.odd

/-- Super-objects form a category with componentwise identities
and composition. -/
instance instCategory [Category.{v} A] : Category (Doubled A) where
  Hom := Hom
  id X := ⟨𝟙 X.even, 𝟙 X.odd⟩
  comp f g := ⟨f.even ≫ g.even, f.odd ≫ g.odd⟩

/-- The even component of a morphism of super-objects. -/
def evenHom [Category.{v} A]
    {X Y : Doubled A} (f : X ⟶ Y) : X.even ⟶ Y.even :=
  Hom.even f

/-- The odd component of a morphism of super-objects. -/
def oddHom [Category.{v} A]
    {X Y : Doubled A} (f : X ⟶ Y) : X.odd ⟶ Y.odd :=
  Hom.odd f

/-- Morphisms of super-objects agreeing in both components are
equal. -/
@[ext]
theorem hom_ext [Category.{v} A]
    {X Y : Doubled A} {f g : X ⟶ Y}
    (he : evenHom f = evenHom g) (ho : oddHom f = oddHom g) :
    f = g :=
  Hom.ext he ho

/-- A morphism of super-objects from a pair of component
morphisms. -/
def homMk [Category.{v} A]
    {X Y : Doubled A} (fe : X.even ⟶ Y.even)
    (fo : X.odd ⟶ Y.odd) : X ⟶ Y :=
  ⟨fe, fo⟩

@[simp]
theorem evenHom_homMk [Category.{v} A]
    {X Y : Doubled A} (fe : X.even ⟶ Y.even)
    (fo : X.odd ⟶ Y.odd) : evenHom (homMk fe fo) = fe :=
  rfl

@[simp]
theorem oddHom_homMk [Category.{v} A]
    {X Y : Doubled A} (fe : X.even ⟶ Y.even)
    (fo : X.odd ⟶ Y.odd) : oddHom (homMk fe fo) = fo :=
  rfl

@[simp]
theorem evenHom_id [Category.{v} A]
    (X : Doubled A) : evenHom (𝟙 X) = 𝟙 X.even :=
  rfl

@[simp]
theorem oddHom_id [Category.{v} A]
    (X : Doubled A) : oddHom (𝟙 X) = 𝟙 X.odd :=
  rfl

@[simp]
theorem evenHom_comp [Category.{v} A]
    {X Y Z : Doubled A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    evenHom (f ≫ g) = evenHom f ≫ evenHom g :=
  rfl

@[simp]
theorem oddHom_comp [Category.{v} A]
    {X Y Z : Doubled A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    oddHom (f ≫ g) = oddHom f ≫ oddHom g :=
  rfl

/-- An isomorphism of super-objects from a pair of component
isomorphisms. -/
@[simps]
def isoMk [Category.{v} A]
    {X Y : Doubled A} (e : X.even ≅ Y.even)
    (o : X.odd ≅ Y.odd) : X ≅ Y where
  hom := homMk e.hom o.hom
  inv := homMk e.inv o.inv
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp

section Preadditive

/-- The componentwise zero morphism. -/
instance homZero [Category.{v} A] [Preadditive A]
    (X Y : Doubled A) : Zero (X ⟶ Y) :=
  ⟨homMk 0 0⟩

/-- Componentwise addition of morphisms. -/
instance homAdd [Category.{v} A] [Preadditive A]
    (X Y : Doubled A) : Add (X ⟶ Y) :=
  ⟨fun f g => homMk (evenHom f + evenHom g) (oddHom f + oddHom g)⟩

/-- Componentwise negation of morphisms. -/
instance homNeg [Category.{v} A] [Preadditive A]
    (X Y : Doubled A) : Neg (X ⟶ Y) :=
  ⟨fun f => homMk (-evenHom f) (-oddHom f)⟩

/-- The componentwise additive group of morphisms. -/
instance homAddCommGroup [Category.{v} A] [Preadditive A]
    (X Y : Doubled A) : AddCommGroup (X ⟶ Y) where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc _ _ _ := Hom.ext (add_assoc _ _ _) (add_assoc _ _ _)
  zero_add _ := Hom.ext (zero_add _) (zero_add _)
  add_zero _ := Hom.ext (add_zero _) (add_zero _)
  add_comm _ _ := Hom.ext (add_comm _ _) (add_comm _ _)
  neg_add_cancel _ :=
    Hom.ext (neg_add_cancel _) (neg_add_cancel _)

@[simp]
theorem evenHom_add [Category.{v} A] [Preadditive A]
    {X Y : Doubled A} (f g : X ⟶ Y) :
    evenHom (f + g) = evenHom f + evenHom g :=
  rfl

@[simp]
theorem oddHom_add [Category.{v} A] [Preadditive A]
    {X Y : Doubled A} (f g : X ⟶ Y) :
    oddHom (f + g) = oddHom f + oddHom g :=
  rfl

@[simp]
theorem evenHom_zero [Category.{v} A] [Preadditive A]
    {X Y : Doubled A} :
    evenHom (0 : X ⟶ Y) = 0 :=
  rfl

@[simp]
theorem oddHom_zero [Category.{v} A] [Preadditive A]
    {X Y : Doubled A} :
    oddHom (0 : X ⟶ Y) = 0 :=
  rfl

@[simp]
theorem evenHom_neg [Category.{v} A] [Preadditive A]
    {X Y : Doubled A} (f : X ⟶ Y) :
    evenHom (-f) = -evenHom f :=
  rfl

@[simp]
theorem oddHom_neg [Category.{v} A] [Preadditive A]
    {X Y : Doubled A} (f : X ⟶ Y) :
    oddHom (-f) = -oddHom f :=
  rfl

@[simp]
theorem evenHom_sub [Category.{v} A] [Preadditive A]
    {X Y : Doubled A} (f g : X ⟶ Y) :
    evenHom (f - g) = evenHom f - evenHom g := by
  rw [sub_eq_add_neg, sub_eq_add_neg, evenHom_add, evenHom_neg]

@[simp]
theorem oddHom_sub [Category.{v} A] [Preadditive A]
    {X Y : Doubled A} (f g : X ⟶ Y) :
    oddHom (f - g) = oddHom f - oddHom g := by
  rw [sub_eq_add_neg, sub_eq_add_neg, oddHom_add, oddHom_neg]

/-- The doubling of a preadditive category is preadditive,
componentwise. -/
instance instPreadditive
    [Category.{v} A] [Preadditive A] : Preadditive (Doubled A) where
  add_comp _ _ _ _ _ _ :=
    Hom.ext (Preadditive.add_comp _ _ _ _ _ _)
      (Preadditive.add_comp _ _ _ _ _ _)
  comp_add _ _ _ _ _ _ :=
    Hom.ext (Preadditive.comp_add _ _ _ _ _ _)
      (Preadditive.comp_add _ _ _ _ _ _)

/-- A super-object with two zero components is a zero object. -/
theorem isZero [Category.{v} A]
    (X : Doubled A) (he : IsZero X.even)
    (ho : IsZero X.odd) : IsZero X where
  unique_to _ :=
    ⟨⟨⟨homMk (he.to_ _) (ho.to_ _)⟩,
      fun _ => Hom.ext (he.eq_of_src _ _) (ho.eq_of_src _ _)⟩⟩
  unique_from _ :=
    ⟨⟨⟨homMk (he.from_ _) (ho.from_ _)⟩,
      fun _ => Hom.ext (he.eq_of_tgt _ _) (ho.eq_of_tgt _ _)⟩⟩

open ZeroObject in
/-- The doubling of a category with a zero object has a zero
object, with both components zero. -/
instance instHasZeroObject [Category.{v} A]
    [HasZeroObject A] :
    HasZeroObject (Doubled A) :=
  ⟨⟨0, 0⟩, isZero _ (isZero_zero A) (isZero_zero A)⟩

end Preadditive

section Linear

/-- The componentwise ℂ-module of morphisms. -/
instance homModule [Category.{v} A] [Preadditive A] [CategoryTheory.Linear ℂ A]
    (X Y : Doubled A) : Module ℂ (X ⟶ Y) where
  smul c f := homMk (c • evenHom f) (c • oddHom f)
  one_smul _ := Hom.ext (one_smul _ _) (one_smul _ _)
  mul_smul _ _ _ := Hom.ext (mul_smul _ _ _) (mul_smul _ _ _)
  smul_zero _ := Hom.ext (smul_zero _) (smul_zero _)
  smul_add _ _ _ := Hom.ext (smul_add _ _ _) (smul_add _ _ _)
  add_smul _ _ _ := Hom.ext (add_smul _ _ _) (add_smul _ _ _)
  zero_smul _ := Hom.ext (zero_smul _ _) (zero_smul _ _)

@[simp]
theorem evenHom_smul
    [Category.{v} A] [Preadditive A] [CategoryTheory.Linear ℂ A]
    {X Y : Doubled A} (c : ℂ) (f : X ⟶ Y) :
    evenHom (c • f) = c • evenHom f :=
  rfl

@[simp]
theorem oddHom_smul [Category.{v} A] [Preadditive A] [CategoryTheory.Linear ℂ A]
    {X Y : Doubled A} (c : ℂ) (f : X ⟶ Y) :
    oddHom (c • f) = c • oddHom f :=
  rfl

/-- The doubling of a ℂ-linear category is ℂ-linear,
componentwise. -/
instance instLinear
    [Category.{v} A] [Preadditive A] [CategoryTheory.Linear ℂ A] :
    CategoryTheory.Linear ℂ (Doubled A) where
  smul_comp _ _ _ _ _ _ :=
    Hom.ext (Linear.smul_comp _ _ _ _ _ _)
      (Linear.smul_comp _ _ _ _ _ _)
  comp_smul _ _ _ _ _ _ :=
    Hom.ext (Linear.comp_smul _ _ _ _ _ _)
      (Linear.comp_smul _ _ _ _ _ _)

end Linear

section Distributors

/-- The matrix map out of a right-whiskered binary biproduct. -/
def descRight [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A]
    {M N Z T : A} (f : M ⊗ Z ⟶ T) (g : N ⊗ Z ⟶ T) :
    (M ⊞ N) ⊗ Z ⟶ T :=
  (biprodTensorIso M N Z).hom ≫ biprod.desc f g

/-- The matrix map out of a left-whiskered binary biproduct. -/
def descLeft [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A]
    {X M N T : A} (f : X ⊗ M ⟶ T) (g : X ⊗ N ⟶ T) :
    X ⊗ (M ⊞ N) ⟶ T :=
  (tensorBiprodIso X M N).hom ≫ biprod.desc f g

@[reassoc (attr := simp)]
theorem inl_descRight [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A]
    {M N Z T : A} (f : M ⊗ Z ⟶ T)
    (g : N ⊗ Z ⟶ T) : (biprod.inl ▷ Z) ≫ descRight f g = f := by
  simp [descRight]

@[reassoc (attr := simp)]
theorem inr_descRight [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A]
    {M N Z T : A} (f : M ⊗ Z ⟶ T)
    (g : N ⊗ Z ⟶ T) : (biprod.inr ▷ Z) ≫ descRight f g = g := by
  simp [descRight]

@[reassoc (attr := simp)]
theorem inl_descLeft [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A]
    {X M N T : A} (f : X ⊗ M ⟶ T)
    (g : X ⊗ N ⟶ T) : (X ◁ biprod.inl) ≫ descLeft f g = f := by
  simp [descLeft]

@[reassoc (attr := simp)]
theorem inr_descLeft [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A]
    {X M N T : A} (f : X ⊗ M ⟶ T)
    (g : X ⊗ N ⟶ T) : (X ◁ biprod.inr) ≫ descLeft f g = g := by
  simp [descLeft]

/-- `inl_descRight` in tensor-of-morphisms shape.  Not a simp
lemma: `⊗ₘ 𝟙` normalises to the whiskering, where
`inl_descRight` already applies. -/
@[reassoc]
theorem inl_id_descRight [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A]
    {M N Z T : A} (f : M ⊗ Z ⟶ T)
    (g : N ⊗ Z ⟶ T) :
    (biprod.inl ⊗ₘ 𝟙 Z) ≫ descRight f g = f := by
  rw [tensorHom_id, inl_descRight]

/-- `inr_descRight` in tensor-of-morphisms shape.  Not a simp
lemma: `⊗ₘ 𝟙` normalises to the whiskering, where
`inr_descRight` already applies. -/
@[reassoc]
theorem inr_id_descRight [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A]
    {M N Z T : A} (f : M ⊗ Z ⟶ T)
    (g : N ⊗ Z ⟶ T) :
    (biprod.inr ⊗ₘ 𝟙 Z) ≫ descRight f g = g := by
  rw [tensorHom_id, inr_descRight]

/-- `inl_descLeft` in tensor-of-morphisms shape.  Not a simp
lemma: `𝟙 ⊗ₘ` normalises to the whiskering, where `inl_descLeft`
already applies. -/
@[reassoc]
theorem id_inl_descLeft [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A]
    {X M N T : A} (f : X ⊗ M ⟶ T)
    (g : X ⊗ N ⟶ T) :
    (𝟙 X ⊗ₘ biprod.inl) ≫ descLeft f g = f := by
  rw [id_tensorHom, inl_descLeft]

/-- `inr_descLeft` in tensor-of-morphisms shape.  Not a simp
lemma: `𝟙 ⊗ₘ` normalises to the whiskering, where `inr_descLeft`
already applies. -/
@[reassoc]
theorem id_inr_descLeft [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A]
    {X M N T : A} (f : X ⊗ M ⟶ T)
    (g : X ⊗ N ⟶ T) :
    (𝟙 X ⊗ₘ biprod.inr) ≫ descLeft f g = g := by
  rw [id_tensorHom, inr_descLeft]

@[reassoc (attr := simp)]
theorem inl_map_whiskerRight
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A]
    {M N M' N' Z : A} (f : M ⟶ M')
    (g : N ⟶ N') :
    (biprod.inl ▷ Z) ≫ (biprod.map f g ▷ Z) =
      (f ▷ Z) ≫ (biprod.inl ▷ Z) := by
  rw [← comp_whiskerRight, biprod.inl_map, comp_whiskerRight]

@[reassoc (attr := simp)]
theorem inr_map_whiskerRight
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A]
    {M N M' N' Z : A} (f : M ⟶ M')
    (g : N ⟶ N') :
    (biprod.inr ▷ Z) ≫ (biprod.map f g ▷ Z) =
      (g ▷ Z) ≫ (biprod.inr ▷ Z) := by
  rw [← comp_whiskerRight, biprod.inr_map, comp_whiskerRight]

@[reassoc (attr := simp)]
theorem inl_desc_whiskerRight
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A]
    {M N T Z : A} (f : M ⟶ T)
    (g : N ⟶ T) :
    (biprod.inl ▷ Z) ≫ (biprod.desc f g ▷ Z) = f ▷ Z := by
  rw [← comp_whiskerRight, biprod.inl_desc]

@[reassoc (attr := simp)]
theorem inr_desc_whiskerRight
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A]
    {M N T Z : A} (f : M ⟶ T)
    (g : N ⟶ T) :
    (biprod.inr ▷ Z) ≫ (biprod.desc f g ▷ Z) = g ▷ Z := by
  rw [← comp_whiskerRight, biprod.inr_desc]

@[reassoc (attr := simp)]
theorem inl_map_whiskerLeft
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A]
    {X M N M' N' : A} (f : M ⟶ M')
    (g : N ⟶ N') :
    (X ◁ biprod.inl) ≫ (X ◁ biprod.map f g) =
      (X ◁ f) ≫ (X ◁ biprod.inl) := by
  rw [← whiskerLeft_comp, biprod.inl_map, whiskerLeft_comp]

@[reassoc (attr := simp)]
theorem inr_map_whiskerLeft
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A]
    {X M N M' N' : A} (f : M ⟶ M')
    (g : N ⟶ N') :
    (X ◁ biprod.inr) ≫ (X ◁ biprod.map f g) =
      (X ◁ g) ≫ (X ◁ biprod.inr) := by
  rw [← whiskerLeft_comp, biprod.inr_map, whiskerLeft_comp]

@[reassoc (attr := simp)]
theorem inl_desc_whiskerLeft
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A]
    {X M N T : A} (f : M ⟶ T)
    (g : N ⟶ T) :
    (X ◁ biprod.inl) ≫ (X ◁ biprod.desc f g) = X ◁ f := by
  rw [← whiskerLeft_comp, biprod.inl_desc]

@[reassoc (attr := simp)]
theorem inr_desc_whiskerLeft
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A]
    {X M N T : A} (f : M ⟶ T)
    (g : N ⟶ T) :
    (X ◁ biprod.inr) ≫ (X ◁ biprod.desc f g) = X ◁ g := by
  rw [← whiskerLeft_comp, biprod.inr_desc]

@[reassoc (attr := simp)]
theorem whiskerLeft_lift_descLeft
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A]
    {X M N T U : A} (f : U ⟶ M)
    (g : U ⟶ N) (h : X ⊗ M ⟶ T) (k : X ⊗ N ⟶ T) :
    (X ◁ biprod.lift f g) ≫ descLeft h k =
      (X ◁ f) ≫ h + (X ◁ g) ≫ k := by
  rw [descLeft, ← Category.assoc]
  rw [show (X ◁ biprod.lift f g) ≫ (tensorBiprodIso X M N).hom =
      biprod.lift (X ◁ f) (X ◁ g) by
    apply biprod.hom_ext <;> simp [tensorBiprodIso, ← whiskerLeft_comp]]
  rw [biprod.lift_desc]

@[reassoc (attr := simp)]
theorem lift_whiskerRight_descRight
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A]
    {M N Z T U : A} (f : U ⟶ M)
    (g : U ⟶ N) (h : M ⊗ Z ⟶ T) (k : N ⊗ Z ⟶ T) :
    (biprod.lift f g ▷ Z) ≫ descRight h k =
      (f ▷ Z) ≫ h + (g ▷ Z) ≫ k := by
  rw [descRight, ← Category.assoc]
  rw [show (biprod.lift f g ▷ Z) ≫ (biprodTensorIso M N Z).hom =
      biprod.lift (f ▷ Z) (g ▷ Z) by
    apply biprod.hom_ext <;> simp [biprodTensorIso, ← comp_whiskerRight]]
  rw [biprod.lift_desc]

/-- Maps out of a right-whiskered binary biproduct are determined
by their composites with the whiskered inclusions. -/
theorem tensorRight_ext [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A]
    {M N Z T : A} {f g : (M ⊞ N) ⊗ Z ⟶ T}
    (h₁ : (biprod.inl ▷ Z) ≫ f = (biprod.inl ▷ Z) ≫ g)
    (h₂ : (biprod.inr ▷ Z) ≫ f = (biprod.inr ▷ Z) ≫ g) : f = g := by
  rw [← cancel_epi (biprodTensorIso M N Z).inv]
  apply biprod.hom_ext'
  · simpa only [biprodTensorIso, biprod.inl_desc_assoc] using h₁
  · simpa only [biprodTensorIso, biprod.inr_desc_assoc] using h₂

/-- Maps out of a left-whiskered binary biproduct are determined
by their composites with the whiskered inclusions. -/
theorem tensorLeft_ext [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A]
    {X M N T : A} {f g : X ⊗ (M ⊞ N) ⟶ T}
    (h₁ : (X ◁ biprod.inl) ≫ f = (X ◁ biprod.inl) ≫ g)
    (h₂ : (X ◁ biprod.inr) ≫ f = (X ◁ biprod.inr) ≫ g) : f = g := by
  rw [← cancel_epi (tensorBiprodIso X M N).inv]
  apply biprod.hom_ext'
  · simpa only [tensorBiprodIso, biprod.inl_desc_assoc] using h₁
  · simpa only [tensorBiprodIso, biprod.inr_desc_assoc] using h₂

end Distributors

section GradedTensor

/-- The graded tensor product of super-objects: parities add, so
each component of the product is a biproduct of two mixed blocks. -/
abbrev tensorObj [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A]
    (X Y : Doubled A) : Doubled A where
  even := X.even ⊗ Y.even ⊞ X.odd ⊗ Y.odd
  odd := X.even ⊗ Y.odd ⊞ X.odd ⊗ Y.even

@[simp]
theorem tensorObj_even [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A]
    (X Y : Doubled A) :
    (tensorObj X Y).even = (X.even ⊗ Y.even ⊞ X.odd ⊗ Y.odd) :=
  rfl

@[simp]
theorem tensorObj_odd [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A]
    (X Y : Doubled A) :
    (tensorObj X Y).odd = (X.even ⊗ Y.odd ⊞ X.odd ⊗ Y.even) :=
  rfl

/-- The graded tensor product of morphisms, blockwise. -/
def tensorHom [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A]
    {X₁ Y₁ X₂ Y₂ : Doubled A} (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) : tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂ :=
  homMk
    (biprod.map (evenHom f ⊗ₘ evenHom g) (oddHom f ⊗ₘ oddHom g))
    (biprod.map (evenHom f ⊗ₘ oddHom g) (oddHom f ⊗ₘ evenHom g))

/-- Left whiskering of super-objects, blockwise. -/
def whiskerLeft [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A]
    (X : Doubled A) {Y₁ Y₂ : Doubled A} (g : Y₁ ⟶ Y₂) :
    tensorObj X Y₁ ⟶ tensorObj X Y₂ :=
  homMk
    (biprod.map (X.even ◁ evenHom g) (X.odd ◁ oddHom g))
    (biprod.map (X.even ◁ oddHom g) (X.odd ◁ evenHom g))

/-- Right whiskering of super-objects, blockwise. -/
def whiskerRight [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A]
    {X₁ X₂ : Doubled A} (f : X₁ ⟶ X₂) (Y : Doubled A) :
    tensorObj X₁ Y ⟶ tensorObj X₂ Y :=
  homMk
    (biprod.map (evenHom f ▷ Y.even) (oddHom f ▷ Y.odd))
    (biprod.map (evenHom f ▷ Y.odd) (oddHom f ▷ Y.even))

/-- The even component of the associator: each of the four parity
blocks re-associates through `A`'s associator and is routed to the
matching block of the right-nested product. -/
def assocEven [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A]
    (X Y Z : Doubled A) :
    (tensorObj (tensorObj X Y) Z).even ≅
      (tensorObj X (tensorObj Y Z)).even where
  hom := biprod.desc
    (descRight
      ((α_ X.even Y.even Z.even).hom ≫
        X.even ◁ biprod.inl ≫ biprod.inl)
      ((α_ X.odd Y.odd Z.even).hom ≫
        X.odd ◁ biprod.inr ≫ biprod.inr))
    (descRight
      ((α_ X.even Y.odd Z.odd).hom ≫
        X.even ◁ biprod.inr ≫ biprod.inl)
      ((α_ X.odd Y.even Z.odd).hom ≫
        X.odd ◁ biprod.inl ≫ biprod.inr))
  inv := biprod.desc
    (descLeft
      ((α_ X.even Y.even Z.even).inv ≫
        biprod.inl ▷ Z.even ≫ biprod.inl)
      ((α_ X.even Y.odd Z.odd).inv ≫
        biprod.inl ▷ Z.odd ≫ biprod.inr))
    (descLeft
      ((α_ X.odd Y.even Z.odd).inv ≫
        biprod.inr ▷ Z.odd ≫ biprod.inr)
      ((α_ X.odd Y.odd Z.even).inv ≫
        biprod.inr ▷ Z.even ≫ biprod.inl))
  hom_inv_id := by
    apply biprod.hom_ext' <;> apply tensorRight_ext <;> simp
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply tensorLeft_ext <;> simp

/-- The odd component of the associator. -/
def assocOdd [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A]
    (X Y Z : Doubled A) :
    (tensorObj (tensorObj X Y) Z).odd ≅
      (tensorObj X (tensorObj Y Z)).odd where
  hom := biprod.desc
    (descRight
      ((α_ X.even Y.even Z.odd).hom ≫
        X.even ◁ biprod.inl ≫ biprod.inl)
      ((α_ X.odd Y.odd Z.odd).hom ≫
        X.odd ◁ biprod.inr ≫ biprod.inr))
    (descRight
      ((α_ X.even Y.odd Z.even).hom ≫
        X.even ◁ biprod.inr ≫ biprod.inl)
      ((α_ X.odd Y.even Z.even).hom ≫
        X.odd ◁ biprod.inl ≫ biprod.inr))
  inv := biprod.desc
    (descLeft
      ((α_ X.even Y.even Z.odd).inv ≫
        biprod.inl ▷ Z.odd ≫ biprod.inl)
      ((α_ X.even Y.odd Z.even).inv ≫
        biprod.inl ▷ Z.even ≫ biprod.inr))
    (descLeft
      ((α_ X.odd Y.even Z.even).inv ≫
        biprod.inr ▷ Z.even ≫ biprod.inr)
      ((α_ X.odd Y.odd Z.odd).inv ≫
        biprod.inr ▷ Z.odd ≫ biprod.inl))
  hom_inv_id := by
    apply biprod.hom_ext' <;> apply tensorRight_ext <;> simp
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply tensorLeft_ext <;> simp

end GradedTensor

section Total

/-- The summing functor `X ↦ X.even ⊞ X.odd`.  It is faithful, and
the monoidal coherences of the doubling are induced along it. -/
abbrev total [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A] :
    Doubled A ⥤ A where
  obj X := X.even ⊞ X.odd
  map f := biprod.map (evenHom f) (oddHom f)
  map_id _ := by ext <;> simp
  map_comp _ _ := by ext <;> simp

@[simp]
theorem total_obj [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    (X : Doubled A) :
    total.obj X = (X.even ⊞ X.odd) :=
  rfl

@[simp]
theorem total_map [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    {X Y : Doubled A} (f : X ⟶ Y) :
    total.map f = biprod.map (evenHom f) (oddHom f) :=
  rfl

/-- The summing functor is faithful: both components are recovered
as matrix entries. -/
instance [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A] :
    (total (A := A)).Faithful where
  map_injective {X Y f g} h := by
    ext
    · calc evenHom f
          = biprod.inl ≫ total.map f ≫ biprod.fst := by simp
        _ = biprod.inl ≫ total.map g ≫ biprod.fst := by rw [h]
        _ = evenHom g := by simp
    · calc oddHom f
          = biprod.inr ≫ total.map f ≫ biprod.snd := by simp
        _ = biprod.inr ≫ total.map g ≫ biprod.snd := by rw [h]
        _ = oddHom g := by simp

end Total

section UnitAndStruct

open ZeroObject

/-- The monoidal unit of the doubling: the unit of `A` in even
degree, the zero object in odd degree. -/
abbrev unit [Category.{v} A] [MonoidalCategory A] [HasZeroObject A] : Doubled A :=
  ⟨𝟙_ A, 0⟩

/-- A left tensor factor which is the zero object kills the
product. -/
theorem isZero_zeroTensor [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasZeroObject A]
    (M : A) : IsZero ((0 : A) ⊗ M) :=
  (tensorRight M).map_isZero (isZero_zero A)

/-- A right tensor factor which is the zero object kills the
product. -/
theorem isZero_tensorZero [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasZeroObject A]
    (M : A) : IsZero (M ⊗ (0 : A)) :=
  (tensorLeft M).map_isZero (isZero_zero A)

/-- Collapse of a unit block against a zero block, in the shape of
the left unitor components. -/
def leftUnitorComp [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (M M' : A) :
    ((𝟙_ A) ⊗ M ⊞ (0 : A) ⊗ M') ≅ M where
  hom := biprod.desc (λ_ M).hom 0
  inv := (λ_ M).inv ≫ biprod.inl
  hom_inv_id := by
    apply biprod.hom_ext'
    · simp
    · exact (isZero_zeroTensor M').eq_of_src _ _
  inv_hom_id := by simp

/-- Collapse of a unit block against a zero block, in the shape of
the even right unitor component. -/
def rightUnitorComp [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (M M' : A) :
    (M ⊗ 𝟙_ A ⊞ M' ⊗ (0 : A)) ≅ M where
  hom := biprod.desc (ρ_ M).hom 0
  inv := (ρ_ M).inv ≫ biprod.inl
  hom_inv_id := by
    apply biprod.hom_ext'
    · simp
    · exact (isZero_tensorZero M').eq_of_src _ _
  inv_hom_id := by simp

/-- Collapse of a unit block against a zero block, in the shape of
the odd right unitor component. -/
def rightUnitorCompOdd [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (M M' : A) :
    (M' ⊗ (0 : A) ⊞ M ⊗ 𝟙_ A) ≅ M where
  hom := biprod.desc 0 (ρ_ M).hom
  inv := (ρ_ M).inv ≫ biprod.inr
  hom_inv_id := by
    apply biprod.hom_ext'
    · exact (isZero_tensorZero M').eq_of_src _ _
    · simp
  inv_hom_id := by simp

/-- The monoidal skeleton of the doubling: graded tensor product,
unit `(𝟙_ A, 0)`, blockwise structural isomorphisms. -/
instance instMonoidalCategoryStruct
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A] :
    MonoidalCategoryStruct (Doubled A) where
  tensorObj := tensorObj
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  tensorHom := tensorHom
  tensorUnit := unit
  associator X Y Z := isoMk (assocEven X Y Z) (assocOdd X Y Z)
  leftUnitor X :=
    isoMk (leftUnitorComp X.even X.odd) (leftUnitorComp X.odd X.even)
  rightUnitor X :=
    isoMk (rightUnitorComp X.even X.odd)
      (rightUnitorCompOdd X.odd X.even)

/-! ### Components of the monoidal notation -/

@[simp]
theorem unit_even [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A] :
    (𝟙_ (Doubled A)).even = 𝟙_ A :=
  rfl

@[simp]
theorem unit_odd [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A] :
    (𝟙_ (Doubled A)).odd = (0 : A) :=
  rfl

@[simp]
theorem tensor_even [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (X Y : Doubled A) :
    (X ⊗ Y).even = (X.even ⊗ Y.even ⊞ X.odd ⊗ Y.odd) :=
  rfl

@[simp]
theorem tensor_odd [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (X Y : Doubled A) :
    (X ⊗ Y).odd = (X.even ⊗ Y.odd ⊞ X.odd ⊗ Y.even) :=
  rfl

@[simp]
theorem evenHom_tensor [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    {X₁ Y₁ X₂ Y₂ : Doubled A} (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    evenHom (f ⊗ₘ g) =
      biprod.map (evenHom f ⊗ₘ evenHom g) (oddHom f ⊗ₘ oddHom g) :=
  rfl

@[simp]
theorem oddHom_tensor [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    {X₁ Y₁ X₂ Y₂ : Doubled A} (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    oddHom (f ⊗ₘ g) =
      biprod.map (evenHom f ⊗ₘ oddHom g) (oddHom f ⊗ₘ evenHom g) :=
  rfl

@[simp]
theorem evenHom_whiskerLeft
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (X : Doubled A) {Y₁ Y₂ : Doubled A}
    (g : Y₁ ⟶ Y₂) :
    evenHom (X ◁ g) =
      biprod.map (X.even ◁ evenHom g) (X.odd ◁ oddHom g) :=
  rfl

@[simp]
theorem oddHom_whiskerLeft [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (X : Doubled A) {Y₁ Y₂ : Doubled A}
    (g : Y₁ ⟶ Y₂) :
    oddHom (X ◁ g) =
      biprod.map (X.even ◁ oddHom g) (X.odd ◁ evenHom g) :=
  rfl

@[simp]
theorem evenHom_whiskerRight
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    {X₁ X₂ : Doubled A} (f : X₁ ⟶ X₂)
    (Y : Doubled A) :
    evenHom (f ▷ Y) =
      biprod.map (evenHom f ▷ Y.even) (oddHom f ▷ Y.odd) :=
  rfl

@[simp]
theorem oddHom_whiskerRight
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    {X₁ X₂ : Doubled A} (f : X₁ ⟶ X₂)
    (Y : Doubled A) :
    oddHom (f ▷ Y) =
      biprod.map (evenHom f ▷ Y.odd) (oddHom f ▷ Y.even) :=
  rfl

@[simp]
theorem evenHom_associator_hom
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (X Y Z : Doubled A) :
    evenHom (α_ X Y Z).hom = (assocEven X Y Z).hom :=
  rfl

@[simp]
theorem oddHom_associator_hom
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (X Y Z : Doubled A) :
    oddHom (α_ X Y Z).hom = (assocOdd X Y Z).hom :=
  rfl

@[simp]
theorem evenHom_associator_inv
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (X Y Z : Doubled A) :
    evenHom (α_ X Y Z).inv = (assocEven X Y Z).inv :=
  rfl

@[simp]
theorem oddHom_associator_inv
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (X Y Z : Doubled A) :
    oddHom (α_ X Y Z).inv = (assocOdd X Y Z).inv :=
  rfl

@[simp]
theorem evenHom_leftUnitor_hom
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (X : Doubled A) :
    evenHom (λ_ X).hom = (leftUnitorComp X.even X.odd).hom :=
  rfl

@[simp]
theorem oddHom_leftUnitor_hom
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (X : Doubled A) :
    oddHom (λ_ X).hom = (leftUnitorComp X.odd X.even).hom :=
  rfl

@[simp]
theorem evenHom_leftUnitor_inv
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (X : Doubled A) :
    evenHom (λ_ X).inv = (leftUnitorComp X.even X.odd).inv :=
  rfl

@[simp]
theorem oddHom_leftUnitor_inv
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (X : Doubled A) :
    oddHom (λ_ X).inv = (leftUnitorComp X.odd X.even).inv :=
  rfl

@[simp]
theorem evenHom_rightUnitor_hom
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (X : Doubled A) :
    evenHom (ρ_ X).hom = (rightUnitorComp X.even X.odd).hom :=
  rfl

@[simp]
theorem oddHom_rightUnitor_hom
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (X : Doubled A) :
    oddHom (ρ_ X).hom = (rightUnitorCompOdd X.odd X.even).hom :=
  rfl

@[simp]
theorem evenHom_rightUnitor_inv
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (X : Doubled A) :
    evenHom (ρ_ X).inv = (rightUnitorComp X.even X.odd).inv :=
  rfl

@[simp]
theorem oddHom_rightUnitor_inv
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (X : Doubled A) :
    oddHom (ρ_ X).inv = (rightUnitorCompOdd X.odd X.even).inv :=
  rfl

/-- The multiplicative comparison of the summing functor: double
distribution followed by the parity shuffle. -/
def muIso [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (X Y : Doubled A) :
    total.obj X ⊗ total.obj Y ≅ total.obj (X ⊗ Y) where
  hom := descRight
    (descLeft (biprod.inl ≫ biprod.inl) (biprod.inl ≫ biprod.inr))
    (descLeft (biprod.inr ≫ biprod.inr) (biprod.inr ≫ biprod.inl))
  inv := biprod.desc
    (biprod.desc (biprod.inl ⊗ₘ biprod.inl)
      (biprod.inr ⊗ₘ biprod.inr))
    (biprod.desc (biprod.inl ⊗ₘ biprod.inr)
      (biprod.inr ⊗ₘ biprod.inl))
  hom_inv_id := by
    apply tensorRight_ext <;> apply tensorLeft_ext <;>
      simp [← tensorHom_def']
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext' <;>
      simp [tensorHom_def']

/-- The unit comparison of the summing functor. -/
def epsIso [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A] :
    𝟙_ A ≅ total.obj (𝟙_ (Doubled A)) where
  hom := biprod.inl
  inv := biprod.fst
  hom_inv_id := by simp
  inv_hom_id := by
    apply biprod.hom_ext'
    · simp
    · exact (isZero_zero A).eq_of_src _ _

/-- The summing functor intertwines the graded tensor of morphisms
with the ambient tensor, through the comparison `muIso`. -/
@[reassoc]
theorem total_tensorHom_muIso_inv
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    {X₁ Y₁ X₂ Y₂ : Doubled A}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    total.map (f ⊗ₘ g) ≫ (muIso Y₁ Y₂).inv =
      (muIso X₁ X₂).inv ≫ (total.map f ⊗ₘ total.map g) := by
  apply biprod.hom_ext' <;> apply biprod.hom_ext' <;>
    simp [muIso]

/-- The summing functor intertwines graded left whiskering with
ambient left whiskering, through the comparison `muIso`. -/
@[reassoc]
theorem total_whiskerLeft_muIso_inv
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (X : Doubled A)
    {Y₁ Y₂ : Doubled A} (g : Y₁ ⟶ Y₂) :
    total.map (X ◁ g) ≫ (muIso X Y₂).inv =
      (muIso X Y₁).inv ≫ (total.obj X ◁ total.map g) := by
  apply biprod.hom_ext' <;> apply biprod.hom_ext' <;>
    simp [muIso, ← id_tensorHom]

/-- The summing functor intertwines graded right whiskering with
ambient right whiskering, through the comparison `muIso`. -/
@[reassoc]
theorem total_whiskerRight_muIso_inv
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    {X₁ X₂ : Doubled A}
    (f : X₁ ⟶ X₂) (Y : Doubled A) :
    total.map (f ▷ Y) ≫ (muIso X₂ Y).inv =
      (muIso X₁ Y).inv ≫ (total.map f ▷ total.obj Y) := by
  apply biprod.hom_ext' <;> apply biprod.hom_ext' <;>
    simp [muIso, ← tensorHom_id]

/-- The summing functor intertwines the graded associator with the
ambient associator, through the comparison `muIso`. -/
@[reassoc]
theorem total_associator_muIso_inv
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (X Y Z : Doubled A) :
    total.map (α_ X Y Z).hom ≫ (muIso X (Y ⊗ Z)).inv ≫
        (𝟙 (total.obj X) ⊗ₘ (muIso Y Z).inv) =
      (muIso (X ⊗ Y) Z).inv ≫
        ((muIso X Y).inv ⊗ₘ 𝟙 (total.obj Z)) ≫
        (α_ (total.obj X) (total.obj Y) (total.obj Z)).hom := by
  apply biprod.hom_ext' <;> apply biprod.hom_ext' <;>
    apply tensorRight_ext <;>
    simp [muIso, assocEven, assocOdd, ← id_tensorHom,
      ← tensorHom_id, inl_id_descRight_assoc,
      inr_id_descRight_assoc]

/-- The inducing data exhibiting the graded structural morphisms
as the images of `A`'s structural morphisms under the parity
distributors. -/
def totalInducingData [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A] :
    Monoidal.InducingFunctorData (total (A := A)) where
  μIso := muIso
  εIso := epsIso
  whiskerLeft_eq X _ _ f := by
    rw [← Category.assoc, ← total_whiskerLeft_muIso_inv,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  whiskerRight_eq f Y := by
    rw [← Category.assoc, ← total_whiskerRight_muIso_inv,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  tensorHom_eq f g := by
    rw [← Category.assoc, ← total_tensorHom_muIso_inv,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  associator_eq X Y Z := by
    simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
      Iso.refl_hom, Category.assoc]
    rw [← total_associator_muIso_inv_assoc]
    simp
  leftUnitor_eq X := by
    simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
      Iso.refl_hom, Category.assoc]
    apply biprod.hom_ext' <;> apply biprod.hom_ext' <;>
      simp [muIso, epsIso, leftUnitorComp, tensorHom_def,
        whisker_exchange_assoc, -comp_whiskerRight,
        ← comp_whiskerRight_assoc]
  rightUnitor_eq X := by
    simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
      Iso.refl_hom, Category.assoc]
    apply biprod.hom_ext' <;> apply biprod.hom_ext' <;>
      simp [muIso, epsIso, rightUnitorComp, rightUnitorCompOdd,
        tensorHom_def, -whiskerLeft_comp, ← whiskerLeft_comp_assoc]

/-- The doubling of a monoidal category is monoidal, with the
graded tensor product: the coherences are induced along the
faithful summing functor. -/
instance instMonoidalCategory
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A] :
    MonoidalCategory (Doubled A) :=
  Monoidal.induced total totalInducingData

/-- The summing functor is monoidal. -/
instance [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A] :
    (total (A := A)).Monoidal :=
  Monoidal.fromInducedMonoidal total totalInducingData

end UnitAndStruct

section MonoidalPreadditive

private theorem doubled_whiskerLeft_zero
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (X Y Z : Doubled A) : X ◁ (0 : Y ⟶ Z) = 0 := by
  ext
  · change biprod.map (X.even ◁ (0 : Y.even ⟶ Z.even))
        (X.odd ◁ (0 : Y.odd ⟶ Z.odd)) =
      (0 : X.even ⊗ Y.even ⊞ X.odd ⊗ Y.odd ⟶
        X.even ⊗ Z.even ⊞ X.odd ⊗ Z.odd)
    apply biprod.hom_ext <;> simp
  · change biprod.map (X.even ◁ (0 : Y.odd ⟶ Z.odd))
        (X.odd ◁ (0 : Y.even ⟶ Z.even)) =
      (0 : X.even ⊗ Y.odd ⊞ X.odd ⊗ Y.even ⟶
        X.even ⊗ Z.odd ⊞ X.odd ⊗ Z.even)
    apply biprod.hom_ext <;> simp

/-- The doubling of a monoidal preadditive category is monoidal
preadditive, componentwise.  Each component equation is restated
(`show`) with its objects in literal biproduct form, so that the
ambient simp lemmas apply. -/
instance instMonoidalPreadditive
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A] :
    MonoidalPreadditive (Doubled A) where
  whiskerLeft_zero := doubled_whiskerLeft_zero _ _ _
  zero_whiskerRight {X Y Z} := by
    ext
    · change biprod.map ((0 : Y.even ⟶ Z.even) ▷ X.even)
          ((0 : Y.odd ⟶ Z.odd) ▷ X.odd) =
        (0 : Y.even ⊗ X.even ⊞ Y.odd ⊗ X.odd ⟶
          Z.even ⊗ X.even ⊞ Z.odd ⊗ X.odd)
      apply biprod.hom_ext <;> simp
    · change biprod.map ((0 : Y.even ⟶ Z.even) ▷ X.odd)
          ((0 : Y.odd ⟶ Z.odd) ▷ X.even) =
        (0 : Y.even ⊗ X.odd ⊞ Y.odd ⊗ X.even ⟶
          Z.even ⊗ X.odd ⊞ Z.odd ⊗ X.even)
      apply biprod.hom_ext <;> simp
  whiskerLeft_add {X Y Z} f g := by
    ext
    · change biprod.map (X.even ◁ (evenHom f + evenHom g))
          (X.odd ◁ (oddHom f + oddHom g)) =
        biprod.map (X.even ◁ evenHom f) (X.odd ◁ oddHom f) +
          biprod.map (X.even ◁ evenHom g) (X.odd ◁ oddHom g)
      apply biprod.hom_ext <;> simp
    · change biprod.map (X.even ◁ (oddHom f + oddHom g))
          (X.odd ◁ (evenHom f + evenHom g)) =
        biprod.map (X.even ◁ oddHom f) (X.odd ◁ evenHom f) +
          biprod.map (X.even ◁ oddHom g) (X.odd ◁ evenHom g)
      apply biprod.hom_ext <;> simp
  add_whiskerRight {X Y Z} f g := by
    ext
    · change biprod.map ((evenHom f + evenHom g) ▷ X.even)
          ((oddHom f + oddHom g) ▷ X.odd) =
        biprod.map (evenHom f ▷ X.even) (oddHom f ▷ X.odd) +
          biprod.map (evenHom g ▷ X.even) (oddHom g ▷ X.odd)
      apply biprod.hom_ext <;> simp
    · change biprod.map ((evenHom f + evenHom g) ▷ X.odd)
          ((oddHom f + oddHom g) ▷ X.even) =
        biprod.map (evenHom f ▷ X.odd) (oddHom f ▷ X.even) +
          biprod.map (evenHom g ▷ X.odd) (oddHom g ▷ X.even)
      apply biprod.hom_ext <;> simp

/-- The doubling of a monoidal ℂ-linear category is monoidal
ℂ-linear, componentwise. -/
instance instMonoidalLinear
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    [CategoryTheory.Linear ℂ A]
    [MonoidalLinear ℂ A] : MonoidalLinear ℂ (Doubled A) where
  whiskerLeft_smul X {Y Z} r f := by
    ext
    · change biprod.map (X.even ◁ (r • evenHom f))
          (X.odd ◁ (r • oddHom f)) =
        r • biprod.map (X.even ◁ evenHom f) (X.odd ◁ oddHom f)
      apply biprod.hom_ext <;> simp
    · change biprod.map (X.even ◁ (r • oddHom f))
          (X.odd ◁ (r • evenHom f)) =
        r • biprod.map (X.even ◁ oddHom f) (X.odd ◁ evenHom f)
      apply biprod.hom_ext <;> simp
  smul_whiskerRight r {Y Z} f X := by
    ext
    · change biprod.map ((r • evenHom f) ▷ X.even)
          ((r • oddHom f) ▷ X.odd) =
        r • biprod.map (evenHom f ▷ X.even) (oddHom f ▷ X.odd)
      apply biprod.hom_ext <;> simp
    · change biprod.map ((r • evenHom f) ▷ X.odd)
          ((r • oddHom f) ▷ X.even) =
        r • biprod.map (evenHom f ▷ X.odd) (oddHom f ▷ X.even)
      apply biprod.hom_ext <;> simp

end MonoidalPreadditive

section Braided

/-- The even component of the Koszul braiding: `A`'s braiding on
each parity block, with the sign `-1` on the odd⊗odd block. -/
def braidingEven [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    [SymmetricCategory A]
    (X Y : Doubled A) : (X ⊗ Y).even ≅ (Y ⊗ X).even where
  hom := biprod.map (β_ X.even Y.even).hom (-(β_ X.odd Y.odd).hom)
  inv := biprod.map (β_ Y.even X.even).hom (-(β_ Y.odd X.odd).hom)
  hom_inv_id := by apply biprod.hom_ext <;> simp
  inv_hom_id := by apply biprod.hom_ext <;> simp

/-- The odd component of the Koszul braiding: the two mixed blocks
swap through `A`'s braiding, with no sign. -/
def braidingOdd [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    [SymmetricCategory A]
    (X Y : Doubled A) : (X ⊗ Y).odd ≅ (Y ⊗ X).odd where
  hom := biprod.desc ((β_ X.even Y.odd).hom ≫ biprod.inr)
    ((β_ X.odd Y.even).hom ≫ biprod.inl)
  inv := biprod.desc ((β_ Y.even X.odd).hom ≫ biprod.inr)
    ((β_ Y.odd X.even).hom ≫ biprod.inl)
  hom_inv_id := by apply biprod.hom_ext' <;> simp
  inv_hom_id := by apply biprod.hom_ext' <;> simp

/-- The doubling of a symmetric category is braided, with the
Koszul-signed braiding. -/
instance instBraidedCategory
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    [SymmetricCategory A] : BraidedCategory (Doubled A) where
  braiding X Y := isoMk (braidingEven X Y) (braidingOdd X Y)
  braiding_naturality_right X {_ _} f := by
    ext <;> apply biprod.hom_ext' <;>
      simp [braidingEven, braidingOdd]
  braiding_naturality_left f Z := by
    ext <;> apply biprod.hom_ext' <;>
      simp [braidingEven, braidingOdd]
  hexagon_forward X Y Z := by
    ext
    · apply biprod.hom_ext'
      · apply tensorRight_ext
        · simp [braidingEven, braidingOdd, assocEven]
        · simp [braidingEven, braidingOdd, assocEven,
            Preadditive.neg_comp, Preadditive.comp_neg]
      · apply tensorRight_ext
        · simp [braidingEven, braidingOdd, assocEven]
        · simp [braidingEven, braidingOdd, assocEven,
            Preadditive.neg_comp, Preadditive.comp_neg]
    · apply biprod.hom_ext' <;> apply tensorRight_ext <;>
        simp [braidingEven, braidingOdd,  assocOdd,
          Preadditive.neg_comp, Preadditive.comp_neg]
  hexagon_reverse X Y Z := by
    ext
    · apply biprod.hom_ext'
      · apply tensorLeft_ext
        · simp [braidingEven, braidingOdd, assocEven]
        · simp [braidingEven, braidingOdd, assocEven,
            Preadditive.neg_comp, Preadditive.comp_neg]
      · apply tensorLeft_ext
        · simp [braidingEven, braidingOdd, assocEven,
            Preadditive.neg_comp, Preadditive.comp_neg]
        · simp [braidingEven, braidingOdd, assocEven]
    · apply biprod.hom_ext' <;> apply tensorLeft_ext <;>
        simp [braidingEven, braidingOdd,  assocOdd,
          Preadditive.neg_comp, Preadditive.comp_neg]

/-- The doubling of a symmetric category is symmetric: the Koszul
sign squares away. -/
instance instSymmetricCategory
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    [SymmetricCategory A] : SymmetricCategory (Doubled A) where
  symmetry X Y := by
    ext
    · change biprod.map (β_ X.even Y.even).hom
          (-(β_ X.odd Y.odd).hom) ≫
        biprod.map (β_ Y.even X.even).hom
          (-(β_ Y.odd X.odd).hom) =
        𝟙 (X.even ⊗ Y.even ⊞ X.odd ⊗ Y.odd)
      apply biprod.hom_ext <;> simp
    · change biprod.desc ((β_ X.even Y.odd).hom ≫ biprod.inr)
          ((β_ X.odd Y.even).hom ≫ biprod.inl) ≫
        biprod.desc ((β_ Y.even X.odd).hom ≫ biprod.inr)
          ((β_ Y.odd X.even).hom ≫ biprod.inl) =
        𝟙 (X.even ⊗ Y.odd ⊞ X.odd ⊗ Y.even)
      apply biprod.hom_ext' <;> simp

end Braided

section EvenEmbed

open ZeroObject

/-- A biproduct of two zero objects is a zero object. -/
theorem isZero_biprod [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    {M N : A} (hM : IsZero M) (hN : IsZero N) :
    IsZero (M ⊞ N) where
  unique_to _ :=
    ⟨⟨⟨biprod.desc (hM.to_ _) (hN.to_ _)⟩, fun _ =>
      biprod.hom_ext' _ _ (hM.eq_of_src _ _) (hN.eq_of_src _ _)⟩⟩
  unique_from _ :=
    ⟨⟨⟨biprod.lift (hM.from_ _) (hN.from_ _)⟩, fun _ =>
      biprod.hom_ext _ _ (hM.eq_of_tgt _ _) (hN.eq_of_tgt _ _)⟩⟩

/-- The even embedding `X ↦ (X, 0)`. -/
abbrev evenEmbed
    [Category.{v} A] [Preadditive A] [HasZeroObject A] : A ⥤ Doubled A where
  obj X := ⟨X, 0⟩
  map f := homMk f (𝟙 (0 : A))
  map_id _ := rfl
  map_comp _ _ := by ext; simp

@[simp]
theorem evenEmbed_obj_even [Category.{v} A] [Preadditive A] [HasZeroObject A]
    (X : A) : (evenEmbed.obj X).even = X :=
  rfl

@[simp]
theorem evenEmbed_obj_odd [Category.{v} A] [Preadditive A] [HasZeroObject A]
    (X : A) :
    (evenEmbed.obj X).odd = (0 : A) :=
  rfl

@[simp]
theorem evenHom_evenEmbed_map [Category.{v} A] [Preadditive A] [HasZeroObject A]
    {X Y : A} (f : X ⟶ Y) :
    evenHom (evenEmbed.map f) = f :=
  rfl

/-- The even embedding is faithful. -/
instance [Category.{v} A] [Preadditive A] [HasZeroObject A] :
    (evenEmbed (A := A)).Faithful where
  map_injective h := congrArg evenHom h

/-- The even embedding is full. -/
instance [Category.{v} A] [Preadditive A] [HasZeroObject A] :
    (evenEmbed (A := A)).Full where
  map_surjective f :=
    ⟨evenHom f, hom_ext rfl ((isZero_zero A).eq_of_src _ _)⟩

/-- The even embedding is additive. -/
instance [Category.{v} A] [Preadditive A] [HasZeroObject A] :
    (evenEmbed (A := A)).Additive where
  map_add := by
    intros
    ext
    · rfl

/-- The even embedding is ℂ-linear. -/
instance [Category.{v} A] [Preadditive A] [HasZeroObject A]
    [CategoryTheory.Linear ℂ A] :
    (evenEmbed (A := A)).Linear ℂ where
  map_smul := by
    intros
    ext
    · rfl

/-- The even embedding is monoidal up to isomorphism: the graded
tensor of two even objects collapses to the even tensor. -/
def evenEmbedTensorIso [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (X Y : A) :
    evenEmbed.obj X ⊗ evenEmbed.obj Y ≅ evenEmbed.obj (X ⊗ Y) :=
  isoMk (isoBiprodZero (isZero_zeroTensor _)).symm
    (((isZero_biprod (isZero_tensorZero _) (isZero_zeroTensor _)).iso
      (isZero_zero A)))

/-- The even embedding intertwines the braidings through
`evenEmbedTensorIso`. -/
theorem evenEmbedTensorIso_braided
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    [SymmetricCategory A] (X Y : A) :
    (β_ (evenEmbed.obj X) (evenEmbed.obj Y)).hom ≫
        (evenEmbedTensorIso Y X).hom =
      (evenEmbedTensorIso X Y).hom ≫ evenEmbed.map (β_ X Y).hom := by
  ext
  · change biprod.map (β_ X Y).hom (-(β_ (0 : A) (0 : A)).hom) ≫
        biprod.fst = biprod.fst ≫ (β_ X Y).hom
    simp

/-- The unit comparison of the even embedding: definitional. -/
def evenEmbedUnitIso [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A] :
    𝟙_ (Doubled A) ≅ evenEmbed.obj (𝟙_ A) :=
  Iso.refl _

end EvenEmbed

section OddUnit

open ZeroObject

/-- The odd unit: the unit of `A` placed in odd degree.  Together
with `oddUnitSq` and `braiding_oddUnit` this is exactly the
invertible odd object required by Deligne 2.9. -/
abbrev oddUnit
    [Category.{v} A] [MonoidalCategory A] [HasZeroObject A] : Doubled A :=
  ⟨0, 𝟙_ A⟩

@[simp]
theorem oddUnit_even [Category.{v} A] [MonoidalCategory A] [HasZeroObject A] :
    (oddUnit (A := A)).even = (0 : A) :=
  rfl

@[simp]
theorem oddUnit_odd [Category.{v} A] [MonoidalCategory A] [HasZeroObject A] :
    (oddUnit (A := A)).odd = 𝟙_ A :=
  rfl

/-- The odd unit squares to the monoidal unit. -/
def oddUnitSq [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A] :
    oddUnit ⊗ oddUnit ≅ 𝟙_ (Doubled A) :=
  isoMk
    { hom := biprod.desc 0 (λ_ (𝟙_ A)).hom
      inv := (λ_ (𝟙_ A)).inv ≫ biprod.inr
      hom_inv_id := by
        apply biprod.hom_ext'
        · exact (isZero_zeroTensor _).eq_of_src _ _
        · simp
      inv_hom_id := by simp }
    ((isZero_biprod (isZero_zeroTensor _) (isZero_tensorZero _)).iso
      (isZero_zero A))

/-- The braiding of the odd unit with itself is `-1`: the Koszul
sign made visible on a single object. -/
theorem braiding_oddUnit [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    [SymmetricCategory A] :
    (β_ (oddUnit (A := A)) oddUnit).hom = -𝟙 (oddUnit ⊗ oddUnit) := by
  ext
  · change biprod.map (β_ (0 : A) (0 : A)).hom
        (-(β_ (𝟙_ A) (𝟙_ A)).hom) =
      -𝟙 ((0 : A) ⊗ (0 : A) ⊞ 𝟙_ A ⊗ 𝟙_ A)
    apply biprod.hom_ext
    · exact (isZero_zeroTensor _).eq_of_tgt _ _
    · simp [braiding_tensorUnit_right, ← unitors_equal,
        Preadditive.neg_comp, Preadditive.comp_neg]
  · exact (isZero_biprod (isZero_zeroTensor _)
      (isZero_tensorZero _)).eq_of_src _ _

end OddUnit

section Biproducts

/-- The componentwise binary bicone on a pair of super-objects. -/
def binaryBicone [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    (X Y : Doubled A) : BinaryBicone X Y where
  pt := ⟨X.even ⊞ Y.even, X.odd ⊞ Y.odd⟩
  fst := homMk biprod.fst biprod.fst
  snd := homMk biprod.snd biprod.snd
  inl := homMk biprod.inl biprod.inl
  inr := homMk biprod.inr biprod.inr
  inl_fst := by ext <;> simp
  inl_snd := by ext <;> simp
  inr_fst := by ext <;> simp
  inr_snd := by ext <;> simp

/-- The doubling has componentwise binary biproducts. -/
instance instHasBinaryBiproducts
    [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A] :
    HasBinaryBiproducts (Doubled A) where
  has_binary_biproduct X Y :=
    hasBinaryBiproduct_of_total (binaryBicone X Y) (by
      ext
      · change biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr =
          𝟙 (X.even ⊞ Y.even)
        exact biprod.total
      · change biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr =
          𝟙 (X.odd ⊞ Y.odd)
        exact biprod.total)

/-- The doubling has finite products: it has a zero object and
componentwise binary biproducts. -/
instance instHasFiniteProducts
    [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    [HasZeroObject A] :
    HasFiniteProducts (Doubled A) :=
  hasFiniteProducts_of_has_binary_and_terminal

end Biproducts

section Decomposition

open ZeroObject

/-- Every super-object is the biproduct of its even part and the
odd-unit twist of its odd part: the decomposition through which
Schur-vanishing transports from `A` to the doubling. -/
def decomposition [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (X : Doubled A) :
    X ≅ evenEmbed.obj X.even ⊞ (oddUnit ⊗ evenEmbed.obj X.odd) where
  hom := biprod.lift (homMk (𝟙 X.even) 0)
    (homMk 0 ((λ_ X.odd).inv ≫ biprod.inr))
  inv := biprod.desc (homMk (𝟙 X.even) 0)
    (homMk 0 (biprod.desc 0 (λ_ X.odd).hom))
  hom_inv_id := by
    rw [biprod.lift_desc]
    ext
    · change 𝟙 X.even ≫ 𝟙 X.even +
          (0 : X.even ⟶ ((0 : A) ⊗ X.odd ⊞ 𝟙_ A ⊗ (0 : A))) ≫
            (0 : ((0 : A) ⊗ X.odd ⊞ 𝟙_ A ⊗ (0 : A)) ⟶ X.even) =
        𝟙 X.even
      simp
    · change (0 : X.odd ⟶ (0 : A)) ≫ (0 : (0 : A) ⟶ X.odd) +
          ((λ_ X.odd).inv ≫ biprod.inr) ≫
            biprod.desc 0 (λ_ X.odd).hom =
        𝟙 X.odd
      simp
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext
    · -- (inl, fst)
      ext
      · simp
    · -- (inl, snd)
      ext
      · exact (isZero_biprod (isZero_zeroTensor _)
          (isZero_tensorZero _)).eq_of_tgt _ _
    · -- (inr, fst)
      ext
      · exact (isZero_biprod (isZero_zeroTensor _)
          (isZero_tensorZero _)).eq_of_src _ _
    · -- (inr, snd)
      rw [biprod.inr_desc_assoc, Category.assoc, biprod.lift_snd,
        Category.comp_id, biprod.inr_snd]
      ext
      · exact (isZero_biprod (isZero_zeroTensor _)
          (isZero_tensorZero _)).eq_of_src _ _
      · change biprod.desc 0 (λ_ X.odd).hom ≫
            (λ_ X.odd).inv ≫ biprod.inr =
          𝟙 ((0 : A) ⊗ (0 : A) ⊞ 𝟙_ A ⊗ X.odd)
        apply biprod.hom_ext'
        · exact (isZero_zeroTensor _).eq_of_src _ _
        · simp

end Decomposition

section Kernels

/-- The componentwise kernel fork of a morphism of
super-objects. -/
def kernelFork [Category.{v} A] [Preadditive A] [HasKernels A]
    {X Y : Doubled A} (f : X ⟶ Y) : KernelFork f :=
  KernelFork.ofι
    (homMk (kernel.ι (evenHom f)) (kernel.ι (oddHom f)) :
      (⟨kernel (evenHom f), kernel (oddHom f)⟩ : Doubled A) ⟶ X)
    (by ext <;> simp)

/-- The componentwise kernel fork is limiting. -/
def kernelForkIsLimit [Category.{v} A] [Preadditive A] [HasKernels A]
    {X Y : Doubled A} (f : X ⟶ Y) :
    IsLimit (kernelFork f) :=
  KernelFork.IsLimit.ofι _ (by ext <;> simp)
    (fun g' eq' => homMk
      (kernel.lift _ (evenHom g')
        (show _ from congrArg evenHom eq'))
      (kernel.lift _ (oddHom g')
        (show _ from congrArg oddHom eq')))
    (fun g' eq' => by ext <;> simp)
    (fun g' eq' m hm => by
      ext
      · simp only [evenHom_homMk, kernel.lift_ι]
        exact congrArg evenHom hm
      · simp only [oddHom_homMk, kernel.lift_ι]
        exact congrArg oddHom hm)

/-- The doubling has componentwise kernels. -/
instance instHasKernels [Category.{v} A] [Preadditive A] [HasKernels A] :
    HasKernels (Doubled A) where
  has_limit f := HasLimit.mk
    { cone := kernelFork f
      isLimit := kernelForkIsLimit f }

end Kernels

section Cokernels

/-- The componentwise cokernel cofork of a morphism of
super-objects. -/
def cokernelCofork [Category.{v} A] [Preadditive A] [HasCokernels A]
    {X Y : Doubled A} (f : X ⟶ Y) :
    CokernelCofork f :=
  CokernelCofork.ofπ
    (homMk (cokernel.π (evenHom f)) (cokernel.π (oddHom f)) :
      Y ⟶ (⟨cokernel (evenHom f), cokernel (oddHom f)⟩ : Doubled A))
    (by ext <;> simp)

/-- The componentwise cokernel cofork is colimiting. -/
def cokernelCoforkIsColimit [Category.{v} A] [Preadditive A] [HasCokernels A]
    {X Y : Doubled A} (f : X ⟶ Y) :
    IsColimit (cokernelCofork f) :=
  CokernelCofork.IsColimit.ofπ _ (by ext <;> simp)
    (fun g' eq' => homMk
      (cokernel.desc _ (evenHom g')
        (show _ from congrArg evenHom eq'))
      (cokernel.desc _ (oddHom g')
        (show _ from congrArg oddHom eq')))
    (fun g' eq' => by ext <;> simp)
    (fun g' eq' m hm => by
      ext
      · simp only [evenHom_homMk, cokernel.π_desc]
        exact congrArg evenHom hm
      · simp only [oddHom_homMk, cokernel.π_desc]
        exact congrArg oddHom hm)

/-- The doubling has componentwise cokernels. -/
instance instHasCokernels [Category.{v} A] [Preadditive A] [HasCokernels A] :
    HasCokernels (Doubled A) where
  has_colimit f := HasColimit.mk
    { cocone := cokernelCofork f
      isColimit := cokernelCoforkIsColimit f }

end Cokernels

section IsoComponents

/-- A morphism of super-objects whose two components are
isomorphisms is an isomorphism. -/
theorem isIso_of_components [Category.{v} A]
    {X Y : Doubled A} (f : X ⟶ Y)
    [IsIso (evenHom f)] [IsIso (oddHom f)] : IsIso f :=
  ⟨homMk (inv (evenHom f)) (inv (oddHom f)),
    hom_ext (by simp) (by simp), hom_ext (by simp) (by simp)⟩

end IsoComponents

section Rigid

open ZeroObject

/-- Componentwise exact pairings pair the doubled objects: the
evaluations and coevaluations act blockwise on matching parities,
and the odd components vanish. -/
@[reducible]
def exactPairing [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (P Q : Doubled A) [ExactPairing P.even Q.even]
    [ExactPairing P.odd Q.odd] : ExactPairing P Q where
  coevaluation' := homMk
    (biprod.lift (η_ P.even Q.even) (η_ P.odd Q.odd)) 0
  evaluation' := homMk
    (biprod.desc (ε_ P.even Q.even) (ε_ P.odd Q.odd)) 0
  coevaluation_evaluation' := by
    ext
    · apply biprod.hom_ext'
      · simp [assocEven, rightUnitorComp, leftUnitorComp]
      · exact (isZero_tensorZero _).eq_of_src _ _
    · apply biprod.hom_ext'
      · exact (isZero_tensorZero _).eq_of_src _ _
      · simp [assocOdd, rightUnitorCompOdd, leftUnitorComp]
  evaluation_coevaluation' := by
    ext
    · apply biprod.hom_ext'
      · simp [assocEven, rightUnitorComp, leftUnitorComp]
      · exact (isZero_zeroTensor _).eq_of_src _ _
    · apply biprod.hom_ext'
      · simp [assocOdd, rightUnitorCompOdd, leftUnitorComp]
      · exact (isZero_zeroTensor _).eq_of_src _ _

/-- The doubling of a right rigid category is right rigid, with
componentwise duals. -/
instance instRightRigidCategory
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    [RightRigidCategory A] :
    RightRigidCategory (Doubled A) where
  rightDual X :=
    { rightDual := ⟨X.evenᘁ, X.oddᘁ⟩
      exact := exactPairing X ⟨X.evenᘁ, X.oddᘁ⟩ }

/-- The doubling of a left rigid category is left rigid, with
componentwise duals. -/
instance instLeftRigidCategory
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    [LeftRigidCategory A] :
    LeftRigidCategory (Doubled A) where
  leftDual X :=
    { leftDual := ⟨ᘁX.even, ᘁX.odd⟩
      exact := exactPairing ⟨ᘁX.even, ᘁX.odd⟩ X }

/-- The doubling of a rigid category is rigid. -/
instance instRigidCategory [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    [RigidCategory A] :
    RigidCategory (Doubled A) where

end Rigid

end Doubled

end

end RS
