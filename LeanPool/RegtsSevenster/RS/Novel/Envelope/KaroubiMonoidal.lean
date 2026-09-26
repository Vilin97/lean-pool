/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Monoidal structure on the Karoubi envelope

For a monoidal category `C`, the Karoubi envelope `Karoubi C` inherits a
monoidal structure:

* **Objects**: `(A, p) ⊗ (B, q) = (A ⊗ B, p ⊗ₘ q)`, the tensor of
  idempotents being idempotent by the interchange law.
* **Morphisms**: `f ⊗ₘ g` on underlying morphisms.
* **Unit**: `(𝟙_ C, 𝟙 (𝟙_ C))`.
* **Structural isomorphisms**: conjugates of the associators and unitors
  of `C` by the idempotents — e.g. the associator has underlying morphism
  `((p ⊗ₘ q) ⊗ₘ r) ≫ α_{A,B,C}.hom`.

The canonical functor `toKaroubi C : C ⥤ Karoubi C` is strong monoidal.

When `C` is braided (respectively symmetric), so is `Karoubi C`.
-/

@[expose] public section

namespace RS

open CategoryTheory CategoryTheory.Category CategoryTheory.Idempotents
open CategoryTheory.MonoidalCategory

universe v u

variable {C : Type u}

/-! ### Auxiliary lemmas for idempotent-conjugated morphisms -/

/-- The tensor product of idempotents is idempotent. -/
private theorem tensorHom_idem [Category.{v} C] [MonoidalCategory C]
    {A B : C} {p : A ⟶ A} {q : B ⟶ B}
    (hp : p ≫ p = p) (hq : q ≫ q = q) :
    (p ⊗ₘ q) ≫ (p ⊗ₘ q) = p ⊗ₘ q := by
  rw [tensorHom_comp_tensorHom, hp, hq]

/-- Comm condition for tensor product morphisms in the Karoubi envelope. -/
private theorem karoubi_tensorHom_comm [Category.{v} C] [MonoidalCategory C]
    {P₁ Q₁ P₂ Q₂ : Karoubi C} (f : P₁ ⟶ Q₁) (g : P₂ ⟶ Q₂) :
    (P₁.p ⊗ₘ P₂.p) ≫ (f.f ⊗ₘ g.f) ≫ (Q₁.p ⊗ₘ Q₂.p) = f.f ⊗ₘ g.f := by
  simp only [tensorHom_comp_tensorHom, Karoubi.p_comp, Karoubi.comp_p]

/-- The Karoubi comm condition `p ≫ (p ≫ f) ≫ q = p ≫ f` holds whenever `p, q`
are idempotent and `p ≫ f = f ≫ q` (naturality). -/
private theorem conj_comm [Category.{v} C]
    {A B : C} (p : A ⟶ A) (q : B ⟶ B)
    (hp : p ≫ p = p) (hq : q ≫ q = q) (f : A ⟶ B)
    (hnat : p ≫ f = f ≫ q) :
    p ≫ (p ≫ f) ≫ q = p ≫ f := by
  simp only [← assoc, hp]
  rw [hnat, assoc, hq]

/-- If `p ≫ φ.hom = φ.hom ≫ q` and `p` is idempotent, then
`(p ≫ φ.hom) ≫ (q ≫ φ.inv) = p`. -/
private theorem conj_iso_hom_inv [Category.{v} C]
    {A B : C} (p : A ⟶ A) (q : B ⟶ B)
    (hp : p ≫ p = p) (φ : A ≅ B) (hnat : p ≫ φ.hom = φ.hom ≫ q) :
    (p ≫ φ.hom) ≫ (q ≫ φ.inv) = p := by
  have hnat_assoc : ∀ {E : C} (h : B ⟶ E),
      p ≫ φ.hom ≫ h = φ.hom ≫ q ≫ h := by
    intro E h; rw [← assoc, hnat, assoc]
  rw [assoc, ← hnat_assoc, Iso.hom_inv_id, comp_id, hp]

/-- If `p ≫ φ.hom = φ.hom ≫ q` and `q` is idempotent, then
`(q ≫ φ.inv) ≫ (p ≫ φ.hom) = q`. -/
private theorem conj_iso_inv_hom [Category.{v} C]
    {A B : C} (p : A ⟶ A) (q : B ⟶ B)
    (hq : q ≫ q = q) (φ : A ≅ B) (hnat : p ≫ φ.hom = φ.hom ≫ q) :
    (q ≫ φ.inv) ≫ (p ≫ φ.hom) = q := by
  have inv_nat : q ≫ φ.inv = φ.inv ≫ p := by
    rw [← cancel_mono φ.hom, assoc, Iso.inv_hom_id, comp_id,
        assoc, hnat, ← assoc, Iso.inv_hom_id, id_comp]
  have inv_nat_assoc : ∀ {E : C} (h : A ⟶ E),
      q ≫ φ.inv ≫ h = φ.inv ≫ p ≫ h := by
    intro E h; rw [← assoc, inv_nat, assoc]
  rw [assoc, ← inv_nat_assoc, Iso.inv_hom_id, comp_id, hq]

/-! ### Decomposition of tensor products with compositions

When one argument of `⊗ₘ` is idempotent, a composition in the other argument
can be extracted as a composition of tensor products.  These lemmas are needed
because `rw` / `simp` cannot rewrite subexpressions *inside* `⊗ₘ` arguments
due to dependent-type motive construction failures. -/

/-- Decompose `(f ≫ g) ⊗ₘ q` into `(f ⊗ₘ q) ≫ (g ⊗ₘ q)` when `q` is
idempotent. -/
private theorem tensorHom_comp_left_idem_right
    [Category.{v} C] [MonoidalCategory C]
    {A B D : C}
    {p : A ⟶ A} (f : A ⟶ B) (q : D ⟶ D) (hq : q ≫ q = q) :
    (p ≫ f) ⊗ₘ q = (p ⊗ₘ q) ≫ (f ⊗ₘ q) := by
  have : (p ≫ f) ⊗ₘ q = (p ≫ f) ⊗ₘ (q ≫ q) := by congr 1; exact hq.symm
  rw [this, ← tensorHom_comp_tensorHom]

/-- Decompose `p ⊗ₘ (f ≫ g)` into `(p ⊗ₘ f) ≫ (p ⊗ₘ g)` when `p` is
idempotent. -/
private theorem tensorHom_idem_left_comp_right
    [Category.{v} C] [MonoidalCategory C]
    {A D E : C}
    (p : A ⟶ A) (hp : p ≫ p = p) {q : D ⟶ D} (g : D ⟶ E) :
    p ⊗ₘ (q ≫ g) = (p ⊗ₘ q) ≫ (p ⊗ₘ g) := by
  have : p ⊗ₘ (q ≫ g) = (p ≫ p) ⊗ₘ (q ≫ g) := by congr 1; exact hp.symm
  rw [this, ← tensorHom_comp_tensorHom]

/-! ### Naturality of structural isomorphisms with idempotents

These lemmas state the naturality of the associator, left unitor, and
right unitor (and their inverses) applied to the idempotent morphisms of
Karoubi objects.  They are proved outside any Karoubi-struct context so
that `rw` with `id_tensorHom`/`tensorHom_id` avoids dependent-type
motive failures. -/

private theorem assoc_nat [Category.{v} C] [MonoidalCategory C]
    (X Y Z : Karoubi C) :
    ((X.p ⊗ₘ Y.p) ⊗ₘ Z.p) ≫ (α_ X.X Y.X Z.X).hom =
    (α_ X.X Y.X Z.X).hom ≫ (X.p ⊗ₘ (Y.p ⊗ₘ Z.p)) :=
  associator_naturality X.p Y.p Z.p

private theorem assoc_inv_nat [Category.{v} C] [MonoidalCategory C]
    (X Y Z : Karoubi C) :
    (X.p ⊗ₘ (Y.p ⊗ₘ Z.p)) ≫ (α_ X.X Y.X Z.X).inv =
    (α_ X.X Y.X Z.X).inv ≫ ((X.p ⊗ₘ Y.p) ⊗ₘ Z.p) := by
  rw [← cancel_mono (α_ X.X Y.X Z.X).hom, assoc, Iso.inv_hom_id, comp_id,
      assoc, associator_naturality, ← assoc, Iso.inv_hom_id, id_comp]

private theorem leftUnit_nat [Category.{v} C] [MonoidalCategory C]
    (X : Karoubi C) :
    (𝟙 (𝟙_ C) ⊗ₘ X.p) ≫ (λ_ X.X).hom = (λ_ X.X).hom ≫ X.p := by
  rw [id_tensorHom]; exact leftUnitor_naturality X.p

private theorem leftUnit_inv_nat [Category.{v} C] [MonoidalCategory C]
    (X : Karoubi C) :
    X.p ≫ (λ_ X.X).inv = (λ_ X.X).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ X.p) := by
  rw [id_tensorHom]; exact leftUnitor_inv_naturality X.p

private theorem rightUnit_nat [Category.{v} C] [MonoidalCategory C]
    (X : Karoubi C) :
    (X.p ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ X.X).hom = (ρ_ X.X).hom ≫ X.p := by
  rw [tensorHom_id]; exact rightUnitor_naturality X.p

private theorem rightUnit_inv_nat [Category.{v} C] [MonoidalCategory C]
    (X : Karoubi C) :
    X.p ≫ (ρ_ X.X).inv = (ρ_ X.X).inv ≫ (X.p ⊗ₘ 𝟙 (𝟙_ C)) := by
  rw [tensorHom_id]; exact rightUnitor_inv_naturality X.p

/-! ### Data: `MonoidalCategoryStruct` on `Karoubi C` -/

/-- The monoidal data on the Karoubi envelope: tensor of
idempotents, conjugated structural isomorphisms. -/
instance karoubiMonoidalStruct [Category.{v} C] [MonoidalCategory C] :
    MonoidalCategoryStruct (Karoubi C) where
  tensorObj X Y :=
    ⟨X.X ⊗ Y.X, X.p ⊗ₘ Y.p, by exact tensorHom_idem X.idem Y.idem⟩
  whiskerLeft X _ _ f :=
    ⟨X.p ⊗ₘ f.f, by exact karoubi_tensorHom_comm (⟨X.p, by simp [X.idem]⟩ : X ⟶ X) f⟩
  whiskerRight f Y :=
    ⟨f.f ⊗ₘ Y.p, by exact karoubi_tensorHom_comm f (⟨Y.p, by simp [Y.idem]⟩ : Y ⟶ Y)⟩
  tensorHom f g := ⟨f.f ⊗ₘ g.f, by exact karoubi_tensorHom_comm f g⟩
  tensorUnit := ⟨𝟙_ C, 𝟙 (𝟙_ C), by simp⟩
  associator X Y Z :=
    { hom := ⟨((X.p ⊗ₘ Y.p) ⊗ₘ Z.p) ≫ (α_ X.X Y.X Z.X).hom,
              by exact (conj_comm _ _
                (tensorHom_idem (tensorHom_idem X.idem Y.idem) Z.idem)
                (tensorHom_idem X.idem (tensorHom_idem Y.idem Z.idem))
                _ (assoc_nat X Y Z))⟩
      inv := ⟨(X.p ⊗ₘ (Y.p ⊗ₘ Z.p)) ≫ (α_ X.X Y.X Z.X).inv,
              by exact (conj_comm _ _
                (tensorHom_idem X.idem (tensorHom_idem Y.idem Z.idem))
                (tensorHom_idem (tensorHom_idem X.idem Y.idem) Z.idem)
                _ (assoc_inv_nat X Y Z))⟩
      hom_inv_id := by
        apply Karoubi.hom_ext; simp only [Karoubi.comp_f, Karoubi.id_f]
        exact conj_iso_hom_inv _ _
          (tensorHom_idem (tensorHom_idem X.idem Y.idem) Z.idem)
          _ (assoc_nat X Y Z)
      inv_hom_id := by
        apply Karoubi.hom_ext; simp only [Karoubi.comp_f, Karoubi.id_f]
        exact conj_iso_inv_hom _ _
          (tensorHom_idem X.idem (tensorHom_idem Y.idem Z.idem))
          _ (assoc_nat X Y Z) }
  leftUnitor X :=
    { hom := ⟨(𝟙 (𝟙_ C) ⊗ₘ X.p) ≫ (λ_ X.X).hom,
              by exact (conj_comm _ _
                (tensorHom_idem (by simp) X.idem) X.idem
                _ (leftUnit_nat X))⟩
      inv := ⟨X.p ≫ (λ_ X.X).inv,
              by exact (conj_comm _ _ X.idem
                (tensorHom_idem (by simp) X.idem)
                _ (leftUnit_inv_nat X))⟩
      hom_inv_id := by
        apply Karoubi.hom_ext; simp only [Karoubi.comp_f, Karoubi.id_f]
        exact conj_iso_hom_inv _ _
          (tensorHom_idem (by simp) X.idem) _ (leftUnit_nat X)
      inv_hom_id := by
        apply Karoubi.hom_ext; simp only [Karoubi.comp_f, Karoubi.id_f]
        exact conj_iso_inv_hom _ _ X.idem _ (leftUnit_nat X) }
  rightUnitor X :=
    { hom := ⟨(X.p ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ X.X).hom,
              by exact (conj_comm _ _
                (tensorHom_idem X.idem (by simp)) X.idem
                _ (rightUnit_nat X))⟩
      inv := ⟨X.p ≫ (ρ_ X.X).inv,
              by exact (conj_comm _ _ X.idem
                (tensorHom_idem X.idem (by simp))
                _ (rightUnit_inv_nat X))⟩
      hom_inv_id := by
        apply Karoubi.hom_ext; simp only [Karoubi.comp_f, Karoubi.id_f]
        exact conj_iso_hom_inv _ _
          (tensorHom_idem X.idem (by simp)) _ (rightUnit_nat X)
      inv_hom_id := by
        apply Karoubi.hom_ext; simp only [Karoubi.comp_f, Karoubi.id_f]
        exact conj_iso_inv_hom _ _ X.idem _ (rightUnit_nat X) }

/-! ### Simp lemmas for the Karoubi monoidal data

These unfold the `.f` and `.p` projections of the Karoubi monoidal
structure to morphisms in `C`.  They are all definitional equalities. -/

@[simp] private theorem karoubiTensorHom_f [Category.{v} C] [MonoidalCategory C]
    {P₁ Q₁ P₂ Q₂ : Karoubi C} (f : P₁ ⟶ Q₁) (g : P₂ ⟶ Q₂) :
    (f ⊗ₘ g : _ ⟶ _).f = f.f ⊗ₘ g.f := rfl

@[simp] private theorem karoubiTensorObj_p [Category.{v} C] [MonoidalCategory C]
    (X Y : Karoubi C) :
    (X ⊗ Y : Karoubi C).p = X.p ⊗ₘ Y.p := rfl

@[simp] private theorem karoubiTensorObj_X [Category.{v} C] [MonoidalCategory C]
    (X Y : Karoubi C) :
    (X ⊗ Y : Karoubi C).X = X.X ⊗ Y.X := rfl

@[simp] private theorem karoubiTensorUnit_p
    [Category.{v} C] [MonoidalCategory C] :
    (𝟙_ (Karoubi C)).p = 𝟙 (𝟙_ C) := rfl

@[simp] private theorem karoubiTensorUnit_X
    [Category.{v} C] [MonoidalCategory C] :
    (𝟙_ (Karoubi C)).X = 𝟙_ C := rfl

@[simp] private theorem karoubiAssociator_hom_f
    [Category.{v} C] [MonoidalCategory C]
    (X Y Z : Karoubi C) :
    (α_ X Y Z).hom.f =
    ((X.p ⊗ₘ Y.p) ⊗ₘ Z.p) ≫ (α_ X.X Y.X Z.X).hom := rfl

@[simp] private theorem karoubiLeftUnitor_hom_f
    [Category.{v} C] [MonoidalCategory C]
    (X : Karoubi C) :
    (λ_ X).hom.f = (𝟙 (𝟙_ C) ⊗ₘ X.p) ≫ (λ_ X.X).hom := rfl

@[simp] private theorem karoubiRightUnitor_hom_f
    [Category.{v} C] [MonoidalCategory C]
    (X : Karoubi C) :
    (ρ_ X).hom.f = (X.p ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ X.X).hom := rfl

@[simp] private theorem karoubiWhiskerLeft_f
    [Category.{v} C] [MonoidalCategory C]
    (X : Karoubi C) {Y Z : Karoubi C} (f : Y ⟶ Z) :
    (X ◁ f).f = X.p ⊗ₘ f.f := rfl

@[simp] private theorem karoubiWhiskerRight_f
    [Category.{v} C] [MonoidalCategory C]
    {X Y : Karoubi C} (f : X ⟶ Y) (Z : Karoubi C) :
    (f ▷ Z).f = f.f ⊗ₘ Z.p := rfl

@[simp] private theorem karoubiAssociator_inv_f
    [Category.{v} C] [MonoidalCategory C]
    (X Y Z : Karoubi C) :
    (α_ X Y Z).inv.f =
    (X.p ⊗ₘ (Y.p ⊗ₘ Z.p)) ≫ (α_ X.X Y.X Z.X).inv := rfl

@[simp] private theorem karoubiLeftUnitor_inv_f
    [Category.{v} C] [MonoidalCategory C]
    (X : Karoubi C) :
    (λ_ X).inv.f = X.p ≫ (λ_ X.X).inv := rfl

@[simp] private theorem karoubiRightUnitor_inv_f
    [Category.{v} C] [MonoidalCategory C]
    (X : Karoubi C) :
    (ρ_ X).inv.f = X.p ≫ (ρ_ X.X).inv := rfl

/-! ### Axioms: `MonoidalCategory` on `Karoubi C`

The monoidal axioms (interchange, naturality, pentagon, triangle) are
proved by reducing to the underlying morphisms in `C` via `hom_ext` and
the Karoubi simp lemmas `p_comp`, `comp_p`, `idem`. -/

private theorem karoubi_id_tensorHom_id [Category.{v} C] [MonoidalCategory C]
    (X₁ X₂ : Karoubi C) :
    tensorHom (𝟙 X₁) (𝟙 X₂) = 𝟙 (tensorObj X₁ X₂) := by
  apply Karoubi.hom_ext; simp [Karoubi.id_f]

private theorem karoubi_id_tensorHom [Category.{v} C] [MonoidalCategory C]
    (X : Karoubi C) {Y₁ Y₂ : Karoubi C}
    (f : Y₁ ⟶ Y₂) : tensorHom (𝟙 X) f = whiskerLeft X f :=
  Karoubi.hom_ext _ _ rfl

private theorem karoubi_tensorHom_id [Category.{v} C] [MonoidalCategory C]
    {X₁ X₂ : Karoubi C} (f : X₁ ⟶ X₂)
    (Y : Karoubi C) : tensorHom f (𝟙 Y) = whiskerRight f Y :=
  Karoubi.hom_ext _ _ rfl

private theorem karoubi_tensorHom_comp [Category.{v} C] [MonoidalCategory C]
    {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Karoubi C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂) := by
  apply Karoubi.hom_ext
  simp [Karoubi.comp_f, tensorHom_comp_tensorHom]

private theorem karoubi_associator_naturality
    [Category.{v} C] [MonoidalCategory C]
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Karoubi C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
      (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
  apply Karoubi.hom_ext
  simp only [Karoubi.comp_f, karoubiTensorHom_f, karoubiAssociator_hom_f]
  simp only [← assoc, associator_naturality]
  simp only [assoc, tensorHom_comp_tensorHom, Karoubi.comp_p, Karoubi.p_comp]

/-! ### Bridge lemmas: tensorHom form of C axioms

The mathlib `MonoidalCategory` axioms for C use `◁` / `▷` (whiskerLeft /
whiskerRight) while `ofTensorHom` expects `𝟙 X ⊗ₘ f` / `f ⊗ₘ 𝟙 Y`.
These helpers restate the relevant C axioms in `tensorHom` form, proved
outside the Karoubi struct context where `rw [id_tensorHom]` is safe. -/

private theorem tensorHom_leftUnitor_naturality
    [Category.{v} C] [MonoidalCategory C]
    {X Y : C} (f : X ⟶ Y) :
    (𝟙 (𝟙_ C) ⊗ₘ f) ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by
  rw [id_tensorHom]; exact leftUnitor_naturality f

private theorem tensorHom_rightUnitor_naturality
    [Category.{v} C] [MonoidalCategory C]
    {X Y : C} (f : X ⟶ Y) :
    (f ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
  rw [tensorHom_id]; exact rightUnitor_naturality f

@[reassoc] private theorem tensorHom_pentagon_eq
    [Category.{v} C] [MonoidalCategory C]
    (W X Y Z : C) :
    ((α_ W X Y).hom ⊗ₘ 𝟙 Z) ≫ (α_ W (X ⊗ Y) Z).hom ≫
      (𝟙 W ⊗ₘ (α_ X Y Z).hom) =
    (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom := by
  rw [id_tensorHom, tensorHom_id]; exact pentagon W X Y Z

@[reassoc] private theorem tensorHom_triangle_eq
    [Category.{v} C] [MonoidalCategory C]
    (X Y : C) :
    (α_ X (𝟙_ C) Y).hom ≫ (𝟙 X ⊗ₘ (λ_ Y).hom) =
    (ρ_ X).hom ⊗ₘ 𝟙 Y := by
  rw [id_tensorHom, tensorHom_id]; exact triangle X Y

private theorem karoubi_leftUnitor_naturality
    [Category.{v} C] [MonoidalCategory C]
    {X Y : Karoubi C} (f : X ⟶ Y) :
    tensorHom (𝟙 (𝟙_ (Karoubi C))) f ≫ (leftUnitor Y).hom =
      (leftUnitor X).hom ≫ f := by
  apply Karoubi.hom_ext
  simp only [Karoubi.comp_f, Karoubi.id_f, karoubiTensorHom_f,
             karoubiLeftUnitor_hom_f, karoubiTensorUnit_p]
  rw [← assoc, tensorHom_comp_tensorHom]
  have h : (𝟙 (𝟙_ C) ≫ 𝟙 (𝟙_ C)) ⊗ₘ (f.f ≫ Y.p) = 𝟙 (𝟙_ C) ⊗ₘ f.f := by
    congr 1
    · exact id_comp _
    · exact Karoubi.comp_p f
  rw [h, tensorHom_leftUnitor_naturality, leftUnit_nat, assoc, Karoubi.p_comp]

private theorem karoubi_rightUnitor_naturality
    [Category.{v} C] [MonoidalCategory C]
    {X Y : Karoubi C} (f : X ⟶ Y) :
    tensorHom f (𝟙 (𝟙_ (Karoubi C))) ≫ (rightUnitor Y).hom =
      (rightUnitor X).hom ≫ f := by
  apply Karoubi.hom_ext
  simp only [Karoubi.comp_f, Karoubi.id_f, karoubiTensorHom_f,
             karoubiRightUnitor_hom_f, karoubiTensorUnit_p]
  rw [← assoc, tensorHom_comp_tensorHom]
  have h : (f.f ≫ Y.p) ⊗ₘ (𝟙 (𝟙_ C) ≫ 𝟙 (𝟙_ C)) = f.f ⊗ₘ 𝟙 (𝟙_ C) := by
    congr 1
    · exact Karoubi.comp_p f
    · exact id_comp _
  rw [h, tensorHom_rightUnitor_naturality, rightUnit_nat, assoc, Karoubi.p_comp]

-- Pentagon: the proof strategy is to decompose compositions from inside
-- `⊗ₘ`, use naturality to move intermediate idempotents past associators,
-- absorb duplicate idempotents, then replace `(α ⊗ p)` / `(p ⊗ α)` with
-- `(α ⊗ 𝟙)` / `(𝟙 ⊗ α)` using the merge+congr technique, and finally
-- apply the C pentagon.
private theorem karoubi_pentagon [Category.{v} C] [MonoidalCategory C]
    (W X Y Z : Karoubi C) :
    tensorHom (associator W X Y).hom (𝟙 Z) ≫
        (associator W (tensorObj X Y) Z).hom ≫
        tensorHom (𝟙 W) (associator X Y Z).hom =
      (associator (tensorObj W X) Y Z).hom ≫
        (associator W X (tensorObj Y Z)).hom := by
  apply Karoubi.hom_ext
  simp only [Karoubi.comp_f, Karoubi.id_f, karoubiTensorHom_f,
             karoubiAssociator_hom_f, karoubiTensorObj_p, karoubiTensorObj_X]
  -- Extract compositions from inside `⊗ₘ` to the top level.
  rw [tensorHom_comp_left_idem_right _ _ Z.idem,
      tensorHom_idem_left_comp_right _ W.idem]
  simp only [assoc]
  -- Move `(pW ⊗ pXY) ⊗ pZ` past `α₂` via associator naturality.
  rw [associator_naturality_assoc W.p (X.p ⊗ₘ Y.p) Z.p]
  -- Absorb `(pW ⊗ (pXY ⊗ pZ)) ≫ (pW ⊗ (pXY ⊗ pZ))`.
  have h_absorb : ∀ {E : C} (h : W.X ⊗ ((X.X ⊗ Y.X) ⊗ Z.X) ⟶ E),
      (W.p ⊗ₘ ((X.p ⊗ₘ Y.p) ⊗ₘ Z.p)) ≫
        ((W.p ⊗ₘ ((X.p ⊗ₘ Y.p) ⊗ₘ Z.p)) ≫ h) =
      (W.p ⊗ₘ ((X.p ⊗ₘ Y.p) ⊗ₘ Z.p)) ≫ h := by
    intro E h
    rw [← assoc, tensorHom_idem W.idem
      (tensorHom_idem (tensorHom_idem X.idem Y.idem) Z.idem)]
  rw [h_absorb]
  -- Replace `src₄ ≫ (α₁ ⊗ pZ)` with `src₄ ≫ (α₁ ⊗ 𝟙 Z.X)` by merging
  -- the adjacent tensor products and simplifying `pZ ≫ pZ = pZ ≫ 𝟙`.
  have h_left : ∀ {E : C} (h : (W.X ⊗ (X.X ⊗ Y.X)) ⊗ Z.X ⟶ E),
      (((W.p ⊗ₘ X.p) ⊗ₘ Y.p) ⊗ₘ Z.p) ≫
        (((α_ W.X X.X Y.X).hom ⊗ₘ Z.p) ≫ h) =
      (((W.p ⊗ₘ X.p) ⊗ₘ Y.p) ⊗ₘ Z.p) ≫
        (((α_ W.X X.X Y.X).hom ⊗ₘ 𝟙 Z.X) ≫ h) := by
    intro E h; simp only [← assoc]; congr 1
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    congr 1; rw [Z.idem, comp_id]
  rw [h_left]
  -- Replace `(pW ⊗ (pXY ⊗ pZ)) ≫ (pW ⊗ α₃)` with `(𝟙 ⊗ α₃) ≫ tgt₅`
  -- by merging and applying associator naturality inside the congr.
  have h_right :
      (W.p ⊗ₘ ((X.p ⊗ₘ Y.p) ⊗ₘ Z.p)) ≫ (W.p ⊗ₘ (α_ X.X Y.X Z.X).hom) =
      (𝟙 W.X ⊗ₘ (α_ X.X Y.X Z.X).hom) ≫
        (W.p ⊗ₘ (X.p ⊗ₘ (Y.p ⊗ₘ Z.p))) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    congr 1
    · rw [W.idem, id_comp]
    · exact associator_naturality X.p Y.p Z.p
  rw [h_right]
  -- Apply the C pentagon (reassoc form) and finish with RHS naturality.
  rw [tensorHom_pentagon_eq_assoc, associator_naturality W.p X.p (Y.p ⊗ₘ Z.p)]

-- Triangle: same decomposition + merge+congr strategy as the pentagon.
private theorem karoubi_triangle [Category.{v} C] [MonoidalCategory C]
    (X Y : Karoubi C) :
    (associator X (𝟙_ (Karoubi C)) Y).hom ≫
      tensorHom (𝟙 X) (leftUnitor Y).hom =
    tensorHom (rightUnitor X).hom (𝟙 Y) := by
  apply Karoubi.hom_ext
  simp only [Karoubi.comp_f, Karoubi.id_f, karoubiTensorHom_f,
             karoubiAssociator_hom_f, karoubiLeftUnitor_hom_f,
             karoubiRightUnitor_hom_f,
             karoubiTensorUnit_p, karoubiTensorUnit_X, karoubiTensorObj_X]
  -- Extract compositions from inside `⊗ₘ` to the top level.
  rw [tensorHom_comp_left_idem_right _ _ Y.idem,
      tensorHom_idem_left_comp_right _ X.idem]
  simp only [assoc]
  -- Move idempotents past the associator via naturality.
  rw [associator_naturality_assoc X.p (𝟙 (𝟙_ C)) Y.p]
  -- Absorb `(pX ⊗ (𝟙 ⊗ pY)) ≫ (pX ⊗ (𝟙 ⊗ pY))`.
  have h_absorb : ∀ {E : C} (h : X.X ⊗ (𝟙_ C ⊗ Y.X) ⟶ E),
      (X.p ⊗ₘ (𝟙 (𝟙_ C) ⊗ₘ Y.p)) ≫
        ((X.p ⊗ₘ (𝟙 (𝟙_ C) ⊗ₘ Y.p)) ≫ h) =
      (X.p ⊗ₘ (𝟙 (𝟙_ C) ⊗ₘ Y.p)) ≫ h := by
    intro E h
    rw [← assoc, tensorHom_idem X.idem (tensorHom_idem (by simp) Y.idem)]
  rw [h_absorb]
  -- Merge the LHS tensor products and apply left unitor naturality.
  have h_merge :
      (X.p ⊗ₘ (𝟙 (𝟙_ C) ⊗ₘ Y.p)) ≫ (X.p ⊗ₘ (λ_ Y.X).hom) =
      (𝟙 X.X ⊗ₘ (λ_ Y.X).hom) ≫ (X.p ⊗ₘ Y.p) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    congr 1
    · rw [X.idem, id_comp]
    · exact leftUnit_nat Y
  rw [h_merge]
  -- Merge the RHS tensor products and apply right unitor naturality.
  have h_rhs :
      ((X.p ⊗ₘ 𝟙 (𝟙_ C)) ⊗ₘ Y.p) ≫ ((ρ_ X.X).hom ⊗ₘ Y.p) =
      ((ρ_ X.X).hom ⊗ₘ 𝟙 Y.X) ≫ (X.p ⊗ₘ Y.p) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    congr 1
    · exact rightUnit_nat X
    · rw [Y.idem, id_comp]
  rw [h_rhs]
  -- Apply the C triangle (reassoc form).
  rw [tensorHom_triangle_eq_assoc]

/-- Those data satisfy the monoidal axioms, each inherited from the
ambient category by conjugation. -/
instance karoubiMonoidal
    [Category.{v} C] [MonoidalCategory C] : MonoidalCategory (Karoubi C) := by
  exact MonoidalCategory.ofTensorHom
    (id_tensorHom_id := by exact karoubi_id_tensorHom_id)
    (id_tensorHom := by exact karoubi_id_tensorHom)
    (tensorHom_id := by exact karoubi_tensorHom_id)
    (tensorHom_comp_tensorHom := by exact karoubi_tensorHom_comp)
    (associator_naturality := by exact karoubi_associator_naturality)
    (leftUnitor_naturality := by exact karoubi_leftUnitor_naturality)
    (rightUnitor_naturality := by exact karoubi_rightUnitor_naturality)
    (pentagon := by exact karoubi_pentagon)
    (triangle := by exact karoubi_triangle)

/-! ### The canonical functor `toKaroubi C` is strong monoidal -/

/-- The underlying object of `toKaroubi C` on `X`. -/
@[simp] private theorem toKaroubi_obj_X [Category.{v} C]
    (X : C) :
    ((toKaroubi C).obj X).X = X := rfl

/-- The idempotent of `toKaroubi C` on `X` is the identity. -/
@[simp] private theorem toKaroubi_obj_p [Category.{v} C]
    (X : C) :
    ((toKaroubi C).obj X).p = 𝟙 X := rfl

/-- The underlying morphism of `toKaroubi C` on `f`. -/
@[simp] private theorem toKaroubi_map_f [Category.{v} C]
    {X Y : C} (f : X ⟶ Y) :
    ((toKaroubi C).map f).f = f := rfl

/-! ### Strong monoidality

The functor `toKaroubi C : C ⥤ Karoubi C` sends `X` to `⟨X, 𝟙 X⟩`.  It
preserves the tensor unit on the nose and the tensor product up to the
canonical identification `𝟙 X ⊗ₘ 𝟙 Y = 𝟙 (X ⊗ Y)`. -/

-- The eight coherence fields of a monoidal functor
-- elaborate together.
/-- The embedding is monoidal. -/
noncomputable instance toKaroubiMonoidal
    [Category.{v} C] [MonoidalCategory C] : Functor.Monoidal (toKaroubi C) where
  ε := 𝟙 _
  μ X Y := ⟨𝟙 (X ⊗ Y), by simp [comp_id]⟩
  η := 𝟙 _
  δ X Y := ⟨𝟙 (X ⊗ Y), by simp [comp_id]⟩
  ε_η := by apply Karoubi.hom_ext; simp
  η_ε := by apply Karoubi.hom_ext; simp
  μ_δ X Y := by apply Karoubi.hom_ext; simp
  δ_μ X Y := by apply Karoubi.hom_ext; simp
  μ_natural_left f X' := by
    apply Karoubi.hom_ext; simp [Karoubi.comp_f, karoubiWhiskerRight_f]
  μ_natural_right X' f := by
    apply Karoubi.hom_ext; simp [Karoubi.comp_f, karoubiWhiskerLeft_f]
  δ_natural_left f X' := by
    apply Karoubi.hom_ext; simp [Karoubi.comp_f, karoubiWhiskerRight_f]
  δ_natural_right X' f := by
    apply Karoubi.hom_ext; simp [Karoubi.comp_f, karoubiWhiskerLeft_f]
  associativity X Y Z := by
    apply Karoubi.hom_ext
    simp [Karoubi.comp_f, karoubiWhiskerRight_f, karoubiWhiskerLeft_f,
          karoubiAssociator_hom_f, karoubiTensorObj_X]
  oplax_associativity X Y Z := by
    apply Karoubi.hom_ext
    simp [Karoubi.comp_f, karoubiWhiskerRight_f, karoubiWhiskerLeft_f,
          karoubiAssociator_hom_f, karoubiTensorObj_X]
  left_unitality X := by
    apply Karoubi.hom_ext
    simp [Karoubi.comp_f, karoubiLeftUnitor_hom_f, karoubiTensorUnit_X]
  right_unitality X := by
    apply Karoubi.hom_ext
    simp [Karoubi.comp_f, karoubiRightUnitor_hom_f, karoubiTensorUnit_X]
  oplax_left_unitality X := by
    apply Karoubi.hom_ext
    simp [Karoubi.comp_f, karoubiLeftUnitor_inv_f, karoubiTensorUnit_X]
  oplax_right_unitality X := by
    apply Karoubi.hom_ext
    simp [Karoubi.comp_f, karoubiRightUnitor_inv_f, karoubiTensorUnit_X]

/-! ### Braided and symmetric structure on `Karoubi C`

When `C` carries a braided (resp. symmetric) monoidal structure, so does
`Karoubi C`.  The braiding on `Karoubi C` has underlying morphism
`(p ⊗ₘ q) ≫ (β_ A B).hom`, conjugating the braiding of `C` by the
tensor of idempotents. -/

section Braided

/-- Naturality of the C braiding with respect to the idempotents. -/
private theorem braid_nat
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (X Y : Karoubi C) :
    (X.p ⊗ₘ Y.p) ≫ (β_ X.X Y.X).hom = (β_ X.X Y.X).hom ≫ (Y.p ⊗ₘ X.p) :=
  BraidedCategory.braiding_naturality X.p Y.p

private theorem braid_inv_nat
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (X Y : Karoubi C) :
    (Y.p ⊗ₘ X.p) ≫ (β_ X.X Y.X).inv = (β_ X.X Y.X).inv ≫ (X.p ⊗ₘ Y.p) := by
  rw [← cancel_mono (β_ X.X Y.X).hom, assoc, Iso.inv_hom_id, comp_id,
      assoc, braid_nat, ← assoc, Iso.inv_hom_id, id_comp]

/-- The braiding isomorphism on Karoubi objects, defined prior to the instance
so that simp lemmas for the `.f` projection are available inside the axiom
proofs. -/
noncomputable def karoubiBraidingIso
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (X Y : Karoubi C) :
    tensorObj X Y ≅ tensorObj Y X where
  hom := ⟨(X.p ⊗ₘ Y.p) ≫ (β_ X.X Y.X).hom,
          by exact (conj_comm _ _
            (tensorHom_idem X.idem Y.idem)
            (tensorHom_idem Y.idem X.idem)
            _ (braid_nat X Y))⟩
  inv := ⟨(Y.p ⊗ₘ X.p) ≫ (β_ X.X Y.X).inv,
          by exact (conj_comm _ _
            (tensorHom_idem Y.idem X.idem)
            (tensorHom_idem X.idem Y.idem)
            _ (braid_inv_nat X Y))⟩
  hom_inv_id := by
    apply Karoubi.hom_ext; simp only [Karoubi.comp_f, Karoubi.id_f]
    exact conj_iso_hom_inv _ _
      (tensorHom_idem X.idem Y.idem) _ (braid_nat X Y)
  inv_hom_id := by
    apply Karoubi.hom_ext; simp only [Karoubi.comp_f, Karoubi.id_f]
    exact conj_iso_inv_hom _ _
      (tensorHom_idem Y.idem X.idem) _ (braid_nat X Y)

@[simp] private theorem karoubiBraidingIso_hom_f
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (X Y : Karoubi C) :
    (karoubiBraidingIso X Y).hom.f = (X.p ⊗ₘ Y.p) ≫ (β_ X.X Y.X).hom := rfl

@[simp] private theorem karoubiBraidingIso_inv_f
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (X Y : Karoubi C) :
    (karoubiBraidingIso X Y).inv.f = (Y.p ⊗ₘ X.p) ≫ (β_ X.X Y.X).inv := rfl

/-- Bridge lemma: the C hexagon_forward stated in `tensorHom` form. -/
@[reassoc] private theorem tensorHom_hexagon_forward_eq
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (X Y Z : C) :
    (α_ X Y Z).hom ≫ (β_ X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
    ((β_ X Y).hom ⊗ₘ 𝟙 Z) ≫ (α_ Y X Z).hom ≫ (𝟙 Y ⊗ₘ (β_ X Z).hom) := by
  rw [id_tensorHom, tensorHom_id]; exact BraidedCategory.hexagon_forward X Y Z

/-- Bridge lemma: the C hexagon_reverse stated in `tensorHom` form. -/
@[reassoc] private theorem tensorHom_hexagon_reverse_eq
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (X Y Z : C) :
    (α_ X Y Z).inv ≫ (β_ (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
    (𝟙 X ⊗ₘ (β_ Y Z).hom) ≫ (α_ X Z Y).inv ≫ ((β_ X Z).hom ⊗ₘ 𝟙 Y) := by
  rw [id_tensorHom, tensorHom_id]; exact BraidedCategory.hexagon_reverse X Y Z

-- Naturality on both sides and both hexagons
-- elaborate together, each conjugating the ambient braiding.
/-- A braiding on the ambient category conjugates to one on the
envelope. -/
noncomputable instance karoubiBraided
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] :
    BraidedCategory (Karoubi C) where
  braiding := karoubiBraidingIso
  -- ═══════ NATURALITY ═══════
  braiding_naturality_right X {Y Z} f := by
    apply Karoubi.hom_ext
    simp only [Karoubi.comp_f, karoubiWhiskerLeft_f, karoubiWhiskerRight_f,
               karoubiBraidingIso_hom_f]
    rw [assoc, ← assoc (X.p ⊗ₘ f.f), tensorHom_comp_tensorHom, X.idem,
      Karoubi.comp_p,
        BraidedCategory.braiding_naturality,
        ← assoc (X.p ⊗ₘ Y.p), braid_nat X Y, assoc]
    congr 1
    rw [tensorHom_comp_tensorHom, Karoubi.p_comp, X.idem]
  braiding_naturality_left {X Y} f Z := by
    apply Karoubi.hom_ext
    simp only [Karoubi.comp_f, karoubiWhiskerLeft_f, karoubiWhiskerRight_f,
               karoubiBraidingIso_hom_f]
    rw [assoc, ← assoc (f.f ⊗ₘ Z.p), tensorHom_comp_tensorHom, Karoubi.comp_p,
      Z.idem,
        BraidedCategory.braiding_naturality,
        ← assoc (X.p ⊗ₘ Z.p), braid_nat X Z, assoc]
    congr 1
    rw [tensorHom_comp_tensorHom, Z.idem, Karoubi.p_comp]
  -- ═══════ THE FORWARD HEXAGON ═══════
  hexagon_forward X Y Z := by
    apply Karoubi.hom_ext
    simp only [Karoubi.comp_f, karoubiWhiskerLeft_f, karoubiWhiskerRight_f,
               karoubiAssociator_hom_f, karoubiBraidingIso_hom_f,
               karoubiTensorObj_p, karoubiTensorObj_X]
    -- Decompose compositions inside ⊗ₘ on the RHS.
    rw [tensorHom_comp_left_idem_right _ _ Z.idem,
        tensorHom_idem_left_comp_right _ Y.idem]
    simp only [assoc]
    -- LHS: absorb idempotents through structural morphisms.
    rw [associator_naturality_assoc X.p Y.p Z.p]
    have h1 : ∀ {E : C} (h : X.X ⊗ (Y.X ⊗ Z.X) ⟶ E),
        (X.p ⊗ₘ (Y.p ⊗ₘ Z.p)) ≫ ((X.p ⊗ₘ (Y.p ⊗ₘ Z.p)) ≫ h) =
        (X.p ⊗ₘ (Y.p ⊗ₘ Z.p)) ≫ h := by
      intro E h
      rw [← assoc, tensorHom_idem X.idem (tensorHom_idem Y.idem Z.idem)]
    rw [h1]
    rw [BraidedCategory.braiding_naturality_assoc X.p (Y.p ⊗ₘ Z.p)]
    have h2 : ∀ {E : C} (h : (Y.X ⊗ Z.X) ⊗ X.X ⟶ E),
        ((Y.p ⊗ₘ Z.p) ⊗ₘ X.p) ≫ (((Y.p ⊗ₘ Z.p) ⊗ₘ X.p) ≫ h) =
        ((Y.p ⊗ₘ Z.p) ⊗ₘ X.p) ≫ h := by
      intro E h
      rw [← assoc, tensorHom_idem (tensorHom_idem Y.idem Z.idem) X.idem]
    rw [h2, associator_naturality Y.p Z.p X.p]
    -- LHS is now: C_hexagon_LHS ≫ (Y.p ⊗ₘ (Z.p ⊗ₘ X.p)).  Apply C hexagon.
    rw [tensorHom_hexagon_forward_eq_assoc]
    -- Goal: (β ⊗ 𝟙) ≫ α ≫ (𝟙 ⊗ β) ≫ (Y.p ⊗ (Z.p ⊗ X.p)) =
    --       (p ⊗ p) ⊗ p ≫ (β ⊗ p) ≫ (p ⊗ p) ⊗ p ≫ α ≫ Y.p ⊗ (p ⊗ p) ≫ Y.p ⊗ β
    -- RHS: replace first 2 terms with (β ⊗ 𝟙) ≫ (p ⊗ p) ⊗ p.
    have rhs_pre :
        ((X.p ⊗ₘ Y.p) ⊗ₘ Z.p) ≫ ((β_ X.X Y.X).hom ⊗ₘ Z.p) =
        ((β_ X.X Y.X).hom ⊗ₘ 𝟙 Z.X) ≫ ((Y.p ⊗ₘ X.p) ⊗ₘ Z.p) := by
      rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
      congr 1
      · exact braid_nat X Y
      · rw [Z.idem, id_comp]
    rw [← assoc ((X.p ⊗ₘ Y.p) ⊗ₘ Z.p), rhs_pre, assoc]
    -- Absorb duplicate idempotent.
    have h3 : ∀ {E : C} (h : (Y.X ⊗ X.X) ⊗ Z.X ⟶ E),
        ((Y.p ⊗ₘ X.p) ⊗ₘ Z.p) ≫ (((Y.p ⊗ₘ X.p) ⊗ₘ Z.p) ≫ h) =
        ((Y.p ⊗ₘ X.p) ⊗ₘ Z.p) ≫ h := by
      intro E h
      rw [← assoc, tensorHom_idem (tensorHom_idem Y.idem X.idem) Z.idem]
    rw [h3]
    -- Move idempotent past associator.
    rw [associator_naturality_assoc Y.p X.p Z.p]
    -- Absorb duplicate idempotent.
    have h4 : ∀ {E : C} (h : Y.X ⊗ (X.X ⊗ Z.X) ⟶ E),
        (Y.p ⊗ₘ (X.p ⊗ₘ Z.p)) ≫ ((Y.p ⊗ₘ (X.p ⊗ₘ Z.p)) ≫ h) =
        (Y.p ⊗ₘ (X.p ⊗ₘ Z.p)) ≫ h := by
      intro E h
      rw [← assoc, tensorHom_idem Y.idem (tensorHom_idem X.idem Z.idem)]
    rw [h4]
    -- Replace last 2 terms with (𝟙 ⊗ β) ≫ (Y.p ⊗ (Z.p ⊗ X.p)).
    have rhs_suf :
        (Y.p ⊗ₘ (X.p ⊗ₘ Z.p)) ≫ (Y.p ⊗ₘ (β_ X.X Z.X).hom) =
        (𝟙 Y.X ⊗ₘ (β_ X.X Z.X).hom) ≫ (Y.p ⊗ₘ (Z.p ⊗ₘ X.p)) := by
      rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
      congr 1
      · rw [Y.idem, id_comp]
      · exact BraidedCategory.braiding_naturality X.p Z.p
    rw [rhs_suf]
  -- ═══════ THE REVERSE HEXAGON ═══════
  hexagon_reverse X Y Z := by
    apply Karoubi.hom_ext
    simp only [Karoubi.comp_f, karoubiWhiskerLeft_f, karoubiWhiskerRight_f,
               karoubiAssociator_inv_f, karoubiBraidingIso_hom_f,
               karoubiTensorObj_p, karoubiTensorObj_X]
    -- Decompose compositions inside ⊗ₘ on the RHS.
    rw [tensorHom_idem_left_comp_right _ X.idem,
        tensorHom_comp_left_idem_right _ _ Y.idem]
    simp only [assoc]
    -- LHS: absorb idempotents through structural morphisms.
    rw [associator_inv_naturality_assoc X.p Y.p Z.p]
    have h1 : ∀ {E : C} (h : (X.X ⊗ Y.X) ⊗ Z.X ⟶ E),
        ((X.p ⊗ₘ Y.p) ⊗ₘ Z.p) ≫ (((X.p ⊗ₘ Y.p) ⊗ₘ Z.p) ≫ h) =
        ((X.p ⊗ₘ Y.p) ⊗ₘ Z.p) ≫ h := by
      intro E h
      rw [← assoc, tensorHom_idem (tensorHom_idem X.idem Y.idem) Z.idem]
    rw [h1]
    rw [BraidedCategory.braiding_naturality_assoc (X.p ⊗ₘ Y.p) Z.p]
    have h2 : ∀ {E : C} (h : Z.X ⊗ (X.X ⊗ Y.X) ⟶ E),
        (Z.p ⊗ₘ (X.p ⊗ₘ Y.p)) ≫ ((Z.p ⊗ₘ (X.p ⊗ₘ Y.p)) ≫ h) =
        (Z.p ⊗ₘ (X.p ⊗ₘ Y.p)) ≫ h := by
      intro E h
      rw [← assoc, tensorHom_idem Z.idem (tensorHom_idem X.idem Y.idem)]
    rw [h2, associator_inv_naturality Z.p X.p Y.p]
    -- LHS is now: C_hexagon_reverse_LHS ≫ ((Z.p ⊗ₘ X.p) ⊗ₘ Y.p). Apply C
    --   hexagon.
    rw [tensorHom_hexagon_reverse_eq_assoc]
    -- Goal: (𝟙 ⊗ β) ≫ α.inv ≫ (β ⊗ 𝟙) ≫ ((Z.p ⊗ X.p) ⊗ Y.p) =
    -- X.p ⊗ (p ⊗ p) ≫ X.p ⊗ β ≫ X.p ⊗ (p ⊗ p) ≫ α.inv ≫ (p ⊗ p) ⊗ Y.p ≫ β ⊗ Y.p
    -- RHS: replace first 2 terms with (𝟙 ⊗ β) ≫ X.p ⊗ (Z.p ⊗ Y.p).
    have rhs_pre :
        (X.p ⊗ₘ (Y.p ⊗ₘ Z.p)) ≫ (X.p ⊗ₘ (β_ Y.X Z.X).hom) =
        (𝟙 X.X ⊗ₘ (β_ Y.X Z.X).hom) ≫ (X.p ⊗ₘ (Z.p ⊗ₘ Y.p)) := by
      rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
      congr 1
      · rw [X.idem, id_comp]
      · exact BraidedCategory.braiding_naturality Y.p Z.p
    rw [← assoc (X.p ⊗ₘ (Y.p ⊗ₘ Z.p)), rhs_pre, assoc]
    -- Absorb duplicate idempotent.
    have h3 : ∀ {E : C} (h : X.X ⊗ (Z.X ⊗ Y.X) ⟶ E),
        (X.p ⊗ₘ (Z.p ⊗ₘ Y.p)) ≫ ((X.p ⊗ₘ (Z.p ⊗ₘ Y.p)) ≫ h) =
        (X.p ⊗ₘ (Z.p ⊗ₘ Y.p)) ≫ h := by
      intro E h
      rw [← assoc, tensorHom_idem X.idem (tensorHom_idem Z.idem Y.idem)]
    rw [h3]
    -- Move idempotent past associator inverse.
    rw [associator_inv_naturality_assoc X.p Z.p Y.p]
    -- Absorb duplicate idempotent.
    have h4 : ∀ {E : C} (h : (X.X ⊗ Z.X) ⊗ Y.X ⟶ E),
        ((X.p ⊗ₘ Z.p) ⊗ₘ Y.p) ≫ (((X.p ⊗ₘ Z.p) ⊗ₘ Y.p) ≫ h) =
        ((X.p ⊗ₘ Z.p) ⊗ₘ Y.p) ≫ h := by
      intro E h
      rw [← assoc, tensorHom_idem (tensorHom_idem X.idem Z.idem) Y.idem]
    rw [h4]
    -- Replace last 2 terms with (β ⊗ 𝟙) ≫ ((Z.p ⊗ X.p) ⊗ Y.p).
    have rhs_suf :
        ((X.p ⊗ₘ Z.p) ⊗ₘ Y.p) ≫ ((β_ X.X Z.X).hom ⊗ₘ Y.p) =
        ((β_ X.X Z.X).hom ⊗ₘ 𝟙 Y.X) ≫ ((Z.p ⊗ₘ X.p) ⊗ₘ Y.p) := by
      rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
      congr 1
      · exact BraidedCategory.braiding_naturality X.p Z.p
      · rw [Y.idem, id_comp]
    rw [rhs_suf]

@[simp] private theorem karoubiBraiding_hom_f
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (X Y : Karoubi C) :
    (β_ X Y).hom.f = (X.p ⊗ₘ Y.p) ≫ (β_ X.X Y.X).hom := rfl

@[simp] private theorem karoubiBraiding_inv_f
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (X Y : Karoubi C) :
    (β_ X Y).inv.f = (Y.p ⊗ₘ X.p) ≫ (β_ X.X Y.X).inv := rfl

end Braided

section Symmetric

/-- And a symmetric one stays symmetric. -/
noncomputable instance karoubiSymmetric
    [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] :
    SymmetricCategory (Karoubi C) where
  symmetry X Y := by
    apply Karoubi.hom_ext
    simp only [Karoubi.comp_f, Karoubi.id_f, karoubiBraiding_hom_f,
      karoubiTensorObj_p, assoc]
    rw [← assoc (X.p ⊗ₘ Y.p), braid_nat X Y, assoc]
    have h : ∀ {E : C} (h : Y.X ⊗ X.X ⟶ E),
        (Y.p ⊗ₘ X.p) ≫ ((Y.p ⊗ₘ X.p) ≫ h) = (Y.p ⊗ₘ X.p) ≫ h := by
      intro E h; rw [← assoc, tensorHom_idem Y.idem X.idem]
    rw [h, braid_nat Y X, ← assoc, SymmetricCategory.symmetry, id_comp]

end Symmetric

end RS
