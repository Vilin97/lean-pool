/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.OddLinePairing

/-!
# Tensoring by the odd line swaps parity

The odd line is self-dual, so tensoring by it is an equivalence on
Hom-spaces: points of a twisted object are odd elements of the
object.  Concretely, `𝟙 ⟶ M ⊗ L` and `L ⟶ M` are the same
ℂ-module, the passage between them being capping the twisting leg
against the square trivialisation.  Both directions are visibly
ℂ-linear, composition and whiskering being bilinear, and the two
round trips are the two triangle identities of the self-duality.

The mirror form, with the twist on the left, is obtained from this
one by transporting along the braiding.
-/

namespace RS

open CategoryTheory MonoidalCategory

universe v u

variable {D : Type u}

/-- Feeding the coevaluation into a map out of `𝟙 ⊗ L` is the same
as feeding it in on the other side: the unitors and the associator
absorb the difference. -/
theorem OddLine.coevaluation_whiskerRight
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D]
    (L : OddLine D) {M : D}
    (g : 𝟙_ D ⊗ L.obj ⟶ M) :
    L.sq.inv ≫ (((λ_ L.obj).inv ≫ g) ▷ L.obj) =
      (ρ_ (𝟙_ D)).inv ≫ (𝟙_ D ◁ L.sq.inv) ≫
        (α_ (𝟙_ D) L.obj L.obj).inv ≫ (g ▷ L.obj) := by
  have hc : ((λ_ L.obj).inv ▷ L.obj) =
      (λ_ (L.obj ⊗ L.obj)).inv ≫ (α_ (𝟙_ D) L.obj L.obj).inv := by
    monoidal
  have h1 : L.sq.inv ≫ ((λ_ L.obj).inv ▷ L.obj) =
      (ρ_ (𝟙_ D)).inv ≫ (𝟙_ D ◁ L.sq.inv) ≫
        (α_ (𝟙_ D) L.obj L.obj).inv := by
    rw [hc, ← Category.assoc, leftUnitor_inv_naturality,
      unitors_inv_equal, Category.assoc]
  rw [MonoidalCategory.comp_whiskerRight, ← Category.assoc, h1]
  simp only [Category.assoc]

/-- **Tensoring by the odd line swaps parity**: points of a
twisted object are odd elements of the object. -/
noncomputable def oddParitySwap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (M : D) :
    (𝟙_ D ⟶ M ⊗ L.obj) ≃ₗ[ℂ] (L.obj ⟶ M) where
  toFun f := (λ_ L.obj).inv ≫ (f ▷ L.obj) ≫
    (α_ M L.obj L.obj).hom ≫ (M ◁ L.sq.hom) ≫ (ρ_ M).hom
  map_add' f g := by
    simp [MonoidalPreadditive.add_whiskerRight, Preadditive.comp_add,
      Preadditive.add_comp]
  map_smul' c f := by
    simp [MonoidalLinear.smul_whiskerRight, Linear.comp_smul,
      Linear.smul_comp]
  invFun g := L.sq.inv ≫ (g ▷ L.obj)
  left_inv f := by
    change L.sq.inv ≫ (((λ_ L.obj).inv ≫ (f ▷ L.obj) ≫
      (α_ M L.obj L.obj).hom ≫ (M ◁ L.sq.hom) ≫ (ρ_ M).hom)
        ▷ L.obj) = f
    let := L.exactPairing
    have hs : ∀ F : 𝟙_ D ⟶ M ⊗ L.obj,
        (tensorRightHomEquiv (𝟙_ D) L.obj L.obj M).symm F =
          (F ▷ L.obj) ≫ (α_ M L.obj L.obj).hom ≫
            (M ◁ L.sq.hom) ≫ (ρ_ M).hom := fun _ => rfl
    have ht : ∀ g : 𝟙_ D ⊗ L.obj ⟶ M,
        (tensorRightHomEquiv (𝟙_ D) L.obj L.obj M) g =
          (ρ_ (𝟙_ D)).inv ≫ (𝟙_ D ◁ L.sq.inv) ≫
            (α_ (𝟙_ D) L.obj L.obj).inv ≫ (g ▷ L.obj) :=
      fun _ => rfl
    rw [← hs, L.coevaluation_whiskerRight, ← ht,
      Equiv.apply_symm_apply]
  right_inv g := by
    change (λ_ L.obj).inv ≫ ((L.sq.inv ≫ (g ▷ L.obj)) ▷ L.obj) ≫
      (α_ M L.obj L.obj).hom ≫ (M ◁ L.sq.hom) ≫ (ρ_ M).hom = g
    let := L.exactPairing
    have hs : ∀ F : 𝟙_ D ⟶ M ⊗ L.obj,
        (tensorRightHomEquiv (𝟙_ D) L.obj L.obj M).symm F =
          (F ▷ L.obj) ≫ (α_ M L.obj L.obj).hom ≫
            (M ◁ L.sq.hom) ≫ (ρ_ M).hom := fun _ => rfl
    have ht : ∀ g : 𝟙_ D ⊗ L.obj ⟶ M,
        (tensorRightHomEquiv (𝟙_ D) L.obj L.obj M) g =
          (ρ_ (𝟙_ D)).inv ≫ (𝟙_ D ◁ L.sq.inv) ≫
            (α_ (𝟙_ D) L.obj L.obj).inv ≫ (g ▷ L.obj) :=
      fun _ => rfl
    have hkey : (tensorRightHomEquiv (𝟙_ D) L.obj L.obj M)
        ((λ_ L.obj).hom ≫ g) = L.sq.inv ≫ (g ▷ L.obj) := by
      rw [ht, ← L.coevaluation_whiskerRight, Iso.inv_hom_id_assoc]
    rw [← hs, ← hkey, Equiv.symm_apply_apply, Iso.inv_hom_id_assoc]

@[simp]
theorem oddParitySwap_apply
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (M : D)
    (f : 𝟙_ D ⟶ M ⊗ L.obj) :
    oddParitySwap L M f = (λ_ L.obj).inv ≫ (f ▷ L.obj) ≫
      (α_ M L.obj L.obj).hom ≫ (M ◁ L.sq.hom) ≫ (ρ_ M).hom :=
  rfl

@[simp]
theorem oddParitySwap_symm_apply
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (M : D)
    (g : L.obj ⟶ M) :
    (oddParitySwap L M).symm g = L.sq.inv ≫ (g ▷ L.obj) :=
  rfl

/-- **Tensoring by the odd line swaps parity**, with the twist on
the left.  Transporting along the braiding reduces this to the
right-handed form. -/
noncomputable def oddParitySwapLeft
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (M : D) :
    (𝟙_ D ⟶ L.obj ⊗ M) ≃ₗ[ℂ] (L.obj ⟶ M) :=
  (Linear.homCongr ℂ (Iso.refl (𝟙_ D)) (β_ L.obj M)).trans
    (oddParitySwap L M)

@[simp]
theorem oddParitySwapLeft_apply
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (M : D)
    (f : 𝟙_ D ⟶ L.obj ⊗ M) :
    oddParitySwapLeft L M f = (λ_ L.obj).inv ≫
      ((f ≫ (β_ L.obj M).hom) ▷ L.obj) ≫
      (α_ M L.obj L.obj).hom ≫ (M ◁ L.sq.hom) ≫ (ρ_ M).hom := by
  rw [oddParitySwapLeft, LinearEquiv.trans_apply,
    Linear.homCongr_apply, oddParitySwap_apply, Iso.refl_inv,
    Category.id_comp]

@[simp]
theorem oddParitySwapLeft_symm_apply
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (M : D)
    (g : L.obj ⟶ M) :
    (oddParitySwapLeft L M).symm g =
      L.sq.inv ≫ (g ▷ L.obj) ≫ (β_ L.obj M).inv := by
  rw [oddParitySwapLeft, LinearEquiv.symm_trans_apply,
    oddParitySwap_symm_apply, Linear.homCongr_symm_apply,
    Iso.refl_hom, Category.id_comp, Category.assoc]

end RS
