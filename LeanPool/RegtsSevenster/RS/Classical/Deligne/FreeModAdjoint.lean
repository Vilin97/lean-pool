/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreeMixRetract
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreeModFunctor

/-!
# The free–forgetful adjunction for module objects

The free module `freeMod A X` on an object `X` of a monoidal
category `D` carries `A ⊗ X` with the action obtained by
multiplying on the left factor.  Maps of `A`-modules out of it are
the same thing as maps out of `X` in `D`: the bijection sends a
module map to its restriction along the unit
`(λ_ X).inv ≫ η[A] ▷ X` and a bare map `g` to its extension
`A ◁ g ≫ actLeft A M.X`.

* `freeModHomEquiv`: the bijection, with both round trips.
* `freeModHom_eq_zero_iff`: a map out of a free module vanishes
  exactly when its restriction along the unit does.  This is the
  additive shadow of the adjunction, available even though the
  hom-sets of `Mod D A` carry no additive structure here.
* `hom_eq_zero_of_generators`: a module map out of `N` vanishes as
  soon as it is killed by a family of free modules whose retracts
  sum to the identity of `N`.
* `freeModAdjunction`: the bijection bundled as an adjunction
  between `freeModFunctor A` and `Mod.forget A`.

All the intermediate statements are phrased in the ambient
language of `A ⊗ X` and a bare action morphism, and are transported
into the category of module objects by definitional unfolding.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

section Bijection

/-- The unit of the free module is cancelled by the free action. -/
theorem freeMod_unit_mul
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (X : D) :
    A ◁ (λ_ X).inv ≫ A ◁ (η[A] ▷ X) ≫
        (α_ A A X).inv ≫ μ[A] ▷ X = 𝟙 (A ⊗ X) := by
  have h₁ : A ◁ (η[A] ▷ X) ≫ (α_ A A X).inv =
      (α_ A (𝟙_ D) X).inv ≫ (A ◁ η[A]) ▷ X :=
    associator_inv_naturality_middle A η[A] X
  have h₂ : A ◁ (λ_ X).inv ≫ (α_ A (𝟙_ D) X).inv =
      (ρ_ A).inv ▷ X := by
    monoidal
  rw [reassoc_of% h₁, reassoc_of% h₂, ← comp_whiskerRight,
    MonObj.mul_one, ← comp_whiskerRight, Iso.inv_hom_id,
    MonoidalCategory.id_whiskerRight]

/-- Restricting an extended map along the unit recovers the map. -/
theorem unit_whiskerLeft_act
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (X Y : D) (act : A ⊗ Y ⟶ Y)
    (hone : η[A] ▷ Y ≫ act = (λ_ Y).hom) (g : X ⟶ Y) :
    (λ_ X).inv ≫ (η[A] ▷ X) ≫ (A ◁ g ≫ act) = g := by
  rw [← whisker_exchange_assoc, hone]
  simp

/-- Extending the restriction of a module map along the unit
recovers the module map. -/
theorem whiskerLeft_unit_cancel
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (X Y : D) (act : A ⊗ Y ⟶ Y)
    (h : A ⊗ X ⟶ Y)
    (hlin : ((α_ A A X).inv ≫ μ[A] ▷ X) ≫ h = A ◁ h ≫ act) :
    A ◁ ((λ_ X).inv ≫ (η[A] ▷ X) ≫ h) ≫ act = h := by
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [← hlin]
  simp only [Category.assoc]
  rw [reassoc_of% (freeMod_unit_mul A X)]

/-- The extension of a map along the free module intertwines the
free action with the given action. -/
theorem whiskerLeft_act_lin
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (X Y : D) (act : A ⊗ Y ⟶ Y)
    (hassoc : A ◁ act ≫ act = (α_ A A Y).inv ≫ μ[A] ▷ Y ≫ act)
    (g : X ⟶ Y) :
    ((α_ A A X).inv ≫ μ[A] ▷ X) ≫ (A ◁ g ≫ act) =
      A ◁ (A ◁ g ≫ act) ≫ act := by
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [← whisker_exchange_assoc, hassoc,
    associator_inv_naturality_right_assoc]

/-- The module law of a map out of a free module, in tensor
form. -/
theorem freeModHom_lin [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (X : D) (M : Mod D A)
    (f : freeMod A X ⟶ M) :
    ((α_ A A X).inv ≫ μ[A] ▷ X) ≫ f.hom =
      A ◁ f.hom ≫ actLeft A M.X :=
  f.isModHom.smul_hom

/-- **The free–forgetful adjunction bijection for module
objects**: module maps out of the free module on `X` are maps out
of `X`, by restriction along the unit. -/
noncomputable def freeModHomEquiv
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (X : D) (M : Mod D A) :
    (freeMod A X ⟶ M) ≃ (X ⟶ M.X) where
  toFun f := (λ_ X).inv ≫ (η[A] ▷ X) ≫ f.hom
  invFun g := Mod.Hom.mk' (A ◁ g ≫ actLeft A M.X)
    (whiskerLeft_act_lin A X M.X (actLeft A M.X)
      (actLeft_actLeft A M.X) g)
  left_inv f := Mod.Hom.ext
    (whiskerLeft_unit_cancel A X M.X (actLeft A M.X) f.hom
      (freeModHom_lin A X M f))
  right_inv g :=
    unit_whiskerLeft_act A X M.X (actLeft A M.X)
      (one_actLeft A M.X) g

@[simp] theorem freeModHomEquiv_apply
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (X : D) (M : Mod D A)
    (f : freeMod A X ⟶ M) :
    freeModHomEquiv A X M f = (λ_ X).inv ≫ (η[A] ▷ X) ≫ f.hom :=
  rfl

@[simp] theorem freeModHomEquiv_symm_apply_hom
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (X : D)
    (M : Mod D A) (g : X ⟶ M.X) :
    ((freeModHomEquiv A X M).symm g).hom = A ◁ g ≫ actLeft A M.X :=
  rfl

end Bijection

section Vanishing

/-- An equivariant map out of a free module vanishes exactly when
its restriction along the unit does. -/
theorem unit_eq_zero_iff [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] (A : D) [MonObj A]
    (X Y : D) (act : A ⊗ Y ⟶ Y)
    (h : A ⊗ X ⟶ Y)
    (hlin : ((α_ A A X).inv ≫ μ[A] ▷ X) ≫ h = A ◁ h ≫ act) :
    h = 0 ↔ (λ_ X).inv ≫ (η[A] ▷ X) ≫ h = 0 := by
  constructor
  · intro hh
    rw [hh, Limits.comp_zero, Limits.comp_zero]
  · intro hh
    refine Eq.trans
      (whiskerLeft_unit_cancel A X Y act h hlin).symm ?_
    rw [hh, MonoidalPreadditive.whiskerLeft_zero, Limits.zero_comp]

/-- **A map out of a free module vanishes exactly when its
restriction along the unit does.**  This replaces the linearity of
the adjunction bijection, which is unavailable because the
hom-sets of `Mod D A` carry no additive structure. -/
theorem freeModHom_eq_zero_iff
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] (A : D) [MonObj A]
    (X : D) (M : Mod D A)
    (f : freeMod A X ⟶ M) :
    f.hom = 0 ↔ (λ_ X).inv ≫ (η[A] ▷ X) ≫ f.hom = 0 :=
  unit_eq_zero_iff A X M.X (actLeft A M.X) f.hom
    (freeModHom_lin A X M f)

/-- **Generation by a finite family of free modules**: a module map
out of `N` vanishes as soon as its restrictions along the units of
a family of free modules whose retracts sum to the identity of `N`
all vanish. -/
theorem hom_eq_zero_of_generators
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] (A : D) [MonObj A]
    {N M : Mod D A} {J : Type}
    [Fintype J] {f : J → D} (s : ∀ i, freeMod A (f i) ⟶ N)
    (r : ∀ i, N ⟶ freeMod A (f i))
    (htot : ∑ i, (r i).hom ≫ (s i).hom = 𝟙 N.X) (g : N ⟶ M)
    (hg : ∀ i, (λ_ (f i)).inv ≫ (η[A] ▷ (f i)) ≫
      (s i).hom ≫ g.hom = 0) :
    g.hom = 0 := by
  have hz : ∀ i, (s i).hom ≫ g.hom = 0 := fun i =>
    (freeModHom_eq_zero_iff A (f i) M (s i ≫ g)).2 (hg i)
  calc g.hom = (∑ i, (r i).hom ≫ (s i).hom) ≫ g.hom := by
        rw [htot, Category.id_comp]
    _ = ∑ i, (r i).hom ≫ (s i).hom ≫ g.hom := by
        simp only [Preadditive.sum_comp, Category.assoc]
    _ = 0 := Finset.sum_eq_zero fun i _ => by
        rw [hz i, Limits.comp_zero]

end Vanishing

section Adjoint

/-- Restriction along the unit is compatible with postcomposition
in the target. -/
theorem unit_comp_assoc [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (X Y Z : D) (h : A ⊗ X ⟶ Y) (k : Y ⟶ Z) :
    (λ_ X).inv ≫ (η[A] ▷ X) ≫ h ≫ k =
      ((λ_ X).inv ≫ (η[A] ▷ X) ≫ h) ≫ k := by
  simp only [Category.assoc]

/-- **The free–forgetful adjunction for module objects.** -/
noncomputable def freeModAdjunction
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] :
    freeModFunctor A ⊣ Mod.forget A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X M => freeModHomEquiv A X M
      homEquiv_naturality_left_symm := by
        intro X' X M u g
        apply Mod.Hom.ext
        change A ◁ (u ≫ g) ≫ actLeft A M.X =
          A ◁ u ≫ A ◁ g ≫ actLeft A M.X
        erw [MonoidalCategory.whiskerLeft_comp, Category.assoc]
      homEquiv_naturality_right := by
        intro X M M' u v
        exact unit_comp_assoc A X M.X M'.X u.hom v.hom }

end Adjoint

end RS
