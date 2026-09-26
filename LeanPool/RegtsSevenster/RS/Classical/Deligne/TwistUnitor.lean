/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreeModShuffle
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.TwistShuffle

/-!
# Unit, associativity and functoriality of the left twist

The twist of a module by an object on the left is unital and
associative, is functorial in both of its slots, and carries the
free modules along the braiding.  Every isomorphism here is a
structural isomorphism of the ambient category, promoted to the
category of modules by checking that it intertwines the twisted
actions.

* `tensorLeftUnitMod`: twisting by the tensor unit is the left
  unitor.
* `tensorLeftAssocMod`: nested twists collapse to a single twist
  by the tensor of the twisting objects.
* functoriality in the module slot and in the twisting object:
  `RS.tensorLeftModWhiskerIso` and `RS.tensorLeftModContextIso`
  of `TwistShuffle.lean`.
* `freeTwistIso`: the free module on a twisted object is the
  twist of the free module, through the carrying isomorphism.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## The unit twist -/

/-- The left unitor intertwines the twist by the tensor unit with
the plain action. -/
theorem actAcross_unit
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A]
    (X : D) [ModObj A X] :
    actAcross A (𝟙_ D) X ≫ (λ_ X).hom =
      (A ◁ (λ_ X).hom) ≫ actLeft A X := by
  have h : (α_ A (𝟙_ D) X).inv ≫ ((β_ A (𝟙_ D)).hom ▷ X) ≫
      (α_ (𝟙_ D) A X).hom ≫ (λ_ (A ⊗ X)).hom =
      A ◁ (λ_ X).hom := by
    rw [braiding_tensorUnit_right]
    monoidal
  rw [actAcross]
  simp only [Category.assoc]
  rw [leftUnitor_naturality, reassoc_of% h]

/-- **The unit twist collapses**: twisting a module by the tensor
unit is the left unitor, as a module isomorphism. -/
noncomputable def tensorLeftUnitMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A]
    (M : Mod D A) :
    tensorLeftMod A (𝟙_ D) M ≅ M where
  hom := Mod.Hom.mk' (λ_ M.X).hom (by
    change actAcross A (𝟙_ D) M.X ≫ (λ_ M.X).hom =
      (A ◁ (λ_ M.X).hom) ≫ actLeft A M.X
    exact actAcross_unit A M.X)
  inv := Mod.Hom.mk' (λ_ M.X).inv (by
    change actLeft A M.X ≫ (λ_ M.X).inv =
      (A ◁ (λ_ M.X).inv) ≫ actAcross A (𝟙_ D) M.X
    exact act_inv_of_act_hom A (λ_ M.X) (actAcross_unit A M.X))
  hom_inv_id := by
    apply Mod.Hom.ext
    exact (λ_ M.X).hom_inv_id
  inv_hom_id := by
    apply Mod.Hom.ext
    exact (λ_ M.X).inv_hom_id

/-! ## Nested twists -/

/-- The associator intertwines the twist by a tensor of twisting
objects with the nested twist. -/
theorem actAcross_assoc_split
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A]
    (V W : D) (M : Mod D A) :
    actAcross A (V ⊗ W) M.X ≫ (α_ V W M.X).hom =
      (A ◁ (α_ V W M.X).hom) ≫
        actAcross A V (tensorLeftMod A W M).X := by
  have h : actAcross A V (tensorLeftMod A W M).X =
      (braidPast A V (W ⊗ M.X)).hom ≫
        (V ◁ actAcross A W M.X) :=
    actAcross_eq_braidPast A V (tensorLeftMod A W M).X
  rw [h]
  exact actAcross_context_split A V W M.X

/-- **Nested twists collapse**: twisting by `W` and then by `V` is
twisting by `V ⊗ W`, through the associator. -/
noncomputable def tensorLeftAssocMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A]
    (V W : D) (M : Mod D A) :
    tensorLeftMod A V (tensorLeftMod A W M) ≅
      tensorLeftMod A (V ⊗ W) M where
  hom := Mod.Hom.mk' (α_ V W M.X).inv (by
    change actAcross A V (tensorLeftMod A W M).X ≫
        (α_ V W M.X).inv =
      (A ◁ (α_ V W M.X).inv) ≫ actAcross A (V ⊗ W) M.X
    exact act_inv_of_act_hom A (α_ V W M.X)
      (actAcross_assoc_split A V W M))
  inv := Mod.Hom.mk' (α_ V W M.X).hom (by
    change actAcross A (V ⊗ W) M.X ≫ (α_ V W M.X).hom =
      (A ◁ (α_ V W M.X).hom) ≫
        actAcross A V (tensorLeftMod A W M).X
    exact actAcross_assoc_split A V W M)
  hom_inv_id := by
    apply Mod.Hom.ext
    exact (α_ V W M.X).inv_hom_id
  inv_hom_id := by
    apply Mod.Hom.ext
    exact (α_ V W M.X).hom_inv_id

/-! ## The free module on a twisted object -/

/-- The carrying isomorphism is natural in the crossing object. -/
theorem braidPast_natural_head
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    {P Q : D} (f : P ⟶ Q) (V T : D) :
    (f ▷ (V ⊗ T)) ≫ (braidPast Q V T).hom =
      (braidPast P V T).hom ≫ (V ◁ (f ▷ T)) := by
  simp only [braidPast_hom]
  rw [associator_inv_naturality_left_assoc,
    ← comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_left,
    comp_whiskerRight_assoc, associator_naturality_middle]
  simp only [Category.assoc]

/-- The carrying isomorphism intertwines the free action on a
twisted object with the twist of the free action. -/
theorem freeTwist_act
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A]
    (V X : D) :
    ((α_ A A (V ⊗ X)).inv ≫ (μ[A] ▷ (V ⊗ X))) ≫
        (braidPast A V X).hom =
      (A ◁ (braidPast A V X).hom) ≫
        actAcross A V (freeMod A X).X := by
  let := freeModObj A X
  have hbp : (braidPast (A ⊗ A) V X).hom =
      (α_ A A (V ⊗ X)).hom ≫ (A ◁ (braidPast A V X).hom) ≫
        (braidPast A V (A ⊗ X)).hom ≫ (V ◁ (α_ A A X).inv) := by
    rw [braidPast_hom]
    exact braidPast_tensor_first A A V X
  change ((α_ A A (V ⊗ X)).inv ≫ (μ[A] ▷ (V ⊗ X))) ≫
      (braidPast A V X).hom =
    (A ◁ (braidPast A V X).hom) ≫ actAcross A V (A ⊗ X)
  rw [actAcross_eq_braidPast A V (A ⊗ X),
    show actLeft A (A ⊗ X) = (α_ A A X).inv ≫ (μ[A] ▷ X)
      from rfl,
    Category.assoc, braidPast_natural_head μ[A] V X, hbp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc,
    ← MonoidalCategory.whiskerLeft_comp]

/-- **The free module on a twisted object**: the free module on
`V ⊗ X` is the twist by `V` of the free module on `X`, through the
isomorphism carrying the algebra across the twisting object. -/
noncomputable def freeTwistIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A]
    (V X : D) :
    freeMod A (V ⊗ X) ≅ tensorLeftMod A V (freeMod A X) where
  hom := Mod.Hom.mk' (braidPast A V X).hom (by
    change ((α_ A A (V ⊗ X)).inv ≫ (μ[A] ▷ (V ⊗ X))) ≫
        (braidPast A V X).hom =
      (A ◁ (braidPast A V X).hom) ≫
        actAcross A V (freeMod A X).X
    exact freeTwist_act A V X)
  inv := Mod.Hom.mk' (braidPast A V X).inv (by
    change actAcross A V (freeMod A X).X ≫
        (braidPast A V X).inv =
      (A ◁ (braidPast A V X).inv) ≫
        ((α_ A A (V ⊗ X)).inv ≫ (μ[A] ▷ (V ⊗ X)))
    exact act_inv_of_act_hom A (braidPast A V X)
      (freeTwist_act A V X))
  hom_inv_id := by
    apply Mod.Hom.ext
    exact (braidPast A V X).hom_inv_id
  inv_hom_id := by
    apply Mod.Hom.ext
    exact (braidPast A V X).inv_hom_id

end RS
