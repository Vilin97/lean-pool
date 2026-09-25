/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Envelope.MatBraided
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.EnvGenerator

/-!
# Monoidal, braided, additive, and linear structure on `Mat_.embedding C`

When `C` is a monoidal preadditive category, the embedding functor
`Mat_.embedding C : C ⥤ Mat_ C` is strong monoidal, braided (when `C` is
braided), additive, and `ℂ`-linear (when `C` is linear).

The key observation is that the embedding sends `X` to the one-by-one
matrix `⟨PUnit, fun _ => X⟩`, so all index types in sight are products of
`PUnit` (hence subsingletons).  Every structural morphism is therefore a
single-entry diagonal matrix carrying the identity of the appropriate
tensor product, and all coherence proofs collapse immediately.

We use `Functor.CoreMonoidal` to avoid manually proving the oplax
coherence conditions: from `εIso`, `μIso`, and the lax axioms, mathlib
automatically derives the full `Functor.Monoidal` structure including
the `OplaxMonoidal` fields.
-/

@[expose] public section

noncomputable section

namespace RS



open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits CategoryTheory.Idempotents

universe v u

variable {C : Type u}

/-! ### The embedding is additive

Mathlib already provides `(Mat_.embedding C).Additive`. -/

example
    [Category.{v} C] [Preadditive C] :
    (Mat_.embedding C).Additive := inferInstance

/-! ### The embedding is `ℂ`-linear -/

section Linear

/-- The embedding into the matrix category is ℂ-linear. -/
instance matEmbeddingLinear
    [Category.{v} C] [Preadditive C] [CategoryTheory.Linear ℂ C] :
    (Mat_.embedding C).Linear ℂ where
  map_smul f r := by ext ⟨⟩ ⟨⟩; rfl

end Linear

/-! #### Naturality and coherence lemmas -/

private theorem matEmb_μ_natural_left
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    {X Y : C} (f : X ⟶ Y) (X' : C) :
    (Mat_.embedding C).map f ▷ (Mat_.embedding C).obj X' ≫ matEmbTensorHom Y X'
      =
    matEmbTensorHom X X' ≫ (Mat_.embedding C).map (f ▷ X') := by
  apply Mat_.hom_ext; intro i j
  have hL : ((Mat_.embedding C).map f ▷ (Mat_.embedding C).obj X' ≫
      matEmbTensorHom Y X') i j =
    ∑ k, ((Mat_.embedding C).map f ▷ (Mat_.embedding C).obj X') i k ≫
      matEmbTensorHom Y X' k j := rfl
  have hR : (matEmbTensorHom X X' ≫ (Mat_.embedding C).map (f ▷ X')) i j =
    ∑ k, matEmbTensorHom X X' i k ≫
      (Mat_.embedding C).map (f ▷ X') k j := rfl
  rw [hL, hR]
  have : Subsingleton ((Mat_.embedding C).obj Y ⊗ (Mat_.embedding C).obj X').ι
    :=
    inferInstanceAs (Subsingleton (PUnit × PUnit))
  have : Subsingleton ((Mat_.embedding C).obj (X ⊗ X')).ι :=
    inferInstanceAs (Subsingleton PUnit)
  set a : ((Mat_.embedding C).obj Y ⊗ (Mat_.embedding C).obj X').ι :=
    (PUnit.unit, PUnit.unit)
  set b : ((Mat_.embedding C).obj (X ⊗ X')).ι := PUnit.unit
  rw [Fintype.sum_subsingleton _ a, Fintype.sum_subsingleton _ b]
  change (f ⊗ₘ (𝟙 ((Mat_.embedding C).obj X') : Mat_.Hom _ _) i.2 a.2) ≫ 𝟙 (Y ⊗
    X') =
    𝟙 (X ⊗ X') ≫ (f ▷ X')
  have : Subsingleton ((Mat_.embedding C).obj X').ι := inferInstanceAs
    (Subsingleton PUnit)
  rw [show i.2 = a.2 from Subsingleton.elim _ _, Mat_.id_apply_self]
  change (f ⊗ₘ 𝟙 X') ≫ 𝟙 (Y ⊗ X') = 𝟙 (X ⊗ X') ≫ (f ▷ X')
  rw [tensorHom_id, comp_id, id_comp]

private theorem matEmb_μ_natural_right
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    {X Y : C} (X' : C) (f : X ⟶ Y) :
    (Mat_.embedding C).obj X' ◁ (Mat_.embedding C).map f ≫ matEmbTensorHom X' Y
      =
    matEmbTensorHom X' X ≫ (Mat_.embedding C).map (X' ◁ f) := by
  apply Mat_.hom_ext; intro i j
  have hL : ((Mat_.embedding C).obj X' ◁ (Mat_.embedding C).map f ≫
      matEmbTensorHom X' Y) i j =
    ∑ k, ((Mat_.embedding C).obj X' ◁ (Mat_.embedding C).map f) i k ≫
      matEmbTensorHom X' Y k j := rfl
  have hR : (matEmbTensorHom X' X ≫ (Mat_.embedding C).map (X' ◁ f)) i j =
    ∑ k, matEmbTensorHom X' X i k ≫
      (Mat_.embedding C).map (X' ◁ f) k j := rfl
  rw [hL, hR]
  have : Subsingleton ((Mat_.embedding C).obj X' ⊗ (Mat_.embedding C).obj Y).ι
    :=
    inferInstanceAs (Subsingleton (PUnit × PUnit))
  have : Subsingleton ((Mat_.embedding C).obj (X' ⊗ X)).ι :=
    inferInstanceAs (Subsingleton PUnit)
  set a : ((Mat_.embedding C).obj X' ⊗ (Mat_.embedding C).obj Y).ι :=
    (PUnit.unit, PUnit.unit)
  set b : ((Mat_.embedding C).obj (X' ⊗ X)).ι := PUnit.unit
  rw [Fintype.sum_subsingleton _ a, Fintype.sum_subsingleton _ b]
  change ((𝟙 ((Mat_.embedding C).obj X') : Mat_.Hom _ _) i.1 a.1 ⊗ₘ f) ≫ 𝟙 (X' ⊗
    Y) =
    𝟙 (X' ⊗ X) ≫ (X' ◁ f)
  have : Subsingleton ((Mat_.embedding C).obj X').ι := inferInstanceAs
    (Subsingleton PUnit)
  rw [show i.1 = a.1 from Subsingleton.elim _ _, Mat_.id_apply_self]
  change (𝟙 X' ⊗ₘ f) ≫ 𝟙 (X' ⊗ Y) = 𝟙 (X' ⊗ X) ≫ (X' ◁ f)
  rw [id_tensorHom, comp_id, id_comp]

/-! #### Associativity -/

-- Restate the private Mat_ associator lemma
open scoped Classical in
private theorem mat_assocHom_apply'
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (M N K : Mat_ C)
    (i : M.ι) (j : N.ι) (k : K.ι) (i' : M.ι) (j' : N.ι) (k' : K.ι) :
    (α_ M N K).hom ((i, j), k) (i', (j', k')) =
      if hi : i = i' then if hj : j = j' then if hk : k = k' then
        eqToHom (by subst hi; subst hj; subst hk; rfl) ≫ (α_ (M.X i') (N.X j')
          (K.X k')).hom
      else 0 else 0 else 0 := rfl

-- Raised budget: associativity of the embedding is checked
-- entrywise on a triple index.
private theorem matEmb_associativity
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (X Y Z : C) :
    matEmbTensorHom X Y ▷ (Mat_.embedding C).obj Z ≫
    matEmbTensorHom (X ⊗ Y) Z ≫ (Mat_.embedding C).map (α_ X Y Z).hom =
    (α_ ((Mat_.embedding C).obj X) ((Mat_.embedding C).obj Y)
      ((Mat_.embedding C).obj Z)).hom ≫
    (Mat_.embedding C).obj X ◁ matEmbTensorHom Y Z ≫
    matEmbTensorHom X (Y ⊗ Z) := by
  apply Mat_.hom_ext; intro i j
  have : Subsingleton ((Mat_.embedding C).obj X).ι := inferInstanceAs
    (Subsingleton PUnit)
  have : Subsingleton ((Mat_.embedding C).obj Y).ι := inferInstanceAs
    (Subsingleton PUnit)
  have : Subsingleton ((Mat_.embedding C).obj Z).ι := inferInstanceAs
    (Subsingleton PUnit)
  -- LHS = (α_ X Y Z).hom
  have hLHS : (matEmbTensorHom X Y ▷ (Mat_.embedding C).obj Z ≫
      matEmbTensorHom (X ⊗ Y) Z ≫ (Mat_.embedding C).map (α_ X Y Z).hom) i j =
      (α_ X Y Z).hom := by
    have h1 : (matEmbTensorHom X Y ▷ (Mat_.embedding C).obj Z ≫
        matEmbTensorHom (X ⊗ Y) Z ≫ (Mat_.embedding C).map (α_ X Y Z).hom) i j =
      ∑ k, (matEmbTensorHom X Y ▷ (Mat_.embedding C).obj Z) i k ≫
        (matEmbTensorHom (X ⊗ Y) Z ≫ (Mat_.embedding C).map (α_ X Y Z).hom) k j
          := rfl
    rw [h1]
    have : Subsingleton ((Mat_.embedding C).obj (X ⊗ Y) ⊗ (Mat_.embedding
      C).obj Z).ι :=
      inferInstanceAs (Subsingleton (PUnit × PUnit))
    set a1 : ((Mat_.embedding C).obj (X ⊗ Y) ⊗ (Mat_.embedding C).obj Z).ι :=
      (PUnit.unit, PUnit.unit)
    rw [Fintype.sum_subsingleton _ a1]
    have h2 : (matEmbTensorHom (X ⊗ Y) Z ≫ (Mat_.embedding C).map (α_ X Y
      Z).hom) a1 j =
      ∑ k, matEmbTensorHom (X ⊗ Y) Z a1 k ≫
        (Mat_.embedding C).map (α_ X Y Z).hom k j := rfl
    rw [h2]
    have : Subsingleton ((Mat_.embedding C).obj ((X ⊗ Y) ⊗ Z)).ι :=
      inferInstanceAs (Subsingleton PUnit)
    set b1 : ((Mat_.embedding C).obj ((X ⊗ Y) ⊗ Z)).ι := PUnit.unit
    rw [Fintype.sum_subsingleton _ b1]
    change (matEmbTensorHom X Y i.1 a1.1 ⊗ₘ (𝟙 ((Mat_.embedding C).obj Z)) i.2
      a1.2) ≫
      𝟙 ((X ⊗ Y) ⊗ Z) ≫ (α_ X Y Z).hom = (α_ X Y Z).hom
    rw [show i.2 = a1.2 from Subsingleton.elim _ _, Mat_.id_apply_self]
    change (𝟙 (X ⊗ Y) ⊗ₘ 𝟙 Z) ≫ 𝟙 ((X ⊗ Y) ⊗ Z) ≫ (α_ X Y Z).hom = (α_ X Y Z).hom
    rw [MonoidalCategory.id_tensorHom_id, id_comp, id_comp]
  -- RHS = (α_ X Y Z).hom
  have hRHS : ((α_ ((Mat_.embedding C).obj X) ((Mat_.embedding C).obj Y)
      ((Mat_.embedding C).obj Z)).hom ≫
      (Mat_.embedding C).obj X ◁ matEmbTensorHom Y Z ≫
      matEmbTensorHom X (Y ⊗ Z)) i j =
      (α_ X Y Z).hom := by
    have h1 : ((α_ ((Mat_.embedding C).obj X) ((Mat_.embedding C).obj Y)
        ((Mat_.embedding C).obj Z)).hom ≫
        (Mat_.embedding C).obj X ◁ matEmbTensorHom Y Z ≫
        matEmbTensorHom X (Y ⊗ Z)) i j =
      ∑ k, (α_ ((Mat_.embedding C).obj X) ((Mat_.embedding C).obj Y)
        ((Mat_.embedding C).obj Z)).hom i k ≫
        ((Mat_.embedding C).obj X ◁ matEmbTensorHom Y Z ≫
         matEmbTensorHom X (Y ⊗ Z)) k j := rfl
    rw [h1]
    have : Subsingleton ((Mat_.embedding C).obj X ⊗
        ((Mat_.embedding C).obj Y ⊗ (Mat_.embedding C).obj Z)).ι :=
      inferInstanceAs (Subsingleton (PUnit × (PUnit × PUnit)))
    set a2 : ((Mat_.embedding C).obj X ⊗
        ((Mat_.embedding C).obj Y ⊗ (Mat_.embedding C).obj Z)).ι :=
      (PUnit.unit, (PUnit.unit, PUnit.unit))
    rw [Fintype.sum_subsingleton _ a2]
    have h2 : ((Mat_.embedding C).obj X ◁ matEmbTensorHom Y Z ≫
        matEmbTensorHom X (Y ⊗ Z)) a2 j =
      ∑ k, ((Mat_.embedding C).obj X ◁ matEmbTensorHom Y Z) a2 k ≫
        matEmbTensorHom X (Y ⊗ Z) k j := rfl
    rw [h2]
    have : Subsingleton ((Mat_.embedding C).obj X ⊗
        (Mat_.embedding C).obj (Y ⊗ Z)).ι :=
      inferInstanceAs (Subsingleton (PUnit × PUnit))
    set b2 : ((Mat_.embedding C).obj X ⊗ (Mat_.embedding C).obj (Y ⊗ Z)).ι :=
      (PUnit.unit, PUnit.unit)
    rw [Fintype.sum_subsingleton _ b2]
    -- Evaluate associator entry separately
    have h_assoc : (α_ ((Mat_.embedding C).obj X) ((Mat_.embedding C).obj Y)
        ((Mat_.embedding C).obj Z)).hom i a2 = (α_ X Y Z).hom := by
      rw [show i = ((i.1.1, i.1.2), i.2) from rfl,
          show a2 = (a2.1, (a2.2.1, a2.2.2)) from rfl,
          mat_assocHom_apply',
          dite_eq_left (Subsingleton.elim i.1.1 a2.1),
          dite_eq_left (Subsingleton.elim i.1.2 a2.2.1),
          dite_eq_left (Subsingleton.elim i.2 a2.2.2)]
      erw [eqToHom_refl, id_comp]; rfl
    rw [h_assoc]
    -- Now: (α_ X Y Z).hom ≫ whiskerLeft ≫ matEmbTensorHom = (α_ X Y Z).hom
    change (α_ X Y Z).hom ≫
      ((𝟙 ((Mat_.embedding C).obj X)) a2.1 b2.1 ⊗ₘ matEmbTensorHom Y Z a2.2
        b2.2) ≫
      𝟙 (X ⊗ (Y ⊗ Z)) = (α_ X Y Z).hom
    rw [show a2.1 = b2.1 from Subsingleton.elim _ _, Mat_.id_apply_self]
    change (α_ X Y Z).hom ≫ (𝟙 X ⊗ₘ 𝟙 (Y ⊗ Z)) ≫ 𝟙 (X ⊗ (Y ⊗ Z)) = (α_ X Y Z).hom
    rw [MonoidalCategory.id_tensorHom_id, id_comp, comp_id]
  rw [hLHS, hRHS]

/-! #### Unitality -/

-- Component lemmas restated from private defs
open scoped Classical in
private theorem mat_leftUnitorHom_apply'
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (M : Mat_ C) (i : PUnit) (j k : M.ι) :
    (λ_ M).hom (i, j) k =
      if h : j = k then eqToHom (by subst h; rfl) ≫ (λ_ (M.X k)).hom else 0
        := rfl

open scoped Classical in
private theorem mat_rightUnitorHom_apply'
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (M : Mat_ C) (i : M.ι) (j : PUnit) (k
  : M.ι) :
    (ρ_ M).hom (i, j) k =
      if h : i = k then eqToHom (by subst h; rfl) ≫ (ρ_ (M.X k)).hom else 0
        := rfl

-- Raised budget: unitality is checked entrywise against the
-- one-object index.
private theorem matEmb_left_unitality
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (X : C) :
    (λ_ ((Mat_.embedding C).obj X)).hom =
    (𝟙 ((Mat_.embedding C).obj (𝟙_ C)) :
      𝟙_ (Mat_ C) ⟶ (Mat_.embedding C).obj (𝟙_ C)) ▷
      (Mat_.embedding C).obj X ≫
    matEmbTensorHom (𝟙_ C) X ≫
    (Mat_.embedding C).map (λ_ X).hom := by
  apply Mat_.hom_ext; intro i j
  have : Subsingleton ((Mat_.embedding C).obj (𝟙_ C)).ι :=
    inferInstanceAs (Subsingleton PUnit)
  have : Subsingleton ((Mat_.embedding C).obj X).ι :=
    inferInstanceAs (Subsingleton PUnit)
  have : Subsingleton (𝟙_ (Mat_ C)).ι :=
    inferInstanceAs (Subsingleton PUnit)
  -- LHS = (λ_ X).hom
  have hLHS : (λ_ ((Mat_.embedding C).obj X)).hom i j = (λ_ X).hom := by
    rw [show i = (i.1, i.2) from rfl, mat_leftUnitorHom_apply',
        dite_eq_left (Subsingleton.elim i.2 j)]
    erw [eqToHom_refl, id_comp]; rfl
  -- RHS = (λ_ X).hom
  have hRHS : ((𝟙 ((Mat_.embedding C).obj (𝟙_ C)) :
      𝟙_ (Mat_ C) ⟶ (Mat_.embedding C).obj (𝟙_ C)) ▷
      (Mat_.embedding C).obj X ≫
    matEmbTensorHom (𝟙_ C) X ≫
    (Mat_.embedding C).map (λ_ X).hom) i j = (λ_ X).hom := by
    have h1 : ((𝟙 ((Mat_.embedding C).obj (𝟙_ C)) :
        𝟙_ (Mat_ C) ⟶ (Mat_.embedding C).obj (𝟙_ C)) ▷
        (Mat_.embedding C).obj X ≫
      (matEmbTensorHom (𝟙_ C) X ≫
       (Mat_.embedding C).map (λ_ X).hom)) i j =
      ∑ k, ((𝟙 ((Mat_.embedding C).obj (𝟙_ C)) :
        𝟙_ (Mat_ C) ⟶ (Mat_.embedding C).obj (𝟙_ C)) ▷
        (Mat_.embedding C).obj X) i k ≫
        (matEmbTensorHom (𝟙_ C) X ≫ (Mat_.embedding C).map (λ_ X).hom) k j
          := rfl
    rw [h1]
    have : Subsingleton ((Mat_.embedding C).obj (𝟙_ C) ⊗ (Mat_.embedding C).obj
      X).ι :=
      inferInstanceAs (Subsingleton (PUnit × PUnit))
    set a : ((Mat_.embedding C).obj (𝟙_ C) ⊗ (Mat_.embedding C).obj X).ι :=
      (PUnit.unit, PUnit.unit)
    rw [Fintype.sum_subsingleton _ a]
    have h2 : (matEmbTensorHom (𝟙_ C) X ≫ (Mat_.embedding C).map (λ_ X).hom) a j
      =
      ∑ k, matEmbTensorHom (𝟙_ C) X a k ≫
        (Mat_.embedding C).map (λ_ X).hom k j := rfl
    rw [h2]
    have : Subsingleton ((Mat_.embedding C).obj (𝟙_ C ⊗ X)).ι :=
      inferInstanceAs (Subsingleton PUnit)
    set b : ((Mat_.embedding C).obj (𝟙_ C ⊗ X)).ι := PUnit.unit
    rw [Fintype.sum_subsingleton _ b]
    change ((𝟙 ((Mat_.embedding C).obj (𝟙_ C)) : Mat_.Hom _ _) i.1 a.1 ⊗ₘ
      (𝟙 ((Mat_.embedding C).obj X) : Mat_.Hom _ _) i.2 a.2) ≫
      𝟙 (𝟙_ C ⊗ X) ≫ (λ_ X).hom = (λ_ X).hom
    rw [show i.1 = a.1 from Subsingleton.elim _ _, Mat_.id_apply_self,
        show i.2 = a.2 from Subsingleton.elim _ _, Mat_.id_apply_self]
    change (𝟙 (𝟙_ C) ⊗ₘ 𝟙 X) ≫ 𝟙 (𝟙_ C ⊗ X) ≫ (λ_ X).hom = (λ_ X).hom
    rw [MonoidalCategory.id_tensorHom_id, id_comp, id_comp]
  rw [hLHS, hRHS]

-- As for left unitality.
private theorem matEmb_right_unitality
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (X : C) :
    (ρ_ ((Mat_.embedding C).obj X)).hom =
    (Mat_.embedding C).obj X ◁
    (𝟙 ((Mat_.embedding C).obj (𝟙_ C)) :
      𝟙_ (Mat_ C) ⟶ (Mat_.embedding C).obj (𝟙_ C)) ≫
    matEmbTensorHom X (𝟙_ C) ≫
    (Mat_.embedding C).map (ρ_ X).hom := by
  apply Mat_.hom_ext; intro i j
  have : Subsingleton ((Mat_.embedding C).obj X).ι := inferInstanceAs
    (Subsingleton PUnit)
  have : Subsingleton ((Mat_.embedding C).obj (𝟙_ C)).ι :=
    inferInstanceAs (Subsingleton PUnit)
  have : Subsingleton (𝟙_ (Mat_ C)).ι := inferInstanceAs (Subsingleton PUnit)
  -- LHS = (ρ_ X).hom
  have hLHS : (ρ_ ((Mat_.embedding C).obj X)).hom i j = (ρ_ X).hom := by
    rw [show i = (i.1, i.2) from rfl, mat_rightUnitorHom_apply',
        dite_eq_left (Subsingleton.elim i.1 j)]
    erw [eqToHom_refl, id_comp]; rfl
  -- RHS = (ρ_ X).hom
  have hRHS : ((Mat_.embedding C).obj X ◁
      (𝟙 ((Mat_.embedding C).obj (𝟙_ C)) :
        𝟙_ (Mat_ C) ⟶ (Mat_.embedding C).obj (𝟙_ C)) ≫
    matEmbTensorHom X (𝟙_ C) ≫
    (Mat_.embedding C).map (ρ_ X).hom) i j = (ρ_ X).hom := by
    have h1 : ((Mat_.embedding C).obj X ◁
        (𝟙 ((Mat_.embedding C).obj (𝟙_ C)) :
          𝟙_ (Mat_ C) ⟶ (Mat_.embedding C).obj (𝟙_ C)) ≫
      (matEmbTensorHom X (𝟙_ C) ≫
       (Mat_.embedding C).map (ρ_ X).hom)) i j =
      ∑ k, ((Mat_.embedding C).obj X ◁
        (𝟙 ((Mat_.embedding C).obj (𝟙_ C)) :
          𝟙_ (Mat_ C) ⟶ (Mat_.embedding C).obj (𝟙_ C))) i k ≫
        (matEmbTensorHom X (𝟙_ C) ≫ (Mat_.embedding C).map (ρ_ X).hom) k j
          := rfl
    rw [h1]
    have : Subsingleton ((Mat_.embedding C).obj X ⊗ (Mat_.embedding C).obj (𝟙_
      C)).ι :=
      inferInstanceAs (Subsingleton (PUnit × PUnit))
    set a : ((Mat_.embedding C).obj X ⊗ (Mat_.embedding C).obj (𝟙_ C)).ι :=
      (PUnit.unit, PUnit.unit)
    rw [Fintype.sum_subsingleton _ a]
    have h2 : (matEmbTensorHom X (𝟙_ C) ≫ (Mat_.embedding C).map (ρ_ X).hom) a j
      =
      ∑ k, matEmbTensorHom X (𝟙_ C) a k ≫
        (Mat_.embedding C).map (ρ_ X).hom k j := rfl
    rw [h2]
    have : Subsingleton ((Mat_.embedding C).obj (X ⊗ 𝟙_ C)).ι :=
      inferInstanceAs (Subsingleton PUnit)
    set b : ((Mat_.embedding C).obj (X ⊗ 𝟙_ C)).ι := PUnit.unit
    rw [Fintype.sum_subsingleton _ b]
    change ((𝟙 ((Mat_.embedding C).obj X) : Mat_.Hom _ _) i.1 a.1 ⊗ₘ
      (𝟙 ((Mat_.embedding C).obj (𝟙_ C)) : Mat_.Hom _ _) i.2 a.2) ≫
      𝟙 (X ⊗ 𝟙_ C) ≫ (ρ_ X).hom = (ρ_ X).hom
    rw [show i.1 = a.1 from Subsingleton.elim _ _, Mat_.id_apply_self,
        show i.2 = a.2 from Subsingleton.elim _ _, Mat_.id_apply_self]
    change (𝟙 X ⊗ₘ 𝟙 (𝟙_ C)) ≫ 𝟙 (X ⊗ 𝟙_ C) ≫ (ρ_ X).hom = (ρ_ X).hom
    rw [MonoidalCategory.id_tensorHom_id, id_comp, id_comp]
  rw [hLHS, hRHS]

/-! #### The CoreMonoidal structure and Monoidal instance -/

/-- The `CoreMonoidal` structure on `Mat_.embedding C`, providing isomorphisms
`εIso : 𝟙_ (Mat_ C) ≅ (Mat_.embedding C).obj (𝟙_ C)`, the identity since
these coincide, and `μIso X Y : emb X ⊗ emb Y ≅ emb (X ⊗ Y)` from
`matEmbTensorIso`. -/
private noncomputable def matEmbCoreMonoidal
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] :
    (Mat_.embedding C).CoreMonoidal where
  εIso := Iso.refl _
  μIso X Y := matEmbTensorIso X Y
  μIso_hom_natural_left := matEmb_μ_natural_left
  μIso_hom_natural_right := matEmb_μ_natural_right
  associativity := matEmb_associativity
  left_unitality := matEmb_left_unitality
  right_unitality := matEmb_right_unitality

/-- The embedding `Mat_.embedding C` is strong monoidal.  The full `Monoidal`
structure, `OplaxMonoidal` coherence included, comes from `CoreMonoidal`. -/
noncomputable instance matEmbeddingMonoidal
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] :
    Functor.Monoidal (Mat_.embedding C) :=
  matEmbCoreMonoidal.toMonoidal

/-! ### The braided structure on `Mat_.embedding C` -/

section Braided

-- Braiding component formula (restated from private def)
open scoped Classical in
private theorem mat_braidHom_apply'
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] [BraidedCategory C]
    (M N : Mat_ C)
    (i₁ : M.ι) (i₂ : N.ι) (j₁ : N.ι) (j₂ : M.ι) :
    (β_ M N).hom (i₁, i₂) (j₁, j₂) =
      if hi : i₂ = j₁ then if hj : i₁ = j₂ then
        eqToHom (by subst hi; subst hj; rfl) ≫ (β_ (M.X j₂) (N.X j₁)).hom
      else 0 else 0 := rfl

-- Raised budget: the braided axiom is checked entrywise through
-- the tensorator.
private theorem matEmb_braided
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] [BraidedCategory C]
    (X Y : C) :
    Functor.LaxMonoidal.μ (Mat_.embedding C) X Y ≫
      (Mat_.embedding C).map (β_ X Y).hom =
    (β_ ((Mat_.embedding C).obj X) ((Mat_.embedding C).obj Y)).hom ≫
      Functor.LaxMonoidal.μ (Mat_.embedding C) Y X := by
  -- μ is matEmbTensorHom by CoreMonoidal construction
  change matEmbTensorHom X Y ≫ (Mat_.embedding C).map (β_ X Y).hom =
    (β_ ((Mat_.embedding C).obj X) ((Mat_.embedding C).obj Y)).hom ≫
      matEmbTensorHom Y X
  apply Mat_.hom_ext; intro i j
  have : Subsingleton ((Mat_.embedding C).obj X).ι := inferInstanceAs
    (Subsingleton PUnit)
  have : Subsingleton ((Mat_.embedding C).obj Y).ι := inferInstanceAs
    (Subsingleton PUnit)
  -- LHS = (β_ X Y).hom
  have hLHS : (matEmbTensorHom X Y ≫ (Mat_.embedding C).map (β_ X Y).hom) i j =
      (β_ X Y).hom := by
    have h1 : (matEmbTensorHom X Y ≫ (Mat_.embedding C).map (β_ X Y).hom) i j =
      ∑ k, matEmbTensorHom X Y i k ≫
        (Mat_.embedding C).map (β_ X Y).hom k j := rfl
    rw [h1]
    have : Subsingleton ((Mat_.embedding C).obj (X ⊗ Y)).ι :=
      inferInstanceAs (Subsingleton PUnit)
    set a : ((Mat_.embedding C).obj (X ⊗ Y)).ι := PUnit.unit
    rw [Fintype.sum_subsingleton _ a]
    change 𝟙 (X ⊗ Y) ≫ (β_ X Y).hom = (β_ X Y).hom
    rw [id_comp]
  -- RHS = (β_ X Y).hom
  have hRHS : ((β_ ((Mat_.embedding C).obj X) ((Mat_.embedding C).obj Y)).hom ≫
      matEmbTensorHom Y X) i j = (β_ X Y).hom := by
    have h1 : ((β_ ((Mat_.embedding C).obj X) ((Mat_.embedding C).obj Y)).hom ≫
        matEmbTensorHom Y X) i j =
      ∑ k, (β_ ((Mat_.embedding C).obj X) ((Mat_.embedding C).obj Y)).hom i k ≫
        matEmbTensorHom Y X k j := rfl
    rw [h1]
    have : Subsingleton ((Mat_.embedding C).obj Y ⊗ (Mat_.embedding C).obj X).ι
      :=
      inferInstanceAs (Subsingleton (PUnit × PUnit))
    set b : ((Mat_.embedding C).obj Y ⊗ (Mat_.embedding C).obj X).ι :=
      (PUnit.unit, PUnit.unit)
    rw [Fintype.sum_subsingleton _ b]
    -- Evaluate braiding entry (erw uses default transparency, avoiding
    -- the ill-typed goal issue that occurs with rw at implicit transparency)
    have h_braid : (β_ ((Mat_.embedding C).obj X) ((Mat_.embedding C).obj
      Y)).hom i b =
        (β_ X Y).hom := by
      erw [show i = (i.1, i.2) from rfl,
           show b = (b.1, b.2) from rfl,
           mat_braidHom_apply',
           dite_eq_left (Subsingleton.elim i.2 b.1),
           dite_eq_left (Subsingleton.elim i.1 b.2)]
      erw [eqToHom_refl, id_comp]; rfl
    rw [h_braid]
    change (β_ X Y).hom ≫ 𝟙 (Y ⊗ X) = (β_ X Y).hom
    rw [comp_id]
  rw [hLHS, hRHS]

/-- The embedding `Mat_.embedding C` is braided when `C` is braided. -/
noncomputable instance matEmbeddingBraided
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] [BraidedCategory C] :
    Functor.Braided (Mat_.embedding C) where
  braided := matEmb_braided

end Braided

end RS

end
