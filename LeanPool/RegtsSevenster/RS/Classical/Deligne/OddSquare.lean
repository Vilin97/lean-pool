/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreeModTensor

/-!
# Contracting the shuffle of two odd twists

The comparison map of Deligne's (2.11.1) at the free module of the
odd line against itself is a shuffle of two morphisms into `R ⊗ 1̄`
followed by the contraction of the two odd legs.  Every such
morphism is a morphism into `R` with an odd leg attached, and the
whole composite then splits: the algebra factors multiply, and what
is left is a pure coherence identity between the two ways of
contracting the two odd legs.

The four instances of that coherence identity — one for each pair
of parities — are the content of this file.  Two of them carry a
sign, and the sign is the self-braiding of the odd line.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

section

variable {D : Type u}

/-- **Splitting off the algebra factors.**  If two morphisms into
`R ⊗ 1̄` are a morphism into `R` with an odd leg attached, then
shuffling them and contracting the two odd legs multiplies the two
morphisms into `R`, after a pure contraction of the odd legs. -/
theorem shuffle_contract
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] (L : OddLine D) (R : D) [MonObj R]
    {A B A' B' : D} (y : A' ⟶ R) (z : B' ⟶ R)
    (pA : A ⟶ A' ⊗ L.obj) (pB : B ⟶ B' ⊗ L.obj) :
    ((pA ≫ (y ▷ L.obj)) ⊗ₘ (pB ≫ (z ▷ L.obj))) ≫
        freeModShuffle R L.obj L.obj ≫ (R ◁ L.sq.hom) ≫
          (ρ_ R).hom =
      ((pA ⊗ₘ pB) ≫ tensorμ A' L.obj B' L.obj ≫
          ((A' ⊗ B') ◁ L.sq.hom) ≫ (ρ_ (A' ⊗ B')).hom) ≫
        ((y ⊗ₘ z) ≫ μ[R]) := by
  have hnat := tensorμ_natural (C := D) y (𝟙 L.obj) z (𝟙 L.obj)
  rw [tensorHom_id, tensorHom_id, tensorHom_id,
    MonoidalCategory.id_whiskerRight] at hnat
  have hfs : ∀ {Z : D} (k : R ⊗ (L.obj ⊗ L.obj) ⟶ Z),
      freeModShuffle R L.obj L.obj ≫ k =
        tensorμ R L.obj R L.obj ≫
          (μ[R] ▷ (L.obj ⊗ L.obj)) ≫ k :=
    fun k => Category.assoc _ _ k
  have hstep : ∀ {W : D} (g : W ⟶ R),
      (g ▷ (L.obj ⊗ L.obj)) ≫ (R ◁ L.sq.hom) ≫ (ρ_ R).hom =
        (W ◁ L.sq.hom) ≫ (ρ_ W).hom ≫ g := by
    intro W g
    rw [← Category.assoc, ← whisker_exchange, Category.assoc,
      rightUnitor_naturality]
  calc ((pA ≫ (y ▷ L.obj)) ⊗ₘ (pB ≫ (z ▷ L.obj))) ≫
        freeModShuffle R L.obj L.obj ≫ (R ◁ L.sq.hom) ≫
          (ρ_ R).hom
      = (pA ⊗ₘ pB) ≫ ((y ▷ L.obj) ⊗ₘ (z ▷ L.obj)) ≫
          tensorμ R L.obj R L.obj ≫ (μ[R] ▷ (L.obj ⊗ L.obj)) ≫
            (R ◁ L.sq.hom) ≫ (ρ_ R).hom := by
        rw [← tensorHom_comp_tensorHom, hfs]
        simp only [Category.assoc]
    _ = (pA ⊗ₘ pB) ≫ tensorμ A' L.obj B' L.obj ≫
          ((y ⊗ₘ z) ▷ (L.obj ⊗ L.obj)) ≫
            (μ[R] ▷ (L.obj ⊗ L.obj)) ≫ (R ◁ L.sq.hom) ≫
              (ρ_ R).hom := by
        rw [← Category.assoc ((y ▷ L.obj) ⊗ₘ (z ▷ L.obj)), hnat]
        simp only [Category.assoc, tensorHom_id]
    _ = (pA ⊗ₘ pB) ≫ tensorμ A' L.obj B' L.obj ≫
          ((A' ⊗ B') ◁ L.sq.hom) ≫ (ρ_ (A' ⊗ B')).hom ≫
            (y ⊗ₘ z) ≫ μ[R] := by
        rw [← comp_whiskerRight_assoc, hstep]
    _ = ((pA ⊗ₘ pB) ≫ tensorμ A' L.obj B' L.obj ≫
          ((A' ⊗ B') ◁ L.sq.hom) ≫ (ρ_ (A' ⊗ B')).hom) ≫
        ((y ⊗ₘ z) ≫ μ[R]) := by
        simp only [Category.assoc]

/-! ## The four contraction identities -/

/-- **The middle-four interchange across two odd lines is minus the
identity**: its only braiding is the self-braiding of the line. -/
theorem tensorμ_oddLine
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] (L : OddLine D)
    (A : D) :
    tensorμ A L.obj L.obj L.obj =
      -𝟙 ((A ⊗ L.obj) ⊗ (L.obj ⊗ L.obj)) := by
  change (α_ A L.obj (L.obj ⊗ L.obj)).hom ≫
      (A ◁ (α_ L.obj L.obj L.obj).inv) ≫
      (A ◁ (β_ L.obj L.obj).hom ▷ L.obj) ≫
      (A ◁ (α_ L.obj L.obj L.obj).hom) ≫
      (α_ A L.obj (L.obj ⊗ L.obj)).inv = _
  rw [L.braid_neg, neg_id_whiskerRight, whiskerLeft_neg_id,
    Preadditive.neg_comp, Preadditive.comp_neg,
    Preadditive.comp_neg]
  refine congrArg Neg.neg ?_
  rw [Category.id_comp]
  monoidal

/-- **Contraction against a coevaluation carries a sign**: the two
odd legs cross. -/
theorem oddContract_neg
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] (L : OddLine D)
    {A A' : D} (pA : A ⟶ A' ⊗ L.obj) :
    (ρ_ A).inv ≫ (pA ⊗ₘ L.sq.inv) ≫
        tensorμ A' L.obj L.obj L.obj ≫
        ((A' ⊗ L.obj) ◁ L.sq.hom) ≫
          (ρ_ (A' ⊗ L.obj)).hom = -pA := by
  rw [tensorμ_oddLine L A']
  simp only [Preadditive.neg_comp, Preadditive.comp_neg,
    Category.id_comp]
  refine congrArg Neg.neg ?_
  rw [tensorHom_def, Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    L.sq.inv_hom_id, MonoidalCategory.whiskerLeft_id,
    Category.id_comp, rightUnitor_naturality, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- **Contraction against a unitor carries no sign**: the free odd
leg passes only the unit. -/
theorem oddContract_pos
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] (L : OddLine D)
    {A A' : D} (pA : A ⟶ A' ⊗ L.obj) :
    (pA ⊗ₘ (λ_ L.obj).inv) ≫ tensorμ A' L.obj (𝟙_ D) L.obj ≫
        ((A' ⊗ 𝟙_ D) ◁ L.sq.hom) ≫ (ρ_ (A' ⊗ 𝟙_ D)).hom =
      (pA ▷ L.obj) ≫ (α_ A' L.obj L.obj).hom ≫
        (A' ◁ L.sq.hom) := by
  have hk : ((A' ⊗ L.obj) ◁ (λ_ L.obj).inv) ≫
      tensorμ A' L.obj (𝟙_ D) L.obj ≫
      ((A' ⊗ 𝟙_ D) ◁ L.sq.hom) ≫ (ρ_ (A' ⊗ 𝟙_ D)).hom =
      (α_ A' L.obj L.obj).hom ≫ (A' ◁ L.sq.hom) := by
    simp only [tensorμ, braiding_tensorUnit_right]
    monoidal
  rw [tensorHom_def, Category.assoc, hk]

/-- The even–even contraction: a sign. -/
theorem oddContract_ee
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] (L : OddLine D) :
    (λ_ (𝟙_ D)).inv ≫ (L.sq.inv ⊗ₘ L.sq.inv) ≫
        tensorμ L.obj L.obj L.obj L.obj ≫
        ((L.obj ⊗ L.obj) ◁ L.sq.hom) ≫
          (ρ_ (L.obj ⊗ L.obj)).hom = -L.sq.inv := by
  rw [unitors_inv_equal]
  exact oddContract_neg L L.sq.inv

/-- The odd–even contraction: a sign. -/
theorem oddContract_oe
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] (L : OddLine D) :
    (ρ_ L.obj).inv ≫ ((λ_ L.obj).inv ⊗ₘ L.sq.inv) ≫
        tensorμ (𝟙_ D) L.obj L.obj L.obj ≫
        ((𝟙_ D ⊗ L.obj) ◁ L.sq.hom) ≫
          (ρ_ (𝟙_ D ⊗ L.obj)).hom = -(λ_ L.obj).inv :=
  oddContract_neg L (λ_ L.obj).inv

/-- The odd–odd contraction: no sign. -/
theorem oddContract_oo
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] (L : OddLine D) :
    L.sq.inv ≫ ((λ_ L.obj).inv ⊗ₘ (λ_ L.obj).inv) ≫
        tensorμ (𝟙_ D) L.obj (𝟙_ D) L.obj ≫
        ((𝟙_ D ⊗ 𝟙_ D) ◁ L.sq.hom) ≫
          (ρ_ (𝟙_ D ⊗ 𝟙_ D)).hom = (λ_ (𝟙_ D)).inv := by
  rw [oddContract_pos L (λ_ L.obj).inv]
  have hc : ((λ_ L.obj).inv ▷ L.obj) ≫
      (α_ (𝟙_ D) L.obj L.obj).hom = (λ_ (L.obj ⊗ L.obj)).inv := by
    monoidal
  rw [← Category.assoc ((λ_ L.obj).inv ▷ L.obj), hc,
    ← leftUnitor_inv_naturality, ← Category.assoc,
    L.sq.inv_hom_id, Category.id_comp]

/-- The even–odd contraction: no sign; it is the triangle identity
of the odd line. -/
theorem oddContract_eo
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] (L : OddLine D) :
    (λ_ L.obj).inv ≫ (L.sq.inv ⊗ₘ (λ_ L.obj).inv) ≫
        tensorμ L.obj L.obj (𝟙_ D) L.obj ≫
        ((L.obj ⊗ 𝟙_ D) ◁ L.sq.hom) ≫
          (ρ_ (L.obj ⊗ 𝟙_ D)).hom = (ρ_ L.obj).inv := by
  rw [oddContract_pos L L.sq.inv, L.evaluation_coevaluation,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end

end RS
