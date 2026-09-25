/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.CatTheory.UnitEnd

/-!
# The categorical trace

The trace of an endomorphism `f : X ⟶ X` in a rigid symmetric
monoidal category: coevaluate at `X`, let `f` act, carry the strand
across its right dual with the braiding, and evaluate.  The result
is a scalar, an endomorphism of the tensor unit.

The basic calculus: the trace of the identity is the categorical
dimension; the trace is additive and ℂ-homogeneous; it is cyclic;
and it is multiplicative over the tensor product.
-/

namespace RS

open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory

universe v u

variable {C : Type u}

/-- The categorical trace of an endomorphism: coevaluate, act, cross
the strand over the right dual, and evaluate. -/
def catTrace [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [RigidCategory C]
    {X : C} (f : X ⟶ X) : End (𝟙_ C) :=
  η_ X Xᘁ ≫ f ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ

/-- The categorical dimension of an object: the closed loop obtained
by crossing the coevaluation strand over the dual and evaluating. -/
def catDim [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [RigidCategory C]
    (X : C) : End (𝟙_ C) :=
  η_ X Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ

/-- The trace of the identity is the categorical dimension. -/
theorem catTrace_id [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [RigidCategory C]
    (X : C) : catTrace (𝟙 X) = catDim X := by
  simp [catTrace, catDim]

/-- The trace is additive. -/
theorem catTrace_add [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [Preadditive C] [MonoidalPreadditive C] [RigidCategory C]
    {X : C} (f g : X ⟶ X) :
    catTrace (f + g) = catTrace f + catTrace g := by
  change η_ X Xᘁ ≫ (f + g) ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ =
    (η_ X Xᘁ ≫ f ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ) +
      (η_ X Xᘁ ≫ g ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ)
  simp [MonoidalPreadditive.add_whiskerRight]

/-- The trace is homogeneous for the ℂ-linear structure. -/
theorem catTrace_smul
    [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C]
    [MonoidalLinear ℂ C] [RigidCategory C]
    {X : C} (a : ℂ) (f : X ⟶ X) :
    catTrace (a • f) = a • catTrace f := by
  change η_ X Xᘁ ≫ (a • f) ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ =
    a • (η_ X Xᘁ ≫ f ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ)
  simp [MonoidalLinear.smul_whiskerRight]

/-- **Cyclicity of the categorical trace.**  Both composites close to
the same loop: pass the strands across the pairing with the adjoint
mates and slide the braiding along. -/
theorem catTrace_comp_comm
    [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [RigidCategory C]
    {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) :
    catTrace (f ≫ g) = catTrace (g ≫ f) := by
  change η_ X Xᘁ ≫ (f ≫ g) ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ =
    η_ Y Yᘁ ≫ (g ≫ f) ▷ Yᘁ ≫ (β_ Y Yᘁ).hom ≫ ε_ Y Yᘁ
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  rw [braiding_naturality_left_assoc,
    ← coevaluation_comp_rightAdjointMate_assoc f,
    braiding_naturality_right_assoc,
    ← rightAdjointMate_comp_evaluation g,
    ← comp_whiskerRight_assoc, ← comp_rightAdjointMate,
    rightAdjointMate_comp_evaluation (g ≫ f),
    ← braiding_naturality_left_assoc]

/-- The loop form of the trace: the braiding may be taken first and
the endomorphism absorbed into the evaluation. -/
theorem catTrace_eq_loop
    [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [RigidCategory C]
    {X : C} (f : X ⟶ X) :
    catTrace f = η_ X Xᘁ ≫ (β_ X Xᘁ).hom ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ := by
  change η_ X Xᘁ ≫ f ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ = _
  rw [braiding_naturality_left_assoc]

/-- The trace computed against a chosen exact pairing. -/
def pairTrace [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    {X D : C} (p : ExactPairing X D) (f : X ⟶ X) :
    End (𝟙_ C) :=
  letI := p
  η_ X D ≫ f ▷ D ≫ (β_ X D).hom ≫ ε_ X D

/-- The trace does not depend on the choice of exact pairing: the
comparison morphism between two right duals carries one pairing's
coevaluation and evaluation to the other's. -/
theorem pairTrace_eq [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    {X D₁ D₂ : C} (p₁ : ExactPairing X D₁)
    (p₂ : ExactPairing X D₂) (f : X ⟶ X) :
    pairTrace p₂ f = pairTrace p₁ f := by
  let := p₁
  let := p₂
  obtain ⟨φ, hA, hB⟩ :
      ∃ φ : D₁ ⟶ D₂, η_ X D₁ ≫ X ◁ φ = η_ X D₂ ∧
        φ ▷ X ≫ ε_ X D₂ = ε_ X D₁ := by
    refine ⟨@rightAdjointMate C _ _ X X ⟨D₂⟩ ⟨D₁⟩ (𝟙 X), ?_, ?_⟩
    · simpa using
        @coevaluation_comp_rightAdjointMate C _ _ X X ⟨D₂⟩ ⟨D₁⟩ (𝟙 X)
    · simpa using
        @rightAdjointMate_comp_evaluation C _ _ X X ⟨D₂⟩ ⟨D₁⟩ (𝟙 X)
  change η_ X D₂ ≫ f ▷ D₂ ≫ (β_ X D₂).hom ≫ ε_ X D₂ =
    η_ X D₁ ≫ f ▷ D₁ ≫ (β_ X D₁).hom ≫ ε_ X D₁
  rw [← hA, assoc, whisker_exchange_assoc,
    braiding_naturality_right_assoc, hB]

/-- The categorical trace is the pairing trace of the canonical
pairing supplied by rigidity. -/
theorem catTrace_eq_pairTrace
    [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [RigidCategory C]
    {X : C} (f : X ⟶ X) :
    catTrace f = pairTrace HasRightDual.exact f :=
  rfl

/-- The block braiding carries the nested coevaluations of a tensor
pairing to nested kinked cups: the strands of each loop cross the
other loop twice with opposite senses, so the two crossings cancel
by symmetry and the loops disentangle. -/
theorem nested_cups [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [RigidCategory C]
    (X Y : C) :
    (η_ X Xᘁ ⊗≫ (X ◁ η_ Y Yᘁ) ▷ Xᘁ ⊗≫ 𝟙 ((X ⊗ Y) ⊗ Yᘁ ⊗ Xᘁ)) ≫
        (β_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ)).hom =
      (η_ Y Yᘁ ≫ (β_ Y Yᘁ).hom) ⊗≫
        Yᘁ ◁ ((η_ X Xᘁ ≫ (β_ X Xᘁ).hom) ▷ Y) ⊗≫
        𝟙 ((Yᘁ ⊗ Xᘁ) ⊗ X ⊗ Y) := by
  calc
    (η_ X Xᘁ ⊗≫ (X ◁ η_ Y Yᘁ) ▷ Xᘁ ⊗≫ 𝟙 ((X ⊗ Y) ⊗ Yᘁ ⊗ Xᘁ)) ≫
        (β_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ)).hom
      -- Expand the block braiding into the four strand crossings.
      = η_ X Xᘁ ⊗≫ (X ◁ η_ Y Yᘁ) ▷ Xᘁ ⊗≫
          X ◁ (β_ Y Yᘁ).hom ▷ Xᘁ ⊗≫
          X ◁ Yᘁ ◁ (β_ Y Xᘁ).hom ⊗≫
          (β_ X Yᘁ).hom ▷ (Xᘁ ⊗ Y) ⊗≫
          Yᘁ ◁ (β_ X Xᘁ).hom ▷ Y ⊗≫
          𝟙 ((Yᘁ ⊗ Xᘁ) ⊗ X ⊗ Y) := by
        rw [braiding_tensor_left_hom, braiding_tensor_right_hom,
          braiding_tensor_right_hom]
        monoidal
      -- Group the two inter-loop crossings for the exchange.
    _ = η_ X Xᘁ ⊗≫ (X ◁ η_ Y Yᘁ) ▷ Xᘁ ⊗≫
          X ◁ (β_ Y Yᘁ).hom ▷ Xᘁ ⊗≫
          ((X ⊗ Yᘁ) ◁ (β_ Y Xᘁ).hom ≫ (β_ X Yᘁ).hom ▷ (Xᘁ ⊗ Y)) ⊗≫
          Yᘁ ◁ (β_ X Xᘁ).hom ▷ Y ⊗≫
          𝟙 ((Yᘁ ⊗ Xᘁ) ⊗ X ⊗ Y) := by
        monoidal
      -- The two crossings act on disjoint strands, so they commute.
    _ = η_ X Xᘁ ⊗≫ (X ◁ η_ Y Yᘁ) ▷ Xᘁ ⊗≫
          X ◁ (β_ Y Yᘁ).hom ▷ Xᘁ ⊗≫
          ((β_ X Yᘁ).hom ▷ (Y ⊗ Xᘁ) ≫ (Yᘁ ⊗ X) ◁ (β_ Y Xᘁ).hom) ⊗≫
          Yᘁ ◁ (β_ X Xᘁ).hom ▷ Y ⊗≫
          𝟙 ((Yᘁ ⊗ Xᘁ) ⊗ X ⊗ Y) := by
        rw [whisker_exchange (β_ X Yᘁ).hom (β_ Y Xᘁ).hom]
      -- Insert a cancelling pair of crossings of `X` and `Y`.
    _ = η_ X Xᘁ ⊗≫ (X ◁ η_ Y Yᘁ) ▷ Xᘁ ⊗≫
          X ◁ (β_ Y Yᘁ).hom ▷ Xᘁ ⊗≫
          (β_ X Yᘁ).hom ▷ (Y ⊗ Xᘁ) ⊗≫
          Yᘁ ◁ ((β_ X Y).hom ≫ (β_ Y X).hom) ▷ Xᘁ ⊗≫
          (Yᘁ ⊗ X) ◁ (β_ Y Xᘁ).hom ⊗≫
          Yᘁ ◁ (β_ X Xᘁ).hom ▷ Y ⊗≫
          𝟙 ((Yᘁ ⊗ Xᘁ) ⊗ X ⊗ Y) := by
        rw [SymmetricCategory.symmetry]
        monoidal
      -- The `X` strand now crosses the whole `g`-loop cup at once.
    _ = η_ X Xᘁ ⊗≫ (X ◁ η_ Y Yᘁ) ▷ Xᘁ ⊗≫
          X ◁ (β_ Y Yᘁ).hom ▷ Xᘁ ⊗≫
          (β_ X (Yᘁ ⊗ Y)).hom ▷ Xᘁ ⊗≫
          Yᘁ ◁ (β_ Y X).hom ▷ Xᘁ ⊗≫
          (Yᘁ ⊗ X) ◁ (β_ Y Xᘁ).hom ⊗≫
          Yᘁ ◁ (β_ X Xᘁ).hom ▷ Y ⊗≫
          𝟙 ((Yᘁ ⊗ Xᘁ) ⊗ X ⊗ Y) := by
        rw [braiding_tensor_right_hom]
        monoidal
      -- Group the kinked cup of the `g`-loop with that crossing.
    _ = η_ X Xᘁ ⊗≫
          ((X ◁ (η_ Y Yᘁ ≫ (β_ Y Yᘁ).hom) ≫
            (β_ X (Yᘁ ⊗ Y)).hom) ▷ Xᘁ) ⊗≫
          Yᘁ ◁ (β_ Y X).hom ▷ Xᘁ ⊗≫
          (Yᘁ ⊗ X) ◁ (β_ Y Xᘁ).hom ⊗≫
          Yᘁ ◁ (β_ X Xᘁ).hom ▷ Y ⊗≫
          𝟙 ((Yᘁ ⊗ Xᘁ) ⊗ X ⊗ Y) := by
        monoidal
      -- Slide the crossing off the cup by naturality.
    _ = η_ X Xᘁ ⊗≫
          (((β_ X (𝟙_ C)).hom ≫
            (η_ Y Yᘁ ≫ (β_ Y Yᘁ).hom) ▷ X) ▷ Xᘁ) ⊗≫
          Yᘁ ◁ (β_ Y X).hom ▷ Xᘁ ⊗≫
          (Yᘁ ⊗ X) ◁ (β_ Y Xᘁ).hom ⊗≫
          Yᘁ ◁ (β_ X Xᘁ).hom ▷ Y ⊗≫
          𝟙 ((Yᘁ ⊗ Xᘁ) ⊗ X ⊗ Y) := by
        rw [braiding_naturality_right X (η_ Y Yᘁ ≫ (β_ Y Yᘁ).hom)]
      -- The unit braiding is coherence; regroup the two cups.
    _ = 𝟙 (𝟙_ C) ⊗≫
          (𝟙_ C ◁ η_ X Xᘁ ≫
            (η_ Y Yᘁ ≫ (β_ Y Yᘁ).hom) ▷ (X ⊗ Xᘁ)) ⊗≫
          Yᘁ ◁ (β_ Y X).hom ▷ Xᘁ ⊗≫
          (Yᘁ ⊗ X) ◁ (β_ Y Xᘁ).hom ⊗≫
          Yᘁ ◁ (β_ X Xᘁ).hom ▷ Y ⊗≫
          𝟙 ((Yᘁ ⊗ Xᘁ) ⊗ X ⊗ Y) := by
        rw [braiding_tensorUnit_right]
        monoidal
      -- The two cups are disjoint, so they exchange.
    _ = 𝟙 (𝟙_ C) ⊗≫
          ((η_ Y Yᘁ ≫ (β_ Y Yᘁ).hom) ▷ (𝟙_ C) ≫
            (Yᘁ ⊗ Y) ◁ η_ X Xᘁ) ⊗≫
          Yᘁ ◁ (β_ Y X).hom ▷ Xᘁ ⊗≫
          (Yᘁ ⊗ X) ◁ (β_ Y Xᘁ).hom ⊗≫
          Yᘁ ◁ (β_ X Xᘁ).hom ▷ Y ⊗≫
          𝟙 ((Yᘁ ⊗ Xᘁ) ⊗ X ⊗ Y) := by
        rw [whisker_exchange (η_ Y Yᘁ ≫ (β_ Y Yᘁ).hom) (η_ X Xᘁ)]
      -- The `Y` strand now crosses the whole `f`-loop cup at once.
    _ = (η_ Y Yᘁ ≫ (β_ Y Yᘁ).hom) ⊗≫
          Yᘁ ◁ (Y ◁ η_ X Xᘁ ≫ (β_ Y (X ⊗ Xᘁ)).hom) ⊗≫
          Yᘁ ◁ (β_ X Xᘁ).hom ▷ Y ⊗≫
          𝟙 ((Yᘁ ⊗ Xᘁ) ⊗ X ⊗ Y) := by
        rw [braiding_tensor_right_hom]
        monoidal
      -- Slide that crossing off the cup by naturality.
    _ = (η_ Y Yᘁ ≫ (β_ Y Yᘁ).hom) ⊗≫
          Yᘁ ◁ ((β_ Y (𝟙_ C)).hom ≫ η_ X Xᘁ ▷ Y) ⊗≫
          Yᘁ ◁ (β_ X Xᘁ).hom ▷ Y ⊗≫
          𝟙 ((Yᘁ ⊗ Xᘁ) ⊗ X ⊗ Y) := by
        rw [braiding_naturality_right Y (η_ X Xᘁ)]
      -- The unit braiding is coherence; absorb the residual kink.
    _ = (η_ Y Yᘁ ≫ (β_ Y Yᘁ).hom) ⊗≫
          Yᘁ ◁ ((η_ X Xᘁ ≫ (β_ X Xᘁ).hom) ▷ Y) ⊗≫
          𝟙 ((Yᘁ ⊗ Xᘁ) ⊗ X ⊗ Y) := by
        rw [braiding_tensorUnit_right]
        monoidal

/-- A scalar whiskered on the right of an object may be moved to the
left: naturality of the braiding at the tensor unit, where the
braiding itself is coherence. -/
private theorem scalar_shift
    [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    (s : 𝟙_ C ⟶ 𝟙_ C) (Y : C) :
    s ▷ Y = 𝟙 (𝟙_ C ⊗ Y) ⊗≫ Y ◁ s ⊗≫ 𝟙 (𝟙_ C ⊗ Y) := by
  have h := braiding_naturality_left s Y
  rw [braiding_tensorUnit_left] at h
  calc s ▷ Y
      = (s ▷ Y ≫ ((λ_ Y).hom ≫ (ρ_ Y).inv)) ⊗≫ 𝟙 (𝟙_ C ⊗ Y) := by
        monoidal
    _ = (((λ_ Y).hom ≫ (ρ_ Y).inv) ≫ Y ◁ s) ⊗≫ 𝟙 (𝟙_ C ⊗ Y) := by
        rw [h]
    _ = 𝟙 (𝟙_ C ⊗ Y) ⊗≫ Y ◁ s ⊗≫ 𝟙 (𝟙_ C ⊗ Y) := by
        monoidal

/-- **Multiplicativity of the categorical trace.**  The trace of a
tensor product of endomorphisms is the product of the traces in the
scalar monoid `End (𝟙_ C)`.  The trace of the tensor product may be
computed against the tensor pairing; there the two loops disentangle
by symmetry and the inner loop contracts to a scalar. -/
theorem catTrace_tensorHom
    [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [RigidCategory C]
    {X Y : C} (f : X ⟶ X) (g : Y ⟶ Y) :
    catTrace (f ⊗ₘ g) = catTrace f * catTrace g := by
  rw [End.mul_def, catTrace_eq_pairTrace (f ⊗ₘ g),
    pairTrace_eq (ExactPairing.tensor : ExactPairing (X ⊗ Y) (Yᘁ ⊗ Xᘁ))
      HasRightDual.exact (f ⊗ₘ g)]
  change η_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ) ≫ (f ⊗ₘ g) ▷ (Yᘁ ⊗ Xᘁ) ≫
      (β_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ)).hom ≫ ε_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ) =
    catTrace g ≫ catTrace f
  obtain ⟨s, hs⟩ : ∃ s : 𝟙_ C ⟶ 𝟙_ C,
      η_ X Xᘁ ≫ (β_ X Xᘁ).hom ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ = s := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : 𝟙_ C ⟶ 𝟙_ C,
      η_ Y Yᘁ ≫ (β_ Y Yᘁ).hom ≫ Yᘁ ◁ g ≫ ε_ Y Yᘁ = t := ⟨_, rfl⟩
  calc
    η_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ) ≫ (f ⊗ₘ g) ▷ (Yᘁ ⊗ Xᘁ) ≫
        (β_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ)).hom ≫ ε_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ)
      -- Take the braiding first and let `f ⊗ₘ g` act afterwards.
      = η_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ) ≫ (β_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ)).hom ≫
          (Yᘁ ⊗ Xᘁ) ◁ (f ⊗ₘ g) ≫ ε_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ) := by
        rw [braiding_naturality_left_assoc]
      -- Expose the components of the tensor pairing.
    _ = ((η_ X Xᘁ ⊗≫ (X ◁ η_ Y Yᘁ) ▷ Xᘁ ⊗≫
          𝟙 ((X ⊗ Y) ⊗ Yᘁ ⊗ Xᘁ)) ≫ (β_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ)).hom) ≫
          (Yᘁ ⊗ Xᘁ) ◁ (f ⊗ₘ g) ≫
          (𝟙 ((Yᘁ ⊗ Xᘁ) ⊗ X ⊗ Y) ⊗≫ Yᘁ ◁ (ε_ X Xᘁ ▷ Y) ⊗≫
            ε_ Y Yᘁ) := by
        rw [ExactPairing.tensor_coevaluation,
          ExactPairing.tensor_evaluation]
        simp only [Category.assoc]
      -- Disentangle the two loops.
    _ = ((η_ Y Yᘁ ≫ (β_ Y Yᘁ).hom) ⊗≫
          Yᘁ ◁ ((η_ X Xᘁ ≫ (β_ X Xᘁ).hom) ▷ Y) ⊗≫
          𝟙 ((Yᘁ ⊗ Xᘁ) ⊗ X ⊗ Y)) ≫
          (Yᘁ ⊗ Xᘁ) ◁ (f ⊗ₘ g) ≫
          (𝟙 ((Yᘁ ⊗ Xᘁ) ⊗ X ⊗ Y) ⊗≫ Yᘁ ◁ (ε_ X Xᘁ ▷ Y) ⊗≫
            ε_ Y Yᘁ) := by
        rw [nested_cups]
      -- Split `f ⊗ₘ g` and push `g` past the inner evaluation.
    _ = (η_ Y Yᘁ ≫ (β_ Y Yᘁ).hom) ⊗≫
          Yᘁ ◁ ((η_ X Xᘁ ≫ (β_ X Xᘁ).hom) ▷ Y) ⊗≫
          (Yᘁ ⊗ Xᘁ) ◁ (f ▷ Y) ⊗≫
          Yᘁ ◁ ((Xᘁ ⊗ X) ◁ g ≫ ε_ X Xᘁ ▷ Y) ⊗≫
          ε_ Y Yᘁ := by
        rw [tensorHom_def]
        monoidal
    _ = (η_ Y Yᘁ ≫ (β_ Y Yᘁ).hom) ⊗≫
          Yᘁ ◁ ((η_ X Xᘁ ≫ (β_ X Xᘁ).hom) ▷ Y) ⊗≫
          (Yᘁ ⊗ Xᘁ) ◁ (f ▷ Y) ⊗≫
          Yᘁ ◁ (ε_ X Xᘁ ▷ Y ≫ 𝟙_ C ◁ g) ⊗≫
          ε_ Y Yᘁ := by
        rw [whisker_exchange (ε_ X Xᘁ) g]
      -- The inner loop closes on `f`.
    _ = (η_ Y Yᘁ ≫ (β_ Y Yᘁ).hom) ⊗≫
          Yᘁ ◁ ((η_ X Xᘁ ≫ (β_ X Xᘁ).hom ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ) ▷ Y) ⊗≫
          Yᘁ ◁ g ⊗≫
          ε_ Y Yᘁ := by
        monoidal
    _ = (η_ Y Yᘁ ≫ (β_ Y Yᘁ).hom) ⊗≫
          Yᘁ ◁ (s ▷ Y) ⊗≫ Yᘁ ◁ g ⊗≫ ε_ Y Yᘁ := by
        rw [hs]
      -- Shift the scalar out of the middle slot.
    _ = (η_ Y Yᘁ ≫ (β_ Y Yᘁ).hom) ⊗≫
          ((Yᘁ ⊗ Y) ◁ s ≫ (Yᘁ ◁ g) ▷ 𝟙_ C) ⊗≫
          ε_ Y Yᘁ := by
        rw [scalar_shift s Y]
        monoidal
    _ = (η_ Y Yᘁ ≫ (β_ Y Yᘁ).hom) ⊗≫
          ((Yᘁ ◁ g) ▷ 𝟙_ C ≫ (Yᘁ ⊗ Y) ◁ s) ⊗≫
          ε_ Y Yᘁ := by
        rw [← whisker_exchange (Yᘁ ◁ g) s]
    _ = (η_ Y Yᘁ ≫ (β_ Y Yᘁ).hom) ⊗≫ (Yᘁ ◁ g) ▷ 𝟙_ C ⊗≫
          ((Yᘁ ⊗ Y) ◁ s ≫ ε_ Y Yᘁ ▷ 𝟙_ C) ⊗≫
          𝟙 (𝟙_ C) := by
        monoidal
    _ = (η_ Y Yᘁ ≫ (β_ Y Yᘁ).hom) ⊗≫ (Yᘁ ◁ g) ▷ 𝟙_ C ⊗≫
          (ε_ Y Yᘁ ▷ 𝟙_ C ≫ 𝟙_ C ◁ s) ⊗≫
          𝟙 (𝟙_ C) := by
        rw [whisker_exchange (ε_ Y Yᘁ) s]
      -- The outer loop closes on `g`, and the scalars compose.
    _ = (η_ Y Yᘁ ≫ (β_ Y Yᘁ).hom ≫ Yᘁ ◁ g ≫ ε_ Y Yᘁ) ≫ s := by
        monoidal
    _ = catTrace g ≫ catTrace f := by
        rw [catTrace_eq_loop g, catTrace_eq_loop f, hs, ht]

/-- **The dimension of the tensor unit is one.**  Computed against
the unit's pairing with itself, the loop closes to the identity
scalar. -/
@[simp]
theorem catDim_unit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [RigidCategory C] : catDim (𝟙_ C) = 1 := by
  have h : catDim (𝟙_ C) = pairTrace exactPairingUnit (𝟙 (𝟙_ C)) := by
    rw [← catTrace_id, catTrace_eq_pairTrace]
    exact pairTrace_eq _ _ _
  rw [h, End.one_def]
  change (ρ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ▷ 𝟙_ C) ≫
    (β_ (𝟙_ C) (𝟙_ C)).hom ≫ (ρ_ (𝟙_ C)).hom = 𝟙 (𝟙_ C)
  rw [braiding_tensorUnit_left, MonoidalCategory.unitors_equal]
  monoidal

/-- **The trace as a ℂ-linear map** into the scalar monoid. -/
def catTraceLin [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C]
    [MonoidalLinear ℂ C] [RigidCategory C]
    (X : C) : End X →ₗ[ℂ] End (𝟙_ C) where
  toFun := catTrace
  map_add' := catTrace_add
  map_smul' := catTrace_smul

end RS
