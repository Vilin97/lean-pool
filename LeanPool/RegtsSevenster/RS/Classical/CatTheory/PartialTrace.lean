/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.CatTheory.Trace

/-!
# The partial categorical trace

Tracing out the last tensor factor: for `f : P ⊗ X ⟶ P ⊗ X` the
partial trace `ptr f : P ⟶ P` closes the `X` strand into a loop and
leaves the `P` strand open.

The calculus: the partial trace absorbs factors acting on `P` alone
from either side, it commutes with whiskering by a further factor on
the left, the partial trace of the braiding of the last two factors
is the identity, and the full trace of a partial trace is the full
trace.  Those are what the cycle-trace factorisation of a
permutation action needs.
-/

@[expose] public section

namespace RS

open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory

universe v u

variable {C : Type u}

/-- **The partial trace** of an endomorphism of `P ⊗ X` over its
last factor: coevaluate an `X` strand beside `P`, let the
endomorphism act, cross the strand over its dual and evaluate. -/
def ptr [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [RigidCategory C]
    {P X : C} (f : P ⊗ X ⟶ P ⊗ X) : P ⟶ P :=
  (ρ_ P).inv ≫ (P ◁ η_ X Xᘁ) ≫ (α_ P X Xᘁ).inv ≫ (f ▷ Xᘁ) ≫
    (α_ P X Xᘁ).hom ≫ (P ◁ ((β_ X Xᘁ).hom ≫ ε_ X Xᘁ)) ≫ (ρ_ P).hom

/-- Whiskering by `P` on the cup side is whiskering on the `P`
strand. -/
@[reassoc]
private theorem coev_whiskerRight
    [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
    (P X : C) (a : P ⟶ P) :
    (P ◁ η_ X Xᘁ) ≫ (α_ P X Xᘁ).inv ≫ ((a ▷ X) ▷ Xᘁ) =
      (a ▷ 𝟙_ C) ≫ (P ◁ η_ X Xᘁ) ≫ (α_ P X Xᘁ).inv := by
  rw [← associator_inv_naturality_left, ← Category.assoc,
    whisker_exchange, Category.assoc]

/-- Whiskering by `P` on the cap side is whiskering on the `P`
strand. -/
@[reassoc]
private theorem whiskerRight_ev
    [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [RigidCategory C]
    (P X : C) (a : P ⟶ P) :
    ((a ▷ X) ▷ Xᘁ) ≫ (α_ P X Xᘁ).hom ≫
        (P ◁ ((β_ X Xᘁ).hom ≫ ε_ X Xᘁ)) =
      ((α_ P X Xᘁ).hom ≫ (P ◁ ((β_ X Xᘁ).hom ≫ ε_ X Xᘁ))) ≫
        (a ▷ 𝟙_ C) := by
  rw [← Category.assoc, associator_naturality_left, Category.assoc,
    ← whisker_exchange, Category.assoc]

/-- The partial trace absorbs a factor acting on `P` alone from the
left. -/
theorem ptr_whiskerRight_comp
    [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [RigidCategory C]
    {P X : C} (a : P ⟶ P)
    (f : P ⊗ X ⟶ P ⊗ X) : ptr ((a ▷ X) ≫ f) = a ≫ ptr f := by
  change (ρ_ P).inv ≫ (P ◁ η_ X Xᘁ) ≫ (α_ P X Xᘁ).inv ≫
      (((a ▷ X) ≫ f) ▷ Xᘁ) ≫ (α_ P X Xᘁ).hom ≫
      (P ◁ ((β_ X Xᘁ).hom ≫ ε_ X Xᘁ)) ≫ (ρ_ P).hom =
    a ≫ (ρ_ P).inv ≫ (P ◁ η_ X Xᘁ) ≫ (α_ P X Xᘁ).inv ≫
      (f ▷ Xᘁ) ≫ (α_ P X Xᘁ).hom ≫
      (P ◁ ((β_ X Xᘁ).hom ≫ ε_ X Xᘁ)) ≫ (ρ_ P).hom
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  rw [coev_whiskerRight_assoc, ← Category.assoc ((ρ_ P).inv),
    ← rightUnitor_inv_naturality]
  simp only [Category.assoc]

/-- The partial trace absorbs a factor acting on `P` alone from the
right. -/
theorem ptr_comp_whiskerRight
    [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [RigidCategory C]
    {P X : C} (a : P ⟶ P)
    (f : P ⊗ X ⟶ P ⊗ X) : ptr (f ≫ (a ▷ X)) = ptr f ≫ a := by
  change (ρ_ P).inv ≫ (P ◁ η_ X Xᘁ) ≫ (α_ P X Xᘁ).inv ≫
      ((f ≫ (a ▷ X)) ▷ Xᘁ) ≫ (α_ P X Xᘁ).hom ≫
      (P ◁ ((β_ X Xᘁ).hom ≫ ε_ X Xᘁ)) ≫ (ρ_ P).hom =
    ((ρ_ P).inv ≫ (P ◁ η_ X Xᘁ) ≫ (α_ P X Xᘁ).inv ≫
      (f ▷ Xᘁ) ≫ (α_ P X Xᘁ).hom ≫
      (P ◁ ((β_ X Xᘁ).hom ≫ ε_ X Xᘁ)) ≫ (ρ_ P).hom) ≫ a
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  rw [whiskerRight_ev_assoc, rightUnitor_naturality]

/-! ## Tracing inside a further factor

Partial trace over the last factor is unaffected by a factor
whiskered on the far left, so it may be computed inside the smaller
tensorand.  Combined with the calculus above this evaluates the
partial trace of the braiding of the last two factors.
-/

/-- **The partial trace passes a left factor.**  A morphism acting
on `R ⊗ X` inside `Q ⊗ (R ⊗ X)` has partial trace `Q ◁ ptr u`.  Both
sides carry the same coevaluation, morphism and evaluation in the
same order, so only the bracketing differs. -/
theorem ptr_whiskerLeft
    [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [RigidCategory C]
    (Q : C) {R X : C} (u : R ⊗ X ⟶ R ⊗ X) :
    ptr ((α_ Q R X).hom ≫ (Q ◁ u) ≫ (α_ Q R X).inv) =
      Q ◁ ptr u := by
  change (ρ_ (Q ⊗ R)).inv ≫ ((Q ⊗ R) ◁ η_ X Xᘁ) ≫
      (α_ (Q ⊗ R) X Xᘁ).inv ≫
      (((α_ Q R X).hom ≫ (Q ◁ u) ≫ (α_ Q R X).inv) ▷ Xᘁ) ≫
      (α_ (Q ⊗ R) X Xᘁ).hom ≫
      ((Q ⊗ R) ◁ ((β_ X Xᘁ).hom ≫ ε_ X Xᘁ)) ≫ (ρ_ (Q ⊗ R)).hom =
    Q ◁ ((ρ_ R).inv ≫ (R ◁ η_ X Xᘁ) ≫ (α_ R X Xᘁ).inv ≫
      (u ▷ Xᘁ) ≫ (α_ R X Xᘁ).hom ≫
      (R ◁ ((β_ X Xᘁ).hom ≫ ε_ X Xᘁ)) ≫ (ρ_ R).hom)
  simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc]
  monoidal

/-- **The partial trace of the braiding is the identity**: the
strand created by the coevaluation crosses the open strand and is
capped against it, and the resulting zig-zag is the snake identity
of the pairing. -/
theorem ptr_braiding [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [RigidCategory C]
    (X : C) : ptr (β_ X X).hom = 𝟙 X := by
  change (ρ_ X).inv ≫ (X ◁ η_ X Xᘁ) ≫ (α_ X X Xᘁ).inv ≫
      ((β_ X X).hom ▷ Xᘁ) ≫ (α_ X X Xᘁ).hom ≫
      (X ◁ ((β_ X Xᘁ).hom ≫ ε_ X Xᘁ)) ≫ (ρ_ X).hom = 𝟙 X
  -- Reassemble the two crossings into the braiding past `X ⊗ Xᘁ`.
  have hbraid : (α_ X X Xᘁ).inv ≫ ((β_ X X).hom ▷ Xᘁ) ≫
      (α_ X X Xᘁ).hom ≫ (X ◁ (β_ X Xᘁ).hom) =
      (β_ X (X ⊗ Xᘁ)).hom ≫ (α_ X Xᘁ X).hom := by
    rw [braiding_tensor_right_hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [whiskerLeft_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hbraid]
  -- Slide the coevaluation through the braiding and close the snake.
  rw [← Category.assoc (X ◁ η_ X Xᘁ), braiding_naturality_right]
  simp only [Category.assoc]
  rw [reassoc_of% (ExactPairing.evaluation_coevaluation X Xᘁ),
    Iso.inv_hom_id, Category.comp_id, braiding_leftUnitor,
    Iso.inv_hom_id]

/-- **The partial trace of a braided last factor**: braiding the
last two factors and then acting by `g` on the last traces to `g`
acting on the factor that remains. -/
theorem ptr_braiding_whiskerLeft
    [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [RigidCategory C]
    (Q X : C) (g : X ⟶ X) :
    ptr (((α_ Q X X).hom ≫ (Q ◁ (β_ X X).hom) ≫ (α_ Q X X).inv) ≫
      ((Q ⊗ X) ◁ g)) = Q ◁ g := by
  have hg : (Q ⊗ X) ◁ g =
      (α_ Q X X).hom ≫ (Q ◁ (X ◁ g)) ≫ (α_ Q X X).inv := by
    rw [← Category.assoc, ← associator_naturality_right,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hsplit : ((α_ Q X X).hom ≫ (Q ◁ (β_ X X).hom) ≫
      (α_ Q X X).inv) ≫ ((Q ⊗ X) ◁ g) =
      (α_ Q X X).hom ≫ (Q ◁ ((β_ X X).hom ≫ (X ◁ g))) ≫
        (α_ Q X X).inv := by
    rw [hg, whiskerLeft_comp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hsplit, ptr_whiskerLeft, ← braiding_naturality_left,
    ptr_whiskerRight_comp, ptr_braiding, Category.comp_id]

/-! ## The full trace of a partial trace

Closing the remaining `P` strand of `ptr f` into a loop closes both
strands of `f`.  The comparison passes through the partial trace
over the *first* factor: against the tensor pairing the two loops of
the full trace disentangle with the `P` loop innermost, and an
exchange of disjoint cups and caps re-nests the loop closure of
`ptr f` into exactly that shape.
-/

/-- The partial trace over the first factor: coevaluate a `P` strand
kinked across its dual on the left, let the endomorphism act, and
evaluate.  This is the shape in which the tensor pairing presents
the inner loop of the full trace on `P ⊗ X`. -/
private def ptl [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [RigidCategory C]
    {P X : C} (f : P ⊗ X ⟶ P ⊗ X) : X ⟶ X :=
  (λ_ X).inv ≫ ((η_ P Pᘁ ≫ (β_ P Pᘁ).hom) ▷ X) ≫ (α_ Pᘁ P X).hom ≫
    (Pᘁ ◁ f) ≫ (α_ Pᘁ P X).inv ≫ (ε_ P Pᘁ ▷ X) ≫ (λ_ X).hom

/-- The full trace is the full trace of the first-factor partial
trace: computed against the tensor pairing, the two loops of the
trace of `f` disentangle into an outer `X` loop around an inner `P`
loop, and the inner loop closed around `f` is exactly `ptl f`. -/
private theorem catTrace_eq_ptl_trace
    [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [RigidCategory C]
    {P X : C}
    (f : P ⊗ X ⟶ P ⊗ X) : catTrace f = catTrace (ptl f) := by
  rw [catTrace_eq_pairTrace f,
    pairTrace_eq
      (ExactPairing.tensor : ExactPairing (P ⊗ X) (Xᘁ ⊗ Pᘁ))
      HasRightDual.exact f]
  change η_ (P ⊗ X) (Xᘁ ⊗ Pᘁ) ≫ f ▷ (Xᘁ ⊗ Pᘁ) ≫
      (β_ (P ⊗ X) (Xᘁ ⊗ Pᘁ)).hom ≫ ε_ (P ⊗ X) (Xᘁ ⊗ Pᘁ) =
    catTrace (ptl f)
  calc
    η_ (P ⊗ X) (Xᘁ ⊗ Pᘁ) ≫ f ▷ (Xᘁ ⊗ Pᘁ) ≫
        (β_ (P ⊗ X) (Xᘁ ⊗ Pᘁ)).hom ≫ ε_ (P ⊗ X) (Xᘁ ⊗ Pᘁ)
      -- Take the braiding first and let `f` act afterwards.
      = η_ (P ⊗ X) (Xᘁ ⊗ Pᘁ) ≫ (β_ (P ⊗ X) (Xᘁ ⊗ Pᘁ)).hom ≫
          (Xᘁ ⊗ Pᘁ) ◁ f ≫ ε_ (P ⊗ X) (Xᘁ ⊗ Pᘁ) := by
        rw [braiding_naturality_left_assoc]
      -- Expose the components of the tensor pairing.
    _ = ((η_ P Pᘁ ⊗≫ (P ◁ η_ X Xᘁ) ▷ Pᘁ ⊗≫
          𝟙 ((P ⊗ X) ⊗ Xᘁ ⊗ Pᘁ)) ≫ (β_ (P ⊗ X) (Xᘁ ⊗ Pᘁ)).hom) ≫
          (Xᘁ ⊗ Pᘁ) ◁ f ≫
          (𝟙 ((Xᘁ ⊗ Pᘁ) ⊗ P ⊗ X) ⊗≫ Xᘁ ◁ (ε_ P Pᘁ ▷ X) ⊗≫
            ε_ X Xᘁ) := by
        rw [ExactPairing.tensor_coevaluation,
          ExactPairing.tensor_evaluation]
        simp only [Category.assoc]
      -- Disentangle the two loops.
    _ = ((η_ X Xᘁ ≫ (β_ X Xᘁ).hom) ⊗≫
          Xᘁ ◁ ((η_ P Pᘁ ≫ (β_ P Pᘁ).hom) ▷ X) ⊗≫
          𝟙 ((Xᘁ ⊗ Pᘁ) ⊗ P ⊗ X)) ≫
          (Xᘁ ⊗ Pᘁ) ◁ f ≫
          (𝟙 ((Xᘁ ⊗ Pᘁ) ⊗ P ⊗ X) ⊗≫ Xᘁ ◁ (ε_ P Pᘁ ▷ X) ⊗≫
            ε_ X Xᘁ) := by
        rw [nested_cups]
      -- The inner `P` loop closes around `f`: it is `ptl f`.
    _ = η_ X Xᘁ ≫ (β_ X Xᘁ).hom ≫ Xᘁ ◁ ptl f ≫ ε_ X Xᘁ := by
        simp only [ptl, whiskerLeft_comp, Category.assoc]
        monoidal
    _ = catTrace (ptl f) := (catTrace_eq_loop (ptl f)).symm

/-- The full trace of the last-factor partial trace is the full
trace of the first-factor partial trace: the two cups are disjoint,
as are the two caps, so exchanging each pair re-nests the loop
closure of `ptr f` as the outer `X` loop around the `P` loop. -/
private theorem ptr_trace_eq_ptl_trace
    [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [RigidCategory C]
    {P X : C}
    (f : P ⊗ X ⟶ P ⊗ X) :
    catTrace (ptr f) = catTrace (ptl f) := by
  rw [catTrace_eq_loop (ptr f)]
  calc
    η_ P Pᘁ ≫ (β_ P Pᘁ).hom ≫ Pᘁ ◁ ptr f ≫ ε_ P Pᘁ
      -- Unfold the partial trace; group cup with cup, cap with cap.
      = 𝟙 (𝟙_ C) ⊗≫
          ((η_ P Pᘁ ≫ (β_ P Pᘁ).hom) ▷ 𝟙_ C ≫
            (Pᘁ ⊗ P) ◁ η_ X Xᘁ) ⊗≫
          Pᘁ ◁ (f ▷ Xᘁ) ⊗≫
          ((Pᘁ ⊗ P) ◁ ((β_ X Xᘁ).hom ≫ ε_ X Xᘁ) ≫
            ε_ P Pᘁ ▷ 𝟙_ C) ⊗≫
          𝟙 (𝟙_ C) := by
        simp only [ptr, whiskerLeft_comp, Category.assoc]
        monoidal
      -- The cups are disjoint, and so are the caps: exchange both.
    _ = 𝟙 (𝟙_ C) ⊗≫
          (𝟙_ C ◁ η_ X Xᘁ ≫
            (η_ P Pᘁ ≫ (β_ P Pᘁ).hom) ▷ (X ⊗ Xᘁ)) ⊗≫
          Pᘁ ◁ (f ▷ Xᘁ) ⊗≫
          (ε_ P Pᘁ ▷ (X ⊗ Xᘁ) ≫
            𝟙_ C ◁ ((β_ X Xᘁ).hom ≫ ε_ X Xᘁ)) ⊗≫
          𝟙 (𝟙_ C) := by
        rw [← whisker_exchange
            (η_ P Pᘁ ≫ (β_ P Pᘁ).hom) (η_ X Xᘁ),
          whisker_exchange (ε_ P Pᘁ)
            ((β_ X Xᘁ).hom ≫ ε_ X Xᘁ)]
      -- The `P` loop closes around `f`: `ptl f` inside an `X` loop.
    _ = η_ X Xᘁ ≫ ptl f ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ := by
        simp only [ptl, comp_whiskerRight, Category.assoc]
        monoidal
    _ = catTrace (ptl f) := rfl

/-- **The full trace of a partial trace is the full trace**: closing
the remaining strand of `ptr f` into a loop closes both strands of
`f`. -/
theorem catTrace_ptr [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [RigidCategory C]
    {P X : C} (f : P ⊗ X ⟶ P ⊗ X) :
    catTrace (ptr f) = catTrace f :=
  (ptr_trace_eq_ptl_trace f).trans (catTrace_eq_ptl_trace f).symm

end RS
