/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModTensor

/-!
# The dual of a module object

Substrate for Deligne (2002), §2.8: over a monoidal category `D`, an
exact pairing `(X, Y)` transports a module structure on `X` (for a
monoid object `A`) to its dual `Y`.

* `actCoev`: the coevaluation twisted by the action, `A ⟶ X ⊗ Y`,
  with unit and multiplication laws `one_actCoev`/`mul_actCoev`.
* `dualActRight`: the contragredient right action `Y ⊗ A ⟶ Y`, the
  mate of the action under the pairing; right-module laws are
  `dualActRight_one` and `dualActRight_dualActRight`.  No braiding
  is needed at this stage.
* `dualActRight_evaluation`/`coevaluation_dualActRight`: the mate
  calculus carrying the dual action across the evaluation and the
  coevaluation of the pairing.
* `dualActLeft`: in a braided category, `(β_ Y A).inv ≫
  dualActRight`; for a commutative monoid this is a left module
  structure, bundled as `dualModObj`/`dualMod`.  The inverse
  braiding is chosen so that the braided right action `actRight`
  derived on the dual is exactly `dualActRight`
  (`actRight_dualMod`), which makes the pairing descend through the
  module-tensor coequalizer on the nose.
* `modPairing : modTensor A (dualMod A X Y) (asMod A X) ⟶ A`, the
  descent of `ε_ X Y ≫ η[A]`.  It is balanced but is not a
  morphism of `A`-modules for a general module; the equivariance
  that does hold is `whiskerLeft_modTensorπ_act_modPairing`.
* `modCopairing : A ⟶ modTensor A (asMod A X) (dualMod A X Y)`,
  the twisted coevaluation followed by the projection.  It is a
  morphism of modules (`mul_modCopairing`), bundled as
  `modCopairingHom`.

Zigzag identities at the `modTensor` level, and nonvanishing of the
copairing, need the multi-tensor coherence layer and are outside
this module's scope.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

section ActCoev

/-- The coevaluation twisted by the action: informally
`a ↦ (a • xᵢ) ⊗ yᵢ` in dual-basis notation. -/
def actCoev
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : D) (Y : D)
    [ExactPairing X Y] [ModObj A X] : A ⟶ X ⊗ Y :=
  (ρ_ A).inv ≫ A ◁ η_ X Y ≫ (α_ A X Y).inv ≫ actLeft A X ▷ Y

/-- The twisted coevaluation, unfolded. -/
lemma actCoev_def
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : D) (Y : D)
    [ExactPairing X Y] [ModObj A X] :
    actCoev A X Y =
      (ρ_ A).inv ≫ A ◁ η_ X Y ≫ (α_ A X Y).inv ≫
        actLeft A X ▷ Y :=
  rfl

/-- Uncurrying the twisted coevaluation recovers the action. -/
@[reassoc]
lemma actCoev_uncurry
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : D) (Y : D)
    [ExactPairing X Y] [ModObj A X] :
    actCoev A X Y ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ε_ X Y ≫
      (ρ_ X).hom = actLeft A X :=
  (tensorRightHomEquiv A X Y X).symm_apply_apply (actLeft A X)

/-- Unit law of the twisted coevaluation. -/
@[reassoc]
lemma one_actCoev
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : D) (Y : D)
    [ExactPairing X Y] [ModObj A X] : η[A] ≫ actCoev A X Y = η_ X Y := by
  rw [actCoev_def, rightUnitor_inv_naturality_assoc,
    ← whisker_exchange_assoc, associator_inv_naturality_left_assoc,
    ← comp_whiskerRight, one_actLeft]
  monoidal

/-- Multiplication law of the twisted coevaluation. -/
@[reassoc]
lemma mul_actCoev
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : D) (Y : D)
    [ExactPairing X Y] [ModObj A X] :
    μ[A] ≫ actCoev A X Y =
      A ◁ actCoev A X Y ≫ (α_ A X Y).inv ≫ actLeft A X ▷ Y := by
  rw [actCoev_def, rightUnitor_inv_naturality_assoc,
    ← whisker_exchange_assoc, associator_inv_naturality_left_assoc,
    ← comp_whiskerRight, mul_actLeft]
  monoidal

/-- The contragredient right action on the dual: informally
`f ⊗ a ↦ f (a • ·)`, that is, `f ⊗ a ↦ f (a • xᵢ) yᵢ` in dual-basis
notation. -/
def dualActRight
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : D) (Y : D)
    [ExactPairing X Y] [ModObj A X] : Y ⊗ A ⟶ Y :=
  Y ◁ actCoev A X Y ≫ (α_ Y X Y).inv ≫ ε_ X Y ▷ Y ≫ (λ_ Y).hom

/-- The contragredient right action, unfolded. -/
lemma dualActRight_def
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : D) (Y : D)
    [ExactPairing X Y] [ModObj A X] :
    dualActRight A X Y =
      Y ◁ actCoev A X Y ≫ (α_ Y X Y).inv ≫ ε_ X Y ▷ Y ≫
        (λ_ Y).hom :=
  rfl

/-- Evaluation compatibility: the contragredient action against the
evaluation is the original action across the pairing.  This is the
workhorse identity of the mate calculus. -/
@[reassoc]
lemma dualActRight_evaluation
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : D) (Y : D)
    [ExactPairing X Y] [ModObj A X] :
    dualActRight A X Y ▷ X ≫ ε_ X Y =
      (α_ Y A X).hom ≫ Y ◁ actLeft A X ≫ ε_ X Y := by
  calc dualActRight A X Y ▷ X ≫ ε_ X Y
      _ = 𝟙 _ ⊗≫ (Y ◁ actCoev A X Y) ▷ X ⊗≫
            (ε_ X Y ▷ (Y ⊗ X) ≫ 𝟙_ D ◁ ε_ X Y) ⊗≫ 𝟙 _ := by
          rw [dualActRight_def]; monoidal
      _ = 𝟙 _ ⊗≫ (Y ◁ actCoev A X Y) ▷ X ⊗≫
            ((Y ⊗ X) ◁ ε_ X Y ≫ ε_ X Y ▷ 𝟙_ D) ⊗≫ 𝟙 _ := by
          rw [← whisker_exchange]
      _ = (α_ Y A X).hom ≫ Y ◁ (actCoev A X Y ▷ X ≫
            (α_ X Y X).hom ≫ X ◁ ε_ X Y ≫ (ρ_ X).hom) ≫
            ε_ X Y := by
          monoidal
      _ = (α_ Y A X).hom ≫ Y ◁ actLeft A X ≫ ε_ X Y := by
          rw [actCoev_uncurry]

/-- Coevaluation compatibility, the mirror of
`dualActRight_evaluation`: inserting the coevaluation and applying
the contragredient action is the twisted coevaluation. -/
@[reassoc]
lemma coevaluation_dualActRight
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : D) (Y : D)
    [ExactPairing X Y] [ModObj A X] :
    η_ X Y ▷ A ≫ (α_ X Y A).hom ≫ X ◁ dualActRight A X Y =
      (λ_ A).hom ≫ actCoev A X Y := by
  have h : (λ_ A).inv ≫ η_ X Y ▷ A ≫ (α_ X Y A).hom ≫
      X ◁ dualActRight A X Y = actCoev A X Y :=
    (tensorLeftHomEquiv A X Y Y).apply_symm_apply (actCoev A X Y)
  rw [← h, Iso.hom_inv_id_assoc]

/-- Unitality of the contragredient right action. -/
@[reassoc]
lemma dualActRight_one
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : D) (Y : D)
    [ExactPairing X Y] [ModObj A X] :
    Y ◁ η[A] ≫ dualActRight A X Y = (ρ_ Y).hom := by
  rw [dualActRight_def, ← MonoidalCategory.whiskerLeft_comp_assoc,
    one_actCoev]
  simp

/-- Associativity of the contragredient right action. -/
@[reassoc]
lemma dualActRight_dualActRight
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : D) (Y : D)
    [ExactPairing X Y] [ModObj A X] :
    dualActRight A X Y ▷ A ≫ dualActRight A X Y =
      (α_ Y A A).hom ≫ Y ◁ μ[A] ≫ dualActRight A X Y := by
  calc dualActRight A X Y ▷ A ≫ dualActRight A X Y
      _ = dualActRight A X Y ▷ A ≫ Y ◁ actCoev A X Y ≫
            (α_ Y X Y).inv ≫ ε_ X Y ▷ Y ≫ (λ_ Y).hom := by
          rw [← dualActRight_def]
      _ = (Y ⊗ A) ◁ actCoev A X Y ≫
            dualActRight A X Y ▷ (X ⊗ Y) ≫
            (α_ Y X Y).inv ≫ ε_ X Y ▷ Y ≫ (λ_ Y).hom := by
          rw [← whisker_exchange_assoc]
      _ = (Y ⊗ A) ◁ actCoev A X Y ≫ (α_ (Y ⊗ A) X Y).inv ≫
            (dualActRight A X Y ▷ X ≫ ε_ X Y) ▷ Y ≫
            (λ_ Y).hom := by
          rw [associator_inv_naturality_left_assoc,
            ← comp_whiskerRight_assoc]
      _ = (Y ⊗ A) ◁ actCoev A X Y ≫ (α_ (Y ⊗ A) X Y).inv ≫
            ((α_ Y A X).hom ≫ Y ◁ actLeft A X ≫ ε_ X Y) ▷ Y ≫
            (λ_ Y).hom := by
          rw [dualActRight_evaluation]
      _ = (α_ Y A A).hom ≫ Y ◁ (μ[A] ≫ actCoev A X Y) ≫
            (α_ Y X Y).inv ≫ ε_ X Y ▷ Y ≫ (λ_ Y).hom := by
          rw [mul_actCoev]; monoidal
      _ = (α_ Y A A).hom ≫ Y ◁ μ[A] ≫ dualActRight A X Y := by
          rw [MonoidalCategory.whiskerLeft_comp_assoc,
            ← dualActRight_def]

end ActCoev

section DualModule

/-- The dual left action: the contragredient right action pulled
back along the inverse braiding.  The inverse braiding (rather than
the braiding `β_ A Y`) is chosen so that the braided right action
`actRight` derived from it is exactly `dualActRight`; see
`actRight_dualMod`. -/
def dualActLeft [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (X : D) (Y : D) [ExactPairing X Y] [ModObj A X] :
    A ⊗ Y ⟶ Y :=
  (β_ Y A).inv ≫ dualActRight A X Y

/-- The dual left action, unfolded. -/
lemma dualActLeft_def [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (X : D) (Y : D) [ExactPairing X Y] [ModObj A X] :
    dualActLeft A X Y = (β_ Y A).inv ≫ dualActRight A X Y :=
  rfl

/-- Unitality of the dual left action. -/
@[reassoc]
lemma one_dualActLeft [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (X : D) (Y : D) [ExactPairing X Y] [ModObj A X] :
    η[A] ▷ Y ≫ dualActLeft A X Y = (λ_ Y).hom := by
  rw [dualActLeft_def, BraidedCategory.braiding_inv_naturality_left_assoc,
    dualActRight_one, braiding_inv_tensorUnit_right]
  simp

/-- Evaluation compatibility for the dual left action. -/
@[reassoc]
lemma dualActLeft_evaluation
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (X : D) (Y : D) [ExactPairing X Y] [ModObj A X] :
    dualActLeft A X Y ▷ X ≫ ε_ X Y =
      (β_ Y A).inv ▷ X ≫ (α_ Y A X).hom ≫ Y ◁ actLeft A X ≫
        ε_ X Y := by
  rw [dualActLeft_def, comp_whiskerRight, Category.assoc,
    dualActRight_evaluation]

/-- Associativity of the dual left action, for a commutative
monoid. -/
@[reassoc]
lemma mul_dualActLeft [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (X : D) (Y : D) [ExactPairing X Y] [ModObj A X]
    [IsCommMonObj A] :
    μ[A] ▷ Y ≫ dualActLeft A X Y =
      (α_ A A Y).hom ≫ A ◁ dualActLeft A X Y ≫
        dualActLeft A X Y := by
  rw [dualActLeft_def, BraidedCategory.braiding_inv_naturality_left_assoc,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    BraidedCategory.braiding_inv_naturality_right_assoc,
    dualActRight_dualActRight, BraidedCategory.braiding_tensor_right_inv,
    BraidedCategory.braiding_tensor_left_inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc,
    IsCommMonObj.mul_comm' A]

/-- The dual module structure on `Y`, for a commutative monoid. -/
@[implicit_reducible]
def dualModObj [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (X : D) (Y : D) [ExactPairing X Y] [ModObj A X]
    [IsCommMonObj A] : ModObj A Y where
  smul := dualActLeft A X Y
  one_smul := one_dualActLeft A X Y
  mul_smul := mul_dualActLeft A X Y

/-- The dual of a module, bundled: `Y` with the transported
action. -/
@[reducible]
def dualMod [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (X : D) (Y : D) [ExactPairing X Y] [ModObj A X]
    [IsCommMonObj A] : Mod D A :=
  letI := dualModObj A X Y
  ⟨Y⟩

/-- On the dual module the action is the dual left action. -/
lemma actLeft_dualMod [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (X : D) (Y : D) [ExactPairing X Y] [ModObj A X]
    [IsCommMonObj A] :
    haveI := dualModObj A X Y
    actLeft A Y = dualActLeft A X Y := rfl

/-- On the dual module the braided right action is exactly the
contragredient right action. -/
lemma actRight_dualMod [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (X : D) (Y : D) [ExactPairing X Y] [ModObj A X]
    [IsCommMonObj A] :
    haveI := dualModObj A X Y
    actRight A Y = dualActRight A X Y := by
  change (β_ Y A).hom ≫ dualActLeft A X Y = dualActRight A X Y
  rw [dualActLeft_def, Iso.hom_inv_id_assoc]

end DualModule

section AsMod

/-- A module object, bundled as a module. -/
@[reducible]
def asMod [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : D)
    [ModObj A X] : Mod D A := ⟨X⟩

end AsMod

section ModDualPairing

/-- The two coequalizer legs agree against the paired evaluation:
this is exactly `dualActRight_evaluation`, thanks to the inverse
braiding convention of `dualActLeft`. -/
lemma modTensorLeg_pair [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] (X : D) (Y : D) [ExactPairing X Y]
    [ModObj A X] :
    modTensorLegM A (dualMod A X Y) (asMod A X) ≫
        (ε_ X Y ≫ η[A]) =
      modTensorLegN A (dualMod A X Y) (asMod A X) ≫
        (ε_ X Y ≫ η[A]) := by
  let := dualModObj A X Y
  change actRight A Y ▷ X ≫ (ε_ X Y ≫ η[A]) =
    ((α_ Y A X).hom ≫ Y ◁ actLeft A X) ≫ (ε_ X Y ≫ η[A])
  rw [actRight_dualMod, dualActRight_evaluation_assoc,
    Category.assoc]

/-- The `A`-valued pairing on the module tensor of the dual with
the module: the descent of `ε_ X Y ≫ η[A]` through the coequalizer.
It is balanced but, for a general module, not a morphism of
`A`-modules; see `whiskerLeft_modTensorπ_act_modPairing` for the
equivariance it does satisfy. -/
noncomputable def modPairing
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] (X : D) (Y : D) [ExactPairing X Y]
    [ModObj A X] [HasCoequalizers D] :
    modTensor A (dualMod A X Y) (asMod A X) ⟶ A :=
  modTensorDesc A (dualMod A X Y) (asMod A X) (ε_ X Y ≫ η[A])
    (modTensorLeg_pair A X Y)

/-- Defining equation of the pairing. -/
@[reassoc (attr := simp)]
lemma modTensorπ_modPairing
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] (X : D) (Y : D) [ExactPairing X Y]
    [ModObj A X] [HasCoequalizers D] :
    modTensorπ A (dualMod A X Y) (asMod A X) ≫ modPairing A X Y =
      ε_ X Y ≫ η[A] :=
  modTensorπ_desc A _ _ _ _

/-- The copairing into the module tensor of the module with its
dual: the twisted coevaluation followed by the projection. -/
noncomputable def modCopairing
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] (X : D) (Y : D) [ExactPairing X Y]
    [ModObj A X] [HasCoequalizers D] :
    A ⟶ modTensor A (asMod A X) (dualMod A X Y) :=
  actCoev A X Y ≫ modTensorπ A (asMod A X) (dualMod A X Y)

/-- The copairing carries the unit to the projected coevaluation. -/
@[reassoc]
lemma one_modCopairing [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] (X : D) (Y : D) [ExactPairing X Y]
    [ModObj A X] [HasCoequalizers D] :
    η[A] ≫ modCopairing A X Y =
      η_ X Y ≫ modTensorπ A (asMod A X) (dualMod A X Y) := by
  rw [modCopairing, one_actCoev_assoc]

/-- Equivariance of the pairing: acting on the tensor product and
pairing equals braiding the scalar through and pairing against the
acted-on module.  For a general module this is the strongest
compatibility available; the pairing is not `A`-linear. -/
@[reassoc]
lemma whiskerLeft_modTensorπ_act_modPairing
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] (X : D) (Y : D) [ExactPairing X Y]
    [ModObj A X] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)] :
    A ◁ modTensorπ A (dualMod A X Y) (asMod A X) ≫
        modTensorAct A (dualMod A X Y) (asMod A X) ≫
        modPairing A X Y =
      (α_ A Y X).inv ≫ (β_ Y A).inv ▷ X ≫ (α_ Y A X).hom ≫
        Y ◁ actLeft A X ≫ ε_ X Y ≫ η[A] := by
  rw [whiskerLeft_modTensorπ_act_assoc, modTensorπ_modPairing]
  let := dualModObj A X Y
  change (α_ A Y X).inv ≫ actLeft A Y ▷ X ≫ ε_ X Y ≫ η[A] = _
  rw [actLeft_dualMod, dualActLeft_evaluation_assoc]

/-- The copairing is a morphism of modules. -/
@[reassoc]
lemma mul_modCopairing [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] (X : D) (Y : D) [ExactPairing X Y]
    [ModObj A X] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)] :
    μ[A] ≫ modCopairing A X Y =
      A ◁ modCopairing A X Y ≫
        modTensorAct A (asMod A X) (dualMod A X Y) := by
  rw [modCopairing, MonoidalCategory.whiskerLeft_comp,
    Category.assoc, whiskerLeft_modTensorπ_act,
    mul_actCoev_assoc]
  simp only [Category.assoc]

/-- The copairing, bundled as a morphism of modules out of the
regular module. -/
noncomputable def modCopairingHom
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] (X : D) (Y : D) [ExactPairing X Y]
    [ModObj A X] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)] :
    regularMod A ⟶ modTensorMod A (asMod A X) (dualMod A X Y) :=
  Mod.Hom.mk' (modCopairing A X Y) (mul_modCopairing A X Y)

end ModDualPairing

section RightDual

/-- The dual left action, specialised to the right dual `Xᘁ`. -/
def rightDualActLeft [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (X : D) [HasRightDual X] [ModObj A X] :
    A ⊗ Xᘁ ⟶ Xᘁ := dualActLeft A X (Xᘁ)

/-- Unitality of the dual left action at the right dual. -/
@[reassoc]
lemma one_rightDualActLeft
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (X : D) [HasRightDual X] [ModObj A X] :
    η[A] ▷ (Xᘁ) ≫ rightDualActLeft A X = (λ_ (Xᘁ)).hom :=
  one_dualActLeft A X (Xᘁ)

/-- Associativity of the dual left action at the right dual. -/
@[reassoc]
lemma mul_rightDualActLeft
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (X : D) [HasRightDual X] [ModObj A X]
    [IsCommMonObj A] :
    μ[A] ▷ (Xᘁ) ≫ rightDualActLeft A X =
      (α_ A A (Xᘁ)).hom ≫ A ◁ rightDualActLeft A X ≫
        rightDualActLeft A X :=
  mul_dualActLeft A X (Xᘁ)

/-- The dual module, specialised to the right dual `Xᘁ`. -/
@[reducible]
def rightDualMod [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (X : D) [HasRightDual X] [ModObj A X]
    [IsCommMonObj A] : Mod D A := dualMod A X (Xᘁ)

end RightDual

end RS
