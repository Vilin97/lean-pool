/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.BraidCoherence
import LeanPool.RegtsSevenster.RS.Classical.Deligne.TensorDatum

/-!
# Paired left actions and the joint action

The zag companion of the paired right action relation: acting on
both carriers on the left and projecting is multiplying the
scalars and acting on the projected pair.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- Pure braid coherence for the zag prefix: reassociating and
braiding the block `P ⊗ Q` past `P'`, then swapping `P'` back past
`P`, agrees with interchanging via `tensorμ` and reassociating.
The block braiding decomposes into the elementary crossings
`β_ Q P'` and `β_ P P'`; the latter cancels against the final
`β_ P' P` by the symmetry axiom, leaving exactly the single
crossing carried by `tensorμ`. -/
@[reassoc]
theorem zag_prefix_coherence
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (P Q P' R : D) :
    (α_ (P ⊗ Q) P' R).inv ≫
      ((β_ (P ⊗ Q) P').hom ▷ R) ≫
      ((α_ P' P Q).inv ▷ R) ≫
      (((β_ P' P).hom ▷ Q) ▷ R) =
      tensorμ P Q P' R ≫ (α_ (P ⊗ P') Q R).inv := by
  calc
    (α_ (P ⊗ Q) P' R).inv ≫
        ((β_ (P ⊗ Q) P').hom ▷ R) ≫
        ((α_ P' P Q).inv ▷ R) ≫
        (((β_ P' P).hom ▷ Q) ▷ R)
        = 𝟙 _ ⊗≫ ((P ◁ (β_ Q P').hom) ▷ R) ⊗≫
            ((((β_ P P').hom ≫ (β_ P' P).hom) ▷ Q) ▷ R) ⊗≫
            𝟙 _ := by
          rw [BraidedCategory.braiding_tensor_left_hom P Q P']
          monoidal
    _ = 𝟙 _ ⊗≫ ((P ◁ (β_ Q P').hom) ▷ R) ⊗≫ 𝟙 _ := by
          rw [SymmetricCategory.symmetry P P']
          monoidal
    _ = tensorμ P Q P' R ≫ (α_ (P ⊗ P') Q R).inv := by
          dsimp only [tensorμ]
          monoidal

/-- **Paired left actions descend to the joint action**: acting on
both carriers on the left and projecting is multiplying the
scalars and acting on the projected pair — the zag companion of
the paired right action relation of the relative tensor. -/
theorem tensorHom_actLeft_π
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A]
    (N₁ N₂ : Mod D A) :
    (actLeft A N₁.X ⊗ₘ actLeft A N₂.X) ≫ modTensorπ A N₁ N₂ =
      tensorμ A N₁.X A N₂.X ≫
        (μ[A] ▷ (N₁.X ⊗ N₂.X)) ≫
        (A ◁ modTensorπ A N₁ N₂) ≫
        modTensorAct A N₁ N₂ := by
  have hR : (A ◁ modTensorπ A N₁ N₂) ≫ modTensorAct A N₁ N₂ =
      ((α_ A N₁.X N₂.X).inv ≫ actLeft A N₁.X ▷ N₂.X) ≫
        modTensorπ A N₁ N₂ :=
    whiskerLeft_modTensorπ_act A N₁ N₂
  have hcond : (actRight A N₁.X ▷ N₂.X) ≫ modTensorπ A N₁ N₂ =
      (α_ N₁.X A N₂.X).hom ≫
        (N₁.X ◁ actLeft A N₂.X) ≫ modTensorπ A N₁ N₂ := by
    have h := modTensor_condition A N₁ N₂
    rw [modTensorLegM, modTensorLegN] at h
    simpa using h
  have hcond' : (N₁.X ◁ actLeft A N₂.X) ≫ modTensorπ A N₁ N₂ =
      (α_ N₁.X A N₂.X).inv ≫
        (actRight A N₁.X ▷ N₂.X) ≫ modTensorπ A N₁ N₂ := by
    rw [hcond, Iso.inv_hom_id_assoc]
  have hAA : actLeft A N₁.X ▷ A ≫ actRight A N₁.X =
      (β_ (A ⊗ N₁.X) A).hom ≫ (α_ A A N₁.X).inv ≫
        ((β_ A A).hom ▷ N₁.X) ≫ μ[A] ▷ N₁.X ≫
        actLeft A N₁.X := by
    conv_rhs => rw [← comp_whiskerRight_assoc,
      IsCommMonObj.mul_comm A]
    rw [(show actRight A N₁.X =
        (β_ N₁.X A).hom ≫ actLeft A N₁.X from rfl),
      ← Category.assoc,
      BraidedCategory.braiding_naturality_left,
      Category.assoc, actLeft_actLeft]
  have h3 : ((actLeft A N₁.X ▷ A ≫ actRight A N₁.X) ▷ N₂.X) ≫
      modTensorπ A N₁ N₂ =
      ((β_ (A ⊗ N₁.X) A).hom ▷ N₂.X) ≫
        ((α_ A A N₁.X).inv ▷ N₂.X) ≫
        (((β_ A A).hom ▷ N₁.X) ▷ N₂.X) ≫
        ((μ[A] ▷ N₁.X) ▷ N₂.X) ≫
        (actLeft A N₁.X ▷ N₂.X) ≫ modTensorπ A N₁ N₂ := by
    rw [hAA]
    simp only [comp_whiskerRight, Category.assoc]
  conv_lhs => rw [MonoidalCategory.tensorHom_def,
    Category.assoc, hcond',
    associator_inv_naturality_left_assoc,
    ← comp_whiskerRight_assoc, h3]
  conv_rhs => rw [hR]
  simp only [Category.assoc]
  conv_rhs => rw [associator_inv_naturality_left_assoc]
  rw [zag_prefix_coherence_assoc A N₁.X A N₂.X]

end RS
