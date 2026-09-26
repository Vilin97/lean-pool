/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainMulLaws

/-!
# Associativity of the tensor product of modules

The associator of the relative tensor of internal modules over a
commutative monoid.  Both directions are double descents: the outer
coequalizer is covered through the whiskered inner projection, the
associator of the ambient category reassociates the cover, and the
two balance conditions are pure slides through associator
naturality together with the coequalizer conditions of source and
target.

* `modTensorπ_actRight`: on the tensor product of modules the
  braided right action, precomposed with the projection, is the
  right action on the second factor.
* `modTensorAssocHom`/`modTensorAssocInv`: the two descents, with
  defining equations against the covers.
* `modTensorAssocIso`: the packaged isomorphism, inverted on the
  covers by cancelling the ambient associators.
* `modTensorAssocModIso`: the associator as an isomorphism of
  bundled modules; inverse linearity follows by cancelling the
  forward map.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- The braided right action on the tensor product of modules,
precomposed with the projection, is the right action on the second
factor. -/
@[reassoc]
theorem modTensorπ_actRight
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (N : Mod D A) :
    (modTensorπ A M N ▷ A) ≫ (β_ (modTensor A M N) A).hom ≫
        modTensorAct A M N =
      (α_ M.X N.X A).hom ≫ (M.X ◁ actRight A N.X) ≫
        modTensorπ A M N := by
  rw [BraidedCategory.braiding_naturality_left_assoc,
    whiskerLeft_modTensorπ_act,
    BraidedCategory.braiding_tensor_left_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← MonoidalCategory.comp_whiskerRight_assoc,
    show ((β_ M.X A).hom ≫ actLeft A M.X) ▷ N.X ≫
        modTensorπ A M N =
      modTensorLegM A M N ≫ modTensorπ A M N from rfl,
    modTensor_condition, modTensorLegN]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  rfl

/-- Companion form of `modTensorπ_actRight`: the right action on
the second factor descends to the braided right action on the
tensor product of modules. -/
@[reassoc]
theorem whiskerLeft_actRight_modTensorπ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (N : Mod D A) :
    (M.X ◁ actRight A N.X) ≫ modTensorπ A M N =
      (α_ M.X N.X A).inv ≫ (modTensorπ A M N ▷ A) ≫
        (β_ (modTensor A M N) A).hom ≫ modTensorAct A M N := by
  rw [modTensorπ_actRight, Iso.inv_hom_id_assoc]

/-- The coequalizer condition of the right-nested tensor product,
stated over the underlying objects. -/
theorem modTensor_condition_right
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    (actRight A M.X ▷ modTensor A N P) ≫
        modTensorπ A M (modTensorMod A N P) =
      (α_ M.X A (modTensor A N P)).hom ≫
        (M.X ◁ modTensorAct A N P) ≫
        modTensorπ A M (modTensorMod A N P) := by
  have h := modTensor_condition A M (modTensorMod A N P)
  rw [modTensorLegM, modTensorLegN, Category.assoc] at h
  exact h

/-- The coequalizer condition of the left-nested tensor product,
stated over the underlying objects. -/
theorem modTensor_condition_left
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    (((β_ (modTensor A M N) A).hom ≫ modTensorAct A M N) ▷ P.X) ≫
        modTensorπ A (modTensorMod A M N) P =
      (α_ (modTensor A M N) A P.X).hom ≫
        (modTensor A M N ◁ actLeft A P.X) ≫
        modTensorπ A (modTensorMod A M N) P := by
  have h := modTensor_condition A (modTensorMod A M N) P
  rw [modTensorLegM, modTensorLegN, Category.assoc] at h
  exact h

/-- The cover of the associator: reassociate and project through
both tensor products of the right-nested side. -/
noncomputable def modTensorAssocCover
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    (M.X ⊗ N.X) ⊗ P.X ⟶ modTensor A M (modTensorMod A N P) :=
  (α_ M.X N.X P.X).hom ≫ (M.X ◁ modTensorπ A N P) ≫
    modTensorπ A M (modTensorMod A N P)

/-- The cover of the associator coequalizes the whiskered inner
balance relation: the monoid sliding between `M` and `N` slides
onto `N` through the conditions of the target. -/
theorem modTensorAssocCover_cond
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    (modTensorLegM A M N ▷ P.X) ≫ modTensorAssocCover A M N P =
      (modTensorLegN A M N ▷ P.X) ≫ modTensorAssocCover A M N P := by
  rw [modTensorLegM, modTensorLegN, modTensorAssocCover]
  conv_lhs => erw [associator_naturality_left_assoc,
    ← whisker_exchange_assoc, modTensor_condition_right,
    associator_naturality_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_modTensorπ_act]
  conv_rhs => rw [MonoidalCategory.comp_whiskerRight,
    Category.assoc, associator_naturality_middle_assoc]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  repeat' erw [Category.assoc]
  erw [pentagon_hom_hom_inv_hom_hom_assoc]

/-- The half-descended associator, on the cover of the outer
coequalizer of the left-nested side. -/
noncomputable def modTensorAssocMid
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    modTensor A M N ⊗ P.X ⟶ modTensor A M (modTensorMod A N P) :=
  modTensorWhiskerRDesc A M N P.X (modTensorAssocCover A M N P)
    (modTensorAssocCover_cond A M N P)

/-- Defining equation of the half-descended associator. -/
@[reassoc (attr := simp)]
theorem whiskerRight_modTensorπ_assocMid
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    (modTensorπ A M N ▷ P.X) ≫ modTensorAssocMid A M N P =
      modTensorAssocCover A M N P :=
  whiskerRight_modTensorπ_whiskerRDesc A M N P.X _ _

/-- The half-descended associator coequalizes the outer balance
relation: the monoid sliding between the `(M, N)`-block and `P`
slides between `N` and `P` through the inner condition of the
target. -/
theorem modTensorAssocMid_cond
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    modTensorLegM A (modTensorMod A M N) P ≫
        modTensorAssocMid A M N P =
      modTensorLegN A (modTensorMod A M N) P ≫
        modTensorAssocMid A M N P := by
  have hNP : (actRight A N.X ▷ P.X) ≫ modTensorπ A N P =
      (α_ N.X A P.X).hom ≫ (N.X ◁ actLeft A P.X) ≫
        modTensorπ A N P := by
    have h := modTensor_condition A N P
    rw [modTensorLegM, modTensorLegN, Category.assoc] at h
    exact h
  refine (cancel_epi ((modTensorπ A M N ▷ A) ▷ P.X)).mp ?_
  change ((modTensorπ A M N ▷ A) ▷ P.X) ≫
      (((β_ (modTensor A M N) A).hom ≫ modTensorAct A M N)
        ▷ P.X) ≫
      modTensorAssocMid A M N P =
    ((modTensorπ A M N ▷ A) ▷ P.X) ≫
      ((α_ (modTensor A M N) A P.X).hom ≫
        (modTensor A M N ◁ actLeft A P.X)) ≫
      modTensorAssocMid A M N P
  conv_lhs => rw [← MonoidalCategory.comp_whiskerRight_assoc,
    modTensorπ_actRight]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  conv_lhs => erw [whiskerRight_modTensorπ_assocMid,
    modTensorAssocCover, associator_naturality_middle_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, hNP]
  conv_rhs => rw [associator_naturality_left_assoc,
    ← whisker_exchange_assoc, whiskerRight_modTensorπ_assocMid,
    modTensorAssocCover, associator_naturality_right_assoc]
  simp only [MonoidalCategory.whiskerLeft_comp]
  repeat' erw [Category.assoc]
  erw [pentagon_assoc]

/-- **The associator of the tensor product of modules**: the
descent of the ambient associator to the relative tensors. -/
noncomputable def modTensorAssocHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    modTensor A (modTensorMod A M N) P ⟶
      modTensor A M (modTensorMod A N P) :=
  modTensorDesc A (modTensorMod A M N) P
    (modTensorAssocMid A M N P) (modTensorAssocMid_cond A M N P)

/-- Defining equation of the associator. -/
@[reassoc (attr := simp)]
theorem modTensorπ_assocHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    modTensorπ A (modTensorMod A M N) P ≫
        modTensorAssocHom A M N P =
      modTensorAssocMid A M N P :=
  modTensorπ_desc A _ _ _ _

/-- The cover of the inverse associator: reassociate backwards and
project through both tensor products of the left-nested side. -/
noncomputable def modTensorAssocInvCover
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    M.X ⊗ (N.X ⊗ P.X) ⟶ modTensor A (modTensorMod A M N) P :=
  (α_ M.X N.X P.X).inv ≫ (modTensorπ A M N ▷ P.X) ≫
    modTensorπ A (modTensorMod A M N) P

/-- The inverse cover coequalizes the whiskered inner balance
relation: the monoid sliding between `N` and `P` slides onto the
`(M, N)`-block through the conditions of the target. -/
theorem modTensorAssocInvCover_cond
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    (M.X ◁ modTensorLegM A N P) ≫
        modTensorAssocInvCover A M N P =
      (M.X ◁ modTensorLegN A N P) ≫
        modTensorAssocInvCover A M N P := by
  rw [modTensorLegM, modTensorLegN, modTensorAssocInvCover]
  conv_lhs => erw [associator_inv_naturality_middle_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    whiskerLeft_actRight_modTensorπ,
    MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.comp_whiskerRight]
  repeat' erw [Category.assoc]
  conv_lhs => erw [modTensor_condition_left,
    associator_naturality_left_assoc, ← whisker_exchange_assoc]
  conv_rhs => rw [MonoidalCategory.whiskerLeft_comp,
    Category.assoc, associator_inv_naturality_right_assoc]
  rw [pentagon_inv_inv_hom_hom_inv_assoc]

/-- The half-descended inverse associator, on the cover of the
outer coequalizer of the right-nested side. -/
noncomputable def modTensorAssocInvMid
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    M.X ⊗ modTensor A N P ⟶ modTensor A (modTensorMod A M N) P :=
  modTensorWhiskerDesc A N P M.X (modTensorAssocInvCover A M N P)
    (modTensorAssocInvCover_cond A M N P)

/-- Defining equation of the half-descended inverse associator. -/
@[reassoc (attr := simp)]
theorem whiskerLeft_modTensorπ_assocInvMid
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    (M.X ◁ modTensorπ A N P) ≫ modTensorAssocInvMid A M N P =
      modTensorAssocInvCover A M N P :=
  whiskerLeft_modTensorπ_whiskerDesc A N P M.X _ _

/-- The half-descended inverse associator coequalizes the outer
balance relation: the monoid sliding between `M` and the
`(N, P)`-block slides between `M` and `N` through the inner
condition of the target. -/
theorem modTensorAssocInvMid_cond
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    modTensorLegM A M (modTensorMod A N P) ≫
        modTensorAssocInvMid A M N P =
      modTensorLegN A M (modTensorMod A N P) ≫
        modTensorAssocInvMid A M N P := by
  have hMN : (actRight A M.X ▷ N.X) ≫ modTensorπ A M N =
      (α_ M.X A N.X).hom ≫ (M.X ◁ actLeft A N.X) ≫
        modTensorπ A M N := by
    have h := modTensor_condition A M N
    rw [modTensorLegM, modTensorLegN, Category.assoc] at h
    exact h
  apply modTensor_whisker_hom_ext A N P (M.X ⊗ A)
  change ((M.X ⊗ A) ◁ modTensorπ A N P) ≫
      (actRight A M.X ▷ modTensor A N P) ≫
      modTensorAssocInvMid A M N P =
    ((M.X ⊗ A) ◁ modTensorπ A N P) ≫
      ((α_ M.X A (modTensor A N P)).hom ≫
        (M.X ◁ modTensorAct A N P)) ≫
      modTensorAssocInvMid A M N P
  conv_lhs => erw [whisker_exchange_assoc,
    whiskerLeft_modTensorπ_assocInvMid, modTensorAssocInvCover,
    associator_inv_naturality_left_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc, hMN]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  conv_rhs => rw [associator_naturality_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_modTensorπ_act]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  conv_rhs => rw [whiskerLeft_modTensorπ_assocInvMid,
    modTensorAssocInvCover,
    associator_inv_naturality_middle_assoc]
  repeat' erw [Category.assoc]
  erw [← pentagon_hom_inv_inv_inv_hom_assoc]

/-- **The inverse associator of the tensor product of modules.** -/
noncomputable def modTensorAssocInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    modTensor A M (modTensorMod A N P) ⟶
      modTensor A (modTensorMod A M N) P :=
  modTensorDesc A M (modTensorMod A N P)
    (modTensorAssocInvMid A M N P)
    (modTensorAssocInvMid_cond A M N P)

/-- Defining equation of the inverse associator. -/
@[reassoc (attr := simp)]
theorem modTensorπ_assocInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    modTensorπ A M (modTensorMod A N P) ≫
        modTensorAssocInv A M N P =
      modTensorAssocInvMid A M N P :=
  modTensorπ_desc A _ _ _ _

/-- The associator retracts the inverse associator. -/
@[reassoc (attr := simp)]
theorem modTensorAssocHom_assocInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    modTensorAssocHom A M N P ≫ modTensorAssocInv A M N P =
      𝟙 (modTensor A (modTensorMod A M N) P) := by
  apply modTensor_hom_ext A (modTensorMod A M N) P
  rw [modTensorπ_assocHom_assoc, Category.comp_id]
  apply modTensor_whiskerR_hom_ext A M N P.X
  change (modTensorπ A M N ▷ P.X) ≫ modTensorAssocMid A M N P ≫
      modTensorAssocInv A M N P =
    (modTensorπ A M N ▷ P.X) ≫
      modTensorπ A (modTensorMod A M N) P
  erw [whiskerRight_modTensorπ_assocMid_assoc, modTensorAssocCover]
  simp only [Category.assoc]
  conv_lhs => erw [Category.assoc]
  erw [modTensorπ_assocInv]
  erw [whiskerLeft_modTensorπ_assocInvMid,
    modTensorAssocInvCover, Iso.hom_inv_id_assoc]

/-- The inverse associator retracts the associator. -/
@[reassoc (attr := simp)]
theorem modTensorAssocInv_assocHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    modTensorAssocInv A M N P ≫ modTensorAssocHom A M N P =
      𝟙 (modTensor A M (modTensorMod A N P)) := by
  apply modTensor_hom_ext A M (modTensorMod A N P)
  rw [modTensorπ_assocInv_assoc, Category.comp_id]
  apply modTensor_whisker_hom_ext A N P M.X
  change (M.X ◁ modTensorπ A N P) ≫ modTensorAssocInvMid A M N P ≫
      modTensorAssocHom A M N P =
    (M.X ◁ modTensorπ A N P) ≫
      modTensorπ A M (modTensorMod A N P)
  erw [whiskerLeft_modTensorπ_assocInvMid_assoc,
    modTensorAssocInvCover]
  simp only [Category.assoc]
  conv_lhs => erw [Category.assoc]
  erw [modTensorπ_assocHom]
  erw [whiskerRight_modTensorπ_assocMid,
    modTensorAssocCover, Iso.inv_hom_id_assoc]

/-- **The associator isomorphism of the tensor product of
modules** (Deligne 2002, §2.3): the relative tensor is associative
up to the descended ambient associator. -/
noncomputable def modTensorAssocIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    modTensor A (modTensorMod A M N) P ≅
      modTensor A M (modTensorMod A N P) where
  hom := modTensorAssocHom A M N P
  inv := modTensorAssocInv A M N P
  hom_inv_id := modTensorAssocHom_assocInv A M N P
  inv_hom_id := modTensorAssocInv_assocHom A M N P

/-- **The associator is a morphism of modules**: it intertwines
the descended actions of the two nestings. -/
@[reassoc]
theorem modTensorAssocHom_act
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    modTensorAct A (modTensorMod A M N) P ≫
        modTensorAssocHom A M N P =
      (A ◁ modTensorAssocHom A M N P) ≫
        modTensorAct A M (modTensorMod A N P) := by
  have hactL : (A ◁ modTensorπ A (modTensorMod A M N) P) ≫
      modTensorAct A (modTensorMod A M N) P ≫
      modTensorAssocHom A M N P =
      (α_ A (modTensor A M N) P.X).inv ≫
        (modTensorAct A M N ▷ P.X) ≫
        modTensorAssocMid A M N P := by
    rw [← Category.assoc, whiskerLeft_modTensorπ_act,
      Category.assoc, modTensorπ_assocHom]
    exact Category.assoc _ _ _
  have hwhk : (A ◁ modTensorπ A (modTensorMod A M N) P) ≫
      (A ◁ modTensorAssocHom A M N P) ≫
      modTensorAct A M (modTensorMod A N P) =
      (A ◁ modTensorAssocMid A M N P) ≫
      modTensorAct A M (modTensorMod A N P) := by
    rw [← MonoidalCategory.whiskerLeft_comp_assoc,
      modTensorπ_assocHom]
    rfl
  have hcov : (A ◁ modTensorAssocCover A M N P) ≫
      modTensorAct A M (modTensorMod A N P) =
      (A ◁ (α_ M.X N.X P.X).hom) ≫
        (A ◁ (M.X ◁ modTensorπ A N P)) ≫
        (α_ A M.X (modTensor A N P)).inv ≫
        ((actLeft A M.X ▷ modTensor A N P) ≫
          modTensorπ A M (modTensorMod A N P)) := by
    erw [modTensorAssocCover]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    conv_lhs => arg 2; erw [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    erw [whiskerLeft_modTensorπ_act]
    exact congrArg (CategoryStruct.comp _)
      (congrArg (CategoryStruct.comp _) (Category.assoc _ _ _))
  apply modTensor_whisker_hom_ext A (modTensorMod A M N) P A
  conv_lhs => rw [hactL]
  conv_rhs => rw [hwhk]
  refine (cancel_epi (A ◁ (modTensorπ A M N ▷ P.X))).mp ?_
  conv_lhs => rw [associator_inv_naturality_middle_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    whiskerLeft_modTensorπ_act]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  conv_lhs => erw [whiskerRight_modTensorπ_assocMid,
    modTensorAssocCover, associator_naturality_left_assoc,
    ← whisker_exchange_assoc]
  conv_rhs => rw [← MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerRight_modTensorπ_assocMid, hcov,
    associator_inv_naturality_right_assoc]
  rw [pentagon_inv_inv_hom_hom_inv_assoc]

/-- The inverse associator intertwines the actions. -/
@[reassoc]
theorem modTensorAssocInv_act
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    modTensorAct A M (modTensorMod A N P) ≫
        modTensorAssocInv A M N P =
      (A ◁ modTensorAssocInv A M N P) ≫
        modTensorAct A (modTensorMod A M N) P := by
  have : IsIso (modTensorAssocHom A M N P) :=
    ⟨modTensorAssocInv A M N P,
      modTensorAssocHom_assocInv A M N P,
      modTensorAssocInv_assocHom A M N P⟩
  rw [← cancel_mono (modTensorAssocHom A M N P), Category.assoc,
    Category.assoc, modTensorAssocInv_assocHom, Category.comp_id,
    modTensorAssocHom_act, ← Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp,
    modTensorAssocInv_assocHom, MonoidalCategory.whiskerLeft_id,
    Category.id_comp]

/-- The associator as a morphism of bundled modules. -/
noncomputable def modTensorAssocModHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    modTensorMod A (modTensorMod A M N) P ⟶
      modTensorMod A M (modTensorMod A N P) :=
  Mod.Hom.mk' (modTensorAssocHom A M N P)
    (modTensorAssocHom_act A M N P)

/-- The inverse associator as a morphism of bundled modules. -/
noncomputable def modTensorAssocModInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    modTensorMod A M (modTensorMod A N P) ⟶
      modTensorMod A (modTensorMod A M N) P :=
  Mod.Hom.mk' (modTensorAssocInv A M N P)
    (modTensorAssocInv_act A M N P)

/-- **The associator of the tensor product of modules, as an
isomorphism of bundled modules.** -/
noncomputable def modTensorAssocModIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    modTensorMod A (modTensorMod A M N) P ≅
      modTensorMod A M (modTensorMod A N P) where
  hom := modTensorAssocModHom A M N P
  inv := modTensorAssocModInv A M N P
  hom_inv_id := Mod.hom_ext _ _
    (modTensorAssocHom_assocInv A M N P)
  inv_hom_id := Mod.hom_ext _ _
    (modTensorAssocInv_assocHom A M N P)

end RS
