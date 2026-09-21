/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModIns

/-!
# Contraction of a leading dual pair on the multi-tensor

The mirror image of the three-window contraction of `ModIns.lean`:
a linear pairing contracts the leading pair of the multi-tensor,
its scalar acting on the head of the remainder from the left, so no
braid is needed at the fold level.  The zag composite inserts a
copairing's image on the right and contracts the leading pair.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- Case analysis for decompositions of the three-element list
`[M', M, N]`: a slot is the leading pair or the boundary. -/
theorem prepend_pair_slot_cases
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    {pre post : List (Mod D A)}
    {M M' N P Q : Mod D A}
    (hd : [M', M, N] = pre ++ P :: Q :: post) :
    (pre = [] ∧ P = M' ∧ Q = M ∧ post = [N]) ∨
    (pre = [M'] ∧ P = M ∧ Q = N ∧ post = []) := by
  rcases pre with _ | ⟨R, pre⟩
  · injection hd with h1 h
    injection h with h2 h3
    exact Or.inl ⟨rfl, h1.symm, h2.symm, h3.symm⟩
  · rcases pre with _ | ⟨S, pre⟩
    · injection hd with h1 h
      injection h with h2 h
      injection h with h3 h4
      exact Or.inr ⟨by rw [h1], h2.symm, h3.symm, h4.symm⟩
    · exact absurd (congrArg List.length hd) (by simp; omega)

section Contract3L

/-- The fold-level three-window contraction of a leading pair: pair
off the leading window, act on the head of the remainder with the
resulting scalar from the left. -/
noncomputable def contract3LFold
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] (A : D)
    [MonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A)
    (N : Mod D A) : modList A [M', M, N] ⟶ modMulti A [N] :=
  (α_ M'.X M.X (N.X ⊗ 𝟙_ D)).inv ≫
    ((modTensorπ A M' M ≫ p) ▷ (N.X ⊗ 𝟙_ D)) ≫
    modListHeadAct A N [] ≫ modMultiπ A [N]

/-- The window morphism of the leading pair passes to the pairing
through the projection. -/
theorem window_contract3LFold
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] (A : D)
    [MonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A)
    (N : Mod D A) (w : (M'.X ⊗ A) ⊗ M.X ⟶ M'.X ⊗ M.X) :
    ((w ▷ modList A [N]) ≫
        (α_ M'.X M.X (modList A [N])).hom) ≫
        contract3LFold A p N =
      ((w ≫ modTensorπ A M' M ≫ p) ▷ (N.X ⊗ 𝟙_ D)) ≫
        modListHeadAct A N [] ≫ modMultiπ A [N] := by
  show ((w ▷ (N.X ⊗ 𝟙_ D)) ≫ (α_ M'.X M.X (N.X ⊗ 𝟙_ D)).hom) ≫
      (α_ M'.X M.X (N.X ⊗ 𝟙_ D)).inv ≫
      ((modTensorπ A M' M ≫ p) ▷ (N.X ⊗ 𝟙_ D)) ≫
      modListHeadAct A N [] ≫ modMultiπ A [N] = _
  rw [Category.assoc, Iso.hom_inv_id_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc]

/-- The pair-slot condition of the leading three-window
contraction: the two window legs of the leading pair agree after
the contraction. -/
theorem contract3LFold_pair_cond
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] (A : D)
    [MonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A)
    (N : Mod D A) :
    modMultiLegM A [] M' M [N] ≫ contract3LFold A p N =
      modMultiLegN A [] M' M [N] ≫ contract3LFold A p N := by
  show ((modTensorLegM A M' M ▷ modList A [N]) ≫
      (α_ M'.X M.X (modList A [N])).hom) ≫
      contract3LFold A p N =
    ((modTensorLegN A M' M ▷ modList A [N]) ≫
      (α_ M'.X M.X (modList A [N])).hom) ≫
      contract3LFold A p N
  rw [window_contract3LFold, window_contract3LFold]
  have hcond2 : modTensorLegM A M' M ≫
      modTensorπ A M' M ≫ p =
    modTensorLegN A M' M ≫ modTensorπ A M' M ≫ p := by
    rw [← Category.assoc, modTensor_condition, Category.assoc]
  exact congrArg (fun t => (t ▷ (N.X ⊗ 𝟙_ D)) ≫
    modListHeadAct A N [] ≫ modMultiπ A [N]) hcond2

/-- The boundary-slot condition of the leading three-window
contraction: the two window legs of the dual--head boundary agree
after the contraction, through the linearity of the pairing. -/
theorem contract3LFold_boundary_cond
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A)
    (hp : haveI := modTensorModObj A M' M
      actLeft A (modTensor A M' M) ≫ p = (A ◁ p) ≫ μ[A])
    (N : Mod D A) :
    modMultiLegM A [M'] M N [] ≫ contract3LFold A p N =
      modMultiLegN A [M'] M N [] ≫ contract3LFold A p N := by
  show (M'.X ◁ (((actRight A M.X ▷ N.X) ▷ (𝟙_ D)) ≫
      (α_ M.X N.X (𝟙_ D)).hom)) ≫
      (α_ M'.X M.X (N.X ⊗ 𝟙_ D)).inv ≫
      ((modTensorπ A M' M ≫ p) ▷ (N.X ⊗ 𝟙_ D)) ≫
      ((α_ A N.X (𝟙_ D)).inv ≫ (actLeft A N.X ▷ (𝟙_ D))) ≫
      modMultiπ A [N] =
    (M'.X ◁ ((((α_ M.X A N.X).hom ≫ (M.X ◁ actLeft A N.X)) ▷
        (𝟙_ D)) ≫ (α_ M.X N.X (𝟙_ D)).hom)) ≫
      (α_ M'.X M.X (N.X ⊗ 𝟙_ D)).inv ≫
      ((modTensorπ A M' M ≫ p) ▷ (N.X ⊗ 𝟙_ D)) ≫
      ((α_ A N.X (𝟙_ D)).inv ≫ (actLeft A N.X ▷ (𝟙_ D))) ≫
      modMultiπ A [N]
  simp only [Category.assoc]
  have hrel : (M'.X ◁ actLeft A M.X) ≫ modTensorπ A M' M =
      (α_ M'.X A M.X).inv ≫ (actRight A M'.X ▷ M.X) ≫
        modTensorπ A M' M := by
    have h := (modTensor_condition A M' M).symm
    rw [modTensorLegM, modTensorLegN, Category.assoc] at h
    rw [← h, Iso.inv_hom_id_assoc]
  have hact : (actLeft A M'.X ▷ M.X) ≫ modTensorπ A M' M =
      (α_ A M'.X M.X).hom ≫ (A ◁ modTensorπ A M' M) ≫
        modTensorAct A M' M := by
    rw [whiskerLeft_modTensorπ_act]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hp' : modTensorAct A M' M ≫ p = (A ◁ p) ≫ μ[A] := hp
  have hbraid : (M'.X ◁ (β_ M.X A).hom) ≫
      (α_ M'.X A M.X).inv ≫ ((β_ M'.X A).hom ▷ M.X) ≫
        (α_ A M'.X M.X).hom =
      (α_ M'.X M.X A).inv ≫ (β_ (M'.X ⊗ M.X) A).hom := by
    rw [BraidedCategory.braiding_tensor_left_hom,
      Iso.inv_hom_id_assoc]
  have hML : (M'.X ◁ actRight A M.X) ≫ modTensorπ A M' M ≫ p =
      (α_ M'.X M.X A).inv ≫
        ((modTensorπ A M' M ≫ p) ▷ A) ≫ μ[A] := by
    show (M'.X ◁ ((β_ M.X A).hom ≫ actLeft A M.X)) ≫
        modTensorπ A M' M ≫ p = _
    rw [MonoidalCategory.whiskerLeft_comp, Category.assoc,
      reassoc_of% hrel]
    show (M'.X ◁ (β_ M.X A).hom) ≫ (α_ M'.X A M.X).inv ≫
        (((β_ M'.X A).hom ≫ actLeft A M'.X) ▷ M.X) ≫
        modTensorπ A M' M ≫ p = _
    rw [MonoidalCategory.comp_whiskerRight, Category.assoc,
      reassoc_of% hact,
      show modTensorAct A M' M ≫ p = (A ◁ p) ≫ μ[A] from hp',
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      reassoc_of% hbraid,
      ← BraidedCategory.braiding_naturality_left_assoc,
      IsCommMonObj.mul_comm]
  conv_lhs => rw [associator_naturality_left,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    associator_inv_naturality_middle_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc, hML,
    MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.comp_whiskerRight, Category.assoc,
    Category.assoc, associator_inv_naturality_left_assoc,
    associator_inv_naturality_left_assoc]
  conv_rhs => rw [MonoidalCategory.comp_whiskerRight,
    Category.assoc, associator_naturality_middle,
    MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    Category.assoc, associator_inv_naturality_right_assoc,
    whisker_exchange_assoc,
    associator_inv_naturality_middle_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    actLeft_actLeft,
    MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.comp_whiskerRight, Category.assoc,
    Category.assoc, associator_inv_naturality_left_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    associator_inv_naturality_left,
    MonoidalCategory.comp_whiskerRight, Category.assoc]
  monoidal

/-- **The multi-level contraction at a leading three-element
window**: a linear pairing contracts the leading pair of the
multi-tensor, the scalar acting on the remaining module. -/
noncomputable def modMultiContract3L
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A)
    (hp : haveI := modTensorModObj A M' M
      actLeft A (modTensor A M' M) ≫ p = (A ◁ p) ≫ μ[A])
    (N : Mod D A) :
    modMulti A [M', M, N] ⟶ modMulti A [N] :=
  modMultiDesc A (contract3LFold A p N)
    (by
      intro pre P Q post hd
      rcases prepend_pair_slot_cases A hd with
        ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
      · subst h1
        replace h2 := h2.symm; subst h2
        replace h3 := h3.symm; subst h3
        subst h4
        have hid : (modListCast A hd.symm ≫
              contract3LFold A p N :
            modList A ([] ++ M' :: M :: [N]) ⟶
              modMulti A [N]) = contract3LFold A p N :=
          Category.id_comp _
        exact ((congrArg (fun t =>
            modMultiLegM A [] M' M [N] ≫ t) hid).trans
          (contract3LFold_pair_cond A p N)).trans
          (congrArg (fun t =>
            modMultiLegN A [] M' M [N] ≫ t) hid.symm)
      · subst h1
        replace h2 := h2.symm; subst h2
        replace h3 := h3.symm; subst h3
        subst h4
        have hid : (modListCast A hd.symm ≫
              contract3LFold A p N :
            modList A ([M'] ++ M :: N :: []) ⟶
              modMulti A [N]) = contract3LFold A p N :=
          Category.id_comp _
        exact ((congrArg (fun t =>
            modMultiLegM A [M'] M N [] ≫ t) hid).trans
          (contract3LFold_boundary_cond A p hp N)).trans
          (congrArg (fun t =>
            modMultiLegN A [M'] M N [] ≫ t) hid.symm))

/-- Defining equation of the leading three-window contraction. -/
@[reassoc (attr := simp)]
theorem modMultiπ_contract3L
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A)
    (hp : haveI := modTensorModObj A M' M
      actLeft A (modTensor A M' M) ≫ p = (A ◁ p) ≫ μ[A])
    (N : Mod D A) :
    modMultiπ A [M', M, N] ≫ modMultiContract3L A p hp N =
      contract3LFold A p N :=
  modMultiπ_desc A _ _

end Contract3L

section ZagCore

/-- **The zag composite** of a copairing and a linear pairing:
insert the copairing on the right, concatenate, and contract the
leading pair.  The zagzig law of a duality datum states that this
composite is the identity. -/
noncomputable def zagComposite
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (c : A ⟶ modTensor A M M')
    (p : modTensor A M' M ⟶ A)
    (hp : haveI := modTensorModObj A M' M
      actLeft A (modTensor A M' M) ≫ p = (A ◁ p) ≫ μ[A]) :
    modMulti A [M'] ⟶ modMulti A [M'] :=
  (ρ_ (modMulti A [M'])).inv ≫
    (modMulti A [M'] ◁ copairImage A c) ≫
    modMultiConcat A [M'] [M, M'] ≫
    modMultiContract3L A p hp M'

end ZagCore

end RS
