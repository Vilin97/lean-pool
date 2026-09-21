/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModCross

/-!
# Insertion and contraction on the multi-tensor

The two workhorses of the Key Lemma's pairing calculus: inserting
a copairing's image at a boundary of the multi-tensor, and
contracting a pairing across one.  Insertion needs no descent —
it lands in the larger multi-tensor through the concatenation;
contraction descends through the coequalizer using the pairing's
linearity.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- The pairing evaluated on the two-element fold. -/
noncomputable def modListPairFold
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D] (A : D) [MonObj A]
    {M M' : Mod D A}
    (p : modTensor A M' M ⟶ A) :
    modList A [M', M] ⟶ A :=
  (M'.X ◁ (ρ_ M.X).hom) ≫ modTensorπ A M' M ≫ p

/-- Case analysis for decompositions of `Xs ++ [M', M]`: a slot
lies inside `Xs`, at the boundary, or inside the pair. -/
theorem append_pair_slot_cases
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    {Xs pre post : List (Mod D A)}
    {M M' P Q : Mod D A}
    (hd : Xs ++ [M', M] = pre ++ P :: Q :: post) :
    (∃ post', post = post' ++ [M', M] ∧
      Xs = pre ++ P :: Q :: post') ∨
    (post = [M] ∧ Q = M' ∧ Xs = pre ++ [P]) ∨
    (post = [] ∧ P = M' ∧ Q = M ∧ Xs = pre) := by
  rcases post.eq_nil_or_concat with h | ⟨post', q, rfl⟩
  · subst h
    have := congrArg List.reverse hd
    simp at this
    obtain ⟨h1, h2, h3⟩ := this
    exact Or.inr (Or.inr ⟨rfl, h2.symm, h1.symm, by
      simpa using congrArg List.reverse h3⟩)
  · rcases post'.eq_nil_or_concat with h | ⟨post'', q', rfl⟩
    · subst h
      have := congrArg List.reverse hd
      simp at this
      obtain ⟨h1, h2, h3⟩ := this
      refine Or.inr (Or.inl ⟨by simp [List.concat, h1],
        h2.symm, ?_⟩)
      have h4 := congrArg List.reverse h3
      simp at h4
      rw [h4]
    · have := congrArg List.reverse hd
      simp at this
      obtain ⟨h1, h2, h3⟩ := this
      refine Or.inl ⟨post'', ⟨by
        rw [show (post''.concat q').concat q =
            post'' ++ [q', q] by simp, h1, h2], ?_⟩⟩
      have h4 := congrArg List.reverse h3
      simp at h4
      simpa using h4

section Contract3

/-- The fold-level three-window contraction: pair off the
trailing window, act on the head with the resulting scalar. -/
noncomputable def contract3Fold
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] (A : D)
    [MonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A)
    (N : Mod D A) : modList A [N, M', M] ⟶ modMulti A [N] :=
  (N.X ◁ ((M'.X ◁ (ρ_ M.X).hom) ≫ modTensorπ A M' M ≫ p)) ≫
    actRight A N.X ≫ (ρ_ N.X).inv ≫ modMultiπ A [N]

/-- The window morphism of the trailing pair passes to the
pairing through the projection. -/
theorem window_contract3Fold
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] (A : D)
    [MonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A)
    (N : Mod D A) (w : (M'.X ⊗ A) ⊗ M.X ⟶ M'.X ⊗ M.X) :
    (N.X ◁ ((w ▷ modList A []) ≫
        (α_ M'.X M.X (modList A [])).hom)) ≫
        contract3Fold A p N =
      (N.X ◁ ((ρ_ ((M'.X ⊗ A) ⊗ M.X)).hom ≫ w ≫
          modTensorπ A M' M ≫ p)) ≫
        actRight A N.X ≫ (ρ_ N.X).inv ≫ modMultiπ A [N] := by
  show (N.X ◁ ((w ▷ (𝟙_ D)) ≫ (α_ M'.X M.X (𝟙_ D)).hom)) ≫
      (N.X ◁ ((M'.X ◁ (ρ_ M.X).hom) ≫
        modTensorπ A M' M ≫ p)) ≫
      actRight A N.X ≫ (ρ_ N.X).inv ≫ modMultiπ A [N] = _
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  have hw : ((w ▷ (𝟙_ D)) ≫ (α_ M'.X M.X (𝟙_ D)).hom) ≫
      (M'.X ◁ (ρ_ M.X).hom) ≫ modTensorπ A M' M ≫ p =
    (ρ_ ((M'.X ⊗ A) ⊗ M.X)).hom ≫ w ≫
      modTensorπ A M' M ≫ p := by
    have hcoh : (α_ M'.X M.X (𝟙_ D)).hom ≫
        (M'.X ◁ (ρ_ M.X).hom) = (ρ_ (M'.X ⊗ M.X)).hom := by
      monoidal
    rw [Category.assoc, reassoc_of% hcoh,
      rightUnitor_naturality_assoc]
  rw [hw]

/-- The boundary-slot condition of the three-window contraction:
the two window legs of the head--dual boundary agree after the
contraction, through the linearity of the pairing. -/
theorem contract3Fold_boundary_cond
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A)
    (hp : haveI := modTensorModObj A M' M
      actLeft A (modTensor A M' M) ≫ p = (A ◁ p) ≫ μ[A])
    (N : Mod D A) :
    modMultiLegM A [] N M' [M] ≫ contract3Fold A p N =
      modMultiLegN A [] N M' [M] ≫ contract3Fold A p N := by
  show (((actRight A N.X ▷ M'.X) ▷ (M.X ⊗ 𝟙_ D)) ≫
      (α_ N.X M'.X (M.X ⊗ 𝟙_ D)).hom) ≫
      (N.X ◁ ((M'.X ◁ (ρ_ M.X).hom) ≫
        modTensorπ A M' M ≫ p)) ≫
      actRight A N.X ≫
      ((ρ_ N.X).inv : N.X ⟶ modList A [N]) ≫
      modMultiπ A [N] =
    ((((α_ N.X A M'.X).hom ≫ (N.X ◁ actLeft A M'.X)) ▷
        (M.X ⊗ 𝟙_ D)) ≫
      (α_ N.X M'.X (M.X ⊗ 𝟙_ D)).hom) ≫
      (N.X ◁ ((M'.X ◁ (ρ_ M.X).hom) ≫
        modTensorπ A M' M ≫ p)) ≫
      actRight A N.X ≫
      ((ρ_ N.X).inv : N.X ⟶ modList A [N]) ≫
      modMultiπ A [N]
  simp only [Category.assoc]
  have hL : (((actRight A N.X ▷ M'.X) ▷ (M.X ⊗ 𝟙_ D)) ≫
      (α_ N.X M'.X (M.X ⊗ 𝟙_ D)).hom) ≫
      (N.X ◁ ((M'.X ◁ (ρ_ M.X).hom) ≫
        modTensorπ A M' M ≫ p)) =
    (α_ (N.X ⊗ A) M'.X (M.X ⊗ 𝟙_ D)).hom ≫
      ((N.X ⊗ A) ◁ ((M'.X ◁ (ρ_ M.X).hom) ≫
        modTensorπ A M' M ≫ p)) ≫
      (actRight A N.X ▷ A) := by
    simp only [Category.assoc]
    rw [associator_naturality_left_assoc, ← whisker_exchange]
  conv_lhs => rw [reassoc_of% hL]
  rw [reassoc_of% (actRight_actRight A N.X)]
  have hp' : modTensorAct A M' M ≫ p = (A ◁ p) ≫ μ[A] := hp
  have hActπ : (actLeft A M'.X ▷ M.X) ≫ modTensorπ A M' M =
      (α_ A M'.X M.X).hom ≫ (A ◁ modTensorπ A M' M) ≫
        modTensorAct A M' M := by
    rw [whiskerLeft_modTensorπ_act]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hInner : (actLeft A M'.X ▷ (M.X ⊗ 𝟙_ D)) ≫
      (M'.X ◁ (ρ_ M.X).hom) ≫ modTensorπ A M' M ≫ p =
    ((A ⊗ M'.X) ◁ (ρ_ M.X).hom) ≫ (α_ A M'.X M.X).hom ≫
      (A ◁ modTensorπ A M' M) ≫ (A ◁ p) ≫ μ[A] := by
    rw [← whisker_exchange_assoc, reassoc_of% hActπ]
    rw [show modTensorAct A M' M ≫ p = (A ◁ p) ≫ μ[A] from hp']
  conv_rhs => rw [comp_whiskerRight, Category.assoc,
    associator_naturality_middle_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, hInner]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  suffices h : (α_ (N.X ⊗ A) M'.X (M.X ⊗ 𝟙_ D)).hom ≫
      ((N.X ⊗ A) ◁ (M'.X ◁ (ρ_ M.X).hom)) ≫
      ((N.X ⊗ A) ◁ modTensorπ A M' M) ≫
      ((N.X ⊗ A) ◁ p) ≫ (α_ N.X A A).hom =
    ((α_ N.X A M'.X).hom ▷ (M.X ⊗ 𝟙_ D)) ≫
      (α_ N.X (A ⊗ M'.X) (M.X ⊗ 𝟙_ D)).hom ≫
      (N.X ◁ ((A ⊗ M'.X) ◁ (ρ_ M.X).hom)) ≫
      (N.X ◁ (α_ A M'.X M.X).hom) ≫
      (N.X ◁ (A ◁ modTensorπ A M' M)) ≫
      (N.X ◁ (A ◁ p)) by
    rw [reassoc_of% h]
  monoidal

/-- **The multi-level contraction at a three-element window**: a
linear pairing contracts the trailing pair of the multi-tensor,
the scalar acting on the head. -/
noncomputable def modMultiContract3
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A)
    (hp : haveI := modTensorModObj A M' M
      actLeft A (modTensor A M' M) ≫ p = (A ◁ p) ≫ μ[A])
    (N : Mod D A) :
    modMulti A [N, M', M] ⟶ modMulti A [N] :=
  modMultiDesc A (contract3Fold A p N)
    (by
      intro pre P Q post hd
      rcases append_pair_slot_cases A (Xs := [N])
          (show [N] ++ [M', M] = pre ++ P :: Q :: post from hd)
        with ⟨post', _, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
      · exact absurd (congrArg List.length h2)
          (by simp; omega)
      · subst h1
        replace h2 := h2.symm; subst h2
        obtain ⟨rfl, hP⟩ : pre = [] ∧ P = N := by
          rcases pre with _ | ⟨R, rest⟩
          · exact ⟨rfl, by simpa using h3.symm⟩
          · exact absurd (congrArg List.length h3) (by simp)
        replace hP := hP.symm; subst hP
        have hid : (modListCast A hd.symm ≫
              contract3Fold A p N :
            modList A ([] ++ N :: M' :: [M]) ⟶
              modMulti A [N]) = contract3Fold A p N :=
          Category.id_comp _
        exact ((congrArg (fun t =>
            modMultiLegM A [] N M' [M] ≫ t) hid).trans
          (contract3Fold_boundary_cond A p hp N)).trans
          (congrArg (fun t =>
            modMultiLegN A [] N M' [M] ≫ t) hid.symm)
      · subst h1
        replace h2 := h2.symm; subst h2
        replace h3 := h3.symm; subst h3
        obtain rfl : pre = [N] := h4.symm
        have hid : (modListCast A hd.symm ≫
              contract3Fold A p N :
            modList A ([N] ++ M' :: M :: []) ⟶
              modMulti A [N]) = contract3Fold A p N :=
          Category.id_comp _
        have hfree : modMultiLegM A [N] M' M [] ≫
              contract3Fold A p N =
            modMultiLegN A [N] M' M [] ≫
              contract3Fold A p N := by
          show (N.X ◁ ((modTensorLegM A M' M ▷ modList A []) ≫
              (α_ M'.X M.X (modList A [])).hom)) ≫
              contract3Fold A p N =
            (N.X ◁ ((modTensorLegN A M' M ▷ modList A []) ≫
              (α_ M'.X M.X (modList A [])).hom)) ≫
              contract3Fold A p N
          rw [window_contract3Fold, window_contract3Fold]
          have hcond2 : modTensorLegM A M' M ≫
              modTensorπ A M' M ≫ p =
            modTensorLegN A M' M ≫ modTensorπ A M' M ≫ p := by
            rw [← Category.assoc, modTensor_condition,
              Category.assoc]
          exact congrArg (fun t => (N.X ◁
            ((ρ_ ((M'.X ⊗ A) ⊗ M.X)).hom ≫ t)) ≫
            actRight A N.X ≫ (ρ_ N.X).inv ≫ modMultiπ A [N])
            hcond2
        exact ((congrArg (fun t =>
            modMultiLegM A [N] M' M [] ≫ t) hid).trans
          hfree).trans
          (congrArg (fun t =>
            modMultiLegN A [N] M' M [] ≫ t) hid.symm))

/-- Defining equation of the three-window contraction. -/
@[reassoc (attr := simp)]
theorem modMultiπ_contract3
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A)
    (hp : haveI := modTensorModObj A M' M
      actLeft A (modTensor A M' M) ≫ p = (A ◁ p) ≫ μ[A])
    (N : Mod D A) :
    modMultiπ A [N, M', M] ≫ modMultiContract3 A p hp N =
      contract3Fold A p N :=
  modMultiπ_desc A _ _

end Contract3

section ZigCore

/-- The image of a copairing at the two-element multi-tensor. -/
noncomputable def copairImage
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] (A : D)
    [MonObj A] {M : Mod D A} {M' : Mod D A}
    (c : A ⟶ modTensor A M M') :
    𝟙_ D ⟶ modMulti A [M, M'] :=
  η[A] ≫ c ≫ (modMultiPair A M M').inv

/-- **The zig composite** of a copairing and a linear pairing:
insert the copairing on the left, concatenate, and contract the
trailing pair.  The zigzag law of a duality datum states that
this composite is the identity. -/
noncomputable def zigComposite
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
    modMulti A [M] ⟶ modMulti A [M] :=
  (λ_ (modMulti A [M])).inv ≫
    (copairImage A c ▷ modMulti A [M]) ≫
    modMultiConcat A [M, M'] [M] ≫
    modMultiContract3 A p hp M

end ZigCore

end RS
