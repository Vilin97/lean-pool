/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainStage2

/-!
# Insertion maps into the splitting-chain stages

Single-module insertions for the two-index splitting chain: the
module inserts into a symmetric power from the left through the
singleton power and the symmetric multiplication, and this
insertion descends through the module-tensor coequalizer into
either slot of a two-index chain stage.  How the descended
insertions meet the stage multiplication and the seed transition is
the subject of [FirstSlot.lean](FirstSlot.lean) and
[SecondSlot.lean](SecondSlot.lean).

* `symInsL`: the insertion `X ⊗ symPow A X (n + 1) ⟶
  symPow A X (n + 2)`, the symmetric multiplication against the
  singleton power.
* `symInsL_actAcross`/`symInsL_actRight`: the insertion is
  compatible with the monoid action on the symmetric factor, in the
  carried-past left form and in the braided right form.
* `chainInsP`/`chainInsQ`: the descended insertions of the dual
  pair's modules into the first and second slots of a two-index
  stage, with defining equations `whiskerLeft_π_chainInsP` and
  `whiskerLeft_π_chainInsQ`.
* `symInsL_symMul`: the insertion is associative against the
  symmetric multiplication, up to the arity transport.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## Insertion into a symmetric power -/

section SymIns

/-- **Left insertion into a symmetric power**: the module enters
through the singleton power and multiplies. -/
noncomputable def symInsL
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (X : D) [ModObj A X]
    (n : ℕ) :
    X ⊗ symPow A X (n + 1) ⟶ symPow A X (n + 2) :=
  ((symPowOne A X).inv ▷ symPow A X (n + 1)) ≫
    symMul A X 1 (n + 1) ≫
    symPowCast A X (by omega : 1 + (n + 1) = n + 2)

/-- The symmetric-power action passes an arity transport. -/
theorem symPowAct_symPowCast
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    {m n : ℕ} (h : m + 1 = n + 1) :
    symPowAct A X m ≫ symPowCast A X h =
      (A ◁ symPowCast A X h) ≫ symPowAct A X n := by
  obtain rfl : m = n := by omega
  have hc : symPowCast A X h = 𝟙 (symPow A X (m + 1)) := rfl
  rw [hc, Category.comp_id, MonoidalCategory.whiskerLeft_id,
    Category.id_comp]

/-- **The insertion is compatible with the action on the symmetric
factor**, in carried-past form: the monoid crosses the inserted
module and acts on the enlarged power. -/
theorem symInsL_actAcross
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (n : ℕ) :
    (braidPast A X (symPow A X (n + 1))).hom ≫
        (X ◁ symPowAct A X n) ≫ symInsL A X n =
      (A ◁ symInsL A X n) ≫ symPowAct A X (n + 1) := by
  have hmul : (braidPast A (symPow A X 1)
        (symPow A X (n + 1))).hom ≫
      (symPow A X 1 ◁ symPowAct A X n) ≫ symMul A X 1 (n + 1) =
      (A ◁ symMul A X 1 (n + 1)) ≫ symPowAct A X (1 + n) :=
    symMul_actRight A X 0 n
  have hcast : symPowAct A X (1 + n) ≫
      symPowCast A X (by omega : 1 + (n + 1) = n + 2) =
      (A ◁ symPowCast A X (by omega : 1 + (n + 1) = n + 2)) ≫
        symPowAct A X (n + 1) :=
    symPowAct_symPowCast A X (by omega : 1 + n + 1 = n + 1 + 1)
  rw [symInsL]
  rw [whisker_exchange_assoc, ← braidPast_natural_context_assoc,
    reassoc_of% hmul, hcast]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]

/-- The carried-past compatibility, solved for the action-first
composite. -/
theorem symInsL_symPowAct
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (n : ℕ) :
    (X ◁ symPowAct A X n) ≫ symInsL A X n =
      (braidPast A X (symPow A X (n + 1))).inv ≫
        (A ◁ symInsL A X n) ≫ symPowAct A X (n + 1) := by
  rw [← symInsL_actAcross A X n, Iso.inv_hom_id_assoc]

/-- Braiding under a context gathers to the braiding of the tensor
pair. -/
private theorem whiskerLeft_braiding_braidPast_inv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (P V B : D) :
    (P ◁ (β_ V B).hom) ≫ (braidPast B P V).inv =
      (α_ P V B).inv ≫ (β_ (P ⊗ V) B).hom := by
  rw [← cancel_mono (braidPast B P V).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [braidPast_hom, BraidedCategory.braiding_tensor_left_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, SymmetricCategory.symmetry,
    MonoidalCategory.id_whiskerRight, Category.id_comp,
    Iso.inv_hom_id, Category.comp_id]

/-- **The insertion is compatible with the braided right action on
the symmetric factor**: the monoid leaves through the inserted
module and acts on the right of the enlarged power. -/
theorem symInsL_actRight
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (n : ℕ) :
    (X ◁ actRight A (symPowMod A X n).X) ≫ symInsL A X n =
      (α_ X (symPow A X (n + 1)) A).inv ≫
        (symInsL A X n ▷ A) ≫
        actRight A (symPowMod A X (n + 1)).X := by
  rw [actRight, actRight,
    show actLeft A (symPowMod A X n).X = symPowAct A X n from
      rfl,
    show actLeft A (symPowMod A X (n + 1)).X =
      symPowAct A X (n + 1) from rfl]
  change (X ◁ ((β_ (symPow A X (n + 1)) A).hom ≫
      symPowAct A X n)) ≫ symInsL A X n =
    (α_ X (symPow A X (n + 1)) A).inv ≫ (symInsL A X n ▷ A) ≫
      (β_ (symPow A X (n + 2)) A).hom ≫ symPowAct A X (n + 1)
  rw [BraidedCategory.braiding_naturality_left_assoc,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    symInsL_symPowAct,
    reassoc_of% (whiskerLeft_braiding_braidPast_inv
      X (symPow A X (n + 1)) A)]

end SymIns

/-! ## Structural crossings for the descent conditions -/

section Structural

/-- A middle action slides under an untouched context and past an
insertion into the first factor. -/
private theorem legN_cross_fst_aux [Category.{v} D] [MonoidalCategory D]
    {P S₁ S₂ B T : D}
    (f : P ⊗ S₁ ⟶ S₂) (a : B ⊗ T ⟶ T) :
    P ◁ ((α_ S₁ B T).hom ≫ (S₁ ◁ a)) ≫
        ((α_ P S₁ T).inv ≫ (f ▷ T)) =
      ((α_ P (S₁ ⊗ B) T).inv ≫
        (((α_ P S₁ B).inv ≫ (f ▷ B)) ▷ T)) ≫
        ((α_ S₂ B T).hom ≫ (S₂ ◁ a)) := by
  have hcoh : (P ◁ (α_ S₁ B T).hom) ≫ (α_ P S₁ (B ⊗ T)).inv =
      (α_ P (S₁ ⊗ B) T).inv ≫ ((α_ P S₁ B).inv ▷ T) ≫
        (α_ (P ⊗ S₁) B T).hom := by
    monoidal
  simp only [MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [associator_inv_naturality_right_assoc,
    whisker_exchange, associator_naturality_left_assoc,
    reassoc_of% hcoh]

/-- A right action on the braided-past factor slides under the
carrying and past an insertion into the second factor. -/
private theorem legM_cross_snd_aux
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    {P Q B T T' : D}
    (g : Q ⊗ B ⟶ Q) (f : P ⊗ T ⟶ T') :
    P ◁ (g ▷ T) ≫
        ((α_ P Q T).inv ≫ ((β_ P Q).hom ▷ T) ≫
          (α_ Q P T).hom ≫ (Q ◁ f)) =
      ((α_ P (Q ⊗ B) T).inv ≫ ((β_ P (Q ⊗ B)).hom ▷ T) ≫
        (α_ (Q ⊗ B) P T).hom ≫ ((Q ⊗ B) ◁ f)) ≫
        (g ▷ T') := by
  rw [associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_right]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange]

/-- The carrying isomorphism, inverted and rewritten through the
symmetry. -/
private theorem braidPast_inv_symm
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (B P T : D) :
    (braidPast B P T).inv =
      (α_ P B T).inv ≫ ((β_ P B).hom ▷ T) ≫ (α_ B P T).hom := by
  rw [← cancel_epi (braidPast B P T).hom, Iso.hom_inv_id,
    braidPast_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, SymmetricCategory.symmetry,
    MonoidalCategory.id_whiskerRight, Category.id_comp,
    Iso.inv_hom_id]

/-- A middle action crosses an insertion into the second factor
under the carrying of the inserted module. -/
private theorem legN_cross_snd_aux
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    {P Q B T T' : D}
    (a : B ⊗ T ⟶ T) (a' : B ⊗ T' ⟶ T') (f : P ⊗ T ⟶ T')
    (hcross : (P ◁ a) ≫ f =
      (braidPast B P T).inv ≫ (B ◁ f) ≫ a') :
    P ◁ ((α_ Q B T).hom ≫ (Q ◁ a)) ≫
        ((α_ P Q T).inv ≫ ((β_ P Q).hom ▷ T) ≫
          (α_ Q P T).hom ≫ (Q ◁ f)) =
      ((α_ P (Q ⊗ B) T).inv ≫ ((β_ P (Q ⊗ B)).hom ▷ T) ≫
        (α_ (Q ⊗ B) P T).hom ≫ ((Q ⊗ B) ◁ f)) ≫
        ((α_ Q B T').hom ≫ (Q ◁ a')) := by
  have hcoh : (P ◁ (α_ Q B T).hom) ≫ (α_ P Q (B ⊗ T)).inv ≫
      ((β_ P Q).hom ▷ (B ⊗ T)) ≫ (α_ Q P (B ⊗ T)).hom ≫
      (Q ◁ (braidPast B P T).inv) =
      (α_ P (Q ⊗ B) T).inv ≫ ((β_ P (Q ⊗ B)).hom ▷ T) ≫
        (α_ (Q ⊗ B) P T).hom ≫ (α_ Q B (P ⊗ T)).hom := by
    rw [braidPast_inv_symm,
      BraidedCategory.braiding_tensor_right_hom]
    simp only [MonoidalCategory.comp_whiskerRight,
      MonoidalCategory.whiskerLeft_comp, Category.assoc]
    monoidal
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_right_assoc,
    whisker_exchange_assoc, associator_naturality_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp, hcross]
  simp only [MonoidalCategory.whiskerLeft_comp]
  rw [associator_naturality_right_assoc, reassoc_of% hcoh]

end Structural

/-! ## Insertion into the first slot -/

section InsP

/-- The two module-tensor legs agree after the insertion of the
dual module into the first slot: the leg acting on the second
factor slides under the insertion, the leg acting on the first
factor crosses it, and the level-`(p + 1, q)` coequalizer absorbs
both. -/
theorem chainInsP_cond
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (p q : ℕ) :
    M'.X ◁ modTensorLegM A (symPowMod A M'.X p)
        (symPowMod A M.X q) ≫
      ((α_ M'.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        (symInsL A M'.X p ▷ symPow A M.X (q + 1)) ≫
        modTensorπ A (symPowMod A M'.X (p + 1))
          (symPowMod A M.X q)) =
    M'.X ◁ modTensorLegN A (symPowMod A M'.X p)
        (symPowMod A M.X q) ≫
      ((α_ M'.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        (symInsL A M'.X p ▷ symPow A M.X (q + 1)) ≫
        modTensorπ A (symPowMod A M'.X (p + 1))
          (symPowMod A M.X q)) := by
  rw [modTensorLegM, modTensorLegN, actRight,
    show actLeft A (symPowMod A M'.X p).X = symPowAct A M'.X p
      from rfl,
    show actLeft A (symPowMod A M.X q).X = symPowAct A M.X q
      from rfl]
  change M'.X ◁ (((β_ (symPow A M'.X (p + 1)) A).hom ≫
        symPowAct A M'.X p) ▷ symPow A M.X (q + 1)) ≫
      ((α_ M'.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        (symInsL A M'.X p ▷ symPow A M.X (q + 1)) ≫
        modTensorπ A (symPowMod A M'.X (p + 1))
          (symPowMod A M.X q)) =
    M'.X ◁ ((α_ (symPow A M'.X (p + 1)) A
          (symPow A M.X (q + 1))).hom ≫
        (symPow A M'.X (p + 1) ◁ symPowAct A M.X q)) ≫
      ((α_ M'.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        (symInsL A M'.X p ▷ symPow A M.X (q + 1)) ≫
        modTensorπ A (symPowMod A M'.X (p + 1))
          (symPowMod A M.X q))
  have hcross : (M'.X ◁ ((β_ (symPow A M'.X (p + 1)) A).hom ≫
        symPowAct A M'.X p)) ≫ symInsL A M'.X p =
      (α_ M'.X (symPow A M'.X (p + 1)) A).inv ≫
        (symInsL A M'.X p ▷ A) ≫
        ((β_ (symPow A M'.X (p + 2)) A).hom ≫
          symPowAct A M'.X (p + 1)) :=
    symInsL_actRight A M'.X p
  have hM : M'.X ◁ (((β_ (symPow A M'.X (p + 1)) A).hom ≫
        symPowAct A M'.X p) ▷ symPow A M.X (q + 1)) ≫
      ((α_ M'.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        (symInsL A M'.X p ▷ symPow A M.X (q + 1))) =
      ((α_ M'.X (symPow A M'.X (p + 1) ⊗ A)
          (symPow A M.X (q + 1))).inv ≫
        (((α_ M'.X (symPow A M'.X (p + 1)) A).inv ≫
          (symInsL A M'.X p ▷ A)) ▷ symPow A M.X (q + 1))) ≫
        (((β_ (symPow A M'.X (p + 2)) A).hom ≫
          symPowAct A M'.X (p + 1)) ▷
            symPow A M.X (q + 1)) := by
    rw [associator_inv_naturality_middle_assoc,
      ← comp_whiskerRight, hcross]
    simp only [MonoidalCategory.comp_whiskerRight,
      Category.assoc]
  have hN : M'.X ◁ ((α_ (symPow A M'.X (p + 1)) A
          (symPow A M.X (q + 1))).hom ≫
        (symPow A M'.X (p + 1) ◁ symPowAct A M.X q)) ≫
      ((α_ M'.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        (symInsL A M'.X p ▷ symPow A M.X (q + 1))) =
      ((α_ M'.X (symPow A M'.X (p + 1) ⊗ A)
          (symPow A M.X (q + 1))).inv ≫
        (((α_ M'.X (symPow A M'.X (p + 1)) A).inv ≫
          (symInsL A M'.X p ▷ A)) ▷ symPow A M.X (q + 1))) ≫
        ((α_ (symPow A M'.X (p + 2)) A
            (symPow A M.X (q + 1))).hom ≫
          (symPow A M'.X (p + 2) ◁ symPowAct A M.X q)) :=
    legN_cross_fst_aux (symInsL A M'.X p) (symPowAct A M.X q)
  have hcond : (((β_ (symPow A M'.X (p + 2)) A).hom ≫
        symPowAct A M'.X (p + 1)) ▷ symPow A M.X (q + 1)) ≫
      modTensorπ A (symPowMod A M'.X (p + 1))
        (symPowMod A M.X q) =
      ((α_ (symPow A M'.X (p + 2)) A
          (symPow A M.X (q + 1))).hom ≫
        (symPow A M'.X (p + 2) ◁ symPowAct A M.X q)) ≫
      modTensorπ A (symPowMod A M'.X (p + 1))
        (symPowMod A M.X q) :=
    modTensor_condition A (symPowMod A M'.X (p + 1))
      (symPowMod A M.X q)
  erw [reassoc_of% hM, reassoc_of% hN, hcond]
  repeat' erw [Category.assoc]

/-- **Insertion into the first slot of a two-index stage**: the
dual module enters the first symmetric power, descended through
the module-tensor coequalizer. -/
noncomputable def chainInsP
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (p q : ℕ) :
    M'.X ⊗ chainStage2 A M M' p q ⟶
      chainStage2 A M M' (p + 1) q :=
  modTensorWhiskerDesc A (symPowMod A M'.X p) (symPowMod A M.X q)
    M'.X
    ((α_ M'.X (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1))).inv ≫
      (symInsL A M'.X p ▷ symPow A M.X (q + 1)) ≫
      modTensorπ A (symPowMod A M'.X (p + 1))
        (symPowMod A M.X q))
    (chainInsP_cond A M M' p q)

/-- Defining equation of the first-slot insertion. -/
@[reassoc]
theorem whiskerLeft_π_chainInsP
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (p q : ℕ) :
    M'.X ◁ modTensorπ A (symPowMod A M'.X p)
        (symPowMod A M.X q) ≫ chainInsP A M M' p q =
      (α_ M'.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        (symInsL A M'.X p ▷ symPow A M.X (q + 1)) ≫
        modTensorπ A (symPowMod A M'.X (p + 1))
          (symPowMod A M.X q) :=
  whiskerLeft_modTensorπ_whiskerDesc A _ _ M'.X _ _

end InsP

/-! ## Insertion into the second slot -/

section InsQ

/-- The two module-tensor legs agree after the insertion of the
module into the second slot: the module is carried past the first
symmetric power, the leg acting on the first factor slides under
the carrying, the leg acting on the second factor crosses the
insertion, and the level-`(p, q + 1)` coequalizer absorbs both. -/
theorem chainInsQ_cond
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (p q : ℕ) :
    M.X ◁ modTensorLegM A (symPowMod A M'.X p)
        (symPowMod A M.X q) ≫
      ((α_ M.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        ((β_ M.X (symPow A M'.X (p + 1))).hom ▷
          symPow A M.X (q + 1)) ≫
        (α_ (symPow A M'.X (p + 1)) M.X
          (symPow A M.X (q + 1))).hom ≫
        (symPow A M'.X (p + 1) ◁ symInsL A M.X q) ≫
        modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X (q + 1))) =
    M.X ◁ modTensorLegN A (symPowMod A M'.X p)
        (symPowMod A M.X q) ≫
      ((α_ M.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        ((β_ M.X (symPow A M'.X (p + 1))).hom ▷
          symPow A M.X (q + 1)) ≫
        (α_ (symPow A M'.X (p + 1)) M.X
          (symPow A M.X (q + 1))).hom ≫
        (symPow A M'.X (p + 1) ◁ symInsL A M.X q) ≫
        modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X (q + 1))) := by
  rw [modTensorLegM, modTensorLegN, actRight,
    show actLeft A (symPowMod A M'.X p).X = symPowAct A M'.X p
      from rfl,
    show actLeft A (symPowMod A M.X q).X = symPowAct A M.X q
      from rfl]
  change M.X ◁ (((β_ (symPow A M'.X (p + 1)) A).hom ≫
        symPowAct A M'.X p) ▷ symPow A M.X (q + 1)) ≫
      ((α_ M.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        ((β_ M.X (symPow A M'.X (p + 1))).hom ▷
          symPow A M.X (q + 1)) ≫
        (α_ (symPow A M'.X (p + 1)) M.X
          (symPow A M.X (q + 1))).hom ≫
        (symPow A M'.X (p + 1) ◁ symInsL A M.X q) ≫
        modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X (q + 1))) =
    M.X ◁ ((α_ (symPow A M'.X (p + 1)) A
          (symPow A M.X (q + 1))).hom ≫
        (symPow A M'.X (p + 1) ◁ symPowAct A M.X q)) ≫
      ((α_ M.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        ((β_ M.X (symPow A M'.X (p + 1))).hom ▷
          symPow A M.X (q + 1)) ≫
        (α_ (symPow A M'.X (p + 1)) M.X
          (symPow A M.X (q + 1))).hom ≫
        (symPow A M'.X (p + 1) ◁ symInsL A M.X q) ≫
        modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X (q + 1)))
  have hM : M.X ◁ (((β_ (symPow A M'.X (p + 1)) A).hom ≫
        symPowAct A M'.X p) ▷ symPow A M.X (q + 1)) ≫
      ((α_ M.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        ((β_ M.X (symPow A M'.X (p + 1))).hom ▷
          symPow A M.X (q + 1)) ≫
        (α_ (symPow A M'.X (p + 1)) M.X
          (symPow A M.X (q + 1))).hom ≫
        (symPow A M'.X (p + 1) ◁ symInsL A M.X q)) =
      ((α_ M.X (symPow A M'.X (p + 1) ⊗ A)
          (symPow A M.X (q + 1))).inv ≫
        ((β_ M.X (symPow A M'.X (p + 1) ⊗ A)).hom ▷
          symPow A M.X (q + 1)) ≫
        (α_ (symPow A M'.X (p + 1) ⊗ A) M.X
          (symPow A M.X (q + 1))).hom ≫
        ((symPow A M'.X (p + 1) ⊗ A) ◁ symInsL A M.X q)) ≫
        (((β_ (symPow A M'.X (p + 1)) A).hom ≫
          symPowAct A M'.X p) ▷ symPow A M.X (q + 2)) :=
    legM_cross_snd_aux
      ((β_ (symPow A M'.X (p + 1)) A).hom ≫ symPowAct A M'.X p)
      (symInsL A M.X q)
  have hN : M.X ◁ ((α_ (symPow A M'.X (p + 1)) A
          (symPow A M.X (q + 1))).hom ≫
        (symPow A M'.X (p + 1) ◁ symPowAct A M.X q)) ≫
      ((α_ M.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        ((β_ M.X (symPow A M'.X (p + 1))).hom ▷
          symPow A M.X (q + 1)) ≫
        (α_ (symPow A M'.X (p + 1)) M.X
          (symPow A M.X (q + 1))).hom ≫
        (symPow A M'.X (p + 1) ◁ symInsL A M.X q)) =
      ((α_ M.X (symPow A M'.X (p + 1) ⊗ A)
          (symPow A M.X (q + 1))).inv ≫
        ((β_ M.X (symPow A M'.X (p + 1) ⊗ A)).hom ▷
          symPow A M.X (q + 1)) ≫
        (α_ (symPow A M'.X (p + 1) ⊗ A) M.X
          (symPow A M.X (q + 1))).hom ≫
        ((symPow A M'.X (p + 1) ⊗ A) ◁ symInsL A M.X q)) ≫
        ((α_ (symPow A M'.X (p + 1)) A
            (symPow A M.X (q + 2))).hom ≫
          (symPow A M'.X (p + 1) ◁
            symPowAct A M.X (q + 1))) :=
    legN_cross_snd_aux (symPowAct A M.X q)
      (symPowAct A M.X (q + 1)) (symInsL A M.X q)
      (symInsL_symPowAct A M.X q)
  have hcond : (((β_ (symPow A M'.X (p + 1)) A).hom ≫
        symPowAct A M'.X p) ▷ symPow A M.X (q + 2)) ≫
      modTensorπ A (symPowMod A M'.X p)
        (symPowMod A M.X (q + 1)) =
      ((α_ (symPow A M'.X (p + 1)) A
          (symPow A M.X (q + 2))).hom ≫
        (symPow A M'.X (p + 1) ◁ symPowAct A M.X (q + 1))) ≫
      modTensorπ A (symPowMod A M'.X p)
        (symPowMod A M.X (q + 1)) :=
    modTensor_condition A (symPowMod A M'.X p)
      (symPowMod A M.X (q + 1))
  erw [reassoc_of% hM, reassoc_of% hN, hcond]
  repeat' erw [Category.assoc]

/-- **Insertion into the second slot of a two-index stage**: the
module is carried past the first symmetric power and enters the
second, descended through the module-tensor coequalizer. -/
noncomputable def chainInsQ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (p q : ℕ) :
    M.X ⊗ chainStage2 A M M' p q ⟶
      chainStage2 A M M' p (q + 1) :=
  modTensorWhiskerDesc A (symPowMod A M'.X p) (symPowMod A M.X q)
    M.X
    ((α_ M.X (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1))).inv ≫
      ((β_ M.X (symPow A M'.X (p + 1))).hom ▷
        symPow A M.X (q + 1)) ≫
      (α_ (symPow A M'.X (p + 1)) M.X
        (symPow A M.X (q + 1))).hom ≫
      (symPow A M'.X (p + 1) ◁ symInsL A M.X q) ≫
      modTensorπ A (symPowMod A M'.X p)
        (symPowMod A M.X (q + 1)))
    (chainInsQ_cond A M M' p q)

/-- Defining equation of the second-slot insertion. -/
@[reassoc]
theorem whiskerLeft_π_chainInsQ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (p q : ℕ) :
    M.X ◁ modTensorπ A (symPowMod A M'.X p)
        (symPowMod A M.X q) ≫ chainInsQ A M M' p q =
      (α_ M.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        ((β_ M.X (symPow A M'.X (p + 1))).hom ▷
          symPow A M.X (q + 1)) ≫
        (α_ (symPow A M'.X (p + 1)) M.X
          (symPow A M.X (q + 1))).hom ≫
        (symPow A M'.X (p + 1) ◁ symInsL A M.X q) ≫
        modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X (q + 1)) :=
  whiskerLeft_modTensorπ_whiskerDesc A _ _ M.X _ _

end InsQ

/-! ## The insertion against the multiplication -/

section InsMul

/-- Arity transports compose. -/
theorem symPowCast_symPowCast
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] [Linear ℂ D]
    (A : D) [MonObj A] (X : D) [ModObj A X]
    {a b c : ℕ} (h : a = b)
    (h' : b = c) :
    symPowCast A X h ≫ symPowCast A X h' =
      symPowCast A X (h.trans h') := by
  subst h h'
  have h1 : symPowCast A X (rfl : a = a) = 𝟙 (symPow A X a) :=
    rfl
  rw [h1, Category.id_comp]

/-- An arity transport of the first factor passes the symmetric
multiplication. -/
private theorem symMul_cast_left
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (X : D) [ModObj A X]
    {a b : ℕ} (h : a = b) (r : ℕ) :
    (symPowCast A X h ▷ symPow A X r) ≫ symMul A X b r =
      symMul A X a r ≫
        symPowCast A X (by omega : a + r = b + r) := by
  subst h
  have h1 : symPowCast A X (rfl : a = a) = 𝟙 (symPow A X a) :=
    rfl
  have h2 : symPowCast A X (by omega : a + r = a + r) =
      𝟙 (symPow A X (a + r)) := rfl
  rw [h1, h2, MonoidalCategory.id_whiskerRight,
    Category.id_comp, Category.comp_id]

/-- **The insertion is associative against the multiplication**:
inserting and multiplying is multiplying and inserting into the
product, up to the arity transport. -/
theorem symInsL_symMul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (X : D) [ModObj A X]
    (m n : ℕ) :
    (symInsL A X m ▷ symPow A X (n + 1)) ≫
        symMul A X (m + 2) (n + 1) =
      (α_ X (symPow A X (m + 1)) (symPow A X (n + 1))).hom ≫
        (X ◁ symMul A X (m + 1) (n + 1)) ≫
        symInsL A X (m + 1 + n) ≫
        symPowCast A X
          (by omega : m + 1 + n + 2 = m + 2 + (n + 1)) := by
  have hcl : (symPowCast A X
        (by omega : 1 + (m + 1) = m + 2) ▷
        symPow A X (n + 1)) ≫ symMul A X (m + 2) (n + 1) =
      symMul A X (1 + (m + 1)) (n + 1) ≫
        symPowCast A X
          (by omega : 1 + (m + 1) + (n + 1) = m + 2 + (n + 1)) :=
    symMul_cast_left A X (by omega : 1 + (m + 1) = m + 2) (n + 1)
  have hassoc := symMul_assoc A X 1 (m + 1) (n + 1)
  rw [symInsL, symInsL]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [hcl, reassoc_of% hassoc, symPowCast_symPowCast,
    symPowCast_symPowCast,
    associator_naturality_left_assoc, ← whisker_exchange_assoc]
  rfl

end InsMul

end RS
