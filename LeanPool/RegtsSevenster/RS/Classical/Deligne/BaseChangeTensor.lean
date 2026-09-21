/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModAssoc
import LeanPool.RegtsSevenster.RS.Classical.Deligne.KeyLemma

/-!
# Base change and the tensor product of modules

The change-of-rings collapse: over a base morphism, the relative
tensor of a module over the new base with an induced module
collapses to the relative tensor over the old base of the
restricted module.  Together with the associativity of the
relative tensor this yields the projection formula: base change
commutes with the tensor product of modules.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- Scalar restriction of a module along the base morphism. -/
noncomputable def restrictMod
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (B : D)
    [MonObj B] (φ : A ⟶ B) [IsMonHom φ] (P : Mod D B) :
    Mod D A := (Mod.comap φ).obj P

@[simp] lemma restrictMod_X
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (B : D)
    [MonObj B] (φ : A ⟶ B) [IsMonHom φ] (P : Mod D B) :
    (restrictMod A B φ P).X = P.X := rfl

/-- The restricted right action acts through the base
morphism. -/
lemma actRight_restrictMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (B : D) [MonObj B] (φ : A ⟶ B) [IsMonHom φ] (P : Mod D B) :
    actRight A (restrictMod A B φ P).X =
      (P.X ◁ φ) ≫ actRight B P.X := by
  show (β_ P.X A).hom ≫ (φ ▷ P.X) ≫ actLeft B P.X =
    (P.X ◁ φ) ≫ (β_ P.X B).hom ≫ actLeft B P.X
  rw [← BraidedCategory.braiding_naturality_right_assoc]

/-- The projection of the restricted-module tensor, retyped at
the carrier of the unrestricted module.  All statements of this
development use this spelling, so that goals remain type-correct
at the instances transparency level. -/
noncomputable def restrictπ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (B : D) [MonObj B] (φ : A ⟶ B)
    [IsMonHom φ] (P : Mod D B) (N : Mod D A) : P.X ⊗ N.X ⟶
    modTensor A (restrictMod A B φ P) N :=
  modTensorπ A (restrictMod A B φ P) N

/-- The balance of the restricted-module tensor, in the retyped
spelling: sliding the base through the base morphism on the
module side is acting on the second factor. -/
theorem restrictπ_cond
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (B : D) [MonObj B] (φ : A ⟶ B)
    [IsMonHom φ] (P : Mod D B) (N : Mod D A) :
    (((P.X ◁ φ) ≫ actRight B P.X) ▷ N.X) ≫
        restrictπ A B φ P N =
      (α_ P.X A N.X).hom ≫ (P.X ◁ actLeft A N.X) ≫
        restrictπ A B φ P N := by
  have h := modTensor_condition A (restrictMod A B φ P) N
  rw [modTensorLegM, modTensorLegN, Category.assoc,
    actRight_restrictMod] at h
  exact h

/-- The cover of the collapse: act the middle base into the
module and project. -/
noncomputable def collapseCover
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (B : D) [MonObj B] (φ : A ⟶ B)
    [IsMonHom φ] (P : Mod D B) (N : Mod D A) : P.X ⊗ (B ⊗ N.X) ⟶
    modTensor A (restrictMod A B φ P) N :=
  (α_ P.X B N.X).inv ≫ (actRight B P.X ▷ N.X) ≫
    restrictπ A B φ P N

/-- The cover of the collapse coequalizes the whiskered balance
of the induced module: the base slides onto the module through
the associativity of the right action and the balance of the
target. -/
theorem collapseCover_cond
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (B : D) [MonObj B]
    [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ] (P : Mod D B) (N : Mod D A) :
    (P.X ◁ modTensorLegM A (restrictRegular φ) N) ≫
        collapseCover A B φ P N =
      (P.X ◁ modTensorLegN A (restrictRegular φ) N) ≫
        collapseCover A B φ P N := by
  have h1 : modTensorLegM A (restrictRegular φ) N =
      ((B ◁ φ) ≫ μ[B]) ▷ N.X :=
    congrArg (· ▷ N.X) (actRight_restrictRegular φ)
  have h2 : modTensorLegN A (restrictRegular φ) N =
      (α_ B A N.X).hom ≫ (B ◁ actLeft A N.X) := rfl
  have hAA : (P.X ◁ μ[B]) ≫ actRight B P.X =
      (α_ P.X B B).inv ≫ (actRight B P.X ▷ B) ≫
        actRight B P.X := by
    rw [actRight_actRight, Iso.inv_hom_id_assoc]
  rw [h1, h2, collapseCover]
  conv_lhs => rw [associator_inv_naturality_middle_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    hAA]
  conv_rhs => rw [MonoidalCategory.whiskerLeft_comp,
    Category.assoc, associator_inv_naturality_right_assoc]
  simp only [MonoidalCategory.comp_whiskerRight,
    Category.assoc]
  have hslide : ((P.X ◁ (B ◁ φ)) ▷ N.X) ≫
      ((α_ P.X B B).inv ▷ N.X) =
      ((α_ P.X B A).inv ▷ N.X) ≫
        (((P.X ⊗ B) ◁ φ) ▷ N.X) := by
    rw [← MonoidalCategory.comp_whiskerRight,
      ← MonoidalCategory.comp_whiskerRight,
      associator_inv_naturality_right]
  have hexch : (((P.X ⊗ B) ◁ φ) ▷ N.X) ≫
      ((actRight B P.X ▷ B) ▷ N.X) =
      ((actRight B P.X ▷ A) ▷ N.X) ≫
        ((P.X ◁ φ) ▷ N.X) := by
    rw [← MonoidalCategory.comp_whiskerRight,
      ← MonoidalCategory.comp_whiskerRight,
      whisker_exchange]
  rw [← Category.assoc ((P.X ◁ (B ◁ φ)) ▷ N.X), hslide]
  rw [Category.assoc, ← Category.assoc
    (((P.X ⊗ B) ◁ φ) ▷ N.X), hexch]
  rw [Category.assoc, ← Category.assoc ((P.X ◁ φ) ▷ N.X),
    ← MonoidalCategory.comp_whiskerRight, restrictπ_cond]
  rw [associator_naturality_left_assoc,
    ← whisker_exchange_assoc]
  rw [reassoc_of% (show (α_ P.X (B ⊗ A) N.X).inv ≫
    ((α_ P.X B A).inv ▷ N.X) ≫ (α_ (P.X ⊗ B) A N.X).hom =
    (P.X ◁ (α_ B A N.X).hom) ≫ (α_ P.X B (A ⊗ N.X)).inv
    from by monoidal)]

/-- The half-descended collapse, on the induced module. -/
noncomputable def collapseMid
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ] (P : Mod D B) (N : Mod D A) :
    P.X ⊗ baseChange φ N ⟶
      modTensor A (restrictMod A B φ P) N :=
  modTensorWhiskerDesc A (restrictRegular φ) N P.X
    (collapseCover A B φ P N) (collapseCover_cond A B φ P N)

/-- Defining equation of the half-descended collapse. -/
@[reassoc (attr := simp)]
theorem whiskerLeft_collapseMid
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ] (P : Mod D B) (N : Mod D A) :
    (P.X ◁ modTensorπ A (restrictRegular φ) N) ≫
        collapseMid A B φ P N = collapseCover A B φ P N :=
  whiskerLeft_modTensorπ_whiskerDesc A _ N P.X _ _

/-- The half-descended collapse coequalizes the outer balance:
sliding the base between the module and the induced factor is
absorbed by the associativity of the right action. -/
theorem collapseMid_cond
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ] (P : Mod D B) (N : Mod D A) :
    modTensorLegM B P (baseChangeMod φ N) ≫
        collapseMid A B φ P N =
      modTensorLegN B P (baseChangeMod φ N) ≫
        collapseMid A B φ P N := by
  apply modTensor_whisker_hom_ext A (restrictRegular φ) N
    (P.X ⊗ B)
  have hL : ((P.X ⊗ B) ◁
      modTensorπ A (restrictRegular φ) N) ≫
      modTensorLegM B P (baseChangeMod φ N) ≫
        collapseMid A B φ P N =
      (actRight B P.X ▷ (B ⊗ N.X)) ≫
        collapseCover A B φ P N := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (whisker_exchange (actRight B P.X)
        (modTensorπ A (restrictRegular φ) N)) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact whisker_eq _ (whiskerLeft_collapseMid A B φ P N)
  have hR : ((P.X ⊗ B) ◁
      modTensorπ A (restrictRegular φ) N) ≫
      modTensorLegN B P (baseChangeMod φ N) ≫
        collapseMid A B φ P N =
      (α_ P.X B (B ⊗ N.X)).hom ≫
        (P.X ◁ ((α_ B B N.X).inv ≫ (μ[B] ▷ N.X))) ≫
        collapseCover A B φ P N := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker (Category.assoc _ _ _).symm
      _) ?_
    refine Eq.trans (eq_whisker (eq_whisker
      (associator_naturality_right P.X B
        (modTensorπ A (restrictRegular φ) N)) _) _) ?_
    refine Eq.trans (eq_whisker (Category.assoc _ _ _) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine whisker_eq _ ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp P.X _ _).symm _) ?_
    refine Eq.trans (eq_whisker (congrArg (fun t => P.X ◁ t)
      (whiskerLeft_modTensorπ_baseChangeAct φ N)) _) ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp P.X _ _) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact whisker_eq _ (whiskerLeft_collapseMid A B φ P N)
  refine hL.trans (Eq.trans ?_ hR.symm)
  rw [collapseCover]
  have hAA : (P.X ◁ μ[B]) ≫ actRight B P.X =
      (α_ P.X B B).inv ≫ (actRight B P.X ▷ B) ≫
        actRight B P.X := by
    rw [actRight_actRight, Iso.inv_hom_id_assoc]
  conv_lhs => rw [associator_inv_naturality_left_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    actRight_actRight]
  conv_rhs => rw [MonoidalCategory.whiskerLeft_comp,
    Category.assoc, associator_inv_naturality_middle_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc, hAA]
  simp only [MonoidalCategory.comp_whiskerRight,
    Category.assoc]
  rw [reassoc_of% (show (α_ (P.X ⊗ B) B N.X).inv ≫
    ((α_ P.X B B).hom ▷ N.X) =
    (α_ P.X B (B ⊗ N.X)).hom ≫ (P.X ◁ (α_ B B N.X).inv) ≫
      (α_ P.X (B ⊗ B) N.X).inv
    from by monoidal)]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, hAA]
  simp only [MonoidalCategory.comp_whiskerRight,
    Category.assoc]

/-- **The collapse**: the relative tensor over the new base with
an induced module collapses onto the relative tensor over the old
base of the restricted module. -/
noncomputable def collapseHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ] (P : Mod D B) (N : Mod D A) :
    modTensor B P (baseChangeMod φ N) ⟶
      modTensor A (restrictMod A B φ P) N :=
  modTensorDesc B P (baseChangeMod φ N)
    (collapseMid A B φ P N) (collapseMid_cond A B φ P N)

/-- Defining equation of the collapse. -/
@[reassoc (attr := simp)]
theorem modTensorπ_collapseHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ] (P : Mod D B) (N : Mod D A) :
    modTensorπ B P (baseChangeMod φ N) ≫
        collapseHom A B φ P N = collapseMid A B φ P N :=
  modTensorπ_desc B P (baseChangeMod φ N) _ _

/-- The unit insertion into the induced module. -/
noncomputable def unitSlot
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (B : D) [MonObj B] (φ : A ⟶ B)
    [IsMonHom φ] (N : Mod D A) : N.X ⟶ baseChange φ N :=
  (λ_ N.X).inv ≫ (η[B] ▷ N.X) ≫
    modTensorπ A (restrictRegular φ) N

/-- Acting before the unit insertion is acting through the base
morphism after it: the balance of the induced module at the
unit. -/
theorem actLeft_unitSlot
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (B : D) [MonObj B]
    [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ] (N : Mod D A) :
    actLeft A N.X ≫ unitSlot A B φ N =
      (φ ▷ N.X) ≫ modTensorπ A (restrictRegular φ) N := by
  have h := modTensor_condition A (restrictRegular φ) N
  have h1 : modTensorLegM A (restrictRegular φ) N =
      ((B ◁ φ) ≫ μ[B]) ▷ N.X :=
    congrArg (· ▷ N.X) (actRight_restrictRegular φ)
  have h2 : modTensorLegN A (restrictRegular φ) N =
      (α_ B A N.X).hom ≫ (B ◁ actLeft A N.X) := rfl
  rw [h1, h2] at h
  have hi := congrArg (fun t =>
    (((λ_ A).inv ≫ (η[B] ▷ A)) ▷ N.X) ≫ t) h
  simp only [Category.assoc] at hi
  rw [← MonoidalCategory.comp_whiskerRight_assoc] at hi
  rw [show ((λ_ A).inv ≫ (η[B] ▷ A)) ≫ (B ◁ φ) ≫ μ[B] =
    φ ≫ (λ_ B).inv ≫ (η[B] ▷ B) ≫ μ[B] from by
      simp only [Category.assoc]
      rw [← whisker_exchange_assoc,
        leftUnitor_inv_naturality_assoc]] at hi
  rw [MonObj.one_mul, Iso.inv_hom_id, Category.comp_id] at hi
  have hR2 : (((λ_ A).inv ≫ (η[B] ▷ A)) ▷ N.X) ≫
      (α_ B A N.X).hom ≫ (B ◁ actLeft A N.X) ≫
      modTensorπ A (restrictRegular φ) N =
      actLeft A N.X ≫ unitSlot A B φ N := by
    rw [MonoidalCategory.comp_whiskerRight, Category.assoc,
      associator_naturality_left_assoc,
      ← whisker_exchange_assoc]
    rw [reassoc_of% (show ((λ_ A).inv ▷ N.X) ≫
      (α_ (𝟙_ D) A N.X).hom = (λ_ (A ⊗ N.X)).inv
      from by monoidal)]
    rw [← leftUnitor_inv_naturality_assoc, unitSlot]
    rfl
  exact (hi.trans hR2).symm

/-- Acting on the unit insertion is the projection: the inserted
unit is absorbed by the action. -/
theorem whiskerLeft_unitSlot_baseChangeAct
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ] (N : Mod D A) :
    (B ◁ unitSlot A B φ N) ≫ baseChangeAct φ N =
      modTensorπ A (restrictRegular φ) N := by
  have hcoh : ((B ◁ (λ_ N.X).inv) ≫ (B ◁ (η[B] ▷ N.X))) ≫
      ((α_ B B N.X).inv ≫ (μ[B] ▷ N.X)) = 𝟙 (B ⊗ N.X) := by
    simp only [Category.assoc]
    rw [associator_inv_naturality_middle_assoc,
      ← MonoidalCategory.comp_whiskerRight,
      MonObj.mul_one]
    monoidal
  erw [unitSlot, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    Category.assoc]
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (whiskerLeft_modTensorπ_baseChangeAct φ N))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker hcoh _) ?_
  exact Category.id_comp _

/-- The projection of the new-base tensor, retyped at the
induced-module carrier. -/
noncomputable def bcπ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ] (P : Mod D B) (N : Mod D A) : P.X ⊗ baseChange φ N ⟶
    modTensor B P (baseChangeMod φ N) :=
  modTensorπ B P (baseChangeMod φ N)

/-- The balance of the new-base tensor, in the retyped
spelling. -/
theorem bcπ_cond [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ] (P : Mod D B) (N : Mod D A) :
    (actRight B P.X ▷ baseChange φ N) ≫ bcπ A B φ P N =
      (α_ P.X B (baseChange φ N)).hom ≫
        (P.X ◁ baseChangeAct φ N) ≫ bcπ A B φ P N := by
  have h := modTensor_condition B P (baseChangeMod φ N)
  rw [modTensorLegM, modTensorLegN, Category.assoc] at h
  exact h

/-- The cover of the inverse collapse: insert the unit of the
new base and project. -/
noncomputable def collapseInvCover
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ] (P : Mod D B) (N : Mod D A) : P.X ⊗ N.X ⟶
    modTensor B P (baseChangeMod φ N) :=
  (P.X ◁ unitSlot A B φ N) ≫ bcπ A B φ P N

/-- The cover of the inverse collapse coequalizes the balance of
the restricted-module tensor: the old base enters the induced
factor through the unit insertion. -/
theorem collapseInvCover_cond
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ] (P : Mod D B) (N : Mod D A) :
    modTensorLegM A (restrictMod A B φ P) N ≫
        collapseInvCover A B φ P N =
      modTensorLegN A (restrictMod A B φ P) N ≫
        collapseInvCover A B φ P N := by
  have h1 : modTensorLegM A (restrictMod A B φ P) N =
      ((P.X ◁ φ) ≫ actRight B P.X) ▷ N.X :=
    congrArg (· ▷ N.X) (actRight_restrictMod A B φ P)
  have h2 : modTensorLegN A (restrictMod A B φ P) N =
      (α_ P.X A N.X).hom ≫ (P.X ◁ actLeft A N.X) := rfl
  have hin : (A ◁ unitSlot A B φ N) ≫
      ((φ ▷ baseChange φ N) ≫ baseChangeAct φ N) =
      actLeft A N.X ≫ unitSlot A B φ N := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (whisker_exchange φ (unitSlot A B φ N)) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (whiskerLeft_unitSlot_baseChangeAct A B φ N)) ?_
    exact (actLeft_unitSlot A B φ N).symm
  rw [h1, h2, collapseInvCover]
  have hstep : (((P.X ◁ φ) ≫ actRight B P.X) ▷
      baseChange φ N) ≫ bcπ A B φ P N =
      (α_ P.X A (baseChange φ N)).hom ≫
        (P.X ◁ ((φ ▷ baseChange φ N) ≫
          baseChangeAct φ N)) ≫ bcπ A B φ P N := by
    refine Eq.trans (eq_whisker
      (MonoidalCategory.comp_whiskerRight _ _ _) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (bcπ_cond A B φ P N)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (associator_naturality_middle P.X φ
        (baseChange φ N)) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine whisker_eq _ ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact eq_whisker
      (MonoidalCategory.whiskerLeft_comp P.X _ _).symm _
  have hstep2 : ((P.X ⊗ A) ◁ unitSlot A B φ N) ≫
      (α_ P.X A (baseChange φ N)).hom ≫
      (P.X ◁ ((φ ▷ baseChange φ N) ≫
        baseChangeAct φ N)) ≫ bcπ A B φ P N =
      (α_ P.X A N.X).hom ≫
        (P.X ◁ (actLeft A N.X ≫ unitSlot A B φ N)) ≫
        bcπ A B φ P N := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (associator_naturality_right P.X A
        (unitSlot A B φ N)) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine whisker_eq _ ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp P.X _ _).symm _) ?_
    exact eq_whisker (congrArg (fun t => P.X ◁ t) hin) _
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (whisker_exchange
    ((P.X ◁ φ) ≫ actRight B P.X)
    (unitSlot A B φ N)).symm _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ hstep) ?_
  refine Eq.trans hstep2 ?_
  refine Eq.symm ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine whisker_eq _ ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (MonoidalCategory.whiskerLeft_comp P.X _ _).symm _) ?_
  exact Eq.refl _

/-- **The inverse collapse**: descend the unit insertion. -/
noncomputable def collapseInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ] (P : Mod D B) (N : Mod D A) :
    modTensor A (restrictMod A B φ P) N ⟶
      modTensor B P (baseChangeMod φ N) :=
  modTensorDesc A (restrictMod A B φ P) N
    (collapseInvCover A B φ P N)
    (collapseInvCover_cond A B φ P N)

/-- Defining equation of the inverse collapse. -/
@[reassoc (attr := simp)]
theorem restrictπ_collapseInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ] (P : Mod D B) (N : Mod D A) :
    restrictπ A B φ P N ≫ collapseInv A B φ P N =
      collapseInvCover A B φ P N :=
  modTensorπ_desc A (restrictMod A B φ P) N _ _

/-- The inserted unit is absorbed by the half-descended
collapse. -/
theorem whiskerLeft_unitSlot_collapseMid
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ] (P : Mod D B) (N : Mod D A) :
    (P.X ◁ unitSlot A B φ N) ≫ collapseMid A B φ P N =
      restrictπ A B φ P N := by
  have hcoh : (P.X ◁ (λ_ N.X).inv) ≫
      ((P.X ◁ (η[B] ▷ N.X)) ≫
        ((α_ P.X B N.X).inv ≫ (actRight B P.X ▷ N.X))) =
      𝟙 (P.X ⊗ N.X) := by
    rw [associator_inv_naturality_middle_assoc,
      ← MonoidalCategory.comp_whiskerRight, actRight_one]
    monoidal
  erw [unitSlot, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    Category.assoc]
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (whiskerLeft_collapseMid A B φ P N))) ?_
  rw [collapseCover]
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (Category.assoc _ _ _).symm)) ?_
  refine Eq.trans (whisker_eq _
    (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker hcoh _) ?_
  exact Category.id_comp _

/-- The collapse retracts the inverse collapse. -/
@[reassoc (attr := simp)]
theorem collapseInv_collapseHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ] (P : Mod D B) (N : Mod D A) :
    collapseInv A B φ P N ≫ collapseHom A B φ P N =
      𝟙 (modTensor A (restrictMod A B φ P) N) := by
  apply modTensor_hom_ext A (restrictMod A B φ P) N
  rw [Category.comp_id]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (restrictπ_collapseInv A B φ P N) _) ?_
  rw [collapseInvCover]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _
    (modTensorπ_collapseHom A B φ P N)) ?_
  exact whiskerLeft_unitSlot_collapseMid A B φ P N

/-- The inverse collapse retracts the collapse. -/
@[reassoc (attr := simp)]
theorem collapseHom_collapseInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ] (P : Mod D B) (N : Mod D A) :
    collapseHom A B φ P N ≫ collapseInv A B φ P N =
      𝟙 (modTensor B P (baseChangeMod φ N)) := by
  apply modTensor_hom_ext B P (baseChangeMod φ N)
  rw [Category.comp_id]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (modTensorπ_collapseHom A B φ P N) _) ?_
  apply modTensor_whisker_hom_ext A (restrictRegular φ) N P.X
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (whiskerLeft_collapseMid A B φ P N) _) ?_
  rw [collapseCover]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (restrictπ_collapseInv A B φ P N))) ?_
  rw [collapseInvCover]
  refine Eq.trans (whisker_eq _
    (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker
    (whisker_exchange (actRight B P.X)
      (unitSlot A B φ N)).symm _)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (bcπ_cond A B φ P N))) ?_
  refine Eq.trans (whisker_eq _
    (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker
    (associator_naturality_right P.X B
      (unitSlot A B φ N)) _)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (Iso.inv_hom_id _) _) ?_
  refine Eq.trans (Category.id_comp _) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (MonoidalCategory.whiskerLeft_comp P.X _ _).symm _) ?_
  exact eq_whisker (congrArg (fun t => P.X ◁ t)
    (whiskerLeft_unitSlot_baseChangeAct A B φ N)) _

/-- **The change-of-rings collapse**, packaged. -/
noncomputable def collapseIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ] (P : Mod D B) (N : Mod D A) :
    modTensor B P (baseChangeMod φ N) ≅
      modTensor A (restrictMod A B φ P) N where
  hom := collapseHom A B φ P N
  inv := collapseInv A B φ P N
  hom_inv_id := collapseHom_collapseInv A B φ P N
  inv_hom_id := collapseInv_collapseHom A B φ P N

/-- The restricted action of a base change is the descended
module action on the relative tensor. -/
theorem actLeft_restrict_baseChange
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ]
    (M : Mod D A) :
    (φ ▷ baseChange φ M) ≫ baseChangeAct φ M =
      modTensorAct A (restrictRegular φ) M := by
  apply modTensor_whisker_hom_ext A (restrictRegular φ) M A
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (whisker_exchange φ
    (modTensorπ A (restrictRegular φ) M)) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _
    (whiskerLeft_modTensorπ_baseChangeAct φ M)) ?_
  refine Eq.symm ?_
  refine Eq.trans
    (whiskerLeft_modTensorπ_act A (restrictRegular φ) M) ?_
  have hact : (letI := ModObj.regular B;
      letI := Mod.scalarRestriction φ B; actLeft A B) =
      (φ ▷ B) ≫ μ[B] := rfl
  refine Eq.trans (eq_whisker (whisker_eq _
    (congrArg (· ▷ M.X) hact)) _) ?_
  rw [MonoidalCategory.comp_whiskerRight]
  refine Eq.trans (eq_whisker
    (Category.assoc _ _ _).symm _) ?_
  refine Eq.trans (eq_whisker (eq_whisker
    (associator_inv_naturality_left φ B M.X).symm _) _) ?_
  exact Eq.trans (eq_whisker (Category.assoc
      (φ ▷ (B ⊗ M.X)) (α_ B B M.X).inv (μ[B] ▷ M.X))
    (modTensorπ A (restrictRegular φ) M))
    (Category.assoc (φ ▷ (B ⊗ M.X))
      ((α_ B B M.X).inv ≫ (μ[B] ▷ M.X))
      (modTensorπ A (restrictRegular φ) M))

/-- Bundled modules with the same carrier and the same action
are equal. -/
private theorem mod_ext [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    {X : D} (i₁ i₂ : ModObj A X)
    (h : i₁.smul = i₂.smul) :
    (letI := i₁; (⟨X⟩ : Mod D A)) =
      (letI := i₂; (⟨X⟩ : Mod D A)) := by
  cases i₁; cases i₂
  cases h
  rfl

/-- **The restricted base change is the module tensor with the
restricted regular module.** -/
theorem restrictMod_baseChange_eq
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ]
    (M : Mod D A) :
    restrictMod A B φ (baseChangeMod φ M) =
      modTensorMod A (restrictRegular φ) M :=
  mod_ext A _ _ (actLeft_restrict_baseChange A B φ M)

/-- **The projection formula**: the relative tensor over the new
base of two base changes is the base change of the relative
tensor. -/
noncomputable def projFormula
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ]
    (M N : Mod D A) :
    modTensor B (baseChangeMod φ M) (baseChangeMod φ N) ≅
      baseChange φ (modTensorMod A M N) :=
  (collapseIso A B φ (baseChangeMod φ M) N).trans
    ((eqToIso (congrArg (fun P => modTensor A P N)
      (restrictMod_baseChange_eq A B φ M))).trans
      (modTensorAssocIso A (restrictRegular φ) M N))

section Datum

/-- **The base change of the pairing**: collapse, apply the
pairing under the base, and collapse the regular module. -/
noncomputable def baseChangePair
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M') :
    modTensor B (baseChangeMod φ M')
      (baseChangeMod φ M) ⟶ B :=
  (projFormula A B φ M' M).hom ≫
    modTensorMap A (𝟙 (restrictRegular φ)) (d.pairMod) ≫
    (modTensorUnitRight A (restrictRegular φ)).hom

/-- **The base change of the copairing.** -/
noncomputable def baseChangeCopair
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M') :
    B ⟶ modTensor B (baseChangeMod φ M)
      (baseChangeMod φ M') :=
  (modTensorUnitRight A (restrictRegular φ)).inv ≫
    modTensorMap A (𝟙 (restrictRegular φ)) (d.copairMod) ≫
    (projFormula A B φ M M').inv

end Datum

end RS
