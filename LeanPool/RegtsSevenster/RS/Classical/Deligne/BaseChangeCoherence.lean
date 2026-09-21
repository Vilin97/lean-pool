/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.BaseChangeDatum
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SandwichRetract

/-!
# Coherence of the base-change structure map

The projection formula is compatible with the right unit
collapse: contracting the regular factor before or after the
base change gives the same map.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **The cast leg is invisible on projections**: the
restricted projection, transported along the identification of
the restricted base change, is the projection of the relative
tensor. -/
theorem restrictπ_cast
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ]
    (M N : Mod D A) :
    restrictπ A B φ (baseChangeMod φ M) N ≫
        eqToHom (congrArg (fun R => modTensor A R N)
          (restrictMod_baseChange_eq A B φ M)) =
      modTensorπ A
        (modTensorMod A (restrictRegular φ) M) N := by
  have h := restrictMod_baseChange_eq A B φ M
  have key : ∀ (P Q : Mod D A) (hPQ : P = Q),
      modTensorπ A P N ≫
          eqToHom (congrArg (fun R => modTensor A R N) hPQ) =
        eqToHom (congrArg (fun R => R.X ⊗ N.X) hPQ) ≫
          modTensorπ A Q N := by
    intro P Q hPQ
    subst hPQ
    simp
  refine Eq.trans (key _ _ h) ?_
  refine Eq.trans (eq_whisker (show
    eqToHom (congrArg (fun R : Mod D A => R.X ⊗ N.X) h) =
      𝟙 ((baseChangeMod φ M).X ⊗ N.X) from rfl) _) ?_
  exact Category.id_comp _

/-- **The projection formula on the cover**: composing the
structure map with the inner projection unwinds to the right
action of the new base followed by the half-descended module
associator, with no transport left in the way. -/
theorem projFormula_cover
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ]
    (M N : Mod D A) :
    ((baseChangeMod φ M).X ◁
        modTensorπ A (restrictRegular φ) N) ≫
        modTensorπ B (baseChangeMod φ M) (baseChangeMod φ N) ≫
        (projFormula A B φ M N).hom =
      (α_ (baseChangeMod φ M).X B N.X).inv ≫
        (actRight B (baseChangeMod φ M).X ▷ N.X) ≫
        modTensorAssocMid A (restrictRegular φ) M N := by
  have hpf : (projFormula A B φ M N).hom =
      collapseHom A B φ (baseChangeMod φ M) N ≫
        eqToHom (congrArg (fun P => modTensor A P N)
          (restrictMod_baseChange_eq A B φ M)) ≫
        modTensorAssocHom A (restrictRegular φ) M N := rfl
  have hmid : ∀ {Z : D}
      (h : modTensor A (restrictMod A B φ
        (baseChangeMod φ M)) N ⟶ Z),
      ((baseChangeMod φ M).X ◁
          modTensorπ A (restrictRegular φ) N) ≫
          modTensorπ B (baseChangeMod φ M)
            (baseChangeMod φ N) ≫
          collapseHom A B φ (baseChangeMod φ M) N ≫ h =
        (α_ (baseChangeMod φ M).X B N.X).inv ≫
          (actRight B (baseChangeMod φ M).X ▷ N.X) ≫
          restrictπ A B φ (baseChangeMod φ M) N ≫ h := by
    intro Z h
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
    refine Eq.trans (whisker_eq _ (eq_whisker
      (modTensorπ_collapseHom A B φ
        (baseChangeMod φ M) N) h)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (whiskerLeft_collapseMid A B φ (baseChangeMod φ M) N)
      h) ?_
    rw [collapseCover]
    simp only [Category.assoc]
  rw [hpf]
  refine Eq.trans (hmid _) ?_
  refine whisker_eq _ (whisker_eq _ ?_)
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (restrictπ_cast A B φ M N) _) ?_
  exact modTensorπ_assocHom A (restrictRegular φ) M N

/-- **The module triangle**: reassociating and collapsing the
regular factor on the right is the braided right action on the
relative tensor. -/
theorem modTensorAssocMid_unitRight
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A]
    (P N : Mod D A) :
    modTensorAssocMid A P N (regularMod A) ≫
        modTensorMap A (𝟙 P) (modTensorUnitRightMod A N).hom =
      actRight A (modTensorMod A P N).X := by
  have key : ∀ {Z : D}
      (h : modTensor A P (modTensorMod A N (regularMod A)) ⟶ Z),
      (modTensorπ A P N ▷ (regularMod A).X) ≫
          modTensorAssocMid A P N (regularMod A) ≫ h =
        (α_ P.X N.X A).hom ≫
          (P.X ◁ modTensorπ A N (regularMod A)) ≫
          modTensorπ A P (modTensorMod A N (regularMod A)) ≫
            h := by
    intro Z h
    rw [← Category.assoc, whiskerRight_modTensorπ_assocMid,
      modTensorAssocCover]
    simp only [Category.assoc]
  have tail : modTensorπ A P (modTensorMod A N (regularMod A)) ≫
      modTensorMap A (𝟙 P) (modTensorUnitRightMod A N).hom =
    (P.X ◁ (modTensorUnitRight A N).hom) ≫ modTensorπ A P N := by
    rw [modTensorπ_map, Mod.id_hom',
      MonoidalCategory.id_tensorHom]
    rfl
  have hfold : (P.X ◁ modTensorπ A N (regularMod A)) ≫
      (P.X ◁ (modTensorUnitRight A N).hom) =
    P.X ◁ actRight A N.X := by
    rw [← MonoidalCategory.whiskerLeft_comp,
      modTensorUnitRight_hom, modTensorπ_desc]
  apply modTensor_whiskerR_hom_ext A P N (regularMod A).X
  refine Eq.trans (key _) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ tail)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker hfold _)) ?_
  exact (modTensorπ_actRight A P N).symm

/-- The restricted action on a base change: the `A`-action on the
relative tensor is the `B`-action taken through the base
morphism. -/
theorem actRight_modTensor_restrictRegular
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ]
    (M : Mod D A) :
    actRight A (modTensorMod A (restrictRegular φ) M).X =
      ((baseChangeMod φ M).X ◁ φ) ≫
        actRight B (baseChangeMod φ M).X := by
  have h := actLeft_restrict_baseChange A B φ M
  show (β_ (baseChange φ M) A).hom ≫
    modTensorAct A (restrictRegular φ) M = _
  rw [← h]
  show (β_ (baseChange φ M) A).hom ≫ (φ ▷ baseChange φ M) ≫
      baseChangeAct φ M =
    ((baseChange φ M) ◁ φ) ≫ (β_ (baseChange φ M) B).hom ≫
      baseChangeAct φ M
  rw [← BraidedCategory.braiding_naturality_right_assoc]

/-- **The unit coherence of the projection formula**: collapsing
the regular factor after the base change agrees with collapsing
the base-changed regular module over the new base. -/
theorem projFormula_unitRight
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ]
    (M : Mod D A) :
    (projFormula A B φ M (regularMod A)).hom ≫
        modTensorMap A (𝟙 (restrictRegular φ))
          (modTensorUnitRightMod A M).hom =
      modTensorMap B (𝟙 (baseChangeMod φ M))
          (baseChangeUnitIso A B φ).hom ≫
        (modTensorUnitRight B (baseChangeMod φ M)).hom := by
  have hslide : (α_ (baseChangeMod φ M).X B A).inv ≫
      (actRight B (baseChangeMod φ M).X ▷ A) ≫
      ((baseChangeMod φ M).X ◁ φ) ≫
      actRight B (baseChangeMod φ M).X =
    ((baseChangeMod φ M).X ◁ ((B ◁ φ) ≫ μ[B])) ≫
      actRight B (baseChangeMod φ M).X := by
    rw [← whisker_exchange_assoc]
    rw [actRight_actRight, ← associator_inv_naturality_right_assoc,
      Iso.inv_hom_id_assoc, MonoidalCategory.whiskerLeft_comp]
    simp only [Category.assoc]
  have hright : ((baseChangeMod φ M).X ◁
      modTensorπ A (restrictRegular φ) (regularMod A)) ≫
      modTensorπ B (baseChangeMod φ M)
        (baseChangeMod φ (regularMod A)) ≫
      modTensorMap B (𝟙 (baseChangeMod φ M))
        (baseChangeUnitIso A B φ).hom ≫
      (modTensorUnitRight B (baseChangeMod φ M)).hom =
    ((baseChangeMod φ M).X ◁ ((B ◁ φ) ≫ μ[B])) ≫
      actRight B (baseChangeMod φ M).X := by
    have hmap : modTensorπ B (baseChangeMod φ M)
        (baseChangeMod φ (regularMod A)) ≫
        modTensorMap B (𝟙 (baseChangeMod φ M))
          (baseChangeUnitIso A B φ).hom ≫
        (modTensorUnitRight B (baseChangeMod φ M)).hom =
      ((baseChangeMod φ M).X ◁
          (modTensorUnitRight A (restrictRegular φ)).hom) ≫
        actRight B (baseChangeMod φ M).X := by
      rw [modTensorπ_map_assoc, Mod.id_hom',
        MonoidalCategory.id_tensorHom, modTensorUnitRight_hom,
        modTensorπ_desc]
      rfl
    refine Eq.trans (whisker_eq _ hmap) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine eq_whisker ?_ _
    rw [← MonoidalCategory.whiskerLeft_comp,
      modTensorUnitRight_hom, modTensorπ_desc,
      actRight_restrictRegular]
  apply modTensor_hom_ext
  apply modTensor_whisker_hom_ext A (restrictRegular φ)
    (regularMod A) (baseChangeMod φ M).X
  refine Eq.trans ?_ hright.symm
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (projFormula_cover A B φ M (regularMod A)) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (modTensorAssocMid_unitRight A (restrictRegular φ) M))) ?_
  rw [actRight_modTensor_restrictRegular A B φ M]
  exact hslide

/-- A module map into the regular module intertwines the braided
right action with multiplication. -/
theorem actRight_toRegular
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [IsCommMonObj A]
    (Q : Mod D A) (g : Q ⟶ regularMod A) :
    actRight A Q.X ≫ g.hom = (g.hom ▷ A) ≫ μ[A] := by
  have hlin : actLeft A Q.X ≫ g.hom = (A ◁ g.hom) ≫ μ[A] :=
    g.isModHom.smul_hom
  show ((β_ Q.X A).hom ≫ actLeft A Q.X) ≫ g.hom = _
  rw [Category.assoc, hlin,
    ← BraidedCategory.braiding_naturality_left_assoc,
    IsCommMonObj.mul_comm]

/-- **The module triangle on the left**: reassociating and
collapsing the regular factor in the middle is the collapse of the
leading factor against the balance. -/
theorem modTensorAssocMid_unitLeft
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A]
    (P N : Mod D A) :
    modTensorAssocMid A P (regularMod A) N ≫
        modTensorMap A (𝟙 P) (modTensorUnitLeftMod A N).hom =
      ((modTensorUnitRight A P).hom ▷ N.X) ≫
        modTensorπ A P N := by
  have key : ∀ {Z : D}
      (h : modTensor A P
        (modTensorMod A (regularMod A) N) ⟶ Z),
      (modTensorπ A P (regularMod A) ▷ N.X) ≫
          modTensorAssocMid A P (regularMod A) N ≫ h =
        (α_ P.X A N.X).hom ≫
          (P.X ◁ modTensorπ A (regularMod A) N) ≫
          modTensorπ A P (modTensorMod A (regularMod A) N) ≫
            h := by
    intro Z h
    rw [← Category.assoc, whiskerRight_modTensorπ_assocMid,
      modTensorAssocCover]
    simp only [Category.assoc]
  have tail : modTensorπ A P
      (modTensorMod A (regularMod A) N) ≫
      modTensorMap A (𝟙 P) (modTensorUnitLeftMod A N).hom =
    (P.X ◁ (modTensorUnitLeft A N).hom) ≫ modTensorπ A P N := by
    rw [modTensorπ_map, Mod.id_hom',
      MonoidalCategory.id_tensorHom]
    rfl
  have hfold : (P.X ◁ modTensorπ A (regularMod A) N) ≫
      (P.X ◁ (modTensorUnitLeft A N).hom) =
    P.X ◁ actLeft A N.X := by
    rw [← MonoidalCategory.whiskerLeft_comp,
      modTensorUnitLeft_hom, modTensorπ_desc]
  have hR : (modTensorπ A P (regularMod A) ▷ N.X) ≫
      ((modTensorUnitRight A P).hom ▷ N.X) ≫
        modTensorπ A P N =
    (α_ P.X A N.X).hom ≫ (P.X ◁ actLeft A N.X) ≫
      modTensorπ A P N := by
    rw [← MonoidalCategory.comp_whiskerRight_assoc,
      modTensorUnitRight_hom, modTensorπ_desc]
    have h := modTensor_condition A P N
    rw [modTensorLegM, modTensorLegN, Category.assoc] at h
    exact h
  apply modTensor_whiskerR_hom_ext A P (regularMod A) N.X
  refine Eq.trans (key _) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ tail)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker hfold _)) ?_
  exact hR.symm

/-- **The left unit coherence of the projection formula**:
collapsing the regular factor on the left commutes with the base
change. -/
theorem projFormula_unitLeft
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ]
    (N : Mod D A) :
    (projFormula A B φ (regularMod A) N).hom ≫
        modTensorMap A (𝟙 (restrictRegular φ))
          (modTensorUnitLeftMod A N).hom =
      modTensorMap B (baseChangeUnitIso A B φ).hom
          (𝟙 (baseChangeMod φ N)) ≫
        (modTensorUnitLeft B (baseChangeMod φ N)).hom := by
  have hu : actRight B (baseChangeMod φ (regularMod A)).X ≫
      (modTensorUnitRight A (restrictRegular φ)).hom =
    ((modTensorUnitRight A (restrictRegular φ)).hom ▷ B) ≫
      μ[B] :=
    actRight_toRegular B (baseChangeMod φ (regularMod A))
      (baseChangeUnitIso A B φ).hom
  have hend : ∀ (Y : D) (r : Y ⊗ B ⟶ Y) (uu : Y ⟶ B),
      r ≫ uu = (uu ▷ B) ≫ μ[B] →
      (α_ Y B N.X).inv ≫ (r ▷ N.X) ≫ (uu ▷ N.X) ≫
          modTensorπ A (restrictRegular φ) N =
        (uu ▷ (B ⊗ N.X)) ≫
          ((α_ B B N.X).inv ≫ (μ[B] ▷ N.X)) ≫
            modTensorπ A (restrictRegular φ) N := by
    intro Y r uu hh
    rw [← MonoidalCategory.comp_whiskerRight_assoc, hh,
      MonoidalCategory.comp_whiskerRight]
    simp only [Category.assoc]
    rw [← associator_inv_naturality_left_assoc]
  have hright : ((baseChangeMod φ (regularMod A)).X ◁
      modTensorπ A (restrictRegular φ) N) ≫
      modTensorπ B (baseChangeMod φ (regularMod A))
        (baseChangeMod φ N) ≫
      modTensorMap B (baseChangeUnitIso A B φ).hom
        (𝟙 (baseChangeMod φ N)) ≫
      (modTensorUnitLeft B (baseChangeMod φ N)).hom =
    ((modTensorUnitRight A (restrictRegular φ)).hom ▷
        (B ⊗ N.X)) ≫
      ((α_ B B N.X).inv ≫ (μ[B] ▷ N.X)) ≫
        modTensorπ A (restrictRegular φ) N := by
    have hmap : modTensorπ B (baseChangeMod φ (regularMod A))
        (baseChangeMod φ N) ≫
        modTensorMap B (baseChangeUnitIso A B φ).hom
          (𝟙 (baseChangeMod φ N)) ≫
        (modTensorUnitLeft B (baseChangeMod φ N)).hom =
      ((modTensorUnitRight A (restrictRegular φ)).hom ▷
          (baseChangeMod φ N).X) ≫
        actLeft B (baseChangeMod φ N).X := by
      rw [modTensorπ_map_assoc, Mod.id_hom',
        MonoidalCategory.tensorHom_id, modTensorUnitLeft_hom,
        modTensorπ_desc]
      rfl
    refine Eq.trans (whisker_eq _ hmap) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker (whisker_exchange _ _) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact whisker_eq _
      (whiskerLeft_modTensorπ_baseChangeAct φ N)
  apply modTensor_hom_ext
  apply modTensor_whisker_hom_ext A (restrictRegular φ) N
    (baseChangeMod φ (regularMod A)).X
  refine Eq.trans ?_ hright.symm
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (projFormula_cover A B φ (regularMod A) N) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (modTensorAssocMid_unitLeft A (restrictRegular φ) N))) ?_
  exact hend _ _ _ hu

/-- The projection into a base change, whiskered against the new
base, multiplies the two base factors after braiding the trailing
one past the module. -/
theorem whiskerRight_modTensorπ_actRight_baseChange
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ]
    (M : Mod D A) :
    (modTensorπ A (restrictRegular φ) M ▷ B) ≫
        actRight B (baseChangeMod φ M).X =
      ((β_ (B ⊗ M.X) B).hom ≫ (α_ B B M.X).inv ≫
          (μ[B] ▷ M.X)) ≫
        modTensorπ A (restrictRegular φ) M := by
  show (modTensorπ A (restrictRegular φ) M ▷ B) ≫
      (β_ (baseChange φ M) B).hom ≫ baseChangeAct φ M = _
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (BraidedCategory.braiding_naturality_left
      (modTensorπ A (restrictRegular φ) M) B) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _
    (whiskerLeft_modTensorπ_baseChangeAct φ M)) ?_
  simp only [Category.assoc]
  rfl

/-- **The projection formula on the full cover**: on the two
covering projections the structure map multiplies the two base
factors and projects — an explicit formula with no descent left
in it. -/
theorem projFormula_full_cover
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ]
    (M N : Mod D A) :
    (modTensorπ A (restrictRegular φ) M ▷ (B ⊗ N.X)) ≫
        ((baseChangeMod φ M).X ◁
          modTensorπ A (restrictRegular φ) N) ≫
        modTensorπ B (baseChangeMod φ M) (baseChangeMod φ N) ≫
        (projFormula A B φ M N).hom =
      (α_ (B ⊗ M.X) B N.X).inv ≫
        (((β_ (B ⊗ M.X) B).hom ≫ (α_ B B M.X).inv ≫
            (μ[B] ▷ M.X)) ▷ N.X) ≫
        (α_ B M.X N.X).hom ≫ (B ◁ modTensorπ A M N) ≫
        modTensorπ A (restrictRegular φ)
          (modTensorMod A M N) := by
  have key : ∀ {Z : D}
      (r : modTensor A (restrictRegular φ) M ⊗ B ⟶
        modTensor A (restrictRegular φ) M)
      (h : modTensor A (restrictRegular φ) M ⊗ N.X ⟶ Z),
      (modTensorπ A (restrictRegular φ) M ▷ (B ⊗ N.X)) ≫
          (α_ (modTensor A (restrictRegular φ) M) B N.X).inv ≫
          (r ▷ N.X) ≫ h =
        (α_ (B ⊗ M.X) B N.X).inv ≫
          (((modTensorπ A (restrictRegular φ) M ▷ B) ≫ r)
            ▷ N.X) ≫ h := by
    intro Z r h
    rw [associator_inv_naturality_left_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc]
  refine Eq.trans (whisker_eq _
    (projFormula_cover A B φ M N)) ?_
  refine Eq.trans (key _ _) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker
    (congrArg (fun t => t ▷ N.X)
      (whiskerRight_modTensorπ_actRight_baseChange A B φ M))
    _)) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker
    (MonoidalCategory.comp_whiskerRight _ _ _) _)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (whiskerRight_modTensorπ_assocMid A
      (restrictRegular φ) M N))) ?_
  rw [modTensorAssocCover]
  rfl

section BaseShuffle

/-- **The base shuffle**: bringing the second copy of the base to
the front and multiplying is the middle-four interchange followed
by the multiplication.  Commutativity of the base is what makes
the two orders agree. -/
theorem baseShuffle
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (B : D)
    [MonObj B] [IsCommMonObj B]
    (Q W : D) :
    (α_ (B ⊗ Q) B W).inv ≫
        (((β_ (B ⊗ Q) B).hom ≫ (α_ B B Q).inv ≫
          (μ[B] ▷ Q)) ▷ W) ≫ (α_ B Q W).hom =
      tensorμ B Q B W ≫ (μ[B] ▷ (Q ⊗ W)) := by
  have hS₁ : (α_ (B ⊗ Q) B W).inv ≫ ((α_ B Q B).hom ▷ W) ≫
      (α_ B (Q ⊗ B) W).hom =
    (α_ B Q (B ⊗ W)).hom ≫ (B ◁ (α_ Q B W).inv) := by
    monoidal
  have hS₂ : (α_ B (B ⊗ Q) W).inv ≫ ((α_ B B Q).inv ▷ W) ≫
      (α_ (B ⊗ B) Q W).hom =
    (B ◁ (α_ B Q W).hom) ≫ (α_ B B (Q ⊗ W)).inv := by
    monoidal
  have hmid : ((B ◁ (β_ Q B).hom) ▷ W) =
      (α_ B (Q ⊗ B) W).hom ≫ (B ◁ ((β_ Q B).hom ▷ W)) ≫
        (α_ B (B ⊗ Q) W).inv := by
    rw [← associator_naturality_middle_assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hcw : (((β_ B B).hom ▷ Q) ▷ W) ≫ ((μ[B] ▷ Q) ▷ W) =
      (μ[B] ▷ Q) ▷ W := by
    rw [← MonoidalCategory.comp_whiskerRight,
      ← MonoidalCategory.comp_whiskerRight,
      IsCommMonObj.mul_comm]
  have hlast : ((μ[B] ▷ Q) ▷ W) ≫ (α_ B Q W).hom =
      (α_ (B ⊗ B) Q W).hom ≫ (μ[B] ▷ (Q ⊗ W)) :=
    associator_naturality_left μ[B] Q W
  rw [BraidedCategory.braiding_tensor_left_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc,
    MonoidalCategory.comp_whiskerRight]
  rw [reassoc_of% hcw]
  rw [tensorμ]
  simp only [Category.assoc]
  rw [hmid]
  simp only [Category.assoc]
  rw [hlast, reassoc_of% hS₂, reassoc_of% hS₁]

end BaseShuffle

/-- **The base multiplication is associative on covers**:
interchange-and-multiply is the structure map of a lax monoidal
functor, so it satisfies the associativity square. -/
theorem baseAssoc
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (B : D)
    [MonObj B]
    (Q₁ Q₂ Q₃ : D) :
    ((tensorμ B Q₁ B Q₂ ≫ (μ[B] ▷ (Q₁ ⊗ Q₂))) ▷ (B ⊗ Q₃)) ≫
        tensorμ B (Q₁ ⊗ Q₂) B Q₃ ≫
        (μ[B] ▷ ((Q₁ ⊗ Q₂) ⊗ Q₃)) ≫
        (B ◁ (α_ Q₁ Q₂ Q₃).hom) =
      (α_ (B ⊗ Q₁) (B ⊗ Q₂) (B ⊗ Q₃)).hom ≫
        ((B ⊗ Q₁) ◁ (tensorμ B Q₂ B Q₃ ≫
          (μ[B] ▷ (Q₂ ⊗ Q₃)))) ≫
        tensorμ B Q₁ B (Q₂ ⊗ Q₃) ≫
        (μ[B] ▷ (Q₁ ⊗ (Q₂ ⊗ Q₃))) := by
  have hass := tensor_associativity B Q₁ B Q₂ B Q₃
  simp only [MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [← MonoidalCategory.tensorHom_id μ[B] (Q₁ ⊗ Q₂),
    tensorμ_natural_left_assoc]
  rw [← MonoidalCategory.tensorHom_id μ[B] (Q₂ ⊗ Q₃),
    tensorμ_natural_right_assoc]
  rw [← reassoc_of% hass]
  have hL : ((μ[B] ▷ B) ⊗ₘ (𝟙 (Q₁ ⊗ Q₂) ▷ Q₃)) ≫
      (μ[B] ▷ ((Q₁ ⊗ Q₂) ⊗ Q₃)) ≫
      (B ◁ (α_ Q₁ Q₂ Q₃).hom) =
    (((μ[B] ▷ B) ≫ μ[B]) ⊗ₘ (α_ Q₁ Q₂ Q₃).hom) := by
    rw [MonoidalCategory.id_whiskerRight,
      ← MonoidalCategory.tensorHom_id μ[B] ((Q₁ ⊗ Q₂) ⊗ Q₃),
      ← MonoidalCategory.id_tensorHom B (α_ Q₁ Q₂ Q₃).hom,
      tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    simp
  have hR : ((α_ B B B).hom ⊗ₘ (α_ Q₁ Q₂ Q₃).hom) ≫
      ((B ◁ μ[B]) ⊗ₘ (Q₁ ◁ 𝟙 (Q₂ ⊗ Q₃))) ≫
      (μ[B] ▷ (Q₁ ⊗ (Q₂ ⊗ Q₃))) =
    (((α_ B B B).hom ≫ (B ◁ μ[B]) ≫ μ[B]) ⊗ₘ
      (α_ Q₁ Q₂ Q₃).hom) := by
    rw [MonoidalCategory.whiskerLeft_id,
      ← MonoidalCategory.tensorHom_id μ[B] (Q₁ ⊗ (Q₂ ⊗ Q₃)),
      tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    simp
  rw [hL, hR, MonObj.mul_assoc]

/-- Interchange-and-multiply is natural in the first module
slot. -/
theorem baseMul_natural_left
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (B : D)
    [MonObj B]
    {Q Q' : D} (f : Q ⟶ Q') (W : D) :
    ((B ◁ f) ▷ (B ⊗ W)) ≫ tensorμ B Q' B W ≫
        (μ[B] ▷ (Q' ⊗ W)) =
      tensorμ B Q B W ≫ (μ[B] ▷ (Q ⊗ W)) ≫
        (B ◁ (f ▷ W)) := by
  rw [← MonoidalCategory.id_tensorHom B f,
    tensorμ_natural_left_assoc,
    MonoidalCategory.id_whiskerRight,
    MonoidalCategory.id_tensorHom, whisker_exchange]

/-- Interchange-and-multiply is natural in the second module
slot. -/
theorem baseMul_natural_right
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (B : D)
    [MonObj B]
    (Q : D) {W W' : D} (g : W ⟶ W') :
    ((B ⊗ Q) ◁ (B ◁ g)) ≫ tensorμ B Q B W' ≫
        (μ[B] ▷ (Q ⊗ W')) =
      tensorμ B Q B W ≫ (μ[B] ▷ (Q ⊗ W)) ≫
        (B ◁ (Q ◁ g)) := by
  rw [← MonoidalCategory.id_tensorHom B g,
    tensorμ_natural_right_assoc,
    MonoidalCategory.whiskerLeft_id,
    MonoidalCategory.id_tensorHom, whisker_exchange]

/-- **The projection formula on the full cover, in interchange
form**: the structure map multiplies the two base factors through
the middle-four interchange and projects. -/
theorem projFormula_tensorμ_cover
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ]
    (M N : Mod D A) :
    (modTensorπ A (restrictRegular φ) M ▷ (B ⊗ N.X)) ≫
        ((baseChangeMod φ M).X ◁
          modTensorπ A (restrictRegular φ) N) ≫
        modTensorπ B (baseChangeMod φ M) (baseChangeMod φ N) ≫
        (projFormula A B φ M N).hom =
      tensorμ B M.X B N.X ≫ (μ[B] ▷ (M.X ⊗ N.X)) ≫
        (B ◁ modTensorπ A M N) ≫
        modTensorπ A (restrictRegular φ)
          (modTensorMod A M N) := by
  rw [projFormula_full_cover,
    reassoc_of% (baseShuffle B M.X N.X)]

/-- **The core of the associator coherence**: on the triple cover
the two ways of multiplying three base factors and projecting
agree.  Naturality of interchange-and-multiply moves the two
projections to the right, the defining equation of the
half-descended associator merges them, and what is left is the
associativity of interchange-and-multiply. -/
theorem projFormula_assoc_core
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B]
    (M N P : Mod D A) :
    (((tensorμ B M.X B N.X ≫ (μ[B] ▷ (M.X ⊗ N.X))) ≫
        (B ◁ modTensorπ A M N)) ▷ (B ⊗ P.X)) ≫
      (tensorμ B (modTensor A M N) B P.X ≫
        (μ[B] ▷ (modTensor A M N ⊗ P.X))) ≫
      (B ◁ modTensorAssocMid A M N P) =
    (α_ (B ⊗ M.X) (B ⊗ N.X) (B ⊗ P.X)).hom ≫
      ((B ⊗ M.X) ◁ ((tensorμ B N.X B P.X ≫
        (μ[B] ▷ (N.X ⊗ P.X))) ≫ (B ◁ modTensorπ A N P))) ≫
      (tensorμ B M.X B (modTensor A N P) ≫
        (μ[B] ▷ (M.X ⊗ modTensor A N P))) ≫
      (B ◁ modTensorπ A M (modTensorMod A N P)) := by
  have hcov : (modTensorπ A M N ▷ P.X) ≫
      modTensorAssocMid A M N P =
    (α_ M.X N.X P.X).hom ≫ (M.X ◁ modTensorπ A N P) ≫
      modTensorπ A M (modTensorMod A N P) := by
    rw [whiskerRight_modTensorπ_assocMid, modTensorAssocCover]
  conv_lhs =>
    rw [MonoidalCategory.comp_whiskerRight]
    simp only [Category.assoc]
    rw [reassoc_of%
      (baseMul_natural_left B (modTensorπ A M N) P.X)]
    rw [← MonoidalCategory.whiskerLeft_comp, hcov,
      MonoidalCategory.whiskerLeft_comp,
      MonoidalCategory.whiskerLeft_comp]
    simp only [Category.assoc]
    rw [reassoc_of% (baseAssoc B M.X N.X P.X)]
  conv_rhs =>
    rw [MonoidalCategory.whiskerLeft_comp]
    simp only [Category.assoc]
    rw [reassoc_of%
      (baseMul_natural_right B M.X (modTensorπ A N P))]

section ExtRR

/-- Whiskering the module-tensor coequalizer twice on the right
yields a colimit cofork. -/
noncomputable def modTensorWhiskerRRIsColimit
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (M : Mod D A) (N : Mod D A)
    (Y W : D) :
    IsColimit (Cofork.ofπ ((modTensorπ A M N ▷ Y) ▷ W)
      (by rw [← MonoidalCategory.comp_whiskerRight,
        ← MonoidalCategory.comp_whiskerRight,
        modTensor_condition,
        MonoidalCategory.comp_whiskerRight,
        MonoidalCategory.comp_whiskerRight]) :
      Cofork ((modTensorLegM A M N ▷ Y) ▷ W)
        ((modTensorLegN A M N ▷ Y) ▷ W)) :=
  isColimitOfHasCoequalizerOfPreservesColimit
    (tensorRight Y ⋙ tensorRight W) _ _

/-- Morphisms out of a twice right-whiskered tensor product of
modules are determined by the doubly whiskered projection. -/
lemma modTensor_whiskerRR_hom_ext
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (M : Mod D A) (N : Mod D A)
    (Y W : D) {Z : D}
    {k l : (modTensor A M N ⊗ Y) ⊗ W ⟶ Z}
    (h : ((modTensorπ A M N ▷ Y) ▷ W) ≫ k =
      ((modTensorπ A M N ▷ Y) ▷ W) ≫ l) : k = l :=
  Cofork.IsColimit.hom_ext
    (modTensorWhiskerRRIsColimit A M N Y W) h

end ExtRR

section AssocMidNatural

/-- The half-descended associator is natural in the third
slot. -/
theorem modTensorAssocMid_natural_right
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (P : Mod D A)
    (M : Mod D A)
    {N N' : Mod D A} (g : N ⟶ N') :
    modTensorAssocMid A P M N ≫
        modTensorMap A (𝟙 P) (modTensorMapMod A (𝟙 M) g) =
      ((modTensorMod A P M).X ◁ g.hom) ≫
        modTensorAssocMid A P M N' := by
  have hg : modTensorπ A M N ≫ modTensorMap A (𝟙 M) g =
      (M.X ◁ g.hom) ≫ modTensorπ A M N' := by
    rw [modTensorπ_map, Mod.id_hom',
      MonoidalCategory.id_tensorHom]
  have hP : modTensorπ A P (modTensorMod A M N) ≫
      modTensorMap A (𝟙 P) (modTensorMapMod A (𝟙 M) g) =
    (P.X ◁ modTensorMap A (𝟙 M) g) ≫
      modTensorπ A P (modTensorMod A M N') := by
    rw [modTensorπ_map, Mod.id_hom',
      MonoidalCategory.id_tensorHom]
    rfl
  have key : ∀ {Z : D}
      (h : modTensor A P (modTensorMod A M N) ⟶ Z),
      (modTensorπ A P M ▷ N.X) ≫
          modTensorAssocMid A P M N ≫ h =
        (α_ P.X M.X N.X).hom ≫ (P.X ◁ modTensorπ A M N) ≫
          modTensorπ A P (modTensorMod A M N) ≫ h := by
    intro Z h
    rw [← Category.assoc, whiskerRight_modTensorπ_assocMid,
      modTensorAssocCover]
    simp only [Category.assoc]
  have key' : (modTensorπ A P M ▷ N'.X) ≫
      modTensorAssocMid A P M N' =
    (α_ P.X M.X N'.X).hom ≫ (P.X ◁ modTensorπ A M N') ≫
      modTensorπ A P (modTensorMod A M N') := by
    rw [whiskerRight_modTensorπ_assocMid, modTensorAssocCover]
  apply modTensor_whiskerR_hom_ext A P M N.X
  refine Eq.trans (key _) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ hP)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker
    ((MonoidalCategory.whiskerLeft_comp P.X _ _).symm.trans
      (congrArg (fun t => P.X ◁ t) hg)) _)) ?_
  refine Eq.symm ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (whisker_exchange (modTensorπ A P M) g.hom).symm _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ key') ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (associator_naturality_right P.X M.X g.hom) _) ?_
  simp only [Category.assoc,
    MonoidalCategory.whiskerLeft_comp]

/-- The half-descended associator is natural in the second
slot. -/
theorem modTensorAssocMid_natural_mid
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (P : Mod D A)
    {M M' : Mod D A} (f : M ⟶ M') (N : Mod D A) :
    modTensorAssocMid A P M N ≫
        modTensorMap A (𝟙 P) (modTensorMapMod A f (𝟙 N)) =
      (modTensorMap A (𝟙 P) f ▷ N.X) ≫
        modTensorAssocMid A P M' N := by
  have hf : modTensorπ A M N ≫ modTensorMap A f (𝟙 N) =
      (f.hom ▷ N.X) ≫ modTensorπ A M' N := by
    rw [modTensorπ_map, Mod.id_hom',
      MonoidalCategory.tensorHom_id]
  have hP : modTensorπ A P (modTensorMod A M N) ≫
      modTensorMap A (𝟙 P) (modTensorMapMod A f (𝟙 N)) =
    (P.X ◁ modTensorMap A f (𝟙 N)) ≫
      modTensorπ A P (modTensorMod A M' N) := by
    rw [modTensorπ_map, Mod.id_hom',
      MonoidalCategory.id_tensorHom]
    rfl
  have hQ : modTensorπ A P M ≫ modTensorMap A (𝟙 P) f =
      (P.X ◁ f.hom) ≫ modTensorπ A P M' := by
    rw [modTensorπ_map, Mod.id_hom',
      MonoidalCategory.id_tensorHom]
  have key : ∀ {Z : D}
      (h : modTensor A P (modTensorMod A M N) ⟶ Z),
      (modTensorπ A P M ▷ N.X) ≫
          modTensorAssocMid A P M N ≫ h =
        (α_ P.X M.X N.X).hom ≫ (P.X ◁ modTensorπ A M N) ≫
          modTensorπ A P (modTensorMod A M N) ≫ h := by
    intro Z h
    rw [← Category.assoc, whiskerRight_modTensorπ_assocMid,
      modTensorAssocCover]
    simp only [Category.assoc]
  have key' : (modTensorπ A P M' ▷ N.X) ≫
      modTensorAssocMid A P M' N =
    (α_ P.X M'.X N.X).hom ≫ (P.X ◁ modTensorπ A M' N) ≫
      modTensorπ A P (modTensorMod A M' N) := by
    rw [whiskerRight_modTensorπ_assocMid, modTensorAssocCover]
  apply modTensor_whiskerR_hom_ext A P M N.X
  refine Eq.trans (key _) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ hP)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker
    ((MonoidalCategory.whiskerLeft_comp P.X _ _).symm.trans
      (congrArg (fun t => P.X ◁ t) hf)) _)) ?_
  refine Eq.symm ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    ((MonoidalCategory.comp_whiskerRight _ _ _).symm.trans
      (congrArg (fun t => t ▷ N.X) hQ)) _) ?_
  refine Eq.trans (eq_whisker
    (MonoidalCategory.comp_whiskerRight _ _ _) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ key') ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (associator_naturality_middle P.X f.hom N.X) _) ?_
  simp only [Category.assoc,
    MonoidalCategory.whiskerLeft_comp]

end AssocMidNatural

end RS
