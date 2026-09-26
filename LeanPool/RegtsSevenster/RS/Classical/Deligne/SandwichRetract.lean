/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.BaseChangeTensor
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreeModShuffle

/-!
# The sandwich retract legs

The insertion and contraction making a module a retract of its
double-dual sandwich, built from bundled pieces: the unit
collapses of the relative tensor as module isomorphisms, the
bundled copairing and pairing, and the associator.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- The left unit collapse intertwines the actions. -/
theorem modTensorUnitLeft_act
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (N : Mod D A) :
    modTensorAct A (regularMod A) N ≫
        (modTensorUnitLeft A N).hom =
      (A ◁ (modTensorUnitLeft A N).hom) ≫ actLeft A N.X := by
  apply modTensor_whisker_hom_ext A (regularMod A) N A
  have hπ : modTensorπ A (regularMod A) N ≫
      (modTensorUnitLeft A N).hom = actLeft A N.X :=
    modTensorπ_desc A (regularMod A) N _ _
  have hL : (A ◁ modTensorπ A (regularMod A) N) ≫
      modTensorAct A (regularMod A) N ≫
      (modTensorUnitLeft A N).hom =
      ((α_ A A N.X).inv ≫ (μ[A] ▷ N.X)) ≫
        actLeft A N.X := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (whiskerLeft_modTensorπ_act A (regularMod A) N) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact whisker_eq _ hπ
  have hR : (A ◁ modTensorπ A (regularMod A) N) ≫
      (A ◁ (modTensorUnitLeft A N).hom) ≫ actLeft A N.X =
      (A ◁ actLeft A N.X) ≫ actLeft A N.X := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp A _ _).symm _) ?_
    exact eq_whisker (congrArg (fun t => A ◁ t) hπ) _
  refine hL.trans (Eq.trans ?_ hR.symm)
  refine Eq.symm ?_
  refine Eq.trans (actLeft_actLeft A N.X) ?_
  simp only [Category.assoc]

/-- **The left unit collapse, as a module isomorphism.** -/
noncomputable def modTensorUnitLeftMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (N : Mod D A) :
    modTensorMod A (regularMod A) N ≅ N where
  hom := Mod.Hom.mk' (modTensorUnitLeft A N).hom (by
    exact modTensorUnitLeft_act A N)
  inv := Mod.Hom.mk' (modTensorUnitLeft A N).inv (by
    exact act_inv_of_act_hom A (modTensorUnitLeft A N)
      (modTensorUnitLeft_act A N))
  hom_inv_id := by
    apply Mod.Hom.ext
    exact (modTensorUnitLeft A N).hom_inv_id
  inv_hom_id := by
    apply Mod.Hom.ext
    exact (modTensorUnitLeft A N).inv_hom_id

/-- The right unit collapse intertwines the actions. -/
theorem modTensorUnitRight_act
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A]
    (M : Mod D A) :
    modTensorAct A M (regularMod A) ≫
        (modTensorUnitRight A M).hom =
      (A ◁ (modTensorUnitRight A M).hom) ≫
        actLeft A M.X := by
  apply modTensor_whisker_hom_ext A M (regularMod A) A
  have hπ : modTensorπ A M (regularMod A) ≫
      (modTensorUnitRight A M).hom = actRight A M.X :=
    modTensorπ_desc A M (regularMod A) _ _
  have hL : (A ◁ modTensorπ A M (regularMod A)) ≫
      modTensorAct A M (regularMod A) ≫
      (modTensorUnitRight A M).hom =
      ((α_ A M.X A).inv ≫ (actLeft A M.X ▷ A)) ≫
        actRight A M.X := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (whiskerLeft_modTensorπ_act A M (regularMod A)) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact whisker_eq _ hπ
  have hR : (A ◁ modTensorπ A M (regularMod A)) ≫
      (A ◁ (modTensorUnitRight A M).hom) ≫
        actLeft A M.X =
      (A ◁ actRight A M.X) ≫ actLeft A M.X := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp A _ _).symm _) ?_
    exact eq_whisker (congrArg (fun t => A ◁ t) hπ) _
  refine hL.trans (Eq.trans ?_ hR.symm)
  refine Eq.symm ?_
  refine Eq.trans (actLeft_actRight A M.X) ?_
  simp only [Category.assoc]

/-- **The right unit collapse, as a module isomorphism.** -/
noncomputable def modTensorUnitRightMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A]
    (M : Mod D A) :
    modTensorMod A M (regularMod A) ≅ M where
  hom := Mod.Hom.mk' (modTensorUnitRight A M).hom (by
    exact modTensorUnitRight_act A M)
  inv := Mod.Hom.mk' (modTensorUnitRight A M).inv (by
    exact act_inv_of_act_hom A (modTensorUnitRight A M)
      (modTensorUnitRight_act A M))
  hom_inv_id := by
    apply Mod.Hom.ext
    exact (modTensorUnitRight A M).hom_inv_id
  inv_hom_id := by
    apply Mod.Hom.ext
    exact (modTensorUnitRight A M).inv_hom_id

section Legs

/-- **The sandwich insertion**: expand the unit and insert the
copairing on the left. -/
noncomputable def sandwichIns
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M') :
    M ⟶ modTensorMod A (modTensorMod A M M') M :=
  (modTensorUnitLeftMod A M).symm.hom ≫
    modTensorMapMod A (d.copairMod) (𝟙 M)

/-- **The sandwich contraction**: reassociate, contract the
trailing pair, and collapse the unit. -/
noncomputable def sandwichCon
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M') :
    modTensorMod A (modTensorMod A M M') M ⟶ M :=
  (modTensorAssocModIso A M M' M).hom ≫
    modTensorMapMod A (𝟙 M) (d.pairMod) ≫
    (modTensorUnitRightMod A M).hom

/-- **The dual sandwich insertion**: expand the unit and insert
the copairing on the right. -/
noncomputable def sandwichInsR
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M') :
    M' ⟶ modTensorMod A M' (modTensorMod A M M') :=
  (modTensorUnitRightMod A M').symm.hom ≫
    modTensorMapMod A (𝟙 M') (d.copairMod)

/-- **The dual sandwich contraction**: reassociate backwards,
contract the leading pair, and collapse the unit. -/
noncomputable def sandwichConR
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M') :
    modTensorMod A M' (modTensorMod A M M') ⟶ M' :=
  (modTensorAssocModIso A M' M M').inv ≫
    modTensorMapMod A (d.pairMod) (𝟙 M') ≫
    (modTensorUnitLeftMod A M').hom

end Legs

end RS
