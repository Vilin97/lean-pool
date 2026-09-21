/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.UnitBase
import LeanPool.RegtsSevenster.RS.Classical.Deligne.ZigzagCarrier

/-!
# The duality datum over the trivial base

An exact pairing of the ambient category induces a duality datum
between the corresponding modules over the tensor unit: the
relative tensor collapses to the plain tensor, and the pairing
and copairing pass through the collapse.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- The pairing over the trivial base: collapse and evaluate. -/
noncomputable def unitBasePair
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (X : D) (Y : D) [ExactPairing X Y] :
    modTensor (𝟙_ D) (unitMod Y) (unitMod X) ⟶ 𝟙_ D :=
  (modTensorUnitBase (unitMod Y) (unitMod X)).hom ≫ ε_ X Y

/-- The copairing over the trivial base: coevaluate and embed. -/
noncomputable def unitBaseCopair
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (X : D) (Y : D) [ExactPairing X Y] :
    𝟙_ D ⟶ modTensor (𝟙_ D) (unitMod X) (unitMod Y) :=
  η_ X Y ≫ (modTensorUnitBase (unitMod X) (unitMod Y)).inv

/-- The pairing is linear over the trivial base. -/
theorem unitBasePair_linear
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (X : D) (Y : D) [ExactPairing X Y] :
    (letI := modTensorModObj (𝟙_ D) (unitMod Y) (unitMod X);
    actLeft (𝟙_ D)
      (modTensor (𝟙_ D) (unitMod Y) (unitMod X))) ≫
      unitBasePair X Y =
    ((𝟙_ D) ◁ unitBasePair X Y) ≫ μ[𝟙_ D] := by
  rw [actLeft_unitBase _
    (inst := modTensorModObj (𝟙_ D) (unitMod Y) (unitMod X))]
  rw [show μ[𝟙_ D] = (λ_ (𝟙_ D)).hom from rfl]
  exact (leftUnitor_naturality (unitBasePair X Y)).symm

/-- The copairing is linear over the trivial base. -/
theorem unitBaseCopair_linear
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (X : D) (Y : D) [ExactPairing X Y] :
    μ[𝟙_ D] ≫ unitBaseCopair X Y =
    ((𝟙_ D) ◁ unitBaseCopair X Y) ≫
      (letI := modTensorModObj (𝟙_ D) (unitMod X) (unitMod Y);
      actLeft (𝟙_ D)
        (modTensor (𝟙_ D) (unitMod X) (unitMod Y))) := by
  rw [actLeft_unitBase _
    (inst := modTensorModObj (𝟙_ D) (unitMod X) (unitMod Y))]
  rw [show μ[𝟙_ D] = (λ_ (𝟙_ D)).hom from rfl]
  exact (leftUnitor_naturality (unitBaseCopair X Y)).symm

/-- **The duality datum over the trivial base** attached to an
exact pairing of the ambient category. -/
noncomputable def unitBaseDatum
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (X : D) (Y : D) [ExactPairing X Y] :
    ModDualityDatum (𝟙_ D) (unitMod X) (unitMod Y) where
  pair := unitBasePair X Y
  copair := unitBaseCopair X Y
  pair_linear := unitBasePair_linear X Y
  copair_linear := unitBaseCopair_linear X Y

/-- **The trivial-base datum satisfies the zigzag laws**: through
the collapse they are the zigzag identities of the exact
pairing. -/
theorem unitBaseDatum_zigzag
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (X : D) (Y : D) [ExactPairing X Y] :
    ModZigzagDatum (𝟙_ D) (unitBaseDatum X Y) := by
  have h2 : modTensorπ (𝟙_ D) (unitMod Y) (unitMod X) ≫
      (unitBaseDatum X Y).pair = ε_ X Y := by
    have hπ : modTensorπ (𝟙_ D) (unitMod Y) (unitMod X) ≫
        (modTensorUnitBase (unitMod Y) (unitMod X)).hom =
        𝟙 ((unitMod Y).X ⊗ (unitMod X).X) :=
      (modTensorUnitBase (unitMod Y) (unitMod X)).inv_hom_id
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker hπ _) ?_
    exact Category.id_comp _
  apply modZigzagDatum_of_carrier
  · have h1 : ((modTensorUnitBase (unitMod X)
        (unitMod Y)).inv ▷ X) ≫
        zigContract (𝟙_ D) (unitBaseDatum X Y).pair
          (unitBaseDatum X Y).pair_linear =
        (α_ X Y X).hom ≫
          (X ◁ (modTensorπ (𝟙_ D) (unitMod Y) (unitMod X) ≫
            (unitBaseDatum X Y).pair)) ≫
          actRight (𝟙_ D) X :=
      whiskerRight_modTensorπ_zigContract (𝟙_ D) _ _
    have h4 : (α_ X Y X).hom ≫
        (X ◁ (modTensorπ (𝟙_ D) (unitMod Y) (unitMod X) ≫
          (unitBaseDatum X Y).pair)) ≫
        actRight (𝟙_ D) X =
        (α_ X Y X).hom ≫ (X ◁ ε_ X Y) ≫ (ρ_ X).hom := by
      refine whisker_eq _ ?_
      refine Eq.trans (eq_whisker (congrArg
        (fun t => X ◁ t) h2) _) ?_
      exact whisker_eq _ (actRight_unitBase X)
    show (λ_ X).inv ≫
      ((η[𝟙_ D] ≫ (unitBaseDatum X Y).copair) ▷ X) ≫
      zigContract (𝟙_ D) (unitBaseDatum X Y).pair
        (unitBaseDatum X Y).pair_linear = 𝟙 X
    rw [show η[𝟙_ D] ≫ (unitBaseDatum X Y).copair =
      η_ X Y ≫ (modTensorUnitBase (unitMod X)
        (unitMod Y)).inv from Category.id_comp _]
    erw [MonoidalCategory.comp_whiskerRight, Category.assoc]
    refine Eq.trans (whisker_eq _ (whisker_eq _
      (h1.trans h4))) ?_
    have hzz : η_ X Y ▷ X ≫ (α_ X Y X).hom ≫
        (X ◁ ε_ X Y) ≫ (ρ_ X).hom =
        (λ_ X).hom ≫ (ρ_ X).inv ≫ (ρ_ X).hom :=
      (reassoc_of%
        (ExactPairing.evaluation_coevaluation X Y))
        ((ρ_ X).hom)
    refine Eq.trans (whisker_eq _ hzz) ?_
    refine Eq.trans (whisker_eq _ (whisker_eq _
      (ρ_ X).inv_hom_id)) ?_
    refine Eq.trans (whisker_eq _ (Category.comp_id _)) ?_
    exact (λ_ X).inv_hom_id
  · have h1 : (Y ◁ (modTensorUnitBase (unitMod X)
        (unitMod Y)).inv) ≫
        zagContract (𝟙_ D) (unitBaseDatum X Y).pair
          (unitBaseDatum X Y).pair_linear =
        (α_ Y X Y).inv ≫
          ((modTensorπ (𝟙_ D) (unitMod Y) (unitMod X) ≫
            (unitBaseDatum X Y).pair) ▷ Y) ≫
          actLeft (𝟙_ D) Y :=
      whiskerLeft_modTensorπ_zagContract (𝟙_ D)
        (unitBaseDatum X Y).pair
        (unitBaseDatum X Y).pair_linear
    have h4 : (α_ Y X Y).inv ≫
        ((modTensorπ (𝟙_ D) (unitMod Y) (unitMod X) ≫
          (unitBaseDatum X Y).pair) ▷ Y) ≫
        actLeft (𝟙_ D) Y =
        (α_ Y X Y).inv ≫ (ε_ X Y ▷ Y) ≫ (λ_ Y).hom := by
      refine whisker_eq _ ?_
      refine Eq.trans (eq_whisker (congrArg
        (fun t => t ▷ Y) h2) _) ?_
      exact whisker_eq _ (actLeft_unitBase Y)
    show (ρ_ Y).inv ≫
      (Y ◁ (η[𝟙_ D] ≫ (unitBaseDatum X Y).copair)) ≫
      zagContract (𝟙_ D) (unitBaseDatum X Y).pair
        (unitBaseDatum X Y).pair_linear = 𝟙 Y
    rw [show η[𝟙_ D] ≫ (unitBaseDatum X Y).copair =
      η_ X Y ≫ (modTensorUnitBase (unitMod X)
        (unitMod Y)).inv from Category.id_comp _]
    erw [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    refine Eq.trans (whisker_eq _ (whisker_eq _
      (h1.trans h4))) ?_
    have hzz : Y ◁ η_ X Y ≫ (α_ Y X Y).inv ≫
        (ε_ X Y ▷ Y) ≫ (λ_ Y).hom =
        (ρ_ Y).hom ≫ (λ_ Y).inv ≫ (λ_ Y).hom :=
      (reassoc_of%
        (ExactPairing.coevaluation_evaluation X Y))
        ((λ_ Y).hom)
    refine Eq.trans (whisker_eq _ hzz) ?_
    refine Eq.trans (whisker_eq _ (whisker_eq _
      (λ_ Y).inv_hom_id)) ?_
    refine Eq.trans (whisker_eq _ (Category.comp_id _)) ?_
    exact (ρ_ Y).inv_hom_id

end RS
