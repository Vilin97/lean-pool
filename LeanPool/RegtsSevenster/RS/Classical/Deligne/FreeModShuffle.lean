/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.CatTheory.WhiskerAdditive
import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModBiprod
import LeanPool.RegtsSevenster.RS.Classical.Deligne.Rappel210

/-!
# Free modules on units and biproducts

The free module on the tensor unit is the regular module, and
the free module on a biproduct is the biproduct of the free
modules: the bookkeeping of the mixed free part of the dévissage
decomposition.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- The right unitor intertwines the free action on the unit
with the regular action. -/
theorem freeModUnit_linear
    [Category.{v} D] [MonoidalCategory D] (B : D) [MonObj B] :
    ((α_ B B (𝟙_ D)).inv ≫ μ[B] ▷ (𝟙_ D)) ≫
        (ρ_ B).hom =
      (B ◁ (ρ_ B).hom) ≫ μ[B] := by
  rw [Category.assoc, rightUnitor_naturality,
    ← Category.assoc]
  rw [show (α_ B B (𝟙_ D)).inv ≫ (ρ_ (B ⊗ B)).hom =
    B ◁ (ρ_ B).hom from by monoidal]

/-- **The free module on the unit is the regular module.** -/
noncomputable def freeModUnitIso
    [Category.{v} D] [MonoidalCategory D] (B : D) [MonObj B] :
    freeMod B (𝟙_ D) ≅ regularMod B where
  hom := Mod.Hom.mk' (ρ_ B).hom (by
    show ((α_ B B (𝟙_ D)).inv ≫ μ[B] ▷ (𝟙_ D)) ≫
        (ρ_ B).hom = (B ◁ (ρ_ B).hom) ≫ μ[B]
    exact freeModUnit_linear B)
  inv := Mod.Hom.mk' (ρ_ B).inv (by
    show μ[B] ≫ (ρ_ B).inv = (B ◁ (ρ_ B).inv) ≫
      ((α_ B B (𝟙_ D)).inv ≫ μ[B] ▷ (𝟙_ D))
    refine (cancel_mono (ρ_ B).hom).mp ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (ρ_ B).inv_hom_id) ?_
    refine Eq.trans (Category.comp_id _) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (freeModUnit_linear B)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    refine Eq.trans (eq_whisker (congrArg (fun t => B ◁ t)
      (ρ_ B).inv_hom_id) _) ?_
    rw [MonoidalCategory.whiskerLeft_id, Category.id_comp])
  hom_inv_id := by
    apply Mod.Hom.ext
    exact (ρ_ B).hom_inv_id
  inv_hom_id := by
    apply Mod.Hom.ext
    exact (ρ_ B).inv_hom_id

section Biprod

/-- The distributor intertwines the free actions. -/
theorem freeModBiprod_linear
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (B : D) [MonObj B] (X : D) (Y : D) :
    ((α_ B B (X ⊞ Y)).inv ≫ μ[B] ▷ (X ⊞ Y)) ≫
        biprod.lift (B ◁ biprod.fst) (B ◁ biprod.snd) =
      (B ◁ biprod.lift (B ◁ biprod.fst) (B ◁ biprod.snd)) ≫
        modBiprodAct B (freeMod B X) (freeMod B Y) := by
  apply biprod.hom_ext
  · rw [Category.assoc, Category.assoc, biprod.lift_fst]
    refine Eq.trans (whisker_eq _
      (whisker_exchange μ[B] (biprod.fst :
        X ⊞ Y ⟶ X)).symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (associator_inv_naturality_right B B
        (biprod.fst : X ⊞ Y ⟶ X)).symm _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (modBiprodAct_fst B (freeMod B X) (freeMod B Y))) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    refine Eq.trans (eq_whisker (congrArg (fun t => B ◁ t)
      (biprod.lift_fst (B ◁ (biprod.fst : X ⊞ Y ⟶ X))
        (B ◁ (biprod.snd : X ⊞ Y ⟶ Y)))) _) ?_
    rfl
  · rw [Category.assoc, Category.assoc, biprod.lift_snd]
    refine Eq.trans (whisker_eq _
      (whisker_exchange μ[B] (biprod.snd :
        X ⊞ Y ⟶ Y)).symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (associator_inv_naturality_right B B
        (biprod.snd : X ⊞ Y ⟶ Y)).symm _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (modBiprodAct_snd B (freeMod B X) (freeMod B Y))) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    refine Eq.trans (eq_whisker (congrArg (fun t => B ◁ t)
      (biprod.lift_snd (B ◁ (biprod.fst : X ⊞ Y ⟶ X))
        (B ◁ (biprod.snd : X ⊞ Y ⟶ Y)))) _) ?_
    rfl

/-- The inverse of a linear isomorphism is linear. -/
theorem act_inv_of_act_hom [Category.{v} D] [MonoidalCategory D] (B : D)
    {P Q : D} {actP : B ⊗ P ⟶ P}
    {actQ : B ⊗ Q ⟶ Q} (e : P ≅ Q)
    (h : actP ≫ e.hom = (B ◁ e.hom) ≫ actQ) :
    actQ ≫ e.inv = (B ◁ e.inv) ≫ actP := by
  have h1 : actQ ≫ e.inv =
      (B ◁ e.inv) ≫ ((B ◁ e.hom) ≫ actQ) ≫ e.inv := by
    rw [← Category.assoc, ← Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp, e.inv_hom_id,
      MonoidalCategory.whiskerLeft_id, Category.id_comp]
  rw [h1, ← h, Category.assoc, e.hom_inv_id,
    Category.comp_id]

/-- **The free module on a biproduct is the biproduct of the
free modules.** -/
noncomputable def freeModBiprodIso
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasBinaryBiproducts D] (B : D) [MonObj B]
    (X : D) (Y : D) :
    freeMod B (X ⊞ Y) ≅
      modBiprod B (freeMod B X) (freeMod B Y) where
  hom := Mod.Hom.mk' (tensorBiprodIso B X Y).hom (by
    show ((α_ B B (X ⊞ Y)).inv ≫ μ[B] ▷ (X ⊞ Y)) ≫
        (tensorBiprodIso B X Y).hom =
      (B ◁ (tensorBiprodIso B X Y).hom) ≫
        modBiprodAct B (freeMod B X) (freeMod B Y)
    exact freeModBiprod_linear B X Y)
  inv := Mod.Hom.mk' (tensorBiprodIso B X Y).inv (by
    show modBiprodAct B (freeMod B X) (freeMod B Y) ≫
        (tensorBiprodIso B X Y).inv =
      (B ◁ (tensorBiprodIso B X Y).inv) ≫
        ((α_ B B (X ⊞ Y)).inv ≫ μ[B] ▷ (X ⊞ Y))
    exact act_inv_of_act_hom B (tensorBiprodIso B X Y)
      (freeModBiprod_linear B X Y))
  hom_inv_id := by
    apply Mod.Hom.ext
    exact (tensorBiprodIso B X Y).hom_inv_id
  inv_hom_id := by
    apply Mod.Hom.ext
    exact (tensorBiprodIso B X Y).inv_hom_id

end Biprod

/-- The free module on an isomorphism. -/
noncomputable def freeModMapIso
    [Category.{v} D] [MonoidalCategory D] (B : D) [MonObj B]
    {V W : D} (e : V ≅ W) :
    freeMod B V ≅ freeMod B W where
  hom := freeModMap B e.hom
  inv := freeModMap B e.inv
  hom_inv_id := by
    apply Mod.Hom.ext
    show (B ◁ e.hom) ≫ (B ◁ e.inv) = 𝟙 (B ⊗ V)
    rw [← MonoidalCategory.whiskerLeft_comp, e.hom_inv_id,
      MonoidalCategory.whiskerLeft_id]
  inv_hom_id := by
    apply Mod.Hom.ext
    show (B ◁ e.inv) ≫ (B ◁ e.hom) = 𝟙 (B ⊗ W)
    rw [← MonoidalCategory.whiskerLeft_comp, e.inv_hom_id,
      MonoidalCategory.whiskerLeft_id]

end RS
