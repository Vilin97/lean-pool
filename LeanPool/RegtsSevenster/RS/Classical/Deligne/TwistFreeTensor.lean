/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SandwichRetract
import LeanPool.RegtsSevenster.RS.Classical.Deligne.TwistUnitor

/-!
# The free module inside the relative tensor

Tensoring against a free module changes nothing but the twist: the
algebra of the free module is absorbed by the relative tensor and
only the generating object survives, carried across by the
braiding.

* `freeRegTwistIso`: the free module on an object is the twist of
  the regular module by that object, through the braiding.
* `freeTensorTwistIso`: the relative tensor of a free module with
  a module is the twist of that module by the generating object.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## The free module as a twisted regular module -/

/-- The braiding intertwines the free action on the generator with
the twist of the regular action: both hexagon legs multiply the
two algebra factors after carrying the generator to the front. -/
theorem freeRegTwist_act
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A]
    (V : D) :
    letI := ModObj.regular A
    ((α_ A A V).inv ≫ (μ[A] ▷ V)) ≫ (β_ A V).hom =
      (A ◁ (β_ A V).hom) ≫ actAcross A V A := by
  letI := ModObj.regular A
  show ((α_ A A V).inv ≫ (μ[A] ▷ V)) ≫ (β_ A V).hom =
    (A ◁ (β_ A V).hom) ≫ actAcross A V A
  rw [actAcross_eq_braidPast, braidPast_hom,
    show actLeft A A = μ[A] from rfl, Category.assoc,
    BraidedCategory.braiding_naturality_left,
    BraidedCategory.braiding_tensor_left_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- **The free module is a twisted regular module**: the free
module on `V` is the twist by `V` of the regular module, through
the braiding carrying the algebra past the generator. -/
noncomputable def freeRegTwistIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A]
    (V : D) :
    freeMod A V ≅ tensorLeftMod A V (regularMod A) where
  hom := Mod.Hom.mk' (β_ A V).hom (by
    letI := ModObj.regular A
    show ((α_ A A V).inv ≫ (μ[A] ▷ V)) ≫ (β_ A V).hom =
      (A ◁ (β_ A V).hom) ≫ actAcross A V A
    exact freeRegTwist_act A V)
  inv := Mod.Hom.mk' (β_ A V).inv (by
    letI := ModObj.regular A
    show actAcross A V A ≫ (β_ A V).inv =
      (A ◁ (β_ A V).inv) ≫ ((α_ A A V).inv ≫ (μ[A] ▷ V))
    exact act_inv_of_act_hom A (β_ A V) (freeRegTwist_act A V))
  hom_inv_id := by
    apply Mod.Hom.ext
    exact (β_ A V).hom_inv_id
  inv_hom_id := by
    apply Mod.Hom.ext
    exact (β_ A V).inv_hom_id

/-! ## Absorbing a free factor -/

/-- **The free factor twists**: the relative tensor of the free
module on `V` with a module `M` is the twist of `M` by `V`.  The
free module is the twisted regular module, the twist shuffle
collects both twists in front, and the regular module is the unit
of the relative tensor. -/
noncomputable def freeTensorTwistIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A]
    (V : D) (M : Mod D A) :
    modTensorMod A (freeMod A V) M ≅ tensorLeftMod A V M :=
  modTensorMapIso A (freeRegTwistIso A V)
      (tensorLeftUnitMod A M).symm ≪≫
    twistShuffleModIso A V (𝟙_ D) (regularMod A) M ≪≫
    tensorLeftModContextIso A (ρ_ V)
      (modTensorMod A (regularMod A) M) ≪≫
    tensorLeftModWhiskerIso A V (modTensorUnitLeftMod A M)

end RS
