/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.BaseChangeMonoidal
import LeanPool.RegtsSevenster.RS.Classical.Deligne.BaseChangeZigzag
import LeanPool.RegtsSevenster.RS.Classical.Deligne.ZigzagSandwich

/-!
# Transport of the zigzag laws along base change

Base change is a strong monoidal functor on modules, and the
zigzag laws of a duality datum are an identity between words in
the monoidal structure.  This file transports the identity: the
base-changed insertion and contraction are the images of the
insertion and contraction, conjugated by the structure map, so
their composite is the image of an identity.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

section Bundled

/-- Functoriality of the relative tensor of morphisms. -/
theorem modTensorMapMod_comp
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A]
    {M M' M'' N N' N'' : Mod D A}
    (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N')
    (g' : N' ⟶ N'') :
    modTensorMapMod A f g ≫ modTensorMapMod A f' g' =
      modTensorMapMod A (f ≫ f') (g ≫ g') :=
  Mod.Hom.ext (modTensorMap_comp A f f' g g').symm

/-- The right unit coherence, as an identity of module maps. -/
theorem projFormulaMod_unitRight
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] (M : Mod D A) :
    (projFormulaMod A B φ M (regularMod A)).hom ≫
        baseChangeMapMod A B φ
          (modTensorUnitRightMod A M).hom =
      modTensorMapMod B (𝟙 (baseChangeMod φ M))
          (baseChangeUnitIso A B φ).hom ≫
        (modTensorUnitRightMod B (baseChangeMod φ M)).hom :=
  Mod.Hom.ext (projFormula_unitRight A B φ M)

/-- The left unit coherence, as an identity of module maps. -/
theorem projFormulaMod_unitLeft
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] (N : Mod D A) :
    (projFormulaMod A B φ (regularMod A) N).hom ≫
        baseChangeMapMod A B φ
          (modTensorUnitLeftMod A N).hom =
      modTensorMapMod B (baseChangeUnitIso A B φ).hom
          (𝟙 (baseChangeMod φ N)) ≫
        (modTensorUnitLeftMod B (baseChangeMod φ N)).hom :=
  Mod.Hom.ext (projFormula_unitLeft A B φ N)

/-- Naturality in the first slot, as an identity of module
maps. -/
theorem projFormulaMod_natural_left
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ]
    {M M' : Mod D A}
    (f : M ⟶ M') (N : Mod D A) :
    modTensorMapMod B (baseChangeMapMod A B φ f)
        (𝟙 (baseChangeMod φ N)) ≫
        (projFormulaMod A B φ M' N).hom =
      (projFormulaMod A B φ M N).hom ≫
        baseChangeMapMod A B φ (modTensorMapMod A f (𝟙 N)) :=
  Mod.Hom.ext (projFormula_natural_left A B φ f N)

/-- Naturality in the second slot, as an identity of module
maps. -/
theorem projFormulaMod_natural_right
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ]
    (M : Mod D A)
    {N N' : Mod D A} (g : N ⟶ N') :
    modTensorMapMod B (𝟙 (baseChangeMod φ M))
        (baseChangeMapMod A B φ g) ≫
        (projFormulaMod A B φ M N').hom =
      (projFormulaMod A B φ M N).hom ≫
        baseChangeMapMod A B φ (modTensorMapMod A (𝟙 M) g) :=
  Mod.Hom.ext (projFormula_natural_right A B φ M g)

/-- The associator coherence, as an identity of module maps. -/
theorem projFormulaMod_assoc
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] (M : Mod D A) (N : Mod D A) (P : Mod D A) :
    modTensorMapMod B (projFormulaMod A B φ M N).hom
        (𝟙 (baseChangeMod φ P)) ≫
      (projFormulaMod A B φ (modTensorMod A M N) P).hom ≫
      baseChangeMapMod A B φ
        (modTensorAssocModIso A M N P).hom =
    (modTensorAssocModIso B (baseChangeMod φ M)
        (baseChangeMod φ N) (baseChangeMod φ P)).hom ≫
      modTensorMapMod B (𝟙 (baseChangeMod φ M))
        (projFormulaMod A B φ N P).hom ≫
      (projFormulaMod A B φ M (modTensorMod A N P)).hom :=
  Mod.Hom.ext (projFormula_assoc A B φ M N P)

end Bundled

section Datum

/-- The base-changed pairing, as the image of the pairing
conjugated by the structure map and the unit. -/
theorem pairMod_baseChangeDatum
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M') :
    (baseChangeDatum A B φ d).pairMod =
      (projFormulaMod A B φ M' M).hom ≫
        baseChangeMapMod A B φ (d.pairMod) ≫
        (baseChangeUnitIso A B φ).hom :=
  Mod.Hom.ext rfl

/-- The base-changed copairing, as the image of the copairing
conjugated by the unit and the structure map. -/
theorem copairMod_baseChangeDatum
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M') :
    (baseChangeDatum A B φ d).copairMod =
      (baseChangeUnitIso A B φ).inv ≫
        baseChangeMapMod A B φ (d.copairMod) ≫
        (projFormulaMod A B φ M M').inv :=
  Mod.Hom.ext rfl

/-- Base change on morphisms preserves composition. -/
theorem baseChangeMapMod_comp
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ]
    {X Y Z : Mod D A} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    baseChangeMapMod A B φ (f ≫ g) =
      baseChangeMapMod A B φ f ≫ baseChangeMapMod A B φ g :=
  Mod.Hom.ext (by
    have h := modTensorMap_comp A (𝟙 (restrictRegular φ))
      (𝟙 (restrictRegular φ)) f g
    rw [Category.comp_id] at h
    exact h)

/-- Base change on morphisms preserves identities. -/
theorem baseChangeMapMod_id
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ]
    (X : Mod D A) :
    baseChangeMapMod A B φ (𝟙 X) = 𝟙 (baseChangeMod φ X) :=
  Mod.Hom.ext (by
    change modTensorMap A (𝟙 (restrictRegular φ)) (𝟙 X) = _
    rw [modTensorMap_id, Mod.id_hom']
    rfl)

section Transport

/-- Composing two relative tensors of morphisms with identity
second slots. -/
theorem modTensorMapMod_compL
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (B : D) [MonObj B] [IsCommMonObj B]
    {X Y Z W : Mod D B} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    modTensorMapMod B f (𝟙 W) ≫ modTensorMapMod B g (𝟙 W) =
      modTensorMapMod B (f ≫ g) (𝟙 W) := by
  rw [modTensorMapMod_comp, Category.comp_id]

/-- Composing two relative tensors of morphisms with identity
first slots. -/
theorem modTensorMapMod_compR
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (B : D) [MonObj B] [IsCommMonObj B]
    {W X Y Z : Mod D B} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    modTensorMapMod B (𝟙 W) f ≫ modTensorMapMod B (𝟙 W) g =
      modTensorMapMod B (𝟙 W) (f ≫ g) := by
  rw [modTensorMapMod_comp, Category.comp_id]

/-- The relative tensor with two identities is the identity. -/
theorem modTensorMapMod_id
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (B : D) [MonObj B] [IsCommMonObj B]
    (X W : Mod D B) :
    modTensorMapMod B (𝟙 X) (𝟙 W) = 𝟙 (modTensorMod B X W) :=
  Mod.Hom.ext (by
    change modTensorMap B (𝟙 X) (𝟙 W) = _
    rw [modTensorMap_id, Mod.id_hom']
    rfl)

/-- **The insertion transports**: the base-changed sandwich
insertion, conjugated by the structure map, is the image of the
insertion. -/
theorem baseChange_sandwichIns
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M') :
    sandwichIns B (baseChangeDatum A B φ d) ≫
        modTensorMapMod B (projFormulaMod A B φ M M').hom
          (𝟙 (baseChangeMod φ M)) ≫
        (projFormulaMod A B φ (modTensorMod A M M') M).hom =
      baseChangeMapMod A B φ (sandwichIns A d) := by
  have hins : sandwichIns B (baseChangeDatum A B φ d) =
      (modTensorUnitLeftMod B (baseChangeMod φ M)).inv ≫
        modTensorMapMod B
          ((baseChangeDatum A B φ d).copairMod)
          (𝟙 (baseChangeMod φ M)) := rfl
  have hunit : (modTensorUnitLeftMod B
        (baseChangeMod φ M)).inv ≫
      modTensorMapMod B (baseChangeUnitIso A B φ).inv
        (𝟙 (baseChangeMod φ M)) =
    baseChangeMapMod A B φ
        (modTensorUnitLeftMod A M).inv ≫
      (projFormulaMod A B φ (regularMod A) M).inv := by
    have hiso : (projFormulaMod A B φ (regularMod A) M).trans
        (baseChangeMapIso A B φ
          (modTensorUnitLeftMod A M)) =
      Iso.trans
        { hom := modTensorMapMod B
            (baseChangeUnitIso A B φ).hom
            (𝟙 (baseChangeMod φ M))
          inv := modTensorMapMod B
            (baseChangeUnitIso A B φ).inv
            (𝟙 (baseChangeMod φ M))
          hom_inv_id := by
            rw [modTensorMapMod_compL, Iso.hom_inv_id,
              modTensorMapMod_id]
          inv_hom_id := by
            rw [modTensorMapMod_compL, Iso.inv_hom_id,
              modTensorMapMod_id] }
        (modTensorUnitLeftMod B (baseChangeMod φ M)) :=
      Iso.ext (projFormulaMod_unitLeft A B φ M)
    have hinv := congrArg Iso.inv hiso
    simp only [Iso.trans_inv] at hinv
    exact hinv.symm
  have hnat := projFormulaMod_natural_left A B φ
    (d.copairMod) M
  have step1 : sandwichIns B (baseChangeDatum A B φ d) ≫
      modTensorMapMod B (projFormulaMod A B φ M M').hom
        (𝟙 (baseChangeMod φ M)) =
    (modTensorUnitLeftMod B (baseChangeMod φ M)).inv ≫
      modTensorMapMod B (baseChangeUnitIso A B φ).inv
        (𝟙 (baseChangeMod φ M)) ≫
      modTensorMapMod B
        (baseChangeMapMod A B φ (d.copairMod))
        (𝟙 (baseChangeMod φ M)) := by
    rw [hins, copairMod_baseChangeDatum, Category.assoc]
    refine whisker_eq _ ?_
    rw [modTensorMapMod_compL, modTensorMapMod_compL]
    refine congrArg (fun t => modTensorMapMod B t
      (𝟙 (baseChangeMod φ M))) ?_
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  rw [← Category.assoc, step1]
  simp only [Category.assoc]
  rw [← Category.assoc, hunit]
  simp only [Category.assoc]
  rw [hnat, Iso.inv_hom_id_assoc, ← baseChangeMapMod_comp]
  rfl

/-- **The contraction transports**: the conjugated image of the
sandwich contraction is the base-changed contraction. -/
theorem baseChange_sandwichCon
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M') :
    (modTensorMapMod B (projFormulaMod A B φ M M').hom
        (𝟙 (baseChangeMod φ M)) ≫
      (projFormulaMod A B φ (modTensorMod A M M') M).hom) ≫
      baseChangeMapMod A B φ (sandwichCon A d) =
    sandwichCon B (baseChangeDatum A B φ d) := by
  have hcon : baseChangeMapMod A B φ (sandwichCon A d) =
      baseChangeMapMod A B φ
          (modTensorAssocModIso A M M' M).hom ≫
        baseChangeMapMod A B φ
          (modTensorMapMod A (𝟙 M) (d.pairMod)) ≫
        baseChangeMapMod A B φ
          (modTensorUnitRightMod A M).hom := by
    rw [← baseChangeMapMod_comp, ← baseChangeMapMod_comp]
    rfl
  have hRHS : sandwichCon B (baseChangeDatum A B φ d) =
      (modTensorAssocModIso B (baseChangeMod φ M)
          (baseChangeMod φ M') (baseChangeMod φ M)).hom ≫
        modTensorMapMod B (𝟙 (baseChangeMod φ M))
          (projFormulaMod A B φ M' M).hom ≫
        modTensorMapMod B (𝟙 (baseChangeMod φ M))
          (baseChangeMapMod A B φ (d.pairMod)) ≫
        modTensorMapMod B (𝟙 (baseChangeMod φ M))
          (baseChangeUnitIso A B φ).hom ≫
        (modTensorUnitRightMod B (baseChangeMod φ M)).hom := by
    change (modTensorAssocModIso B (baseChangeMod φ M)
        (baseChangeMod φ M') (baseChangeMod φ M)).hom ≫
      modTensorMapMod B (𝟙 (baseChangeMod φ M))
        ((baseChangeDatum A B φ d).pairMod) ≫
      (modTensorUnitRightMod B (baseChangeMod φ M)).hom = _
    rw [pairMod_baseChangeDatum, ← modTensorMapMod_compR,
      ← modTensorMapMod_compR]
    simp only [Category.assoc]
  rw [hcon, hRHS]
  simp only [Category.assoc]
  rw [(reassoc_of% (projFormulaMod_assoc A B φ M M' M))]
  rw [← Category.assoc
      (projFormulaMod A B φ M (modTensorMod A M' M)).hom,
    ← projFormulaMod_natural_right A B φ M (d.pairMod),
    Category.assoc, projFormulaMod_unitRight A B φ M]

/-- **The zig triangle transports**: the base-changed datum
satisfies the sandwich retract identity. -/
theorem baseChange_sandwich_zig
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M')
    (hz : ModZigzagDatum A d) :
    sandwichIns B (baseChangeDatum A B φ d) ≫
        sandwichCon B (baseChangeDatum A B φ d) =
      𝟙 (baseChangeMod φ M) := by
  rw [← baseChange_sandwichCon A B φ d, ← Category.assoc,
    baseChange_sandwichIns A B φ d, ← baseChangeMapMod_comp,
    (sandwich_zig_iff A d).mpr (zigzag_carrier_zig A hz),
    baseChangeMapMod_id]

/-- **The carrier zig law of the base-changed datum.** -/
theorem baseChange_carrier_zig
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M')
    (hz : ModZigzagDatum A d) :
    (λ_ (baseChangeMod φ M).X).inv ≫
        ((η[B] ≫ (baseChangeDatum A B φ d).copair) ▷
          (baseChangeMod φ M).X) ≫
        zigContract B (baseChangeDatum A B φ d).pair
          (baseChangeDatum A B φ d).pair_linear =
      𝟙 (baseChangeMod φ M).X :=
  (sandwich_zig_iff B (baseChangeDatum A B φ d)).mp
    (baseChange_sandwich_zig A B φ d hz)

/-- **The dual insertion transports**. -/
theorem baseChange_sandwichInsR
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M') :
    sandwichInsR B (baseChangeDatum A B φ d) ≫
        modTensorMapMod B (𝟙 (baseChangeMod φ M'))
          (projFormulaMod A B φ M M').hom ≫
        (projFormulaMod A B φ M' (modTensorMod A M M')).hom =
      baseChangeMapMod A B φ (sandwichInsR A d) := by
  have hins : sandwichInsR B (baseChangeDatum A B φ d) =
      (modTensorUnitRightMod B (baseChangeMod φ M')).inv ≫
        modTensorMapMod B (𝟙 (baseChangeMod φ M'))
          ((baseChangeDatum A B φ d).copairMod) := rfl
  have hunit : (modTensorUnitRightMod B
        (baseChangeMod φ M')).inv ≫
      modTensorMapMod B (𝟙 (baseChangeMod φ M'))
        (baseChangeUnitIso A B φ).inv =
    baseChangeMapMod A B φ
        (modTensorUnitRightMod A M').inv ≫
      (projFormulaMod A B φ M' (regularMod A)).inv := by
    have hiso : (projFormulaMod A B φ M' (regularMod A)).trans
        (baseChangeMapIso A B φ
          (modTensorUnitRightMod A M')) =
      Iso.trans
        { hom := modTensorMapMod B
            (𝟙 (baseChangeMod φ M'))
            (baseChangeUnitIso A B φ).hom
          inv := modTensorMapMod B
            (𝟙 (baseChangeMod φ M'))
            (baseChangeUnitIso A B φ).inv
          hom_inv_id := by
            rw [modTensorMapMod_compR, Iso.hom_inv_id,
              modTensorMapMod_id]
          inv_hom_id := by
            rw [modTensorMapMod_compR, Iso.inv_hom_id,
              modTensorMapMod_id] }
        (modTensorUnitRightMod B (baseChangeMod φ M')) :=
      Iso.ext (projFormulaMod_unitRight A B φ M')
    have hinv := congrArg Iso.inv hiso
    simp only [Iso.trans_inv] at hinv
    exact hinv.symm
  have hnat := projFormulaMod_natural_right A B φ M'
    (d.copairMod)
  have step1 : sandwichInsR B (baseChangeDatum A B φ d) ≫
      modTensorMapMod B (𝟙 (baseChangeMod φ M'))
        (projFormulaMod A B φ M M').hom =
    (modTensorUnitRightMod B (baseChangeMod φ M')).inv ≫
      modTensorMapMod B (𝟙 (baseChangeMod φ M'))
        (baseChangeUnitIso A B φ).inv ≫
      modTensorMapMod B (𝟙 (baseChangeMod φ M'))
        (baseChangeMapMod A B φ (d.copairMod)) := by
    rw [hins, copairMod_baseChangeDatum, Category.assoc]
    refine whisker_eq _ ?_
    rw [modTensorMapMod_compR, modTensorMapMod_compR]
    refine congrArg (fun t => modTensorMapMod B
      (𝟙 (baseChangeMod φ M')) t) ?_
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  rw [← Category.assoc, step1]
  simp only [Category.assoc]
  rw [← Category.assoc, hunit]
  simp only [Category.assoc]
  rw [hnat, Iso.inv_hom_id_assoc, ← baseChangeMapMod_comp]
  rfl

/-- **The dual contraction transports**. -/
theorem baseChange_sandwichConR
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M') :
    (modTensorMapMod B (𝟙 (baseChangeMod φ M'))
        (projFormulaMod A B φ M M').hom ≫
      (projFormulaMod A B φ M' (modTensorMod A M M')).hom) ≫
      baseChangeMapMod A B φ (sandwichConR A d) =
    sandwichConR B (baseChangeDatum A B φ d) := by
  have hassocInv : modTensorMapMod B
        (𝟙 (baseChangeMod φ M'))
        (projFormulaMod A B φ M M').hom ≫
      (projFormulaMod A B φ M' (modTensorMod A M M')).hom ≫
      baseChangeMapMod A B φ
        (modTensorAssocModIso A M' M M').inv =
    (modTensorAssocModIso B (baseChangeMod φ M')
        (baseChangeMod φ M) (baseChangeMod φ M')).inv ≫
      modTensorMapMod B (projFormulaMod A B φ M' M).hom
        (𝟙 (baseChangeMod φ M')) ≫
      (projFormulaMod A B φ (modTensorMod A M' M) M').hom := by
    have h1 : (modTensorAssocModIso B (baseChangeMod φ M')
          (baseChangeMod φ M) (baseChangeMod φ M')).hom ≫
        modTensorMapMod B (𝟙 (baseChangeMod φ M'))
          (projFormulaMod A B φ M M').hom ≫
        (projFormulaMod A B φ M' (modTensorMod A M M')).hom ≫
        baseChangeMapMod A B φ
          (modTensorAssocModIso A M' M M').inv =
      modTensorMapMod B (projFormulaMod A B φ M' M).hom
          (𝟙 (baseChangeMod φ M')) ≫
        (projFormulaMod A B φ
          (modTensorMod A M' M) M').hom := by
      have hc := congrArg (fun t => t ≫ baseChangeMapMod A B φ
        (modTensorAssocModIso A M' M M').inv)
        (projFormulaMod_assoc A B φ M' M M')
      simp only [Category.assoc] at hc
      rw [← baseChangeMapMod_comp, Iso.hom_inv_id,
        baseChangeMapMod_id, Category.comp_id] at hc
      exact hc.symm
    rw [← h1, Iso.inv_hom_id_assoc]
  have hcon : baseChangeMapMod A B φ (sandwichConR A d) =
      baseChangeMapMod A B φ
          (modTensorAssocModIso A M' M M').inv ≫
        baseChangeMapMod A B φ
          (modTensorMapMod A (d.pairMod) (𝟙 M')) ≫
        baseChangeMapMod A B φ
          (modTensorUnitLeftMod A M').hom := by
    rw [← baseChangeMapMod_comp, ← baseChangeMapMod_comp]
    rfl
  have hRHS : sandwichConR B (baseChangeDatum A B φ d) =
      (modTensorAssocModIso B (baseChangeMod φ M')
          (baseChangeMod φ M) (baseChangeMod φ M')).inv ≫
        modTensorMapMod B (projFormulaMod A B φ M' M).hom
          (𝟙 (baseChangeMod φ M')) ≫
        modTensorMapMod B
          (baseChangeMapMod A B φ (d.pairMod))
          (𝟙 (baseChangeMod φ M')) ≫
        modTensorMapMod B (baseChangeUnitIso A B φ).hom
          (𝟙 (baseChangeMod φ M')) ≫
        (modTensorUnitLeftMod B (baseChangeMod φ M')).hom := by
    change (modTensorAssocModIso B (baseChangeMod φ M')
        (baseChangeMod φ M) (baseChangeMod φ M')).inv ≫
      modTensorMapMod B
        ((baseChangeDatum A B φ d).pairMod)
        (𝟙 (baseChangeMod φ M')) ≫
      (modTensorUnitLeftMod B (baseChangeMod φ M')).hom = _
    rw [pairMod_baseChangeDatum, ← modTensorMapMod_compL,
      ← modTensorMapMod_compL]
    simp only [Category.assoc]
  rw [hcon, hRHS]
  simp only [Category.assoc]
  rw [reassoc_of% hassocInv]
  rw [← Category.assoc
      (projFormulaMod A B φ (modTensorMod A M' M) M').hom,
    ← projFormulaMod_natural_left A B φ (d.pairMod) M',
    Category.assoc, projFormulaMod_unitLeft A B φ M']

/-- **The zag triangle transports**. -/
theorem baseChange_sandwich_zag
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M')
    (hz : ModZigzagDatum A d) :
    sandwichInsR B (baseChangeDatum A B φ d) ≫
        sandwichConR B (baseChangeDatum A B φ d) =
      𝟙 (baseChangeMod φ M') := by
  rw [← baseChange_sandwichConR A B φ d, ← Category.assoc,
    baseChange_sandwichInsR A B φ d, ← baseChangeMapMod_comp,
    (sandwich_zag_iff A d).mpr (zigzag_carrier_zag A hz),
    baseChangeMapMod_id]

/-- **The carrier zag law of the base-changed datum.** -/
theorem baseChange_carrier_zag
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M')
    (hz : ModZigzagDatum A d) :
    (ρ_ (baseChangeMod φ M').X).inv ≫
        ((baseChangeMod φ M').X ◁
          (η[B] ≫ (baseChangeDatum A B φ d).copair)) ≫
        zagContract B (baseChangeDatum A B φ d).pair
          (baseChangeDatum A B φ d).pair_linear =
      𝟙 (baseChangeMod φ M').X :=
  (sandwich_zag_iff B (baseChangeDatum A B φ d)).mp
    (baseChange_sandwich_zag A B φ d hz)

/-- **Base change preserves the zigzag laws.** -/
theorem baseChange_modZigzagDatum
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M')
    (hz : ModZigzagDatum A d) :
    ModZigzagDatum B (baseChangeDatum A B φ d) :=
  modZigzagDatum_of_carrier B
    (baseChange_carrier_zig A B φ d hz)
    (baseChange_carrier_zag A B φ d hz)

end Transport

end Datum

section Statement

variable (D)

/-- **Base change preserves the zigzag laws**: the statement of
record, discharged. -/
theorem baseChangeZigzag
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)] :
    BaseChangeZigzagStatement (D := D) := by
  intro A _ _ M M' d hz B _ _ φ _
  exact baseChange_modZigzagDatum A B φ d hz

end Statement

end RS
