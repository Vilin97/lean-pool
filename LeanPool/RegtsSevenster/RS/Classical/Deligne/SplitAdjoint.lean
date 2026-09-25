/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.BaseChangeAdjoint

/-!
# Adjointness of the split idempotents

The split idempotent on the base change and its dual counterpart
are adjoint for the base-changed pairing: moving either across
the pairing gives the other.  The two coevaluation identities
turn each side into a tensor of the two evaluations, and the
whisker exchange identifies them.

Passing to the complementary idempotents gives the adjointness
in the form the dévissage step consumes.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **The split idempotents are adjoint for the base-changed
pairing.** -/
theorem splitIdem_adj
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] {M : Mod D A} {M' : Mod D A} (v : M.X ⟶ B)
    (w : M'.X ⟶ B)
    (d : ModDualityDatum A M M')
    (hz : ModZigzagDatum A d)
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    (splitIdemDual A B φ v w d hv hw ▷
        (baseChangeMod φ M).X) ≫
        modTensorπ B (baseChangeMod φ M') (baseChangeMod φ M) ≫
        (baseChangeDatum A B φ d).pair =
      ((baseChangeMod φ M').X ◁
          splitIdem A B φ v w d hv hw) ≫
        modTensorπ B (baseChangeMod φ M') (baseChangeMod φ M) ≫
        (baseChangeDatum A B φ d).pair := by
  rw [splitIdemDual, splitIdem,
    MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [splitCoevalDual_pair A B φ v d hz hv,
    splitCoeval_pair A B φ w d hz hw]
  exact (whisker_exchange_assoc (splitEval A B φ w hw)
    (splitEval A B φ v hv) μ[B]).symm

/-- **The complementary split idempotents are adjoint for the
base-changed pairing**, at the carrier. -/
theorem splitComplIdem_adj
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] {M : Mod D A} {M' : Mod D A} (v : M.X ⟶ B)
    (w : M'.X ⟶ B)
    (d : ModDualityDatum A M M')
    (hz : ModZigzagDatum A d)
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    ((𝟙 (baseChange φ M') -
          splitIdemDual A B φ v w d hv hw) ▷
        (baseChangeMod φ M).X) ≫
        modTensorπ B (baseChangeMod φ M') (baseChangeMod φ M) ≫
        (baseChangeDatum A B φ d).pair =
      ((baseChangeMod φ M').X ◁
          (𝟙 (baseChange φ M) -
            splitIdem A B φ v w d hv hw)) ≫
        modTensorπ B (baseChangeMod φ M') (baseChangeMod φ M) ≫
        (baseChangeDatum A B φ d).pair := by
  have hsubR : ∀ {U V : D} (f g : U ⟶ V) (W : D),
      (f - g) ▷ W = f ▷ W - g ▷ W := by
    intro U V f g W
    exact (tensorRight W).map_sub
  have hsubL : ∀ {U V : D} (W : D) (f g : U ⟶ V),
      W ◁ (f - g) = W ◁ f - W ◁ g := by
    intro U V W f g
    exact (tensorLeft W).map_sub
  rw [hsubR, hsubL, Preadditive.sub_comp, Preadditive.sub_comp,
    MonoidalCategory.id_whiskerRight,
    MonoidalCategory.whiskerLeft_id,
    splitIdem_adj A B φ v w d hz hv hw]
  rfl

/-- **Adjointness of the split idempotents**, in the module form
the dévissage step consumes. -/
theorem splitComplMap_adj
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [HasKernels D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ] {M : Mod D A} {M' : Mod D A} (v : M.X ⟶ B)
    (w : M'.X ⟶ B)
    (d : ModDualityDatum A M M')
    (hz : ModZigzagDatum A d)
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B])
    (p : modTensor A M M' ⟶ B)
    (hp : modTensorπ A M M' ≫ p = (v ⊗ₘ w) ≫ μ[B])
    (hδ : η[A] ≫ d.copair ≫ p = η[B]) :
    modTensorMap B
        (splitComplProjModDual A B φ v w d hv hw p hp hδ ≫
          splitComplInclDual A B φ v w d hv hw)
        (𝟙 (baseChangeMod φ M)) ≫
        (baseChangeDatum A B φ d).pair =
      modTensorMap B
        (𝟙 (baseChangeMod φ M'))
        (splitComplProjMod A B φ v w d hv hw p hp hδ ≫
          splitComplIncl A B φ v w d hv hw) ≫
        (baseChangeDatum A B φ d).pair := by
  apply modTensor_hom_ext
  rw [← Category.assoc, ← Category.assoc, modTensorπ_map,
    modTensorπ_map]
  simp only [Category.assoc, Mod.comp_hom', Mod.id_hom',
    MonoidalCategory.tensorHom_id,
    MonoidalCategory.id_tensorHom]
  have hd : (splitComplProjModDual A B φ v w d hv hw p hp
        hδ).hom ≫
      (splitComplInclDual A B φ v w d hv hw).hom =
      𝟙 (baseChange φ M') - splitIdemDual A B φ v w d hv hw :=
    splitComplProjDual_ι A B φ v w d hv hw p hp hδ
  have hpr : (splitComplProjMod A B φ v w d hv hw p hp hδ).hom ≫
      (splitComplIncl A B φ v w d hv hw).hom =
      𝟙 (baseChange φ M) - splitIdem A B φ v w d hv hw :=
    splitComplProj_ι A B φ v w d hv hw p hp hδ
  rw [hd, hpr]
  exact splitComplIdem_adj A B φ v w d hz hv hw

end RS
