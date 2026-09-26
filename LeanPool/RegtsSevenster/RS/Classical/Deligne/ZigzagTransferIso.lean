/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ZigzagTransfer

/-!
# Transport of the zigzag laws along isomorphisms

An isomorphism is a section–retraction pair whose composite
idempotent is the identity, so the adjointness condition of the
transfer is vacuous and the zigzag laws pass across without any
further hypothesis.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

section TransferIso

/-- **Transport of a duality datum along isomorphisms** of the
two modules. -/
noncomputable def ModDualityDatum.transferIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {P : Mod D A} {P' : Mod D A}
    {Q : Mod D A} {Q' : Mod D A} (d₀ : ModDualityDatum A P P') (i : Q ≅ P)
    (i' : Q' ≅ P') :
    ModDualityDatum A Q Q' :=
  d₀.transfer A i.hom i'.hom i.inv i'.inv

/-- The adjointness condition of the transfer is vacuous for
isomorphisms: both composite idempotents are identities. -/
theorem transferIso_adj
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {P : Mod D A} {P' : Mod D A}
    {Q : Mod D A} {Q' : Mod D A} (d₀ : ModDualityDatum A P P') (i : Q ≅ P)
    (i' : Q' ≅ P') :
    modTensorMap A (i'.inv ≫ i'.hom) (𝟙 P) ≫ d₀.pair =
      modTensorMap A (𝟙 P') (i.inv ≫ i.hom) ≫ d₀.pair := by
  rw [i.inv_hom_id, i'.inv_hom_id]

/-- **The zigzag laws transport along isomorphisms.** -/
theorem modZigzagDatum_transferIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {P : Mod D A} {P' : Mod D A}
    {Q : Mod D A} {Q' : Mod D A} (d₀ : ModDualityDatum A P P') (i : Q ≅ P)
    (i' : Q' ≅ P')
    (hz₀ : ModZigzagDatum A d₀) :
    ModZigzagDatum A (d₀.transferIso A i i') :=
  modZigzagDatum_transfer A d₀ i.hom i'.hom i.inv i'.inv hz₀
    i.hom_inv_id i'.hom_inv_id (transferIso_adj A d₀ i i')

end TransferIso

end RS
