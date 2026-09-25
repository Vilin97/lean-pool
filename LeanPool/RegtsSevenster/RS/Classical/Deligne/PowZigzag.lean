/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ZigzagTransfer

/-!
# The power datum inherits the zigzag laws

Deligne's 1.15 tensor part, in chain form: the zigzag laws of a
duality datum pass to its tensor powers.  The bottom stage is the
transfer of the datum along the arity-one comparison isomorphisms
— the transfer theorem applies with trivial idempotents.  The
step peels one inserted couple off the onion-aligned copairing
power against the outermost ring of the nested pairing.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- The arity-one power pairing is the pairing, through the
comparison isomorphisms. -/
theorem modPowPairing_zero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    modPowPairing A M M' d 0 =
      modTensorMap A (fromModPowModZero A M')
        (fromModPowModZero A M) ≫ d.pair := by
  apply modTensor_hom_ext A (modPowMod A M'.X 0)
    (modPowMod A M.X 0)
  rw [modTensorπ_modPowPairing, ← Category.assoc,
    modTensorπ_map]
  have h2 : pairPow A M M' d 1 =
      ((modPowOne A M'.X).hom ⊗ₘ (modPowOne A M.X).hom) ≫
        pairRaw A M M' d := by
    rw [← modPowOne_pairPow A M M' d, ← Category.assoc,
      MonoidalCategory.tensorHom_comp_tensorHom,
      Iso.hom_inv_id, Iso.hom_inv_id,
      MonoidalCategory.id_tensorHom_id, Category.id_comp]
  rw [h2, pairRaw,
    show (fromModPowModZero A M').hom = (modPowOne A M'.X).hom
      from rfl,
    show (fromModPowModZero A M).hom = (modPowOne A M.X).hom
      from rfl, Category.assoc]
  rfl

/-- Duality data with equal pairings and copairings are equal. -/
theorem ModDualityDatum.ext'
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A]
    {N N' : Mod D A}
    {x y : ModDualityDatum A N N'}
    (hp : x.pair = y.pair) (hc : x.copair = y.copair) :
    x = y := by
  obtain ⟨p1, c1, _, _⟩ := x
  obtain ⟨p2, c2, _, _⟩ := y
  simp only at hp hc
  subst hp
  subst hc
  rfl

/-- **The bottom power datum is the transferred datum**: the
arity-one comparison isomorphisms carry the datum to its zeroth
power. -/
theorem powDualityDatum_zero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    powDualityDatum A M M' d 0 =
      d.transfer A (fromModPowModZero A M) (fromModPowModZero A M')
        (toModPowModZero A M) (toModPowModZero A M') :=
  ModDualityDatum.ext' A (modPowPairing_zero A M M' d)
    (powCopairA_zero A M M' d)

/-- **The bottom power datum satisfies the zigzag laws.** -/
theorem powDualityDatum_zigzag_zero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (hz : ModZigzagDatum A d) :
    ModZigzagDatum A (powDualityDatum A M M' d 0) := by
  rw [powDualityDatum_zero A M M' d]
  have hsr : fromModPowModZero A M ≫ toModPowModZero A M =
      𝟙 (modPowMod A M.X 0) :=
    Mod.hom_ext _ _ ((modPowOne A M.X).hom_inv_id)
  have hsr' : fromModPowModZero A M' ≫ toModPowModZero A M' =
      𝟙 (modPowMod A M'.X 0) :=
    Mod.hom_ext _ _ ((modPowOne A M'.X).hom_inv_id)
  have he : toModPowModZero A M ≫ fromModPowModZero A M =
      𝟙 M :=
    Mod.hom_ext _ _ ((modPowOne A M.X).inv_hom_id)
  have he' : toModPowModZero A M' ≫ fromModPowModZero A M' =
      𝟙 M' :=
    Mod.hom_ext _ _ ((modPowOne A M'.X).inv_hom_id)
  exact modZigzagDatum_transfer A d _ _ _ _ hz hsr hsr'
    (by rw [he, he'])

end RS
