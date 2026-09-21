/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.KeyLemma

/-!
# Nonvanishing detection from the zigzag laws

The general engine behind every stage-unit nonvanishing argument
in the Key Lemma: for a duality datum satisfying the zigzag laws,
the copair element detects nonvanishing of the module.  If the
element `η ≫ copair` vanishes then the zig composite vanishes,
yet the zigzag law says it is the identity of the single-factor
multi-tensor, which is therefore zero — and so is the module.

This is the open-diagram detection: it consumes the triangle
identity, never the loop composite, so it is uniform in the
categorical dimension of the module.  Applied to the power,
symmetric-power and chain-stage data it yields the stage units'
nonvanishing exactly from the nonvanishing of the corresponding
power objects.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- If the copair element vanishes, so does the module: the zig
composite factors through the copair element, and the zigzag law
makes it the identity. -/
theorem isZero_of_unit_copair_eq_zero
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M') (hz : ModZigzagDatum A d)
    (h0 : η[A] ≫ d.copair = 0) : IsZero M.X := by
  have hci : copairImage A d.copair = 0 := by
    rw [copairImage, ← Category.assoc, h0, zero_comp]
  have hzig : zigComposite A d.copair d.pair d.pair_linear = 0 := by
    rw [zigComposite, hci]
    simp
  have hid : IsZero (modMulti A [M]) := by
    rw [IsZero.iff_id_eq_zero]
    exact hz.zig.symm.trans hzig
  exact IsZero.of_iso hid (modMultiSingle A M).symm

/-- **The copair element detects nonvanishing**: over a zigzag
datum for a nonzero module, the copair element is nonzero.  This
is the open-diagram stage-unit detection of the Key Lemma. -/
theorem unit_copair_ne_zero
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M') (hz : ModZigzagDatum A d)
    (hM : ¬ IsZero M.X) : η[A] ≫ d.copair ≠ 0 :=
  fun h0 => hM (isZero_of_unit_copair_eq_zero A d hz h0)
