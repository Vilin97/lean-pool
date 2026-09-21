/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainNonzero
import LeanPool.RegtsSevenster.RS.Classical.Deligne.PowPairSucc
import LeanPool.RegtsSevenster.RS.Classical.Deligne.PowSuccMod
import LeanPool.RegtsSevenster.RS.Classical.Deligne.PowZigzag

/-!
# The power zigzag induction

The successor power datum is the transfer of the tensor of the
stage datum and the bottom datum along the merge isomorphism, so
the zigzag laws climb the powers: the base is the arity-one
transfer and the step is the tensor inheritance transferred along
the merge.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **The successor power datum is the transferred tensor
datum**: the merge isomorphism carries the tensor of the stage
datum and the bottom datum to the successor datum. -/
theorem powDualityDatum_succ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (n : ℕ) :
    powDualityDatum A M M' d (n + 1) =
      (tensorDatum A (powDualityDatum A M M' d n)
        (powDualityDatum A M M' d 0)).transfer A
        (powFrontModInv A M.X n) (powBackModInv A M'.X n)
        (powFrontMod A M.X n) (powBackMod A M'.X n) := by
  refine ModDualityDatum.ext' A ?_ ?_
  · show modPowPairing A M M' d (n + 1) =
      modTensorMap A (powBackModInv A M'.X n)
        (powFrontModInv A M.X n) ≫
      tensorPair A (powDualityDatum A M M' d n)
        (powDualityDatum A M M' d 0)
    rw [← modPowPairing_succ_tensor A M M' d n,
      ← Category.assoc, ← modTensorMap_comp]
    rw [show powBackModInv A M'.X n ≫ powMulMod A M'.X n 0 =
        𝟙 (modPowMod A M'.X (n + 1)) from
      powBackModInv_powBackMod A M'.X n]
    rw [show powFrontModInv A M.X n ≫
        (modTensorSwapMod A (modPowMod A M.X n)
            (modPowMod A M.X 0) ≫
          powMulMod A M.X 0 n ≫
          modPowCastMod A M.X
            (by omega : 0 + 1 + n + 1 = n + 2)) =
        𝟙 (modPowMod A M.X (n + 1)) from
      powFrontModInv_powFrontMod A M.X n]
    rw [modTensorMap_id, Category.id_comp]
  · show powCopairA A M M' d (n + 1) =
      tensorCopair A (powDualityDatum A M M' d n)
        (powDualityDatum A M M' d 0) ≫
      modTensorMap A (powFrontMod A M.X n)
        (powBackMod A M'.X n)
    exact powCopairA_succ_tensor A M M' d n

/-- **The power data satisfy the zigzag laws at every arity**:
the base is the arity-one transfer; the step transfers the tensor
inheritance along the merge isomorphism. -/
theorem powDualityDatum_zigzag_all
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (hz : ModZigzagDatum A d) :
    ∀ n, ModZigzagDatum A (powDualityDatum A M M' d n)
  | 0 => powDualityDatum_zigzag_zero A M M' d hz
  | (n + 1) => by
    rw [powDualityDatum_succ A M M' d n]
    have he : powFrontMod A M.X n ≫ powFrontModInv A M.X n =
        𝟙 _ := powFrontMod_powFrontModInv A M.X n
    have he' : powBackMod A M'.X n ≫ powBackModInv A M'.X n =
        𝟙 _ := powBackMod_powBackModInv A M'.X n
    exact modZigzagDatum_transfer A _
      (powFrontModInv A M.X n) (powBackModInv A M'.X n)
      (powFrontMod A M.X n) (powBackMod A M'.X n)
      (tensorDatum_zigzag A
        (powDualityDatum A M M' d n)
        (powDualityDatum A M M' d 0)
        (powDualityDatum_zigzag_all A M M' d hz n)
        (powDualityDatum_zigzag_zero A M M' d hz))
      (powFrontModInv_powFrontMod A M.X n)
      (powBackModInv_powBackMod A M'.X n)
      (by rw [he, he'])

section Detection

/-- **Unconditional nonvanishing of the chain unit stages**: for
a zigzag datum with nonvanishing symmetric powers, every chain
unit stage is nonzero. -/
theorem chainUnitStage_ne_zero_all
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [CategoryTheory.Linear ℂ D] [MonoidalLinear ℂ D]
    (d : ModDualityDatum A M M')
    (hz : ModZigzagDatum A d) (n : ℕ)
    (hS : ¬ IsZero (symPow A M.X (n + 1))) :
    chainUnitStage A M M' d n ≠ 0 :=
  chainUnitStage_ne_zero' A M M' d n
    (powDualityDatum_zigzag_all A M M' d hz n) hS

end Detection

end RS
