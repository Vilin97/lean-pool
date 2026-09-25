/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainBridge
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ZigzagTransfer

/-!
# Nonvanishing of the splitting-chain units

The assembly of the Key Lemma's nonvanishing half: the chain unit
stage is the copair element of the symmetric-power duality datum,
up to the braiding of the module tensor product; so once the
symmetric-power datum satisfies the zigzag laws, a vanishing
stage unit kills the symmetric power.  This is Deligne's
argument: `δⁿ` is the `δ` of a duality between the symmetric
powers (1.15.1), and the `δ` of a duality vanishes only on the
zero module.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **The chain unit stage is the symmetric copair element**, up
to the braiding of the module tensor product: Deligne's 1.15.1
composite. -/
theorem chainUnitStage_eq_symCopair
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [CategoryTheory.Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (n : ℕ) :
    chainUnitStage A M M' d n =
      η[A] ≫ (symDualityDatum A M M' d n).copair ≫
        modTensorSwap A (symPowMod A M.X n) (symPowMod A M'.X n) := by
  have h1 : (symDualityDatum A M M' d n).copair =
      powCopairA A M M' d n ≫
        modTensorMap A (symPowπMod A n) (symPowπMod A n) := rfl
  have hproj : projStage A M M' n =
      modTensorMap A (symPowπMod A n) (symPowπMod A n) ≫
        modTensorSwap A (symPowMod A M.X n)
          (symPowMod A M'.X n) := by
    rw [projStage]
    exact (modTensorMap_swap A (symPowπMod A n)
      (symPowπMod A n)).symm
  erw [h1, Category.assoc, ← powUnitStage_projStage A M M' d n,
    hproj, reassoc_of% (powCopairA_unit A M M' d n)]
  rfl

/-- **Nonvanishing of the chain unit stages**: once the
symmetric-power datum satisfies the zigzag laws, the stage unit
detects the symmetric power. -/
theorem chainUnitStage_ne_zero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [CategoryTheory.Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (n : ℕ)
    (hz : ModZigzagDatum A (symDualityDatum A M M' d n))
    (hS : ¬ IsZero (symPow A M.X (n + 1))) :
    chainUnitStage A M M' d n ≠ 0 := by
  intro h0
  have hcop : η[A] ≫ (symDualityDatum A M M' d n).copair = 0 := by
    have h2 : (η[A] ≫ (symDualityDatum A M M' d n).copair ≫
        modTensorSwap A (symPowMod A M.X n)
          (symPowMod A M'.X n)) ≫
        modTensorSwap A (symPowMod A M'.X n)
          (symPowMod A M.X n) = 0 := by
      rw [← chainUnitStage_eq_symCopair, h0]
      exact zero_comp
    have h3 : η[A] ≫ (symDualityDatum A M M' d n).copair =
        (η[A] ≫ (symDualityDatum A M M' d n).copair ≫
          modTensorSwap A (symPowMod A M.X n)
            (symPowMod A M'.X n)) ≫
          modTensorSwap A (symPowMod A M'.X n)
            (symPowMod A M.X n) := by
      conv_rhs => rw [Category.assoc, Category.assoc,
        modTensorSwap_modTensorSwap, Category.comp_id]
    rw [h3]
    exact h2
  have hM : ¬ IsZero ((symPowMod A M.X n).X) := hS
  exact absurd
    (isZero_of_unit_copair_eq_zero A
      (symDualityDatum A M M' d n) hz hcop) hM

/-- **Nonvanishing from the power-level zigzags**: composing the
detection with the symmetric-power inheritance. -/
theorem chainUnitStage_ne_zero'
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [CategoryTheory.Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (n : ℕ)
    (hz : ModZigzagDatum A (powDualityDatum A M M' d n))
    (hS : ¬ IsZero (symPow A M.X (n + 1))) :
    chainUnitStage A M M' d n ≠ 0 :=
  chainUnitStage_ne_zero A M M' d n
    (symDualityDatum_zigzag A M M' d n hz) hS

end RS
