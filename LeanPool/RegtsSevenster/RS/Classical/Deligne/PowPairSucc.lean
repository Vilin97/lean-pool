/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.PowSucc

/-!
# The pair side of the power step

Deligne's 1.15 power induction, pair side: pushing the primed back
merge and the swapped unprimed front merge into the successor power
pairing yields the tensor pairing of the stage datum with the bottom
datum.  The comparison is taken over the projection cover, where the
successor triangle core (`powDeltaCore_pairing`) supplies the
identity after a symmetric rearrangement of the four carriers; the
rearrangement itself is the retraction `tensorMu_braid_retract`, a
pure braid coherence.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

section Coherence

/-- Interchanging the middle factors twice is the identity: the two
elementary crossings cancel by the symmetry axiom. -/
@[reassoc]
private theorem tensorMu_symm_cancel
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (a b c d : D) :
    tensorμ a b c d ≫ tensorμ a c b d =
      𝟙 ((a ⊗ b) ⊗ (c ⊗ d)) := by
  calc
    tensorμ a b c d ≫ tensorμ a c b d
        = 𝟙 ((a ⊗ b) ⊗ (c ⊗ d)) ⊗≫
            a ◁ ((β_ b c).hom ≫ (β_ c b).hom) ▷ d ⊗≫
            𝟙 ((a ⊗ b) ⊗ (c ⊗ d)) := by
          dsimp only [tensorμ]
          monoidal
    _ = 𝟙 ((a ⊗ b) ⊗ (c ⊗ d)) := by
          rw [SymmetricCategory.symmetry]
          monoidal

/-- **The braid retraction of the double interchange**: shuffling,
braiding slotwise, shuffling the braided blocks, and braiding the
block pair returns every strand to its place. -/
@[reassoc]
private theorem tensorMu_braid_retract
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (W X Y Z : D) :
    tensorμ W X Y Z ≫ ((β_ W Y).hom ⊗ₘ (β_ X Z).hom) ≫
      tensorμ Y W Z X ≫ (β_ (Y ⊗ Z) (W ⊗ X)).hom =
    𝟙 ((W ⊗ X) ⊗ (Y ⊗ Z)) := by
  rw [← tensorμ_braiding_assoc W X Y Z,
    tensorMu_symm_cancel_assoc]
  exact SymmetricCategory.symmetry _ _

end Coherence

section Fold

/-- Evaluating the tensor-pairing word on a pure tensor of
projections: the interchange seats each dual half against its own
carrier, the coordinatewise pairings evaluate, and the fold
multiplies the two scalars. -/
private theorem tensorHom_π_pairFold
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {N₁ : Mod D A} {N₂ : Mod D A}
    {N₁' : Mod D A} {N₂' : Mod D A}
    (d₁ : ModDualityDatum A N₁ N₁')
    (d₂ : ModDualityDatum A N₂ N₂') :
    ((modTensorπ A N₁' N₂' ⊗ₘ modTensorπ A N₁ N₂) :
        (N₁'.X ⊗ N₂'.X) ⊗ (N₁.X ⊗ N₂.X) ⟶ _) ≫
      interchange A N₁' N₂' N₁ N₂ ≫
      modTensorMap A d₁.pairMod d₂.pairMod ≫ regPairFold A =
    tensorμ N₁'.X N₂'.X N₁.X N₂.X ≫
      ((modTensorπ A N₁' N₁ ≫ d₁.pair) ⊗ₘ
        (modTensorπ A N₂' N₂ ≫ d₂.pair)) ≫ μ[A] := by
  have hfold : modTensorπ A (regularMod A) (regularMod A) ≫
      regPairFold A = μ[A] := by
    rw [regPairFold]
    exact modTensorπ_desc A _ _ _ _
  have hm : modTensorπ A (modTensorMod A N₁' N₁)
      (modTensorMod A N₂' N₂) ≫
      modTensorMap A d₁.pairMod d₂.pairMod =
      (d₁.pair ⊗ₘ d₂.pair) ≫
        modTensorπ A (regularMod A) (regularMod A) :=
    modTensorπ_map A d₁.pairMod d₂.pairMod
  have htail : (modTensorπ A N₁' N₁ ⊗ₘ modTensorπ A N₂' N₂) ≫
      modTensorπ A (modTensorMod A N₁' N₁)
        (modTensorMod A N₂' N₂) ≫
      modTensorMap A d₁.pairMod d₂.pairMod ≫
      regPairFold A =
      ((modTensorπ A N₁' N₁ ≫ d₁.pair) ⊗ₘ
        (modTensorπ A N₂' N₂ ≫ d₂.pair)) ≫ μ[A] := by
    have t2 : modTensorπ A (modTensorMod A N₁' N₁)
        (modTensorMod A N₂' N₂) ≫
        modTensorMap A d₁.pairMod d₂.pairMod ≫
        regPairFold A =
        (d₁.pair ⊗ₘ d₂.pair) ≫ μ[A] := by
      rw [← Category.assoc, hm]
      exact (Category.assoc _ _ _).trans
        (congrArg (fun t : (regularMod A).X ⊗
            (regularMod A).X ⟶ A =>
          (d₁.pair ⊗ₘ d₂.pair) ≫ t) hfold)
    exact (congrArg (fun t : (modTensorMod A N₁' N₁).X ⊗
          (modTensorMod A N₂' N₂).X ⟶ A =>
        (modTensorπ A N₁' N₁ ⊗ₘ modTensorπ A N₂' N₂) ≫ t)
      t2).trans (by
        rw [← MonoidalCategory.tensorHom_comp_tensorHom_assoc])
  erw [← Category.assoc, tensorHom_π_interchange, rawInterchangeπ, rawInterchange]
  conv_lhs => erw [Category.assoc]; arg 2; erw [Category.assoc]
  simpa only [Category.assoc] using congrArg (fun t : (N₁'.X ⊗ N₁.X) ⊗ (N₂'.X ⊗ N₂.X) ⟶
      A => tensorμ N₁'.X N₂'.X N₁.X N₂.X ≫ t) htail

end Fold

private theorem modPowPairing_succ_tensor_leftCover
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (n : ℕ) :
    (modTensorπ A (modPowMod A M.X n)
        (modPowMod A M'.X n) ⊗ₘ
      modTensorπ A (modPowMod A M.X 0) (modPowMod A M'.X 0)) ≫
      interchange A (modPowMod A M.X n) (modPowMod A M'.X n)
        (modPowMod A M.X 0) (modPowMod A M'.X 0) ≫
      modTensorMap A
        (modTensorSwapMod A (modPowMod A M.X n)
            (modPowMod A M.X 0) ≫
          powMulMod A M.X 0 n ≫
          modPowCastMod A M.X
            (by omega : 0 + 1 + n + 1 = n + 2))
        (powMulMod A M'.X n 0) ≫
      modTensorSwap A (modPowMod A M.X (n + 1))
        (modPowMod A M'.X (n + 1)) ≫
      modPowPairing A M M' d (n + 1) =
    tensorμ (modPowMod A M.X n).X (modPowMod A M'.X n).X
        (modPowMod A M.X 0).X (modPowMod A M'.X 0).X ≫
      ((modTensorπ A (modPowMod A M.X n)
          (modPowMod A M.X 0) ≫
        (modTensorSwapMod A (modPowMod A M.X n)
            (modPowMod A M.X 0) ≫
          powMulMod A M.X 0 n ≫
          modPowCastMod A M.X
            (by omega : 0 + 1 + n + 1 = n + 2)).hom) ⊗ₘ
        (modTensorπ A (modPowMod A M'.X n)
            (modPowMod A M'.X 0) ≫
          (powMulMod A M'.X n 0).hom)) ≫
      (β_ (modPowMod A M.X (n + 1)).X
        (modPowMod A M'.X (n + 1)).X).hom ≫
      pairPow A M M' d (n + 2) := by
  have hstep : modTensorπ A (modPowMod A M.X (n + 1))
      (modPowMod A M'.X (n + 1)) ≫
      modTensorSwap A (modPowMod A M.X (n + 1))
        (modPowMod A M'.X (n + 1)) ≫
      modPowPairing A M M' d (n + 1) =
      (β_ (modPowMod A M.X (n + 1)).X
        (modPowMod A M'.X (n + 1)).X).hom ≫
      pairPow A M M' d (n + 2) := by
    rw [modTensorπ_swap_assoc, modTensorπ_modPowPairing]
  -- The triangle core, evaluated on the projection cover: left.
  have hL2 : (modTensorπ A (modPowMod A M.X n)
        (modPowMod A M'.X n) ⊗ₘ
      modTensorπ A (modPowMod A M.X 0) (modPowMod A M'.X 0)) ≫
      interchange A (modPowMod A M.X n) (modPowMod A M'.X n)
        (modPowMod A M.X 0) (modPowMod A M'.X 0) ≫
      modTensorMap A
        (modTensorSwapMod A (modPowMod A M.X n)
            (modPowMod A M.X 0) ≫
          powMulMod A M.X 0 n ≫
          modPowCastMod A M.X
            (by omega : 0 + 1 + n + 1 = n + 2))
        (powMulMod A M'.X n 0) ≫
      modTensorSwap A (modPowMod A M.X (n + 1))
        (modPowMod A M'.X (n + 1)) ≫
      modPowPairing A M M' d (n + 1) =
      tensorμ (modPowMod A M.X n).X (modPowMod A M'.X n).X
        (modPowMod A M.X 0).X (modPowMod A M'.X 0).X ≫
      ((modTensorπ A (modPowMod A M.X n)
          (modPowMod A M.X 0) ≫
        (modTensorSwapMod A (modPowMod A M.X n)
            (modPowMod A M.X 0) ≫
          powMulMod A M.X 0 n ≫
          modPowCastMod A M.X
            (by omega : 0 + 1 + n + 1 = n + 2)).hom) ⊗ₘ
        (modTensorπ A (modPowMod A M'.X n)
            (modPowMod A M'.X 0) ≫
          (powMulMod A M'.X n 0).hom)) ≫
      (β_ (modPowMod A M.X (n + 1)).X
        (modPowMod A M'.X (n + 1)).X).hom ≫
      pairPow A M M' d (n + 2) := by
    have hmap2 : modTensorπ A
        (modTensorMod A (modPowMod A M.X n) (modPowMod A M.X 0))
        (modTensorMod A (modPowMod A M'.X n)
          (modPowMod A M'.X 0)) ≫
        modTensorMap A
          (modTensorSwapMod A (modPowMod A M.X n)
              (modPowMod A M.X 0) ≫
            powMulMod A M.X 0 n ≫
            modPowCastMod A M.X
              (by omega : 0 + 1 + n + 1 = n + 2))
          (powMulMod A M'.X n 0) ≫
        modTensorSwap A (modPowMod A M.X (n + 1))
          (modPowMod A M'.X (n + 1)) ≫
        modPowPairing A M M' d (n + 1) =
        ((modTensorSwapMod A (modPowMod A M.X n)
              (modPowMod A M.X 0) ≫
            powMulMod A M.X 0 n ≫
            modPowCastMod A M.X
              (by omega : 0 + 1 + n + 1 = n + 2)).hom ⊗ₘ
          (powMulMod A M'.X n 0).hom) ≫
        (β_ (modPowMod A M.X (n + 1)).X
          (modPowMod A M'.X (n + 1)).X).hom ≫
        pairPow A M M' d (n + 2) := by
      refine Eq.trans (modTensorπ_map_assoc A _ _ _) ?_
      exact congrArg (fun t : (modPowMod A M.X (n + 1)).X ⊗
          (modPowMod A M'.X (n + 1)).X ⟶ A =>
        ((modTensorSwapMod A (modPowMod A M.X n)
              (modPowMod A M.X 0) ≫
            powMulMod A M.X 0 n ≫
            modPowCastMod A M.X
              (by omega : 0 + 1 + n + 1 = n + 2)).hom ⊗ₘ
          (powMulMod A M'.X n 0).hom) ≫ t) hstep
    erw [tensorHom_π_interchange_assoc, rawInterchangeπ, rawInterchange]
    simp only [Category.assoc]
    conv_lhs => arg 2; erw [Category.assoc]
    refine Eq.trans (congrArg (fun t :
        (modTensorMod A (modPowMod A M.X n)
          (modPowMod A M.X 0)).X ⊗
        (modTensorMod A (modPowMod A M'.X n)
          (modPowMod A M'.X 0)).X ⟶ A =>
      tensorμ (modPowMod A M.X n).X (modPowMod A M'.X n).X
          (modPowMod A M.X 0).X (modPowMod A M'.X 0).X ≫
        (modTensorπ A (modPowMod A M.X n)
            (modPowMod A M.X 0) ⊗ₘ
          modTensorπ A (modPowMod A M'.X n)
            (modPowMod A M'.X 0)) ≫ t) hmap2) ?_
    refine congrArg (fun t : ((modPowMod A M.X n).X ⊗
        (modPowMod A M.X 0).X) ⊗
        ((modPowMod A M'.X n).X ⊗
          (modPowMod A M'.X 0).X) ⟶ A =>
      tensorμ (modPowMod A M.X n).X (modPowMod A M'.X n).X
          (modPowMod A M.X 0).X (modPowMod A M'.X 0).X ≫ t) ?_
    exact MonoidalCategory.tensorHom_comp_tensorHom_assoc
      _ _ _ _ _
  -- The triangle core, covered by the projections.
  exact hL2

private theorem modPowPairing_succ_tensor_rightCover
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (n : ℕ) :
    (modTensorπ A (modPowMod A M.X n)
        (modPowMod A M'.X n) ⊗ₘ
      modTensorπ A (modPowMod A M.X 0) (modPowMod A M'.X 0)) ≫
      ((modTensorSwap A (modPowMod A M.X n)
          (modPowMod A M'.X n) ≫
        modPowPairing A M M' d n) ⊗ₘ
        (modTensorSwap A (modPowMod A M.X 0)
            (modPowMod A M'.X 0) ≫
          modPowPairing A M M' d 0)) ≫ μ[A] =
    ((β_ (modPowMod A M.X n).X
          (modPowMod A M'.X n).X).hom ⊗ₘ
        (β_ (modPowMod A M.X 0).X
          (modPowMod A M'.X 0).X).hom) ≫
      ((modTensorπ A (modPowMod A M'.X n)
          (modPowMod A M.X n) ≫
        modPowPairing A M M' d n) ⊗ₘ
        (modTensorπ A (modPowMod A M'.X 0)
            (modPowMod A M.X 0) ≫
          modPowPairing A M M' d 0)) ≫ μ[A] := by
  have hswn : modTensorπ A (modPowMod A M.X n)
      (modPowMod A M'.X n) ≫
      modTensorSwap A (modPowMod A M.X n) (modPowMod A M'.X n) ≫
      modPowPairing A M M' d n =
      (β_ (modPowMod A M.X n).X (modPowMod A M'.X n).X).hom ≫
      modTensorπ A (modPowMod A M'.X n) (modPowMod A M.X n) ≫
      modPowPairing A M M' d n := by
    rw [modTensorπ_swap_assoc]
  have hsw0 : modTensorπ A (modPowMod A M.X 0)
      (modPowMod A M'.X 0) ≫
      modTensorSwap A (modPowMod A M.X 0) (modPowMod A M'.X 0) ≫
      modPowPairing A M M' d 0 =
      (β_ (modPowMod A M.X 0).X (modPowMod A M'.X 0).X).hom ≫
      modTensorπ A (modPowMod A M'.X 0) (modPowMod A M.X 0) ≫
      modPowPairing A M M' d 0 := by
    rw [modTensorπ_swap_assoc]
  -- The triangle core, evaluated on the projection cover: right.
  have hR2 : (modTensorπ A (modPowMod A M.X n)
        (modPowMod A M'.X n) ⊗ₘ
      modTensorπ A (modPowMod A M.X 0) (modPowMod A M'.X 0)) ≫
      ((modTensorSwap A (modPowMod A M.X n)
          (modPowMod A M'.X n) ≫
        modPowPairing A M M' d n) ⊗ₘ
        (modTensorSwap A (modPowMod A M.X 0)
            (modPowMod A M'.X 0) ≫
          modPowPairing A M M' d 0)) ≫ μ[A] =
      ((β_ (modPowMod A M.X n).X
          (modPowMod A M'.X n).X).hom ⊗ₘ
        (β_ (modPowMod A M.X 0).X
          (modPowMod A M'.X 0).X).hom) ≫
      ((modTensorπ A (modPowMod A M'.X n)
          (modPowMod A M.X n) ≫
        modPowPairing A M M' d n) ⊗ₘ
        (modTensorπ A (modPowMod A M'.X 0)
            (modPowMod A M.X 0) ≫
          modPowPairing A M M' d 0)) ≫ μ[A] := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc, hswn,
      hsw0, ← MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  -- The core identity over the cover.
  exact hR2

private theorem modPowPairing_succ_tensor_braidingRetract
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (n : ℕ) :
    tensorμ (modPowMod A M'.X n).X
      (modPowMod A M'.X 0).X (modPowMod A M.X n).X
      (modPowMod A M.X 0).X ≫
      ((β_ (modPowMod A M'.X n).X
          (modPowMod A M.X n).X).hom ⊗ₘ
        (β_ (modPowMod A M'.X 0).X
          (modPowMod A M.X 0).X).hom) ≫
      tensorμ (modPowMod A M.X n).X (modPowMod A M'.X n).X
        (modPowMod A M.X 0).X (modPowMod A M'.X 0).X ≫
      ((modTensorπ A (modPowMod A M.X n)
          (modPowMod A M.X 0) ≫
        (modTensorSwapMod A (modPowMod A M.X n)
            (modPowMod A M.X 0) ≫
          powMulMod A M.X 0 n ≫
          modPowCastMod A M.X
            (by omega : 0 + 1 + n + 1 = n + 2)).hom) ⊗ₘ
        (modTensorπ A (modPowMod A M'.X n)
            (modPowMod A M'.X 0) ≫
          (powMulMod A M'.X n 0).hom)) ≫
      (β_ (modPowMod A M.X (n + 1)).X
        (modPowMod A M'.X (n + 1)).X).hom ≫
      pairPow A M M' d (n + 2) =
    ((modTensorπ A (modPowMod A M'.X n)
          (modPowMod A M'.X 0) ≫
        (powMulMod A M'.X n 0).hom) ⊗ₘ
        (modTensorπ A (modPowMod A M.X n)
            (modPowMod A M.X 0) ≫
          (modTensorSwapMod A (modPowMod A M.X n)
              (modPowMod A M.X 0) ≫
            powMulMod A M.X 0 n ≫
            modPowCastMod A M.X
              (by omega : 0 + 1 + n + 1 = n + 2)).hom)) ≫
      pairPow A M M' d (n + 2) := by
  have hnat3 : ((modTensorπ A (modPowMod A M.X n)
        (modPowMod A M.X 0) ≫
      (modTensorSwapMod A (modPowMod A M.X n)
          (modPowMod A M.X 0) ≫
        powMulMod A M.X 0 n ≫
        modPowCastMod A M.X
          (by omega : 0 + 1 + n + 1 = n + 2)).hom) ⊗ₘ
      (modTensorπ A (modPowMod A M'.X n)
          (modPowMod A M'.X 0) ≫
        (powMulMod A M'.X n 0).hom)) ≫
      (β_ (modPowMod A M.X (n + 1)).X
        (modPowMod A M'.X (n + 1)).X).hom ≫
      pairPow A M M' d (n + 2) =
      (β_ ((modPowMod A M.X n).X ⊗ (modPowMod A M.X 0).X)
        ((modPowMod A M'.X n).X ⊗
          (modPowMod A M'.X 0).X)).hom ≫
      ((modTensorπ A (modPowMod A M'.X n)
          (modPowMod A M'.X 0) ≫
        (powMulMod A M'.X n 0).hom) ⊗ₘ
        (modTensorπ A (modPowMod A M.X n)
            (modPowMod A M.X 0) ≫
          (modTensorSwapMod A (modPowMod A M.X n)
              (modPowMod A M.X 0) ≫
            powMulMod A M.X 0 n ≫
            modPowCastMod A M.X
              (by omega : 0 + 1 + n + 1 = n + 2)).hom)) ≫
      pairPow A M M' d (n + 2) :=
    BraidedCategory.braiding_naturality_assoc
      (modTensorπ A (modPowMod A M.X n)
          (modPowMod A M.X 0) ≫
        (modTensorSwapMod A (modPowMod A M.X n)
            (modPowMod A M.X 0) ≫
          powMulMod A M.X 0 n ≫
          modPowCastMod A M.X
            (by omega : 0 + 1 + n + 1 = n + 2)).hom)
      (modTensorπ A (modPowMod A M'.X n)
          (modPowMod A M'.X 0) ≫
        (powMulMod A M'.X n 0).hom)
      (pairPow A M M' d (n + 2))
  -- The rearrangement retracts onto the merged pair.
  have hfinalL : tensorμ (modPowMod A M'.X n).X
      (modPowMod A M'.X 0).X (modPowMod A M.X n).X
      (modPowMod A M.X 0).X ≫
      ((β_ (modPowMod A M'.X n).X
          (modPowMod A M.X n).X).hom ⊗ₘ
        (β_ (modPowMod A M'.X 0).X
          (modPowMod A M.X 0).X).hom) ≫
      tensorμ (modPowMod A M.X n).X (modPowMod A M'.X n).X
        (modPowMod A M.X 0).X (modPowMod A M'.X 0).X ≫
      ((modTensorπ A (modPowMod A M.X n)
          (modPowMod A M.X 0) ≫
        (modTensorSwapMod A (modPowMod A M.X n)
            (modPowMod A M.X 0) ≫
          powMulMod A M.X 0 n ≫
          modPowCastMod A M.X
            (by omega : 0 + 1 + n + 1 = n + 2)).hom) ⊗ₘ
        (modTensorπ A (modPowMod A M'.X n)
            (modPowMod A M'.X 0) ≫
          (powMulMod A M'.X n 0).hom)) ≫
      (β_ (modPowMod A M.X (n + 1)).X
        (modPowMod A M'.X (n + 1)).X).hom ≫
      pairPow A M M' d (n + 2) =
      ((modTensorπ A (modPowMod A M'.X n)
          (modPowMod A M'.X 0) ≫
        (powMulMod A M'.X n 0).hom) ⊗ₘ
        (modTensorπ A (modPowMod A M.X n)
            (modPowMod A M.X 0) ≫
          (modTensorSwapMod A (modPowMod A M.X n)
              (modPowMod A M.X 0) ≫
            powMulMod A M.X 0 n ≫
            modPowCastMod A M.X
              (by omega : 0 + 1 + n + 1 = n + 2)).hom)) ≫
      pairPow A M M' d (n + 2) := by
    refine Eq.trans (congrArg (fun t :
        ((modPowMod A M.X n).X ⊗ (modPowMod A M.X 0).X) ⊗
        ((modPowMod A M'.X n).X ⊗
          (modPowMod A M'.X 0).X) ⟶ A =>
      tensorμ (modPowMod A M'.X n).X (modPowMod A M'.X 0).X
          (modPowMod A M.X n).X (modPowMod A M.X 0).X ≫
        ((β_ (modPowMod A M'.X n).X
            (modPowMod A M.X n).X).hom ⊗ₘ
          (β_ (modPowMod A M'.X 0).X
            (modPowMod A M.X 0).X).hom) ≫
        tensorμ (modPowMod A M.X n).X (modPowMod A M'.X n).X
          (modPowMod A M.X 0).X (modPowMod A M'.X 0).X ≫ t)
      hnat3) ?_
    exact tensorMu_braid_retract_assoc _ _ _ _ _
  -- The two block braidings cancel.
  exact hfinalL

private theorem modPowPairing_succ_tensor_braidingCancel
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (n : ℕ) :
    ((β_ (modPowMod A M'.X n).X
        (modPowMod A M.X n).X).hom ⊗ₘ
      (β_ (modPowMod A M'.X 0).X
        (modPowMod A M.X 0).X).hom) ≫
      ((β_ (modPowMod A M.X n).X
          (modPowMod A M'.X n).X).hom ⊗ₘ
        (β_ (modPowMod A M.X 0).X
          (modPowMod A M'.X 0).X).hom) ≫
      ((modTensorπ A (modPowMod A M'.X n)
          (modPowMod A M.X n) ≫
        modPowPairing A M M' d n) ⊗ₘ
        (modTensorπ A (modPowMod A M'.X 0)
            (modPowMod A M.X 0) ≫
          modPowPairing A M M' d 0)) ≫ μ[A] =
    ((modTensorπ A (modPowMod A M'.X n)
          (modPowMod A M.X n) ≫
        modPowPairing A M M' d n) ⊗ₘ
        (modTensorπ A (modPowMod A M'.X 0)
            (modPowMod A M.X 0) ≫
          modPowPairing A M M' d 0)) ≫ μ[A] := by
  have hcancel : ((β_ (modPowMod A M'.X n).X
        (modPowMod A M.X n).X).hom ⊗ₘ
      (β_ (modPowMod A M'.X 0).X
        (modPowMod A M.X 0).X).hom) ≫
      ((β_ (modPowMod A M.X n).X
          (modPowMod A M'.X n).X).hom ⊗ₘ
        (β_ (modPowMod A M.X 0).X
          (modPowMod A M'.X 0).X).hom) =
      𝟙 (((modPowMod A M'.X n).X ⊗ (modPowMod A M.X n).X) ⊗
        ((modPowMod A M'.X 0).X ⊗ (modPowMod A M.X 0).X)) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom,
      SymmetricCategory.symmetry, SymmetricCategory.symmetry,
      MonoidalCategory.id_tensorHom_id]
  have htail : ((β_ (modPowMod A M'.X n).X
        (modPowMod A M.X n).X).hom ⊗ₘ
      (β_ (modPowMod A M'.X 0).X
        (modPowMod A M.X 0).X).hom) ≫
      ((β_ (modPowMod A M.X n).X
          (modPowMod A M'.X n).X).hom ⊗ₘ
        (β_ (modPowMod A M.X 0).X
          (modPowMod A M'.X 0).X).hom) ≫
      ((modTensorπ A (modPowMod A M'.X n)
          (modPowMod A M.X n) ≫
        modPowPairing A M M' d n) ⊗ₘ
        (modTensorπ A (modPowMod A M'.X 0)
            (modPowMod A M.X 0) ≫
          modPowPairing A M M' d 0)) ≫ μ[A] =
      ((modTensorπ A (modPowMod A M'.X n)
          (modPowMod A M.X n) ≫
        modPowPairing A M M' d n) ⊗ₘ
        (modTensorπ A (modPowMod A M'.X 0)
            (modPowMod A M.X 0) ≫
          modPowPairing A M M' d 0)) ≫ μ[A] := by
    rw [← Category.assoc, hcancel, Category.id_comp]
  -- The merged pair equals the crossed coordinatewise pairing.
  exact htail

/-- **The pair side of the power step** (Deligne 1.15): pushing the
primed back merge and the swapped unprimed front merge into the
successor power pairing yields the tensor pairing of the stage
datum with the bottom datum. -/
theorem modPowPairing_succ_tensor
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (n : ℕ) :
    modTensorMap A
        (powMulMod A M'.X n 0)
        (modTensorSwapMod A (modPowMod A M.X n)
            (modPowMod A M.X 0) ≫
          powMulMod A M.X 0 n ≫
          modPowCastMod A M.X
            (by omega : 0 + 1 + n + 1 = n + 2)) ≫
      modPowPairing A M M' d (n + 1) =
    tensorPair A (powDualityDatum A M M' d n)
      (powDualityDatum A M M' d 0) := by
  -- Left descent: the merged pairing against the big projection.
  have hLdesc : modTensorπ A
      (modTensorMod A (modPowMod A M'.X n) (modPowMod A M'.X 0))
      (modTensorMod A (modPowMod A M.X n) (modPowMod A M.X 0)) ≫
      modTensorMap A
        (powMulMod A M'.X n 0)
        (modTensorSwapMod A (modPowMod A M.X n)
            (modPowMod A M.X 0) ≫
          powMulMod A M.X 0 n ≫
          modPowCastMod A M.X
            (by omega : 0 + 1 + n + 1 = n + 2)) ≫
      modPowPairing A M M' d (n + 1) =
      ((powMulMod A M'.X n 0).hom ⊗ₘ
        (modTensorSwapMod A (modPowMod A M.X n)
            (modPowMod A M.X 0) ≫
          powMulMod A M.X 0 n ≫
          modPowCastMod A M.X
            (by omega : 0 + 1 + n + 1 = n + 2)).hom) ≫
      pairPow A M M' d (n + 2) := by
    rw [modTensorπ_map_assoc]
    exact congrArg (fun t : (modPowMod A M'.X (n + 1)).X ⊗
        (modPowMod A M.X (n + 1)).X ⟶ A =>
      ((powMulMod A M'.X n 0).hom ⊗ₘ
        (modTensorSwapMod A (modPowMod A M.X n)
            (modPowMod A M.X 0) ≫
          powMulMod A M.X 0 n ≫
          modPowCastMod A M.X
            (by omega : 0 + 1 + n + 1 = n + 2)).hom) ≫ t)
      (modTensorπ_modPowPairing A M M' d (n + 1))
  -- Fuse the covering projections into the merge carriers.
  have hLfuse : (modTensorπ A (modPowMod A M'.X n)
        (modPowMod A M'.X 0) ⊗ₘ
      modTensorπ A (modPowMod A M.X n) (modPowMod A M.X 0)) ≫
      ((powMulMod A M'.X n 0).hom ⊗ₘ
        (modTensorSwapMod A (modPowMod A M.X n)
            (modPowMod A M.X 0) ≫
          powMulMod A M.X 0 n ≫
          modPowCastMod A M.X
            (by omega : 0 + 1 + n + 1 = n + 2)).hom) ≫
      pairPow A M M' d (n + 2) =
      ((modTensorπ A (modPowMod A M'.X n)
          (modPowMod A M'.X 0) ≫
        (powMulMod A M'.X n 0).hom) ⊗ₘ
        (modTensorπ A (modPowMod A M.X n)
            (modPowMod A M.X 0) ≫
          (modTensorSwapMod A (modPowMod A M.X n)
              (modPowMod A M.X 0) ≫
            powMulMod A M.X 0 n ≫
            modPowCastMod A M.X
              (by omega : 0 + 1 + n + 1 = n + 2)).hom)) ≫
      pairPow A M M' d (n + 2) := by
    erw [← Category.assoc,
      MonoidalCategory.tensorHom_comp_tensorHom]
  -- The successor pairing against the swapped projection.
  have hL2 := modPowPairing_succ_tensor_leftCover A M M' d n
  have hcov := congrArg
    (fun t : modTensor A (modPowMod A M.X n)
        (modPowMod A M'.X n) ⊗
        modTensor A (modPowMod A M.X 0)
          (modPowMod A M'.X 0) ⟶ A =>
      (modTensorπ A (modPowMod A M.X n)
          (modPowMod A M'.X n) ⊗ₘ
        modTensorπ A (modPowMod A M.X 0)
          (modPowMod A M'.X 0)) ≫ t)
    (powDeltaCore_pairing A M M' d n)
  -- The stage pairings against the swapped projections.
  have hR2 := modPowPairing_succ_tensor_rightCover A M M' d n
  have hmeet := hL2.symm.trans (hcov.trans hR2)
  -- Braid the merged pair across the successor braiding.
  have hfinalL := modPowPairing_succ_tensor_braidingRetract A M M' d n
  have htail := modPowPairing_succ_tensor_braidingCancel A M M' d n
  have hfinal : ((modTensorπ A (modPowMod A M'.X n)
        (modPowMod A M'.X 0) ≫
      (powMulMod A M'.X n 0).hom) ⊗ₘ
      (modTensorπ A (modPowMod A M.X n)
          (modPowMod A M.X 0) ≫
        (modTensorSwapMod A (modPowMod A M.X n)
            (modPowMod A M.X 0) ≫
          powMulMod A M.X 0 n ≫
          modPowCastMod A M.X
            (by omega : 0 + 1 + n + 1 = n + 2)).hom)) ≫
      pairPow A M M' d (n + 2) =
      tensorμ (modPowMod A M'.X n).X (modPowMod A M'.X 0).X
        (modPowMod A M.X n).X (modPowMod A M.X 0).X ≫
      ((modTensorπ A (modPowMod A M'.X n)
          (modPowMod A M.X n) ≫
        modPowPairing A M M' d n) ⊗ₘ
        (modTensorπ A (modPowMod A M'.X 0)
            (modPowMod A M.X 0) ≫
          modPowPairing A M M' d 0)) ≫ μ[A] := by
    refine Eq.trans hfinalL.symm ?_
    refine Eq.trans (congrArg (fun t :
        ((modPowMod A M.X n).X ⊗ (modPowMod A M'.X n).X) ⊗
        ((modPowMod A M.X 0).X ⊗
          (modPowMod A M'.X 0).X) ⟶ A =>
      tensorμ (modPowMod A M'.X n).X (modPowMod A M'.X 0).X
          (modPowMod A M.X n).X (modPowMod A M.X 0).X ≫
        ((β_ (modPowMod A M'.X n).X
            (modPowMod A M.X n).X).hom ⊗ₘ
          (β_ (modPowMod A M'.X 0).X
            (modPowMod A M.X 0).X).hom) ≫ t)
      hmeet) ?_
    exact congrArg (fun t :
        ((modPowMod A M'.X n).X ⊗ (modPowMod A M.X n).X) ⊗
        ((modPowMod A M'.X 0).X ⊗
          (modPowMod A M.X 0).X) ⟶ A =>
      tensorμ (modPowMod A M'.X n).X (modPowMod A M'.X 0).X
          (modPowMod A M.X n).X (modPowMod A M.X 0).X ≫ t)
      htail
  -- Right descent: the tensor pairing against the big projection.
  have hdesc : modTensorπ A
      (modTensorMod A (modPowMod A M'.X n) (modPowMod A M'.X 0))
      (modTensorMod A (modPowMod A M.X n) (modPowMod A M.X 0)) ≫
      tensorPair A (powDualityDatum A M M' d n)
        (powDualityDatum A M M' d 0) =
      interchange A (modPowMod A M'.X n) (modPowMod A M'.X 0)
        (modPowMod A M.X n) (modPowMod A M.X 0) ≫
      modTensorMap A (powDualityDatum A M M' d n).pairMod
        (powDualityDatum A M M' d 0).pairMod ≫
      regPairFold A := by
    have hpair : tensorPair A (powDualityDatum A M M' d n)
        (powDualityDatum A M M' d 0) =
        interchangeDesc A (modPowMod A M'.X n)
          (modPowMod A M'.X 0) (modPowMod A M.X n)
          (modPowMod A M.X 0) ≫
        modTensorMap A (powDualityDatum A M M' d n).pairMod
          (powDualityDatum A M M' d 0).pairMod ≫
        regPairFold A := rfl
    rw [hpair, ← Category.assoc, modTensorπ_interchangeDesc]
    rfl
  -- The evaluated tensor pairing over the cover.
  have hwP : (modTensorπ A (modPowMod A M'.X n)
        (modPowMod A M'.X 0) ⊗ₘ
      modTensorπ A (modPowMod A M.X n) (modPowMod A M.X 0)) ≫
      interchange A (modPowMod A M'.X n) (modPowMod A M'.X 0)
        (modPowMod A M.X n) (modPowMod A M.X 0) ≫
      modTensorMap A (powDualityDatum A M M' d n).pairMod
        (powDualityDatum A M M' d 0).pairMod ≫
      regPairFold A =
      tensorμ (modPowMod A M'.X n).X (modPowMod A M'.X 0).X
        (modPowMod A M.X n).X (modPowMod A M.X 0).X ≫
      ((modTensorπ A (modPowMod A M'.X n)
          (modPowMod A M.X n) ≫
        modPowPairing A M M' d n) ⊗ₘ
        (modTensorπ A (modPowMod A M'.X 0)
            (modPowMod A M.X 0) ≫
          modPowPairing A M M' d 0)) ≫ μ[A] :=
    tensorHom_π_pairFold A (powDualityDatum A M M' d n)
      (powDualityDatum A M M' d 0)
  -- Assemble both sides over the common cover.
  apply modTensor_hom_ext
  refine (cancel_epi (modTensorπ A (modPowMod A M'.X n)
      (modPowMod A M'.X 0) ⊗ₘ
    modTensorπ A (modPowMod A M.X n)
      (modPowMod A M.X 0))).mp ?_
  refine Eq.trans (congrArg (fun t :
      (modTensorMod A (modPowMod A M'.X n)
        (modPowMod A M'.X 0)).X ⊗
      (modTensorMod A (modPowMod A M.X n)
        (modPowMod A M.X 0)).X ⟶ A =>
    (modTensorπ A (modPowMod A M'.X n)
        (modPowMod A M'.X 0) ⊗ₘ
      modTensorπ A (modPowMod A M.X n)
        (modPowMod A M.X 0)) ≫ t) hLdesc) ?_
  refine Eq.trans hLfuse ?_
  refine Eq.trans hfinal ?_
  refine Eq.trans hwP.symm ?_
  exact (congrArg (fun t :
      (modTensorMod A (modPowMod A M'.X n)
        (modPowMod A M'.X 0)).X ⊗
      (modTensorMod A (modPowMod A M.X n)
        (modPowMod A M.X 0)).X ⟶ A =>
    (modTensorπ A (modPowMod A M'.X n)
        (modPowMod A M'.X 0) ⊗ₘ
      modTensorπ A (modPowMod A M.X n)
        (modPowMod A M.X 0)) ≫ t) hdesc).symm

end RS
