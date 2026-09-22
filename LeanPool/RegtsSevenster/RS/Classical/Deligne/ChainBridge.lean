/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SymDatum

/-!
# The bridge from the power chain to the splitting chain

The symmetriser projection carries the power-chain units to the
splitting-chain units.  Stagewise, a power stage maps to the
matching splitting-chain stage by swapping the pair into
copairing order and projecting both slots onto the symmetric
powers; this projection carries the seed to the seed and
intertwines the transitions, hence transports every power-chain
unit to the corresponding splitting-chain unit.  This is the
wiring that connects the copairing powers of the duality datum
to the stage units that the colimit detection speaks about.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## Interchange coherence in a symmetric category -/

section Interchange

/-- The interchange of the crossed middle pair undoes the
interchange, in a symmetric category. -/
@[reassoc]
theorem tensorμ_tensorμ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (a b c d : D) :
    tensorμ a b c d ≫ tensorμ a c b d =
      𝟙 ((a ⊗ b) ⊗ (c ⊗ d)) := by
  calc tensorμ a b c d ≫ tensorμ a c b d
      = 𝟙 _ ⊗≫ a ◁ ((β_ b c).hom ≫ (β_ c b).hom) ▷ d ⊗≫ 𝟙 _ := by
        dsimp only [tensorμ]
        monoidal
    _ = 𝟙 ((a ⊗ b) ⊗ (c ⊗ d)) := by
        rw [SymmetricCategory.symmetry]
        monoidal

/-- The mirror of `tensorμ_braiding`: interchanging and then
braiding the two blocks equals braiding slotwise and then
interchanging in the exchanged order. -/
@[reassoc]
theorem tensorμ_braiding_right
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (a b c d : D) :
    tensorμ a b c d ≫ (β_ (a ⊗ c) (b ⊗ d)).hom =
      ((β_ a b).hom ⊗ₘ (β_ c d).hom) ≫ tensorμ b a d c := by
  have hβ : (β_ (a ⊗ c) (b ⊗ d)).hom =
      ((β_ (a ⊗ c) (b ⊗ d)).hom ≫ tensorμ b d a c) ≫
        tensorμ b a d c := by
    rw [Category.assoc, tensorμ_tensorμ b d a c,
      Category.comp_id]
  rw [hβ, tensorμ_braiding a c b d]
  simp only [Category.assoc]
  rw [tensorμ_tensorμ_assoc a b c d]

end Interchange

/-! ## Commutativity of the projected power multiplication -/

section SlotComm

/-- **The projected power multiplication is commutative**: after
the symmetriser projection, multiplying in the braided order and
transporting the arity agrees with multiplying directly. -/
theorem braid_modPowMul_cast_symPowπ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (X : D) [ModObj A X]
    (a b : ℕ) {c : ℕ}
    (h : b + a = c) (h' : a + b = c) :
    (β_ (modPow A X a) (modPow A X b)).hom ≫
        modPowMul A X b a ≫ modPowCast A X h ≫ symPowπ A X c =
      modPowMul A X a b ≫ modPowCast A X h' ≫ symPowπ A X c := by
  subst h'
  rw [modPowCast_rfl, Category.id_comp, ← symPowπ_cast A X h,
    ← symPowπ_tensor_symMul_assoc,
    ← BraidedCategory.braiding_naturality_assoc,
    reassoc_of% (symMul_comm A X a b)]
  simp only [symPowCast, eqToHom_trans, eqToHom_refl,
    Category.comp_id]
  rw [symPowπ_tensor_symMul]

end SlotComm

/-! ## The stage projection -/

/-- **The stage projection**: a power stage maps to the matching
splitting-chain stage by swapping the pair into copairing order
and projecting both slots onto the symmetric powers. -/
noncomputable def projStage
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (k : ℕ) :
    powStage A M M' k ⟶ chainStage A M M' k :=
  modTensorSwap A (modPowMod A M.X k) (modPowMod A M'.X k) ≫
    modTensorMap A (symPowπMod A k) (symPowπMod A k)

/-- The stage projection under the stage projections of the
coequalizers: the braiding of the factors followed by the
symmetriser projections. -/
theorem modTensorπ_projStage
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (k : ℕ) :
    modTensorπ A (modPowMod A M.X k) (modPowMod A M'.X k) ≫
        projStage A M M' k =
      (β_ (modPow A M.X (k + 1)) (modPow A M'.X (k + 1))).hom ≫
        (symPowπ A M'.X (k + 1) ⊗ₘ symPowπ A M.X (k + 1)) ≫
        modTensorπ A (symPowMod A M'.X k) (symPowMod A M.X k) := by
  have h1 : modTensorπ A (modPowMod A M.X k)
        (modPowMod A M'.X k) ≫
      modTensorSwap A (modPowMod A M.X k) (modPowMod A M'.X k) ≫
      modTensorMap A (symPowπMod A k) (symPowπMod A k) =
    (β_ (modPow A M.X (k + 1)) (modPow A M'.X (k + 1))).hom ≫
      (symPowπ A M'.X (k + 1) ⊗ₘ symPowπ A M.X (k + 1)) ≫
      modTensorπ A (symPowMod A M'.X k) (symPowMod A M.X k) := by
    rw [modTensorπ_swap_assoc, modTensorπ_map]
    rfl
  exact h1

/-! ## The zero stages -/

/-- The symmetriser projection carries the singleton power stage
of a module to its singleton symmetric-power stage. -/
theorem toModPowModZero_symPowπMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) :
    toModPowModZero A M ≫ symPowπMod A 0 =
      toSymPowModZero A M :=
  Mod.hom_ext _ _ rfl

/-- **The seed bridge**: the stage projection carries the seed of
the power chain to the seed of the splitting chain. -/
theorem powSeed_projStage
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    powSeed A M M' d ≫ projStage A M M' 0 =
      chainSeed A M M' d := by
  have h1 : copairUnit A M M' d ≫
      modTensorMap A (toModPowModZero A M)
        (toModPowModZero A M') ≫
      modTensorSwap A (modPowMod A M.X 0) (modPowMod A M'.X 0) ≫
      modTensorMap A (symPowπMod A 0) (symPowπMod A 0) =
    copairUnit A M M' d ≫ modTensorSwap A M M' ≫
      modTensorMap A (toSymPowModZero A M')
        (toSymPowModZero A M) := by
    rw [reassoc_of% (modTensorMap_swap A (toModPowModZero A M)
        (toModPowModZero A M')),
      ← modTensorMap_comp, toModPowModZero_symPowπMod,
      toModPowModZero_symPowπMod]
  exact (Category.assoc _ _ _).trans h1

/-! ## The multiplication bridge -/

section MulBridge

/-- **The multiplication bridge, at the carriers**: the descended
power multiplication followed by the symmetriser projection is
the slotwise projection followed by the descended symmetric
multiplication. -/
theorem powMulDesc_symPowπ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (m n : ℕ) :
    powMulDesc A X m n ≫ symPowπ A X (m + 1 + n + 1) =
      modTensorMap A (symPowπMod A m) (symPowπMod A n) ≫
        symMulDesc A X m n := by
  apply modTensor_hom_ext
  conv_lhs => rw [modTensorπ_powMulDesc_assoc]
  conv_rhs => rw [modTensorπ_map_assoc, modTensorπ_symMulDesc]
  exact (symPowπ_tensor_symMul A X (m + 1) (n + 1)).symm

end MulBridge

/-! ## The transition bridge -/

/-- **The transition core**: the interchange followed by the
power multiplications and the stage projection is the slotwise
stage projection followed by the chain multiplication. -/
theorem projStage_mul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (k : ℕ) :
    interchange A (modPowMod A M.X k) (modPowMod A M'.X k)
        (modPowMod A M.X 0) (modPowMod A M'.X 0) ≫
      modTensorMap A
        (modTensorSwapMod A (modPowMod A M.X k)
            (modPowMod A M.X 0) ≫
          powMulMod A M.X 0 k ≫
          modPowCastMod A M.X
            (by omega : 0 + 1 + k + 1 = k + 2))
        (powMulMod A M'.X k 0) ≫
      projStage A M M' (k + 1) =
    (projStage A M M' k ⊗ₘ projStage A M M' 0) ≫
      chainMul A M M' k 0 := by
  have hF : modTensorπ A (modPowMod A M.X k)
      (modPowMod A M.X 0) ≫
      (modTensorSwapMod A (modPowMod A M.X k)
          (modPowMod A M.X 0) ≫
        powMulMod A M.X 0 k ≫
        modPowCastMod A M.X
          (by omega : 0 + 1 + k + 1 = k + 2)).hom =
    (β_ (modPow A M.X (k + 1)) (modPow A M.X (0 + 1))).hom ≫
      modPowMul A M.X (0 + 1) (k + 1) ≫
      modPowCast A M.X (by omega : 0 + 1 + k + 1 = k + 2) := by
    show modTensorπ A (modPowMod A M.X k) (modPowMod A M.X 0) ≫
      modTensorSwap A (modPowMod A M.X k) (modPowMod A M.X 0) ≫
      powMulDesc A M.X 0 k ≫
      modPowCast A M.X (by omega : 0 + 1 + k + 1 = k + 2) = _
    rw [modTensorπ_swap_assoc, modTensorπ_powMulDesc_assoc]
    rfl
  have hG : modTensorπ A (modPowMod A M'.X k)
      (modPowMod A M'.X 0) ≫ (powMulMod A M'.X k 0).hom =
    modPowMul A M'.X (k + 1) (0 + 1) := by
    show modTensorπ A (modPowMod A M'.X k)
      (modPowMod A M'.X 0) ≫ powMulDesc A M'.X k 0 = _
    exact modTensorπ_powMulDesc A M'.X k 0
  have hslot :
      (β_ (modPow A M.X (k + 1)) (modPow A M.X (0 + 1))).hom ≫
          modPowMul A M.X (0 + 1) (k + 1) ≫
          modPowCast A M.X
            (by omega : 0 + 1 + k + 1 = k + 2) ≫
          symPowπ A M.X (k + 2) =
        modPowMul A M.X (k + 1) (0 + 1) ≫
          symPowπ A M.X (k + 1 + (0 + 1)) := by
    have h1 := braid_modPowMul_cast_symPowπ A M.X (k + 1) (0 + 1)
      (by omega : 0 + 1 + (k + 1) = k + 1 + (0 + 1))
      (rfl : k + 1 + (0 + 1) = k + 1 + (0 + 1))
    conv at h1 => rhs; rw [modPowCast_rfl, Category.id_comp]
    exact h1
  have h2 : (modTensorπ A (modPowMod A M.X k)
        (modPowMod A M'.X k) ⊗ₘ
      modTensorπ A (modPowMod A M.X 0) (modPowMod A M'.X 0)) ≫
      (interchange A (modPowMod A M.X k) (modPowMod A M'.X k)
          (modPowMod A M.X 0) (modPowMod A M'.X 0) ≫
        modTensorMap A
          (modTensorSwapMod A (modPowMod A M.X k)
              (modPowMod A M.X 0) ≫
            powMulMod A M.X 0 k ≫
            modPowCastMod A M.X
              (by omega : 0 + 1 + k + 1 = k + 2))
          (powMulMod A M'.X k 0) ≫
        projStage A M M' (k + 1)) =
    tensorμ (modPow A M.X (k + 1)) (modPow A M'.X (k + 1))
        (modPow A M.X (0 + 1)) (modPow A M'.X (0 + 1)) ≫
      (((β_ (modPow A M.X (k + 1))
            (modPow A M.X (0 + 1))).hom ≫
          modPowMul A M.X (0 + 1) (k + 1) ≫
          modPowCast A M.X
            (by omega : 0 + 1 + k + 1 = k + 2)) ⊗ₘ
        modPowMul A M'.X (k + 1) (0 + 1)) ≫
      (β_ (modPow A M.X (k + 2)) (modPow A M'.X (k + 2))).hom ≫
      (symPowπ A M'.X (k + 2) ⊗ₘ symPowπ A M.X (k + 2)) ≫
      modTensorπ A (symPowMod A M'.X (k + 1))
        (symPowMod A M.X (k + 1)) := by
    erw [tensorHom_π_interchange_map_assoc, hF, hG,
      modTensorπ_projStage A M M' (k + 1)]
    rfl
  have h3 : tensorμ (modPow A M.X (k + 1)) (modPow A M'.X (k + 1))
        (modPow A M.X (0 + 1)) (modPow A M'.X (0 + 1)) ≫
      (((β_ (modPow A M.X (k + 1))
            (modPow A M.X (0 + 1))).hom ≫
          modPowMul A M.X (0 + 1) (k + 1) ≫
          modPowCast A M.X
            (by omega : 0 + 1 + k + 1 = k + 2)) ⊗ₘ
        modPowMul A M'.X (k + 1) (0 + 1)) ≫
      (β_ (modPow A M.X (k + 2)) (modPow A M'.X (k + 2))).hom ≫
      (symPowπ A M'.X (k + 2) ⊗ₘ symPowπ A M.X (k + 2)) ≫
      modTensorπ A (symPowMod A M'.X (k + 1))
        (symPowMod A M.X (k + 1)) =
    ((β_ (modPow A M.X (k + 1)) (modPow A M'.X (k + 1))).hom ⊗ₘ
        (β_ (modPow A M.X (0 + 1)) (modPow A M'.X (0 + 1))).hom) ≫
      tensorμ (modPow A M'.X (k + 1)) (modPow A M.X (k + 1))
        (modPow A M'.X (0 + 1)) (modPow A M.X (0 + 1)) ≫
      ((modPowMul A M'.X (k + 1) (0 + 1) ≫
          symPowπ A M'.X (k + 1 + (0 + 1))) ⊗ₘ
        (modPowMul A M.X (k + 1) (0 + 1) ≫
          symPowπ A M.X (k + 1 + (0 + 1)))) ≫
      modTensorπ A (symPowMod A M'.X (k + 1))
        (symPowMod A M.X (k + 1)) := by
    erw [BraidedCategory.braiding_naturality_assoc,
      tensorμ_braiding_right_assoc,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc]
    simp only [Category.assoc]
    rw [hslot]
  have h4a : (modTensorπ A (modPowMod A M.X k)
        (modPowMod A M'.X k) ⊗ₘ
      modTensorπ A (modPowMod A M.X 0) (modPowMod A M'.X 0)) ≫
      ((projStage A M M' k ⊗ₘ projStage A M M' 0) ≫
        chainMul A M M' k 0) =
    (((β_ (modPow A M.X (k + 1)) (modPow A M'.X (k + 1))).hom ≫
        (symPowπ A M'.X (k + 1) ⊗ₘ symPowπ A M.X (k + 1)) ≫
        modTensorπ A (symPowMod A M'.X k) (symPowMod A M.X k)) ⊗ₘ
      ((β_ (modPow A M.X (0 + 1)) (modPow A M'.X (0 + 1))).hom ≫
        (symPowπ A M'.X (0 + 1) ⊗ₘ symPowπ A M.X (0 + 1)) ≫
        modTensorπ A (symPowMod A M'.X 0) (symPowMod A M.X 0))) ≫
      chainMul A M M' k 0 := by
    erw [MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      modTensorπ_projStage A M M' k,
      modTensorπ_projStage A M M' 0]
    rfl
  have h4b : (((β_ (modPow A M.X (k + 1))
          (modPow A M'.X (k + 1))).hom ≫
        (symPowπ A M'.X (k + 1) ⊗ₘ symPowπ A M.X (k + 1)) ≫
        modTensorπ A (symPowMod A M'.X k) (symPowMod A M.X k)) ⊗ₘ
      ((β_ (modPow A M.X (0 + 1)) (modPow A M'.X (0 + 1))).hom ≫
        (symPowπ A M'.X (0 + 1) ⊗ₘ symPowπ A M.X (0 + 1)) ≫
        modTensorπ A (symPowMod A M'.X 0) (symPowMod A M.X 0))) ≫
      chainMul A M M' k 0 =
    ((β_ (modPow A M.X (k + 1)) (modPow A M'.X (k + 1))).hom ⊗ₘ
        (β_ (modPow A M.X (0 + 1)) (modPow A M'.X (0 + 1))).hom) ≫
      tensorμ (modPow A M'.X (k + 1)) (modPow A M.X (k + 1))
        (modPow A M'.X (0 + 1)) (modPow A M.X (0 + 1)) ≫
      ((modPowMul A M'.X (k + 1) (0 + 1) ≫
          symPowπ A M'.X (k + 1 + (0 + 1))) ⊗ₘ
        (modPowMul A M.X (k + 1) (0 + 1) ≫
          symPowπ A M.X (k + 1 + (0 + 1)))) ≫
      modTensorπ A (symPowMod A M'.X (k + 1))
        (symPowMod A M.X (k + 1)) := by
    have hs : (((β_ (modPow A M.X (k + 1))
            (modPow A M'.X (k + 1))).hom ≫
          (symPowπ A M'.X (k + 1) ⊗ₘ symPowπ A M.X (k + 1)) ≫
          modTensorπ A (symPowMod A M'.X k)
            (symPowMod A M.X k)) ⊗ₘ
        ((β_ (modPow A M.X (0 + 1))
            (modPow A M'.X (0 + 1))).hom ≫
          (symPowπ A M'.X (0 + 1) ⊗ₘ symPowπ A M.X (0 + 1)) ≫
          modTensorπ A (symPowMod A M'.X 0)
            (symPowMod A M.X 0))) ≫
        chainMul A M M' k 0 =
      ((β_ (modPow A M.X (k + 1)) (modPow A M'.X (k + 1))).hom ⊗ₘ
          (β_ (modPow A M.X (0 + 1))
            (modPow A M'.X (0 + 1))).hom) ≫
        ((symPowπ A M'.X (k + 1) ⊗ₘ symPowπ A M.X (k + 1)) ⊗ₘ
          (symPowπ A M'.X (0 + 1) ⊗ₘ symPowπ A M.X (0 + 1))) ≫
        (modTensorπ A (symPowMod A M'.X k) (symPowMod A M.X k) ⊗ₘ
          modTensorπ A (symPowMod A M'.X 0)
            (symPowMod A M.X 0)) ≫
        chainMul A M M' k 0 := by
      erw [← MonoidalCategory.tensorHom_comp_tensorHom_assoc,
        ← MonoidalCategory.tensorHom_comp_tensorHom_assoc]
    have hmid : ((β_ (modPow A M.X (k + 1))
            (modPow A M'.X (k + 1))).hom ⊗ₘ
          (β_ (modPow A M.X (0 + 1))
            (modPow A M'.X (0 + 1))).hom) ≫
        ((symPowπ A M'.X (k + 1) ⊗ₘ symPowπ A M.X (k + 1)) ⊗ₘ
          (symPowπ A M'.X (0 + 1) ⊗ₘ symPowπ A M.X (0 + 1))) ≫
        (modTensorπ A (symPowMod A M'.X k) (symPowMod A M.X k) ⊗ₘ
          modTensorπ A (symPowMod A M'.X 0)
            (symPowMod A M.X 0)) ≫
        chainMul A M M' k 0 =
      ((β_ (modPow A M.X (k + 1)) (modPow A M'.X (k + 1))).hom ⊗ₘ
          (β_ (modPow A M.X (0 + 1))
            (modPow A M'.X (0 + 1))).hom) ≫
        ((symPowπ A M'.X (k + 1) ⊗ₘ symPowπ A M.X (k + 1)) ⊗ₘ
          (symPowπ A M'.X (0 + 1) ⊗ₘ symPowπ A M.X (0 + 1))) ≫
        tensorμ (symPow A M'.X (k + 1)) (symPow A M.X (k + 1))
          (symPow A M'.X (0 + 1)) (symPow A M.X (0 + 1)) ≫
        (symMul A M'.X (k + 1) (0 + 1) ⊗ₘ
          symMul A M.X (k + 1) (0 + 1)) ≫
        modTensorπ A (symPowMod A M'.X (k + 1 + 0))
          (symPowMod A M.X (k + 1 + 0)) :=
      congrArg (CategoryStruct.comp _)
        (congrArg (CategoryStruct.comp _)
          (tensorHom_π_chainMul A M M' k 0))
    have hend : ((β_ (modPow A M.X (k + 1))
            (modPow A M'.X (k + 1))).hom ⊗ₘ
          (β_ (modPow A M.X (0 + 1))
            (modPow A M'.X (0 + 1))).hom) ≫
        ((symPowπ A M'.X (k + 1) ⊗ₘ symPowπ A M.X (k + 1)) ⊗ₘ
          (symPowπ A M'.X (0 + 1) ⊗ₘ symPowπ A M.X (0 + 1))) ≫
        tensorμ (symPow A M'.X (k + 1)) (symPow A M.X (k + 1))
          (symPow A M'.X (0 + 1)) (symPow A M.X (0 + 1)) ≫
        (symMul A M'.X (k + 1) (0 + 1) ⊗ₘ
          symMul A M.X (k + 1) (0 + 1)) ≫
        modTensorπ A (symPowMod A M'.X (k + 1 + 0))
          (symPowMod A M.X (k + 1 + 0)) =
      ((β_ (modPow A M.X (k + 1)) (modPow A M'.X (k + 1))).hom ⊗ₘ
          (β_ (modPow A M.X (0 + 1))
            (modPow A M'.X (0 + 1))).hom) ≫
        tensorμ (modPow A M'.X (k + 1)) (modPow A M.X (k + 1))
          (modPow A M'.X (0 + 1)) (modPow A M.X (0 + 1)) ≫
        ((modPowMul A M'.X (k + 1) (0 + 1) ≫
            symPowπ A M'.X (k + 1 + (0 + 1))) ⊗ₘ
          (modPowMul A M.X (k + 1) (0 + 1) ≫
            symPowπ A M.X (k + 1 + (0 + 1)))) ≫
        modTensorπ A (symPowMod A M'.X (k + 1))
          (symPowMod A M.X (k + 1)) := by
      erw [tensorμ_natural_assoc,
        MonoidalCategory.tensorHom_comp_tensorHom_assoc,
        symPowπ_tensor_symMul A M'.X (k + 1) (0 + 1),
        symPowπ_tensor_symMul A M.X (k + 1) (0 + 1)]
    exact (hs.trans hmid).trans hend
  refine (cancel_epi
    (modTensorπ A (modPowMod A M.X k) (modPowMod A M'.X k) ⊗ₘ
      modTensorπ A (modPowMod A M.X 0)
        (modPowMod A M'.X 0))).mp ?_
  exact ((h2.trans h3).trans (h4a.trans h4b).symm)

/-- **The transition bridge**: the stage projection intertwines
the power-chain transition with the splitting-chain
transition. -/
theorem powDelta_projStage
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') (k : ℕ) :
    powDelta A M M' d k ≫ projStage A M M' (k + 1) =
      projStage A M M' k ≫ chainDelta A M M' d k := by
  rw [powDelta, chainDelta, ← powSeed_projStage A M M' d,
    MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  conv_rhs => rw [rightUnitor_inv_naturality_assoc,
    ← whisker_exchange_assoc,
    ← MonoidalCategory.tensorHom_def_assoc]
  exact congrArg (CategoryStruct.comp
      (ρ_ (powStage A M M' k)).inv)
    (congrArg (CategoryStruct.comp
        (powStage A M M' k ◁ powSeed A M M' d))
      (by
        erw [Category.assoc]
        exact projStage_mul A M M' k))

/-! ## The unit bridge -/

/-- **The unit bridge**: the stage projection carries every
power-chain unit to the corresponding splitting-chain unit.
Together with the identification of the copairing powers as the
power-chain units, this transports the copair element of the
power datum to the stage units of the splitting chain. -/
theorem powUnitStage_projStage
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (k : ℕ) :
    powUnitStage A M M' d k ≫ projStage A M M' k =
      chainUnitStage A M M' d k := by
  induction k with
  | zero => exact powSeed_projStage A M M' d
  | succ k ih =>
      calc powUnitStage A M M' d (k + 1) ≫
            projStage A M M' (k + 1)
          = powUnitStage A M M' d k ≫ powDelta A M M' d k ≫
              projStage A M M' (k + 1) := by
            rw [← powUnitStage_succ, Category.assoc]
        _ = powUnitStage A M M' d k ≫ projStage A M M' k ≫
              chainDelta A M M' d k := by
            rw [powDelta_projStage A M M' d k]
        _ = chainUnitStage A M M' d (k + 1) := by
            rw [← Category.assoc, ih, chainUnitStage_succ]

end RS
