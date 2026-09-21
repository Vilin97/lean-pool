/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainBofA
import LeanPool.RegtsSevenster.RS.Classical.Deligne.TensorZigzag

/-!
# The successor power datum

The step of the power induction: the copairing power at the
successor stage is the tensor copairing of the stage datum and
the bottom datum, pushed along the transition legs.  The orbit
extension principle reduces the comparison to the unit elements,
where the chain recursion is definitional.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **The orbit extension principle**: a linear map out of the
base is the orbit map of its unit element. -/
theorem act_on_point_eq [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    {X : D} (act : A ⊗ X ⟶ X) (f : A ⟶ X)
    (hf : μ[A] ≫ f = (A ◁ f) ≫ act) :
    f = (ρ_ A).inv ≫ (A ◁ (η[A] ≫ f)) ≫ act := by
  rw [MonoidalCategory.whiskerLeft_comp, Category.assoc,
    ← hf, ← Category.assoc, ← Category.assoc,
    show ((ρ_ A).inv ≫ (A ◁ η[A])) ≫ μ[A] = 𝟙 A from by
      rw [Category.assoc, MonObj.mul_one, Iso.inv_hom_id],
    Category.id_comp]

/-- **The transition is linear**: the power chain transition
intertwines the descended actions of adjacent stages. -/
theorem powDelta_actLeft
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') (n : ℕ) :
    modTensorAct A (modPowMod A M.X n) (modPowMod A M'.X n) ≫
      powDelta A M M' d n =
    (A ◁ powDelta A M M' d n) ≫
      modTensorAct A (modPowMod A M.X (n + 1))
        (modPowMod A M'.X (n + 1)) := by
  have hm : (modTensorAct A (modPowMod A M.X n)
      (modPowMod A M'.X n) ▷
        modTensor A (modPowMod A M.X 0) (modPowMod A M'.X 0)) ≫
      (interchange A (modPowMod A M.X n) (modPowMod A M'.X n)
        (modPowMod A M.X 0) (modPowMod A M'.X 0) ≫
      modTensorMap A
        (modTensorSwapMod A (modPowMod A M.X n)
            (modPowMod A M.X 0) ≫
          powMulMod A M.X 0 n ≫
          modPowCastMod A M.X
            (by omega : 0 + 1 + n + 1 = n + 2))
        (powMulMod A M'.X n 0)) =
      (α_ A
        (modTensor A (modPowMod A M.X n) (modPowMod A M'.X n))
        (modTensor A (modPowMod A M.X 0)
          (modPowMod A M'.X 0))).hom ≫
      (A ◁ (interchange A (modPowMod A M.X n)
          (modPowMod A M'.X n)
          (modPowMod A M.X 0) (modPowMod A M'.X 0) ≫
        modTensorMap A
          (modTensorSwapMod A (modPowMod A M.X n)
              (modPowMod A M.X 0) ≫
            powMulMod A M.X 0 n ≫
            modPowCastMod A M.X
              (by omega : 0 + 1 + n + 1 = n + 2))
          (powMulMod A M'.X n 0))) ≫
      modTensorAct A (modPowMod A M.X (n + 1))
        (modPowMod A M'.X (n + 1)) := by
    rw [← Category.assoc,
      interchange_actLeft A (modPowMod A M.X n)
        (modPowMod A M'.X n) (modPowMod A M.X 0)
        (modPowMod A M'.X 0),
      Category.assoc, Category.assoc, modTensorAct_map,
      MonoidalCategory.whiskerLeft_comp, Category.assoc]
  exact act_insert_linear A
    (modTensorAct A (modPowMod A M.X n) (modPowMod A M'.X n))
    (modTensorAct A (modPowMod A M.X (n + 1))
      (modPowMod A M'.X (n + 1)))
    (powSeed A M M' d)
    (interchange A (modPowMod A M.X n) (modPowMod A M'.X n)
        (modPowMod A M.X 0) (modPowMod A M'.X 0) ≫
      modTensorMap A
        (modTensorSwapMod A (modPowMod A M.X n)
            (modPowMod A M.X 0) ≫
          powMulMod A M.X 0 n ≫
          modPowCastMod A M.X
            (by omega : 0 + 1 + n + 1 = n + 2))
        (powMulMod A M'.X n 0))
    hm

/-- **The successor copairing power is the tensor copairing
pushed along the transition legs** (Deligne 1.15, copair side of
the power step). -/
theorem powCopairA_succ_tensor
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (n : ℕ) :
    powCopairA A M M' d (n + 1) =
      tensorCopair A (powDualityDatum A M M' d n)
        (powDualityDatum A M M' d 0) ≫
      modTensorMap A
        (modTensorSwapMod A (modPowMod A M.X n)
            (modPowMod A M.X 0) ≫
          powMulMod A M.X 0 n ≫
          modPowCastMod A M.X
            (by omega : 0 + 1 + n + 1 = n + 2))
        (powMulMod A M'.X n 0) := by
  have hf : μ[A] ≫
      (tensorCopair A (powDualityDatum A M M' d n)
        (powDualityDatum A M M' d 0) ≫
      modTensorMap A
        (modTensorSwapMod A (modPowMod A M.X n)
            (modPowMod A M.X 0) ≫
          powMulMod A M.X 0 n ≫
          modPowCastMod A M.X
            (by omega : 0 + 1 + n + 1 = n + 2))
        (powMulMod A M'.X n 0)) =
      (A ◁ (tensorCopair A (powDualityDatum A M M' d n)
        (powDualityDatum A M M' d 0) ≫
      modTensorMap A
        (modTensorSwapMod A (modPowMod A M.X n)
            (modPowMod A M.X 0) ≫
          powMulMod A M.X 0 n ≫
          modPowCastMod A M.X
            (by omega : 0 + 1 + n + 1 = n + 2))
        (powMulMod A M'.X n 0))) ≫
      modTensorAct A (modPowMod A M.X (n + 1))
        (modPowMod A M'.X (n + 1)) := by
    rw [← Category.assoc, tensorCopair_linear, Category.assoc,
      modTensorAct_map, ← Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp]
  have hpt : (λ_ (𝟙_ D)).inv ≫
      (powUnitStage A M M' d n ⊗ₘ powSeed A M M' d) =
      powUnitStage A M M' d n ≫
        (ρ_ (powStage A M M' n)).inv ≫
        (powStage A M M' n ◁ powSeed A M M' d) := by
    rw [MonoidalCategory.tensorHom_def, ← Category.assoc,
      show (λ_ (𝟙_ D)).inv = (ρ_ (𝟙_ D)).inv from by
        rw [← unitors_inv_equal],
      ← rightUnitor_inv_naturality, Category.assoc]
  have hu : η[A] ≫
      (tensorCopair A (powDualityDatum A M M' d n)
        (powDualityDatum A M M' d 0) ≫
      modTensorMap A
        (modTensorSwapMod A (modPowMod A M.X n)
            (modPowMod A M.X 0) ≫
          powMulMod A M.X 0 n ≫
          modPowCastMod A M.X
            (by omega : 0 + 1 + n + 1 = n + 2))
        (powMulMod A M'.X n 0)) =
      powUnitStage A M M' d (n + 1) := by
    have h1 : η[A] ≫ powCopairA A M M' d n =
        powUnitStage A M M' d n := powCopairA_unit A M M' d n
    have h2 : η[A] ≫ powCopairA A M M' d 0 =
        powSeed A M M' d := powCopairA_unit A M M' d 0
    rw [← Category.assoc, tensorCopair_point,
      show (powDualityDatum A M M' d n).copair =
        powCopairA A M M' d n from rfl,
      show (powDualityDatum A M M' d 0).copair =
        powCopairA A M M' d 0 from rfl]
    refine Eq.trans (congrArg
      (fun t : 𝟙_ D ⟶ powStage A M M' n =>
        ((λ_ (𝟙_ D)).inv ≫
          (t ⊗ₘ (η[A] ≫ powCopairA A M M' d 0)) ≫
          interchange A (modPowMod A M.X n)
            (modPowMod A M'.X n)
            (modPowMod A M.X 0) (modPowMod A M'.X 0)) ≫
          modTensorMap A
            (modTensorSwapMod A (modPowMod A M.X n)
                (modPowMod A M.X 0) ≫
              powMulMod A M.X 0 n ≫
              modPowCastMod A M.X
                (by omega : 0 + 1 + n + 1 = n + 2))
            (powMulMod A M'.X n 0)) h1) ?_
    refine Eq.trans (congrArg
      (fun t : 𝟙_ D ⟶ powStage A M M' 0 =>
        ((λ_ (𝟙_ D)).inv ≫
          (powUnitStage A M M' d n ⊗ₘ t) ≫
          interchange A (modPowMod A M.X n)
            (modPowMod A M'.X n)
            (modPowMod A M.X 0) (modPowMod A M'.X 0)) ≫
          modTensorMap A
            (modTensorSwapMod A (modPowMod A M.X n)
                (modPowMod A M.X 0) ≫
              powMulMod A M.X 0 n ≫
              modPowCastMod A M.X
                (by omega : 0 + 1 + n + 1 = n + 2))
            (powMulMod A M'.X n 0)) h2) ?_
    rw [reassoc_of% hpt]
    show _ = powUnitStage A M M' d n ≫ powDelta A M M' d n
    rw [powDelta]
    simp only [Category.assoc]
    rfl
  rw [powCopairA, ← hu]
  exact (act_on_point_eq A
    (modTensorAct A (modPowMod A M.X (n + 1))
      (modPowMod A M'.X (n + 1))) _ hf).symm

end RS
