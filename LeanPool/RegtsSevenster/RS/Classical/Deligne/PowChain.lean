/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainDelta

/-!
# The power-level chain and the copairing powers

The module-power mirror of the symmetric chain: the power
multiplication descends through the module-tensor coequalizer and
bundles as a module map; through the interchange, power stages
multiply; the copairing seeds the bottom stage, and the iterated
seed multiplication is the copairing power of the duality datum.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- The two module-tensor legs of a pair of module powers agree
after the power multiplication. -/
theorem modPowMul_modTensor_cond
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (m n : ℕ) :
    modTensorLegM A (modPowMod A X m) (modPowMod A X n) ≫
        modPowMul A X (m + 1) (n + 1) =
      modTensorLegN A (modPowMod A X m) (modPowMod A X n) ≫
        modPowMul A X (m + 1) (n + 1) := by
  have h3 := (modPowMul_actRight A X m n).trans
    (modPowMul_actLeft A X m n).symm
  simp only [braidPast_hom, Category.assoc] at h3
  have h4 := (cancel_epi
    (α_ A (modPow A X (m + 1)) (modPow A X (n + 1))).inv).mp h3
  rw [modTensorLegM, modTensorLegN, actRight,
    show actLeft A (modPowMod A X m).X = modPowAct A X m from
      rfl,
    show actLeft A (modPowMod A X n).X = modPowAct A X n from
      rfl]
  show (((β_ (modPow A X (m + 1)) A).hom ≫ modPowAct A X m) ▷
      modPow A X (n + 1)) ≫ modPowMul A X (m + 1) (n + 1) =
    ((α_ (modPow A X (m + 1)) A (modPow A X (n + 1))).hom ≫
      (modPow A X (m + 1) ◁ modPowAct A X n)) ≫
      modPowMul A X (m + 1) (n + 1)
  rw [comp_whiskerRight, Category.assoc, ← h4,
    ← comp_whiskerRight_assoc, SymmetricCategory.symmetry,
    MonoidalCategory.id_whiskerRight, Category.id_comp]
  simp only [Category.assoc]

/-- **The descended power multiplication** on the module tensor
product of two module powers. -/
noncomputable def powMulDesc
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (m n : ℕ) :
    modTensor A (modPowMod A X m) (modPowMod A X n) ⟶
      modPow A X (m + 1 + n + 1) :=
  modTensorDesc A (modPowMod A X m) (modPowMod A X n)
    (modPowMul A X (m + 1) (n + 1))
    (modPowMul_modTensor_cond A X m n)

/-- Defining equation of the descended power multiplication. -/
@[reassoc (attr := simp)]
theorem modTensorπ_powMulDesc
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (m n : ℕ) :
    modTensorπ A (modPowMod A X m) (modPowMod A X n) ≫
        powMulDesc A X m n = modPowMul A X (m + 1) (n + 1) :=
  modTensorπ_desc A (modPowMod A X m) (modPowMod A X n) _ _

/-- The descended power multiplication intertwines the module
actions. -/
theorem powMulDesc_act
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (m n : ℕ) :
    modTensorAct A (modPowMod A X m) (modPowMod A X n) ≫
        powMulDesc A X m n =
      (A ◁ powMulDesc A X m n) ≫ modPowAct A X (m + 1 + n) := by
  apply modTensor_whisker_hom_ext A (modPowMod A X m)
    (modPowMod A X n) A
  conv_lhs => rw [whiskerLeft_modTensorπ_act_assoc,
    modTensorπ_powMulDesc]
  conv_rhs => rw [← whiskerLeft_comp_assoc,
    modTensorπ_powMulDesc]
  have h := modPowMul_actLeft A X m n
  show (α_ A (modPow A X (m + 1)) (modPow A X (n + 1))).inv ≫
      (modPowAct A X m ▷ modPow A X (n + 1)) ≫
      modPowMul A X (m + 1) (n + 1) =
    (A ◁ modPowMul A X (m + 1) (n + 1)) ≫
      modPowAct A X (m + 1 + n)
  simpa only [Category.assoc] using h

/-- The descended power multiplication as a map of modules. -/
noncomputable def powMulMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (m n : ℕ) :
    modTensorMod A (modPowMod A X m) (modPowMod A X n) ⟶
      modPowMod A X (m + 1 + n) :=
  Mod.Hom.mk' (powMulDesc A X m n) (powMulDesc_act A X m n)

/-- The inverse of the singleton power iso carries the module
action to the descended action. -/
theorem actLeft_modPowOne_inv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X] :
    actLeft A X ≫ (modPowOne A X).inv =
      (A ◁ (modPowOne A X).inv) ≫ modPowAct A X 0 := by
  calc actLeft A X ≫ (modPowOne A X).inv
      = (A ◁ (modPowOne A X).inv) ≫
          (A ◁ (modPowOne A X).hom) ≫ actLeft A X ≫
          (modPowOne A X).inv := by
        rw [← MonoidalCategory.whiskerLeft_comp_assoc,
          Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id,
          Category.id_comp]
    _ = (A ◁ (modPowOne A X).inv) ≫ modPowAct A X 0 := by
        rw [← reassoc_of% (modPowAct_modPowOne A X)]
        simp only [Iso.hom_inv_id, Category.comp_id]

/-- A module maps into the singleton stage of its power tower. -/
noncomputable def toModPowModZero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) :
    M ⟶ modPowMod A M.X 0 :=
  Mod.Hom.mk' ((modPowOne A M.X).inv)
    (actLeft_modPowOne_inv A M.X)

/-- One stage of the power chain: the module tensor product of
matching module powers of the dual pair, in copairing order. -/
noncomputable def powStage
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (k : ℕ) : D :=
  modTensor A (modPowMod A M.X k) (modPowMod A M'.X k)

/-- **The power chain multiplication**: two power stages
interchange and multiply into the stage of summed arity. -/
noncomputable def powChainMul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (m n : ℕ) :
    powStage A M M' m ⊗ powStage A M M' n ⟶
      powStage A M M' (m + 1 + n) :=
  interchange A (modPowMod A M.X m) (modPowMod A M'.X m)
      (modPowMod A M.X n) (modPowMod A M'.X n) ≫
    modTensorMap A (powMulMod A M.X m n) (powMulMod A M'.X m n)

/-- **The seed of the power chain**: the copairing lands in the
bottom stage. -/
noncomputable def powSeed
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    𝟙_ D ⟶ powStage A M M' 0 :=
  copairUnit A M M' d ≫
    modTensorMap A (toModPowModZero A M) (toModPowModZero A M')

/-- An arity transport of module powers, as a map of modules. -/
noncomputable def modPowCastMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    {a b : ℕ} (h : a + 1 = b + 1) :
    modPowMod A X a ⟶ modPowMod A X b :=
  Mod.Hom.mk' (modPowCast A X h) (modPowAct_cast A X h).symm

/-- The braiding of the module tensor product, as a map of
modules. -/
noncomputable def modTensorSwapMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A]
    (P Q : Mod D A) :
    modTensorMod A P Q ⟶ modTensorMod A Q P :=
  Mod.Hom.mk' (modTensorSwap A P Q) (modTensorAct_swap A P Q)

/-- **The power chain transition**: insert the seed at the outer
position of the nested pairing — the new factor joins the
`M`-power at the front and the `M'`-power at the back, so the
peel of the nested pairing removes exactly the inserted pair. -/
noncomputable def powDelta
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (k : ℕ) : powStage A M M' k ⟶ powStage A M M' (k + 1) :=
  (ρ_ (powStage A M M' k)).inv ≫
    (powStage A M M' k ◁ powSeed A M M' d) ≫
    interchange A (modPowMod A M.X k) (modPowMod A M'.X k)
      (modPowMod A M.X 0) (modPowMod A M'.X 0) ≫
    modTensorMap A
      (modTensorSwapMod A (modPowMod A M.X k)
          (modPowMod A M.X 0) ≫
        powMulMod A M.X 0 k ≫
        modPowCastMod A M.X (by omega : 0 + 1 + k + 1 = k + 2))
      (powMulMod A M'.X k 0)

/-- **The copairing powers**: the iterated seed multiplication
along the power chain. -/
noncomputable def powUnitStage
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    (k : ℕ) → (𝟙_ D ⟶ powStage A M M' k)
  | 0 => powSeed A M M' d
  | (k + 1) => powUnitStage A M M' d k ≫ powDelta A M M' d k

/-- The copairing powers ride along the transitions. -/
theorem powUnitStage_succ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') (k : ℕ) :
    powUnitStage A M M' d k ≫ powDelta A M M' d k =
      powUnitStage A M M' d (k + 1) :=
  rfl

end RS
