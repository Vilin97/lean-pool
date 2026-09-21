/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.PairMul

/-!
# The multiplication of the chain algebra

The symmetric multiplication descends through the module-tensor
coequalizer of two symmetric powers, giving a module map of
bundles; through the interchange, the tensor product of two chain
stages multiplies into the chain stage of summed arity.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- The two module-tensor legs of a pair of symmetric powers
agree after the symmetric multiplication. -/
theorem symMul_modTensor_cond
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (m n : ℕ) :
    modTensorLegM A (symPowMod A X m) (symPowMod A X n) ≫
        symMul A X (m + 1) (n + 1) =
      modTensorLegN A (symPowMod A X m) (symPowMod A X n) ≫
        symMul A X (m + 1) (n + 1) := by
  have h3 := (symMul_actRight A X m n).trans
    (symMul_actLeft A X m n).symm
  simp only [braidPast_hom, Category.assoc] at h3
  have h4 := (cancel_epi
    (α_ A (symPow A X (m + 1)) (symPow A X (n + 1))).inv).mp h3
  rw [modTensorLegM, modTensorLegN, actRight,
    show actLeft A (symPowMod A X m).X = symPowAct A X m from
      rfl,
    show actLeft A (symPowMod A X n).X = symPowAct A X n from
      rfl]
  show (((β_ (symPow A X (m + 1)) A).hom ≫ symPowAct A X m) ▷
      symPow A X (n + 1)) ≫ symMul A X (m + 1) (n + 1) =
    ((α_ (symPow A X (m + 1)) A (symPow A X (n + 1))).hom ≫
      (symPow A X (m + 1) ◁ symPowAct A X n)) ≫
      symMul A X (m + 1) (n + 1)
  rw [comp_whiskerRight, Category.assoc, ← h4,
    ← comp_whiskerRight_assoc, SymmetricCategory.symmetry,
    MonoidalCategory.id_whiskerRight, Category.id_comp]
  simp only [Category.assoc]

/-- **The descended symmetric multiplication** on the module
tensor product of two symmetric powers. -/
noncomputable def symMulDesc
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (m n : ℕ) :
    modTensor A (symPowMod A X m) (symPowMod A X n) ⟶
      symPow A X (m + 1 + n + 1) :=
  modTensorDesc A (symPowMod A X m) (symPowMod A X n)
    (symMul A X (m + 1) (n + 1)) (symMul_modTensor_cond A X m n)

/-- Defining equation of the descended multiplication. -/
@[reassoc (attr := simp)]
theorem modTensorπ_symMulDesc
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (m n : ℕ) :
    modTensorπ A (symPowMod A X m) (symPowMod A X n) ≫
        symMulDesc A X m n = symMul A X (m + 1) (n + 1) :=
  modTensorπ_desc A (symPowMod A X m) (symPowMod A X n) _ _

/-- The descended multiplication intertwines the module
actions. -/
theorem symMulDesc_act
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (m n : ℕ) :
    modTensorAct A (symPowMod A X m) (symPowMod A X n) ≫
        symMulDesc A X m n =
      (A ◁ symMulDesc A X m n) ≫ symPowAct A X (m + 1 + n) := by
  apply modTensor_whisker_hom_ext A (symPowMod A X m)
    (symPowMod A X n) A
  conv_lhs => rw [whiskerLeft_modTensorπ_act_assoc,
    modTensorπ_symMulDesc]
  conv_rhs => rw [← whiskerLeft_comp_assoc,
    modTensorπ_symMulDesc]
  have h := symMul_actLeft A X m n
  show (α_ A (symPow A X (m + 1)) (symPow A X (n + 1))).inv ≫
      (symPowAct A X m ▷ symPow A X (n + 1)) ≫
      symMul A X (m + 1) (n + 1) =
    (A ◁ symMul A X (m + 1) (n + 1)) ≫ symPowAct A X (m + 1 + n)
  simpa only [Category.assoc] using h

/-- The descended symmetric multiplication as a map of
modules. -/
noncomputable def symMulMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (m n : ℕ) :
    modTensorMod A (symPowMod A X m) (symPowMod A X n) ⟶
      symPowMod A X (m + 1 + n) :=
  Mod.Hom.mk' (symMulDesc A X m n) (symMulDesc_act A X m n)

/-- One stage of the splitting chain: the module tensor product
of matching symmetric powers of the dual pair. -/
noncomputable def chainStage
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (k : ℕ) : D :=
  modTensor A (symPowMod A M'.X k) (symPowMod A M.X k)

/-- **The chain multiplication**: two stages interchange and
multiply into the stage of summed arity. -/
noncomputable def chainMul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (m n : ℕ) :
    chainStage A M M' m ⊗ chainStage A M M' n ⟶
      chainStage A M M' (m + 1 + n) :=
  interchange A (symPowMod A M'.X m) (symPowMod A M.X m)
      (symPowMod A M'.X n) (symPowMod A M.X n) ≫
    modTensorMap A (symMulMod A M'.X m n) (symMulMod A M.X m n)

/-- Defining equation of the chain multiplication: under the
stage projections it is the raw crossing followed by the
symmetric multiplications. -/
theorem tensorHom_π_chainMul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (m n : ℕ) :
    (modTensorπ A (symPowMod A M'.X m) (symPowMod A M.X m) ⊗ₘ
        modTensorπ A (symPowMod A M'.X n) (symPowMod A M.X n)) ≫
      chainMul A M M' m n =
    tensorμ (symPow A M'.X (m + 1)) (symPow A M.X (m + 1))
        (symPow A M'.X (n + 1)) (symPow A M.X (n + 1)) ≫
      (symMul A M'.X (m + 1) (n + 1) ⊗ₘ
        symMul A M.X (m + 1) (n + 1)) ≫
      modTensorπ A (symPowMod A M'.X (m + 1 + n))
        (symPowMod A M.X (m + 1 + n)) := by
  have h5 : (modTensorπ A (symPowMod A M'.X m)
        (symPowMod A M.X m) ⊗ₘ
      modTensorπ A (symPowMod A M'.X n) (symPowMod A M.X n)) ≫
      chainMul A M M' m n =
    ((modTensorπ A (symPowMod A M'.X m) (symPowMod A M.X m) ⊗ₘ
      modTensorπ A (symPowMod A M'.X n) (symPowMod A M.X n)) ≫
      interchange A (symPowMod A M'.X m) (symPowMod A M.X m)
        (symPowMod A M'.X n) (symPowMod A M.X n)) ≫
      modTensorMap A (symMulMod A M'.X m n)
        (symMulMod A M.X m n) := by
    rw [chainMul]
    exact (Category.assoc _ _ _).symm
  rw [h5, tensorHom_π_interchange, rawInterchangeπ,
    rawInterchange]
  simp only [Category.assoc]
  have h6 : modTensorπ A
      (modTensorMod A (symPowMod A M'.X m) (symPowMod A M'.X n))
      (modTensorMod A (symPowMod A M.X m) (symPowMod A M.X n)) ≫
      modTensorMap A (symMulMod A M'.X m n)
        (symMulMod A M.X m n) =
    ((symMulMod A M'.X m n).hom ⊗ₘ (symMulMod A M.X m n).hom) ≫
      modTensorπ A (symPowMod A M'.X (m + 1 + n))
        (symPowMod A M.X (m + 1 + n)) :=
    modTensorπ_map A (symMulMod A M'.X m n)
      (symMulMod A M.X m n)
  show tensorμ (symPow A M'.X (m + 1)) (symPow A M.X (m + 1))
      (symPow A M'.X (n + 1)) (symPow A M.X (n + 1)) ≫
    (modTensorπ A (symPowMod A M'.X m) (symPowMod A M'.X n) ⊗ₘ
      modTensorπ A (symPowMod A M.X m) (symPowMod A M.X n)) ≫
    modTensorπ A
      (modTensorMod A (symPowMod A M'.X m) (symPowMod A M'.X n))
      (modTensorMod A (symPowMod A M.X m) (symPowMod A M.X n)) ≫
    modTensorMap A (symMulMod A M'.X m n)
      (symMulMod A M.X m n) = _
  refine congrArg (CategoryStruct.comp _) ?_
  refine (congrArg (CategoryStruct.comp _) h6).trans ?_
  rw [show (symMulMod A M'.X m n).hom = symMulDesc A M'.X m n
      from rfl,
    show (symMulMod A M.X m n).hom = symMulDesc A M.X m n from
      rfl, ← Category.assoc]
  show ((modTensorπ A (symPowMod A M'.X m)
        (symPowMod A M'.X n) ⊗ₘ
      modTensorπ A (symPowMod A M.X m) (symPowMod A M.X n)) ≫
      (symMulDesc A M'.X m n ⊗ₘ symMulDesc A M.X m n)) ≫
    modTensorπ A (symPowMod A M'.X (m + 1 + n))
      (symPowMod A M.X (m + 1 + n)) = _
  rw [MonoidalCategory.tensorHom_comp_tensorHom,
    modTensorπ_symMulDesc, modTensorπ_symMulDesc]
  rfl

end RS
