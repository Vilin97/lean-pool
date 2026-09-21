/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.PlainShuffle
import LeanPool.RegtsSevenster.RS.Classical.Deligne.TwistPow

/-!
# The cover factorisation of the twisted power identification

Over the plain tensor-power covers, the twisted power
identification is the diagonal shuffle followed by the projection
of the module factor.  This reduces the conjugation of the
permutation action through the identification to the committed
plain equivariance.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- The arity-one projection is the unitor through the singleton
identification. -/
theorem modPowπ_one [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] (A : D)
    [MonObj A]
    (X : D) [ModObj A X] :
    modPowπ A X 1 ≫ (modPowOne A X).hom = (λ_ X).hom := by
  rw [modPowOne, Iso.trans_hom, ← Category.assoc,
    show modPowπ A X 1 ≫ (modPowTriv A X (by omega)).hom =
      𝟙 (tensorPow D X 1) from
        (modPowTriv A X (by omega)).inv_hom_id,
    Category.id_comp]

/-- The singleton inverse is the unitor into the projection. -/
theorem modPowOne_inv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] (A : D)
    [MonObj A]
    (X : D) [ModObj A X] :
    (modPowOne A X).inv = (λ_ X).inv ≫ modPowπ A X 1 := by
  have h : ((λ_ X).inv ≫ modPowπ A X 1) ≫
      (modPowOne A X).hom = 𝟙 X :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun t : tensorPow D X 1 ⟶ X =>
          (λ_ X).inv ≫ t) (modPowπ_one A X)).trans
        (Iso.inv_hom_id (λ_ X)))
  exact ((Iso.comp_hom_eq_id (modPowOne A X)).mp h).symm

/-- The generic core of the shuffle–concatenation step: against a
map into a tensor pair, the unit shuffle and the two unit
concatenation words dissolve into the source concatenation word.
Every concatenation word at block size one is a unitor windup, so
no braiding beyond the interchange blocks enters. -/
private theorem shuffle_concat_core
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    {P B₁ B₂ : D} (C₁ C₂ : D)
    (f : P ⟶ B₁ ⊗ B₂) :
    (f ⊗ₘ (((λ_ (𝟙_ D)).inv ▷ (C₁ ⊗ C₂)) ≫
        tensorμ (𝟙_ D) (𝟙_ D) C₁ C₂)) ≫
      tensorμ B₁ B₂ (𝟙_ D ⊗ C₁) (𝟙_ D ⊗ C₂) ≫
      (((α_ B₁ (𝟙_ D) C₁).inv ≫ ((ρ_ B₁).hom ▷ C₁)) ▷
        (B₂ ⊗ (𝟙_ D ⊗ C₂))) ≫
      ((B₁ ⊗ C₁) ◁
        ((α_ B₂ (𝟙_ D) C₂).inv ≫ ((ρ_ B₂).hom ▷ C₂))) =
    ((α_ P (𝟙_ D) (C₁ ⊗ C₂)).inv ≫
        ((ρ_ P).hom ▷ (C₁ ⊗ C₂))) ≫
      ((f ▷ (C₁ ⊗ C₂)) ≫ tensorμ B₁ B₂ C₁ C₂) := by
  have hw : ∀ (B C : D), (α_ B (𝟙_ D) C).inv ≫
      ((ρ_ B).hom ▷ C) = B ◁ (λ_ C).hom := by
    intro B C
    monoidal
  rw [hw B₁ C₁, hw B₂ C₂, hw P (C₁ ⊗ C₂)]
  rw [← MonoidalCategory.tensorHom_def (B₁ ◁ (λ_ C₁).hom)
      (B₂ ◁ (λ_ C₂).hom),
    ← tensorμ_natural_right B₁ B₂ (λ_ C₁).hom (λ_ C₂).hom,
    ← MonoidalCategory.id_tensorHom (B₁ ⊗ B₂)
      ((λ_ C₁).hom ⊗ₘ (λ_ C₂).hom),
    ← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
    Category.comp_id, Category.assoc,
    ← tensor_left_unitality C₁ C₂,
    MonoidalCategory.tensorHom_def' f (λ_ (C₁ ⊗ C₂)).hom,
    Category.assoc]

/-- **The shuffle absorbs one concatenated block**: shuffling the
two halves and concatenating both target powers is concatenating
the source power and shuffling.  At block size one every
concatenation word is definitionally a unitor windup, so this is
the generic core, read through the recursions. -/
private theorem shuffle_concat_step
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (V X : D) (k : ℕ) :
    (tensorPowConcat (V ⊗ X) (k + 1) (0 + 1)).inv ≫
        ((plainShuffle V X (k + 1)).hom ⊗ₘ
          (plainShuffle V X (0 + 1)).hom) ≫
        tensorμ (tensorPow D V (k + 1)) (tensorPow D X (k + 1))
          (tensorPow D V (0 + 1)) (tensorPow D X (0 + 1)) ≫
        ((tensorPowConcat V (k + 1) (0 + 1)).hom ▷
          (tensorPow D X (k + 1) ⊗ tensorPow D X (0 + 1))) ≫
        (tensorPow D V (k + 1 + (0 + 1)) ◁
          (tensorPowConcat X (k + 1) (0 + 1)).hom) =
      (plainShuffle V X (k + 1 + 1)).hom := by
  rw [Iso.inv_comp_eq]
  exact shuffle_concat_core V X (plainShuffle V X (k + 1)).hom

/-- The base of the cover factorisation: at arity one the twisted
identification over the plain covers is the unit shuffle over the
module projection. -/
private theorem twistPow_cover_factor_zero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A]
    (V : D) (R : Mod D A) :
    modPowπ A ((tensorLeftMod A V R).X) (0 + 1) ≫
        ((twistPowModIso A V R 0).hom).hom =
      (plainShuffle V R.X (0 + 1)).hom ≫
        ((tensorPow D V (0 + 1)) ◁ modPowπ A R.X (0 + 1)) := by
  rw [twistPowModIso]
  show modPowπ A ((tensorLeftMod A V R).X) 1 ≫
      ((modPowOne A ((tensorLeftMod A V R).X)).hom ≫
        (((λ_ V).inv ▷ R.X) ≫
          ((𝟙_ D ⊗ V) ◁ (modPowOne A R.X).inv))) =
    (plainShuffle V R.X 1).hom ≫
      ((𝟙_ D ⊗ V) ◁ modPowπ A R.X 1)
  rw [← Category.assoc, modPowπ_one, modPowOne_inv,
    MonoidalCategory.whiskerLeft_comp]
  have hL : (λ_ (V ⊗ R.X)).hom ≫ ((λ_ V).inv ▷ R.X) ≫
      ((𝟙_ D ⊗ V) ◁ (λ_ R.X).inv) =
      (plainShuffle V R.X 1).hom := by
    rw [← MonoidalCategory.tensorHom_def,
      show (plainShuffle V R.X 1).hom =
        ((λ_ (𝟙_ D)).inv ▷ (V ⊗ R.X)) ≫
          tensorμ (𝟙_ D) (𝟙_ D) V R.X from rfl,
      tensor_left_unitality V R.X]
    simp only [Category.assoc,
      MonoidalCategory.tensorHom_comp_tensorHom, Iso.hom_inv_id,
      MonoidalCategory.id_tensorHom_id, Category.comp_id]
  exact (reassoc_of% hL) ((𝟙_ D ⊗ V) ◁ modPowπ A R.X 1)

/-- **The cover factorisation**: over the plain covers, the
twisted power identification is the diagonal shuffle followed by
the projection of the module factor. -/
theorem twistPow_cover_factor
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A]
    (V : D) (R : Mod D A) :
    ∀ k : ℕ,
    modPowπ A ((tensorLeftMod A V R).X) (k + 1) ≫
        ((twistPowModIso A V R k).hom).hom =
      (plainShuffle V R.X (k + 1)).hom ≫
        ((tensorPow D V (k + 1)) ◁ modPowπ A R.X (k + 1))
  | 0 => twistPow_cover_factor_zero A V R
  | (k + 1) => by
    rw [twistPowModIso]
    show modPowπ A ((tensorLeftMod A V R).X) (k + 1 + 0 + 1) ≫
        (powSplit A ((tensorLeftMod A V R).X) k 0 ≫
          (modTensorMap A (twistPowModIso A V R k).hom
              (twistPowModIso A V R 0).hom ≫
            (twistShuffleHom A (tensorPow D V (k + 1))
                (tensorPow D V (0 + 1)) (modPowMod A R.X k)
                (modPowMod A R.X 0) ≫
              (((tensorPowConcat V (k + 1) (0 + 1)).hom ▷
                  modTensor A (modPowMod A R.X k)
                    (modPowMod A R.X 0)) ≫
                (tensorPow D V (k + 1 + (0 + 1)) ◁
                  powMulDesc A R.X k 0)))))
      = (plainShuffle V R.X (k + 1 + 1)).hom ≫
          (tensorPow D V (k + 1 + 1) ◁ modPowπ A R.X (k + 1 + 1))
    have hIH : (modPowπ A ((tensorLeftMod A V R).X) (k + 1) ⊗ₘ
          modPowπ A ((tensorLeftMod A V R).X) (0 + 1)) ≫
        (((twistPowModIso A V R k).hom).hom ⊗ₘ
          ((twistPowModIso A V R 0).hom).hom) =
      ((plainShuffle V R.X (k + 1)).hom ⊗ₘ
          (plainShuffle V R.X (0 + 1)).hom) ≫
        ((tensorPow D V (k + 1) ◁ modPowπ A R.X (k + 1)) ⊗ₘ
          (tensorPow D V (0 + 1) ◁ modPowπ A R.X (0 + 1))) :=
      (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _).trans
        ((congrArg₂ (· ⊗ₘ ·) (twistPow_cover_factor A V R k)
            (twistPow_cover_factor_zero A V R)).trans
          (MonoidalCategory.tensorHom_comp_tensorHom
            _ _ _ _).symm)
    have hnat : ((tensorPow D V (k + 1) ◁
            modPowπ A R.X (k + 1)) ⊗ₘ
          (tensorPow D V (0 + 1) ◁ modPowπ A R.X (0 + 1))) ≫
        tensorμ (tensorPow D V (k + 1)) (modPow A R.X (k + 1))
          (tensorPow D V (0 + 1)) (modPow A R.X (0 + 1)) =
      tensorμ (tensorPow D V (k + 1)) (tensorPow D R.X (k + 1))
          (tensorPow D V (0 + 1)) (tensorPow D R.X (0 + 1)) ≫
        ((tensorPow D V (k + 1) ⊗ tensorPow D V (0 + 1)) ◁
          (modPowπ A R.X (k + 1) ⊗ₘ modPowπ A R.X (0 + 1))) := by
      simpa using tensorμ_natural (𝟙 (tensorPow D V (k + 1)))
        (modPowπ A R.X (k + 1)) (𝟙 (tensorPow D V (0 + 1)))
        (modPowπ A R.X (0 + 1))
    have hRside : ((tensorPow D V (k + 1) ⊗
            tensorPow D V (0 + 1)) ◁
          (modPowπ A R.X (k + 1) ⊗ₘ modPowπ A R.X (0 + 1))) ≫
        (((tensorPow D V (k + 1) ⊗ tensorPow D V (0 + 1)) ◁
            modTensorπ A (modPowMod A R.X k)
              (modPowMod A R.X 0)) ≫
          (((tensorPowConcat V (k + 1) (0 + 1)).hom ▷
              modTensor A (modPowMod A R.X k)
                (modPowMod A R.X 0)) ≫
            (tensorPow D V (k + 1 + (0 + 1)) ◁
              powMulDesc A R.X k 0))) =
      ((tensorPowConcat V (k + 1) (0 + 1)).hom ▷
          (tensorPow D R.X (k + 1) ⊗ tensorPow D R.X (0 + 1))) ≫
        ((tensorPow D V (k + 1 + (0 + 1)) ◁
            (tensorPowConcat R.X (k + 1) (0 + 1)).hom) ≫
          (tensorPow D V (k + 1 + (0 + 1)) ◁
            modPowπ A R.X (k + 1 + (0 + 1)))) :=
      ((MonoidalCategory.whiskerLeft_comp_assoc
          (tensorPow D V (k + 1) ⊗ tensorPow D V (0 + 1))
          (modPowπ A R.X (k + 1) ⊗ₘ modPowπ A R.X (0 + 1))
          (modTensorπ A (modPowMod A R.X k) (modPowMod A R.X 0))
          _).symm).trans
        ((MonoidalCategory.whisker_exchange_assoc
            (tensorPowConcat V (k + 1) (0 + 1)).hom
            ((modPowπ A R.X (k + 1) ⊗ₘ modPowπ A R.X (0 + 1)) ≫
              modTensorπ A (modPowMod A R.X k)
                (modPowMod A R.X 0))
            (tensorPow D V (k + 1 + (0 + 1)) ◁
              powMulDesc A R.X k 0)).trans
          (congrArg (fun z =>
              ((tensorPowConcat V (k + 1) (0 + 1)).hom ▷
                (tensorPow D R.X (k + 1) ⊗
                  tensorPow D R.X (0 + 1))) ≫ z)
            (((MonoidalCategory.whiskerLeft_comp
                (tensorPow D V (k + 1 + (0 + 1)))
                ((modPowπ A R.X (k + 1) ⊗ₘ
                    modPowπ A R.X (0 + 1)) ≫
                  modTensorπ A (modPowMod A R.X k)
                    (modPowMod A R.X 0))
                (powMulDesc A R.X k 0)).symm).trans
              ((congrArg (fun z =>
                  tensorPow D V (k + 1 + (0 + 1)) ◁ z)
                ((Category.assoc
                    (modPowπ A R.X (k + 1) ⊗ₘ
                      modPowπ A R.X (0 + 1))
                    (modTensorπ A (modPowMod A R.X k)
                      (modPowMod A R.X 0))
                    (powMulDesc A R.X k 0)).trans
                  ((congrArg (fun z =>
                      (modPowπ A R.X (k + 1) ⊗ₘ
                        modPowπ A R.X (0 + 1)) ≫ z)
                    (modTensorπ_powMulDesc A R.X k 0)).trans
                    (modPowπ_tensor_modPowMul A R.X (k + 1)
                      (0 + 1))))).trans
                (MonoidalCategory.whiskerLeft_comp
                  (tensorPow D V (k + 1 + (0 + 1)))
                  (tensorPowConcat R.X (k + 1) (0 + 1)).hom
                  (modPowπ A R.X (k + 1 + (0 + 1))))))))
    have hTail : modTensorπ A
          (modPowMod A ((tensorLeftMod A V R).X) k)
          (modPowMod A ((tensorLeftMod A V R).X) 0) ≫
        (modTensorMap A (twistPowModIso A V R k).hom
            (twistPowModIso A V R 0).hom ≫
          (twistShuffleHom A (tensorPow D V (k + 1))
              (tensorPow D V (0 + 1)) (modPowMod A R.X k)
              (modPowMod A R.X 0) ≫
            (((tensorPowConcat V (k + 1) (0 + 1)).hom ▷
                modTensor A (modPowMod A R.X k)
                  (modPowMod A R.X 0)) ≫
              (tensorPow D V (k + 1 + (0 + 1)) ◁
                powMulDesc A R.X k 0)))) =
      (((twistPowModIso A V R k).hom).hom ⊗ₘ
          ((twistPowModIso A V R 0).hom).hom) ≫
        (tensorμ (tensorPow D V (k + 1)) (modPow A R.X (k + 1))
            (tensorPow D V (0 + 1)) (modPow A R.X (0 + 1)) ≫
          (((tensorPow D V (k + 1) ⊗ tensorPow D V (0 + 1)) ◁
              modTensorπ A (modPowMod A R.X k)
                (modPowMod A R.X 0)) ≫
            (((tensorPowConcat V (k + 1) (0 + 1)).hom ▷
                modTensor A (modPowMod A R.X k)
                  (modPowMod A R.X 0)) ≫
              (tensorPow D V (k + 1 + (0 + 1)) ◁
                powMulDesc A R.X k 0)))) :=
      (modTensorπ_map_assoc A (twistPowModIso A V R k).hom
          (twistPowModIso A V R 0).hom _).trans
        (congrArg (fun z =>
            (((twistPowModIso A V R k).hom).hom ⊗ₘ
              ((twistPowModIso A V R 0).hom).hom) ≫ z)
          ((modTensorπ_twistShuffleHom_assoc A
              (tensorPow D V (k + 1)) (tensorPow D V (0 + 1))
              (modPowMod A R.X k) (modPowMod A R.X 0) _).trans
            (Category.assoc
              (tensorμ (tensorPow D V (k + 1))
                (modPow A R.X (k + 1)) (tensorPow D V (0 + 1))
                (modPow A R.X (0 + 1)))
              ((tensorPow D V (k + 1) ⊗
                  tensorPow D V (0 + 1)) ◁
                modTensorπ A (modPowMod A R.X k)
                  (modPowMod A R.X 0))
              _)))
    have hMid : (modPowπ A ((tensorLeftMod A V R).X) (k + 1) ⊗ₘ
          modPowπ A ((tensorLeftMod A V R).X) (0 + 1)) ≫
        ((((twistPowModIso A V R k).hom).hom ⊗ₘ
            ((twistPowModIso A V R 0).hom).hom) ≫
          (tensorμ (tensorPow D V (k + 1))
              (modPow A R.X (k + 1)) (tensorPow D V (0 + 1))
              (modPow A R.X (0 + 1)) ≫
            (((tensorPow D V (k + 1) ⊗ tensorPow D V (0 + 1)) ◁
                modTensorπ A (modPowMod A R.X k)
                  (modPowMod A R.X 0)) ≫
              (((tensorPowConcat V (k + 1) (0 + 1)).hom ▷
                  modTensor A (modPowMod A R.X k)
                    (modPowMod A R.X 0)) ≫
                (tensorPow D V (k + 1 + (0 + 1)) ◁
                  powMulDesc A R.X k 0))))) =
      ((plainShuffle V R.X (k + 1)).hom ⊗ₘ
          (plainShuffle V R.X (0 + 1)).hom) ≫
        (((tensorPow D V (k + 1) ◁ modPowπ A R.X (k + 1)) ⊗ₘ
            (tensorPow D V (0 + 1) ◁ modPowπ A R.X (0 + 1))) ≫
          (tensorμ (tensorPow D V (k + 1))
              (modPow A R.X (k + 1)) (tensorPow D V (0 + 1))
              (modPow A R.X (0 + 1)) ≫
            (((tensorPow D V (k + 1) ⊗ tensorPow D V (0 + 1)) ◁
                modTensorπ A (modPowMod A R.X k)
                  (modPowMod A R.X 0)) ≫
              (((tensorPowConcat V (k + 1) (0 + 1)).hom ▷
                  modTensor A (modPowMod A R.X k)
                    (modPowMod A R.X 0)) ≫
                (tensorPow D V (k + 1 + (0 + 1)) ◁
                  powMulDesc A R.X k 0))))) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ tensorμ (tensorPow D V (k + 1))
              (modPow A R.X (k + 1)) (tensorPow D V (0 + 1))
              (modPow A R.X (0 + 1)) ≫
            (((tensorPow D V (k + 1) ⊗ tensorPow D V (0 + 1)) ◁
                modTensorπ A (modPowMod A R.X k)
                  (modPowMod A R.X 0)) ≫
              (((tensorPowConcat V (k + 1) (0 + 1)).hom ▷
                  modTensor A (modPowMod A R.X k)
                    (modPowMod A R.X 0)) ≫
                (tensorPow D V (k + 1 + (0 + 1)) ◁
                  powMulDesc A R.X k 0)))) hIH).trans
          (Category.assoc _ _ _))
    have hW : ((tensorPow D V (k + 1) ◁
            modPowπ A R.X (k + 1)) ⊗ₘ
          (tensorPow D V (0 + 1) ◁ modPowπ A R.X (0 + 1))) ≫
        (tensorμ (tensorPow D V (k + 1)) (modPow A R.X (k + 1))
            (tensorPow D V (0 + 1)) (modPow A R.X (0 + 1)) ≫
          (((tensorPow D V (k + 1) ⊗ tensorPow D V (0 + 1)) ◁
              modTensorπ A (modPowMod A R.X k)
                (modPowMod A R.X 0)) ≫
            (((tensorPowConcat V (k + 1) (0 + 1)).hom ▷
                modTensor A (modPowMod A R.X k)
                  (modPowMod A R.X 0)) ≫
              (tensorPow D V (k + 1 + (0 + 1)) ◁
                powMulDesc A R.X k 0)))) =
      tensorμ (tensorPow D V (k + 1)) (tensorPow D R.X (k + 1))
          (tensorPow D V (0 + 1)) (tensorPow D R.X (0 + 1)) ≫
        (((tensorPowConcat V (k + 1) (0 + 1)).hom ▷
            (tensorPow D R.X (k + 1) ⊗
              tensorPow D R.X (0 + 1))) ≫
          ((tensorPow D V (k + 1 + (0 + 1)) ◁
              (tensorPowConcat R.X (k + 1) (0 + 1)).hom) ≫
            (tensorPow D V (k + 1 + (0 + 1)) ◁
              modPowπ A R.X (k + 1 + (0 + 1))))) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ ((tensorPow D V (k + 1) ⊗
              tensorPow D V (0 + 1)) ◁
              modTensorπ A (modPowMod A R.X k)
                (modPowMod A R.X 0)) ≫
            (((tensorPowConcat V (k + 1) (0 + 1)).hom ▷
                modTensor A (modPowMod A R.X k)
                  (modPowMod A R.X 0)) ≫
              (tensorPow D V (k + 1 + (0 + 1)) ◁
                powMulDesc A R.X k 0))) hnat).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun z =>
                tensorμ (tensorPow D V (k + 1))
                  (tensorPow D R.X (k + 1))
                  (tensorPow D V (0 + 1))
                  (tensorPow D R.X (0 + 1)) ≫ z) hRside)))
    refine (modPowπ_powSplit_assoc A ((tensorLeftMod A V R).X)
      k 0 _).trans ?_
    refine (congrArg (fun z =>
        (tensorPowConcat ((tensorLeftMod A V R).X) (k + 1)
          (0 + 1)).inv ≫
        ((modPowπ A ((tensorLeftMod A V R).X) (k + 1) ⊗ₘ
          modPowπ A ((tensorLeftMod A V R).X) (0 + 1)) ≫ z))
      hTail).trans ?_
    refine (congrArg (fun z =>
        (tensorPowConcat ((tensorLeftMod A V R).X) (k + 1)
          (0 + 1)).inv ≫ z) hMid).trans ?_
    refine (congrArg (fun z =>
        (tensorPowConcat ((tensorLeftMod A V R).X) (k + 1)
          (0 + 1)).inv ≫
        (((plainShuffle V R.X (k + 1)).hom ⊗ₘ
          (plainShuffle V R.X (0 + 1)).hom) ≫ z))
      hW).trans ?_
    exact (reassoc_of% (shuffle_concat_step V R.X k))
      (tensorPow D V (k + 1 + (0 + 1)) ◁
        modPowπ A R.X (k + 1 + (0 + 1)))

end RS
