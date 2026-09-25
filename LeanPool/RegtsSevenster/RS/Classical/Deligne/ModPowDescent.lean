/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.PowCopairing
import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModZero

/-!
# The retract tower of a dualizable module

Iterating the zig retract: a module that is a retract of its
double-dual sandwich is a retract of every stage of the sandwich
tower.  Together with the merge isomorphisms this descends the
vanishing of a relative power to the module itself.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **The sandwich tower**: iterate tensoring with the pair
`M ⊗ M'` on the left. -/
noncomputable def sandwichTower
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A) :
    ℕ → Mod D A
  | 0 => M
  | (k + 1) => modTensorMod A (modTensorMod A M M')
      (sandwichTower A M M' k)

@[simp] lemma sandwichTower_zero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A) :
    sandwichTower A M M' 0 = M := rfl

@[simp] lemma sandwichTower_succ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (k : ℕ) :
    sandwichTower A M M' (k + 1) =
      modTensorMod A (modTensorMod A M M')
        (sandwichTower A M M' k) := rfl

/-- **The retract iterates up the tower**: a module that is a
retract of its sandwich is a retract of every tower stage. -/
theorem sandwichTower_retract
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (i₀ : M ⟶ modTensorMod A (modTensorMod A M M') M)
    (r₀ : modTensorMod A (modTensorMod A M M') M ⟶ M)
    (h₀ : i₀ ≫ r₀ = 𝟙 M) :
    ∀ k : ℕ, ∃ (i : M ⟶ sandwichTower A M M' k)
      (r : sandwichTower A M M' k ⟶ M), i ≫ r = 𝟙 M
  | 0 => ⟨𝟙 M, 𝟙 M, Category.id_comp _⟩
  | (k + 1) => by
    obtain ⟨ik, rk, hk⟩ :=
      sandwichTower_retract A M M' i₀ r₀ h₀ k
    refine ⟨i₀ ≫ modTensorMapMod A (𝟙 _) ik,
      modTensorMapMod A (𝟙 _) rk ≫ r₀, ?_⟩
    have hmid : modTensorMapMod A
        (𝟙 (modTensorMod A M M')) ik ≫
        modTensorMapMod A (𝟙 (modTensorMod A M M')) rk =
        𝟙 (modTensorMod A (modTensorMod A M M') M) := by
      apply Mod.Hom.ext
      change modTensorMap A (𝟙 (modTensorMod A M M')) ik ≫
        modTensorMap A (𝟙 (modTensorMod A M M')) rk =
        𝟙 (modTensor A (modTensorMod A M M') M)
      rw [← modTensorMap_comp, Category.comp_id]
      have hcarrier : ik ≫ rk = 𝟙 M := hk
      rw [hcarrier, modTensorMap_id]
    erw [Category.assoc]
    refine Eq.trans (whisker_eq _
      (Category.assoc _ _ _).symm) ?_
    refine Eq.trans (whisker_eq _ (eq_whisker hmid _)) ?_
    refine Eq.trans (whisker_eq _ (Category.id_comp _)) ?_
    exact h₀

end RS
