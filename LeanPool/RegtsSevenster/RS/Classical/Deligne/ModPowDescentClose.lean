/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.SandwichMerge

/-!
# Descent of power vanishing to the module

Given the sandwich retract of a dualizable module, vanishing of a
relative tensor power descends to the module itself: the retract
iterates up the tower, and the tower reassembles into a power
pair whose first factor is the vanishing power.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **Power vanishing descends along the sandwich retract**: a
module with a sandwich retract whose `(n + 2)`-nd relative power
vanishes is itself zero. -/
theorem isZero_of_sandwich_of_isZero_modPow
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (i₀ : M ⟶ modTensorMod A (modTensorMod A M M') M)
    (r₀ : modTensorMod A (modTensorMod A M M') M ⟶ M)
    (h₀ : i₀ ≫ r₀ = 𝟙 M) {n : ℕ}
    (h : IsZero (modPow A M.X (n + 2))) : IsZero M.X := by
  obtain ⟨i, r, hir⟩ :=
    sandwichTower_retract A M M' i₀ r₀ h₀ (n + 1)
  have hz : IsZero ((sandwichTower A M M' (n + 1)).X) :=
    isZero_sandwichTower_of_isZero_modPow A M M' n h
  rw [IsZero.iff_id_eq_zero]
  have hcar : i.hom ≫ r.hom = 𝟙 M.X :=
    congrArg Mod.Hom.hom hir
  rw [← hcar, hz.eq_of_tgt i.hom 0, Limits.zero_comp]

end RS
