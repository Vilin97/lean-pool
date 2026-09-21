/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.InitDatum
import LeanPool.RegtsSevenster.RS.Classical.Deligne.Prop29State

/-!
# The initial state of the dévissage

Every object with an exact pairing seeds the dévissage: the base
is the tensor unit, no factors are split off, and the remainder
is the object itself with its ambient duality.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

attribute [local instance]
  hasBinaryBiproducts_of_finite_biproducts

/-- **The initial dévissage state**: the trivial base, no split
factors, and the object itself as the remainder. -/
noncomputable def devissageInit
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (L : OddLine D) (X Y : D)
    [ExactPairing X Y] (h1 : ¬ IsZero (𝟙_ D)) :
    DevissageState D L X where
  base := 𝟙_ D
  monObj := inferInstance
  comm := inferInstance
  unit_ne_zero := by
    rw [MonObj.one_def]
    intro h0
    exact h1 (by
      rw [IsZero.iff_id_eq_zero]
      exact h0)
  units := 0
  lines := 0
  rest := unitMod X
  restDual := unitMod Y
  datum := unitBaseDatum X Y
  zigzag := unitBaseDatum_zigzag X Y
  decomp := by
    have hZ : IsZero (freeMod (𝟙_ D) (L.mix 0 0)).X :=
      isZero_whiskerLeft (𝟙_ D) L.isZero_mix_zero
    exact ⟨(freeModUnitBase X).trans
      (modBiprodZeroLeft (𝟙_ D)
        (freeMod (𝟙_ D) (L.mix 0 0)) (unitMod X) hZ).symm⟩

end RS
