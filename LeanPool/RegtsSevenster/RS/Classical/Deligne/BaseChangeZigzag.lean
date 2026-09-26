/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.BaseChangeDatum

/-!
# The zigzag laws of a base-changed duality datum

The statement that base change preserves the zigzag laws, named
so that the dévissage steps can refer to it directly.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **Base change preserves the zigzag laws**: the statement of
record for the dévissage steps. -/
def BaseChangeZigzagStatement
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)] :
    Prop :=
  ∀ (A : D) (_ : MonObj A) (_ : IsCommMonObj A)
    (M M' : Mod D A) (d : ModDualityDatum A M M')
    (_ : ModZigzagDatum A d)
    (B : D) (_ : MonObj B) (_ : IsCommMonObj B)
    (φ : A ⟶ B) (_ : IsMonHom φ),
    ModZigzagDatum B (baseChangeDatum A B φ d)

end RS
