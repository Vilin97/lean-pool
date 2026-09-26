/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.KeyLemmaData

/-!
# The local splitting statement

Deligne's 2.10, the consumed form: over a category where the
tensor structure is exact, every short exact sequence splits
after base change to some nonzero commutative algebra.  The
splitting is a section of the base-changed epimorphism as module
maps over the algebra.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- The action square of the free module on a morphism. -/
theorem freeModMap_lin [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    {V W : D} (f : V ⟶ W) :
    ((α_ A A V).inv ≫ (μ[A] ▷ V)) ≫ (A ◁ f) =
      (A ◁ (A ◁ f)) ≫ ((α_ A A W).inv ≫ (μ[A] ▷ W)) := by
  rw [Category.assoc, ← whisker_exchange,
    ← associator_inv_naturality_right_assoc]

/-- The free module on a morphism. -/
noncomputable def freeModMap
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    {V W : D} (f : V ⟶ W) :
    freeMod A V ⟶ freeMod A W :=
  Mod.Hom.mk' (A ◁ f) (freeModMap_lin A f)

section Statement

-- The short-exactness datum indexes the statement: it records which
-- sequences the assertion is made of, and the proofs of record are
-- stated at this signature.
/-- **The local splitting statement of record** (Deligne 2.10,
the consumed direction): a short exact sequence acquires a
module-level section of its epimorphism after base change to
some nonzero commutative algebra. -/
def Rappel210Statement
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] [Abelian D]
    (S : ShortComplex D) (_ : S.ShortExact) :
    Prop :=
  ∃ (A : D) (_ : MonObj A) (_ : IsCommMonObj A),
    η[A] ≠ 0 ∧
    ∃ s : freeMod A S.X₃ ⟶ freeMod A S.X₂,
      s ≫ freeModMap A S.g = 𝟙 (freeMod A S.X₃)

end Statement

end RS
