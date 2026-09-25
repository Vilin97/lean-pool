/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.DevissageBound
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.StepB
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.DescentClose
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.InitState
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.KillerNonempty

/-!
# The trichotomy, unconditionally

Both steps of the dévissage are constructions, the trichotomy and
the exit are theorems, and a killing diagram bounds the counts, so
the recursion runs to completion from the initial state: an object
killed by some Schur functor is locally a mixed sum of the unit
and the odd line.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v

variable {C : Type v}

attribute [local instance]
  hasBinaryBiproducts_of_finite_biproducts

/-- **The trichotomy of Deligne 2.9, discharged**: an object with
an exact pairing that is killed by some Schur functor is locally
a mixed sum of the unit and the odd line. -/
theorem prop29
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    [CategoryTheory.Linear ℂ (Ind C)] [MonoidalLinear ℂ (Ind C)]
    (P : SchurPackage.{v}) (P₀ : SchurPackage.{0})
    (L : OddLine (Ind C)) (X Y : Ind C) [ExactPairing X Y]
    (h1 : ¬ IsZero (𝟙_ (Ind C))) : Prop29Statement P L X := by
  rintro ⟨lam, hkill⟩
  obtain ⟨mu, hcard, hmu⟩ := exists_killer_card_ne_zero P hkill
  exact devissage_run (Ind C) L X (devissageStepA L X)
    (devissageStepB L X) (devissageTrichotomy P L X)
    (devissageExit (Ind C) L X) (2 * mu.card)
    (devissage_bound P P₀ L X hcard hmu) (devissageInit L X Y h1)

end RS
