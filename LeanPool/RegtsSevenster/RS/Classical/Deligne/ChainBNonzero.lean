/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainBInd
import LeanPool.RegtsSevenster.RS.Classical.Deligne.PowInduct

/-!
# Nonvanishing of the chain algebra unit

The unit of the splitting-chain algebra over the ind-category is
nonzero: the finite-stage detection reduces vanishing to a chain
unit stage, and the power zigzag induction keeps every stage
alive.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v

variable {C : Type v}

/-- **The unit of the splitting-chain algebra is nonzero**: for a
zigzag datum over the ind-category whose symmetric powers all
survive, the unit of the algebra does not vanish. -/
theorem chainBUnit_ne_zero
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    [CategoryTheory.Linear ℂ (Ind C)] [MonoidalLinear ℂ (Ind C)] (B : Ind C)
    [MonObj B] [IsCommMonObj B] (N : Mod (Ind C) B) (N' : Mod (Ind C) B)
    (d : ModDualityDatum B N N')
    (hz : ModZigzagDatum B d)
    (hS : ∀ n, ¬ IsZero (symPow B N.X (n + 1))) :
    chainBUnit B N N' d ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := (chainBUnit_eq_zero_iff B N N' d).mp h
  exact chainUnitStage_ne_zero_all B N N' d hz n (hS n) hn

end RS
