/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Basic
public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Ordinal
public import Mathlib.SetTheory.Ordinal.Family
public import Mathlib.Logic.Small.Defs

/-!
# The size of surreal numbers

The surreal numbers with option sets in universe `u` do not admit an equivalent type in universe
`u`. They contain an injective image of all ordinals in that universe. This certifies the size of
the values, not merely the size of their representations.

This result is relative to the option-set universe. It does not construct a set-theoretic class
model or identify models across universe levels.
-/

universe u

public section

namespace Surreal

/-- Surreal numbers with option sets in universe `u` are not `u`-small. -/
theorem not_small : ¬Small.{u} Surreal.{u} := by
  intro h
  let : Small.{u} Surreal.{u} := h
  exact not_injective_of_ordinal (fun o : Ordinal.{u} ↦ (NatOrdinal.of o).toSurreal)
    (NatOrdinal.toSurreal.injective.comp NatOrdinal.of.injective)

end Surreal
