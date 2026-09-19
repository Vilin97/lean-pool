/-
Copyright (c) 2026 Vasily Ilin, Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Brian Nugent
-/
module

public import LeanPool.GrothendieckVanishing.ClosedImmersion
public import LeanPool.GrothendieckVanishing.ZeroOutside
public import LeanPool.GrothendieckVanishing.GrothendieckVanishing

import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Continuity.Init
import Mathlib.Topology.Sheaves.Init

/-!
# Grothendieck's vanishing theorem

Umbrella module for the Hartshorne III, Theorem 2.7 formalization.

For a Noetherian topological space `X` of dimension `n` and a sheaf `F` of abelian groups
on `X`, the imports below assemble `Hⁱ(X, F) = 0` for all `i > n`.
-/

@[expose] public section
