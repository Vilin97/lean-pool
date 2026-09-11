/-
Copyright (c) 2026 Vasily Ilin, Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Brian Nugent
-/
module

public import LeanPool.GrothendieckVanishing.GrothendieckVanishingOverview
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Continuity.Init
import Mathlib.Topology.Sheaves.Init

/-!
# Grothendieck's Vanishing Theorem

Source: doi:10.1007/978-1-4757-3849-0, url:https://github.com/Vilin97/Clawristotle/tree/grothendieck-vanishing
Authors: Vasily Ilin, Brian Nugent
Status: verified
Main declarations: `GrothendieckVanishing`
Tags: algebraic-geometry, sheaf-theory, topology
MSC: 14F06, 18F20
-/

@[expose] public section
