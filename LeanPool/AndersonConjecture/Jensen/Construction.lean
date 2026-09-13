/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
module

public import LeanPool.AndersonConjecture.Jensen.Construction.ChainHelpers
public import LeanPool.AndersonConjecture.Jensen.Construction.Construction
public import LeanPool.AndersonConjecture.Jensen.Construction.HeitmannProp
public import LeanPool.AndersonConjecture.Jensen.Construction.Transfinite
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Transfinite Construction of the Final Ring

Index file for the `LeanPool.AndersonConjecture.Jensen.Construction` directory:
the transfinite construction assembling the final ring.
-/

@[expose] public section
