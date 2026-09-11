/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
module

public import LeanPool.AndersonConjecture.Jensen.CloseUp.AvoidanceStep
public import LeanPool.AndersonConjecture.Jensen.CloseUp.Base
public import LeanPool.AndersonConjecture.Jensen.CloseUp.CloseUp
public import LeanPool.AndersonConjecture.Jensen.CloseUp.CoprimeSplit
public import LeanPool.AndersonConjecture.Jensen.CloseUp.Factor
public import LeanPool.AndersonConjecture.Jensen.CloseUp.FactorDivisibility
public import LeanPool.AndersonConjecture.Jensen.CloseUp.GcdComplexity
public import LeanPool.AndersonConjecture.Jensen.CloseUp.IntersectionHelpers
public import LeanPool.AndersonConjecture.Jensen.CloseUp.IntersectionStep
public import LeanPool.AndersonConjecture.Jensen.CloseUp.NoCommonFactor
public import LeanPool.AndersonConjecture.Jensen.CloseUp.TwoGen
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Totient
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Closing Up Finitely Generated Ideals

Index file for the `LeanPool.AndersonConjecture.Jensen.CloseUp` directory:
closing up finitely generated ideals (Heitmann, Lemma 4).
-/

@[expose] public section
