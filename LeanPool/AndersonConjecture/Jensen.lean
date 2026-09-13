/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
module

public import LeanPool.AndersonConjecture.Jensen.Adjoin
public import LeanPool.AndersonConjecture.Jensen.Application
public import LeanPool.AndersonConjecture.Jensen.Avoidance
public import LeanPool.AndersonConjecture.Jensen.CloseUp
public import LeanPool.AndersonConjecture.Jensen.CombinedStep
public import LeanPool.AndersonConjecture.Jensen.Construction
public import LeanPool.AndersonConjecture.Jensen.Defs
public import LeanPool.AndersonConjecture.Jensen.Jensen
public import LeanPool.AndersonConjecture.Jensen.KrullDomain
public import LeanPool.AndersonConjecture.Jensen.NSubring
public import LeanPool.AndersonConjecture.Jensen.TransfiniteUnion
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Complex.Order
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.EReal.Inv

/-!
# Jensen's Corollary 2.4: UFDs with Prescribed Completion

Index file for the `LeanPool.AndersonConjecture.Jensen` directory: constructing
a UFD with a prescribed completion (Jensen 2006, building on Loepp 1997 and
Heitmann 1993).
-/

@[expose] public section
