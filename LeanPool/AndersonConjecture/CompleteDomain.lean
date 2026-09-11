/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
module

public import LeanPool.AndersonConjecture.CompleteDomain.CompleteDomain
public import LeanPool.AndersonConjecture.CompleteDomain.Domain
public import LeanPool.AndersonConjecture.CompleteDomain.LocalRing
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Complex.Order
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Nat.Totient

/-!
# Complete Local Domain `T = ℂ[[x,y,z]]/(x²-yz)`

Index file for the `LeanPool.AndersonConjecture.CompleteDomain` directory: the
ring `T = ℂ[[x,y,z]]/(x²-yz)` is a complete two-dimensional Cohen–Macaulay
local domain with a non-principal height-one prime.
-/

@[expose] public section
