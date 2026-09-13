/-
Copyright (c) 2026 Scott Harper, Peiran Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Harper, Peiran Wu
-/
module

public import LeanPool.OrderPQ.Basic
public import LeanPool.OrderPQ.IsCyclic
public import LeanPool.OrderPQ.Main
public import LeanPool.OrderPQ.MonoidHom
public import LeanPool.OrderPQ.MulZMod
public import LeanPool.OrderPQ.PrimeOrder
public import LeanPool.OrderPQ.SemidirectProduct
public import LeanPool.OrderPQ.TorsionBy
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Classification of groups of order p * q

Source: arxiv:2501.09769
Authors: Scott Harper, Peiran Wu
Status: verified
Main declarations: `OrderPQ.exists_card_eq_prime_mul_prime_and_not_isCyclic_iff`
Tags: group-theory, finite-groups, semidirect-products
MSC: 20D20, 20E22, 20D60
-/

@[expose] public section

/-!
## Provenance and scope

This project ports the classification of noncyclic finite groups of order `p * q`, including
the prime-square case and the semidirect-product normal form for the `p < q` case.
The mathematical source is Harper and Wu, "Classifying the groups of order p q in Lean",
arXiv:2501.09769.
-/
