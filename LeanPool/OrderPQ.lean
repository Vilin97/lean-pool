/-
Copyright (c) 2026 Scott Harper, Peiran Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Harper, Peiran Wu
-/

import LeanPool.OrderPQ.Basic
import LeanPool.OrderPQ.IsCyclic
import LeanPool.OrderPQ.Main
import LeanPool.OrderPQ.MonoidHom
import LeanPool.OrderPQ.MulZMod
import LeanPool.OrderPQ.PrimeOrder
import LeanPool.OrderPQ.SemidirectProduct
import LeanPool.OrderPQ.TorsionBy

/-!
# Classification of groups of order p * q

Source: arxiv:2501.09769
Authors: Scott Harper, Peiran Wu
Status: verified
Main declarations: `OrderPQ.exists_card_eq_prime_mul_prime_and_not_isCyclic_iff`
Tags: group-theory, finite-groups, semidirect-products
MSC: 20D20, 20E22, 20D60
-/

/-!
## Provenance and scope

This project ports the classification of noncyclic finite groups of order `p * q`, including
the prime-square case and the semidirect-product normal form for the `p < q` case.
The mathematical source is Harper and Wu, "Classifying the groups of order p q in Lean",
arXiv:2501.09769.
-/
