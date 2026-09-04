/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Fin.Basic

/-!
# Highly order-transitive linear orders

The order-theoretic input of the countably-many-types project (issue #11, Marker Theorem 11.2):
a linear order is **highly order-transitive** when every isomorphism between two finite
increasing tuples extends to an order automorphism. Combined with the local EM equivariance
package (`Methods/LocalEMEquivariance.lean`), such automorphisms of the skeleton induce
structure automorphisms of the term model moving any increasing tuple of skeleton constants to
any other, which is what collapses tuple types to finitely describable orbit data.

This file supplies the consumer-shaped definition. Existence results via ordered fields are in
`HighlyTransitiveField.lean` and `HighlyTransitiveExistence.lean`.
-/

namespace FirstOrder

/-- A linear order is **highly order-transitive** when every isomorphism between two finite
increasing tuples extends to an order automorphism: for all `n` and increasing `n`-tuples
`s, t`, some `e : J ≃o J` has `e (s i) = t i` for all `i`. -/
def HighlyOrderTransitive (J : Type*) [LinearOrder J] : Prop :=
  ∀ (n : ℕ) (s t : Fin n ↪o J), ∃ e : J ≃o J, ∀ i, e (s i) = t i

end FirstOrder
