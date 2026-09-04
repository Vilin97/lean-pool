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

This file is the consumer-shaped INTERFACE: the definition and its transport/restriction
lemmas. Existence at every infinite cardinality (Marker: the order of an ordered field) is a
separate, deferred construction — the model-theoretic argument is developed conditionally on a
highly order-transitive `J`.
-/

namespace FirstOrder

/-- A linear order is **highly order-transitive** when every isomorphism between two finite
increasing tuples extends to an order automorphism: for all `n` and increasing `n`-tuples
`s, t`, some `e : J ≃o J` has `e (s i) = t i` for all `i`. -/
def HighlyOrderTransitive (J : Type*) [LinearOrder J] : Prop :=
  ∀ (n : ℕ) (s t : Fin n ↪o J), ∃ e : J ≃o J, ∀ i, e (s i) = t i

namespace HighlyOrderTransitive

variable {J J' : Type*} [LinearOrder J] [LinearOrder J']

/-- High order-transitivity transports along order isomorphisms. -/
theorem of_orderIso (f : J ≃o J') (hJ : HighlyOrderTransitive J) :
    HighlyOrderTransitive J' := by
  intro n s t
  obtain ⟨e, he⟩ := hJ n (s.trans f.symm.toOrderEmbedding) (t.trans f.symm.toOrderEmbedding)
  refine ⟨(f.symm.trans e).trans f, fun i => ?_⟩
  have h := he i
  show f (e (f.symm (s i))) = t i
  rw [show e (f.symm (s i)) = f.symm (t i) from h]
  exact f.apply_symm_apply (t i)

/-- The two-point instance consumed most often: any point moves to any other point. -/
theorem exists_map_point (hJ : HighlyOrderTransitive J) (x y : J) :
    ∃ e : J ≃o J, e x = y := by
  let emb : J → (Fin 1 ↪o J) := fun z =>
    ⟨⟨fun _ => z, fun a b _ => Subsingleton.elim a b⟩,
      fun {a b} => iff_of_true le_rfl (le_of_eq (Subsingleton.elim a b))⟩
  obtain ⟨e, he⟩ := hJ 1 (emb x) (emb y)
  exact ⟨e, he 0⟩

end HighlyOrderTransitive

end FirstOrder
