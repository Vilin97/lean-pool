/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import Mathlib.Data.Finset.Basic

/-!
# A choice-free `Finset` prelude

One of the project's goals (Goal 3) is to certify that the *information-system*
presentation of Scott domains can be developed in a **purely constructive**
fragment of
Lean: every result must have a `#print axioms` footprint contained in
`[propext, Quot.sound]`, with **no `Classical.choice`** and no use of the law of
excluded
middle.

This is harder than it looks, because several of mathlib's `Finset` *operations*
and even
a few basic *lemmas* transitively depend on `Classical.choice` (through the
`Multiset.dedup` / quotient machinery), in version `v4.30.0`:

* tainted operations: `(· ∪ ·)`, `Finset.image`, `(· ×ˢ ·)`, `Finset.biUnion`, `(·
\ ·)`;
* tainted lemmas: e.g. `Finset.insert_comm`;
* tainted *tactics*: `tauto`, `aesop` (they close goals via classical reasoning).

By contrast the following are choice-free and form our working toolkit: `insert`,
`(· ∩ ·)`, `Finset.filter`, `Finset.fold`, `Multiset.foldr`, the membership/subset
lemmas
(`Finset.mem_insert`, `Finset.mem_singleton`, `Finset.subset_iff`,
`Finset.mem_coe`,
`Finset.coe_subset`, `Finset.mem_inter`, `Finset.ext`), set-level
unions/intersections,
and explicit term-mode/`rintro`/`constructor` proofs.

This file provides the one finite-set operation the development needs but mathlib
only
offers in choice-tainted form: a **binary union of `Finset`s**, built choice-free
by
folding `insert`. Every declaration here is audited to depend only on
`[propext, Quot.sound]`.
-/

namespace Domain.Constructive

variable {α : Type*} [DecidableEq α]

/-- Choice-free commutativity of `insert` (mathlib's `Finset.insert_comm` is
choice-tainted).
Needed to fold `insert` over a `Multiset`. -/
theorem insert_comm' (a b : α) (s : Finset α) :
    insert a (insert b s) = insert b (insert a s) := by
  ext x
  simp only [Finset.mem_insert]
  constructor
  · rintro (h | h | h)
    exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)]
  · rintro (h | h | h)
    exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)]

instance : LeftCommutative (insert : α → Finset α → Finset α) := ⟨insert_comm'⟩

/-- Choice-free binary union of finite sets, obtained by folding `insert` over the
second
argument's underlying multiset. Definitionally equal in content to `u ∪ v`, but —
unlike
mathlib's `(· ∪ ·)` — free of any `Classical.choice` dependency. -/
def funion (u v : Finset α) : Finset α := Multiset.foldr insert u v.1

@[inherit_doc] infixl:65 " ∪' " => funion

theorem mem_foldr_insert (a : α) (u : Finset α) (s : Multiset α) :
    a ∈ Multiset.foldr insert u s ↔ a ∈ u ∨ a ∈ s := by
  refine Multiset.induction_on s ?_ ?_
  · simp
  · intro b t ih
    simp only [Multiset.foldr_cons, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (h | h | h)
      exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)]
    · rintro (h | h | h)
      exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)]

@[simp] theorem mem_funion {a : α} {u v : Finset α} :
    a ∈ u ∪' v ↔ a ∈ u ∨ a ∈ v := mem_foldr_insert a u v.1

/-- The coercion of `u ∪' v` to a `Set` is the (choice-free) set union of the
coercions. -/
theorem coe_funion (u v : Finset α) :
    (↑(u ∪' v) : Set α) = (↑u : Set α) ∪ ↑v := by
  ext x
  simp only [Set.mem_union, Finset.mem_coe, mem_funion]

theorem subset_funion_left (u v : Finset α) : u ⊆ u ∪' v := fun _ hx => mem_funion.2 (Or.inl hx)

theorem subset_funion_right (u v : Finset α) : v ⊆ u ∪' v := fun _ hx => mem_funion.2 (Or.inr hx)

/-- Universal property of the union: `u ∪' v ⊆ w` iff both `u ⊆ w` and `v ⊆ w`. -/
theorem funion_subset_iff {u v w : Finset α} : u ∪' v ⊆ w ↔ u ⊆ w ∧ v ⊆ w := by
  constructor
  · intro h
    exact ⟨fun x hx => h (subset_funion_left u v hx),
           fun x hx => h (subset_funion_right u v hx)⟩
  · rintro ⟨hu, hv⟩ x hx
    rcases mem_funion.1 hx with h | h
    exacts [hu h, hv h]

end Domain.Constructive
