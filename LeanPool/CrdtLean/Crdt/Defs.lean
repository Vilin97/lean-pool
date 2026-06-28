/-
Copyright (c) 2026 crdt-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: crdt-lean contributors
-/
import Mathlib.Data.Finset.Lattice.Fold


/-!
# State-based CRDTs (CvRDTs) — definitions

A **state-based convergent replicated data type** (CvRDT) models a value that is
replicated across many nodes which gossip their full state. Each replica holds an
element of a **join-semilattice** `S` with a least element `⊥` (the initial state),
and the *merge* of two replicas is the join `⊔`.

The three Shapiro–Preguiça–Baquero–Zawirski conditions for a state-based CRDT are
that merge be **commutative, associative, and idempotent**. On a `SemilatticeSup`
these hold definitionally; we record them as named lemmas so downstream proofs and
the kernel API can cite them directly.

A replica's observable state after delivering a finite multiset of update-states is
the join of those states (`replicaState`). Convergence results live in
`Crdt.Convergence`.
-/

namespace Crdt

variable {S : Type*} [SemilatticeSup S]

/-- Merge of two replica states is the join. This is the CvRDT merge operator. -/
def merge (a b : S) : S := a ⊔ b

@[simp] theorem merge_def (a b : S) : merge a b = a ⊔ b := rfl

/-- CvRDT condition 1: merge is commutative. -/
theorem merge_comm (a b : S) : merge a b = merge b a := sup_comm a b

/-- CvRDT condition 2: merge is associative. -/
theorem merge_assoc (a b c : S) : merge (merge a b) c = merge a (merge b c) :=
  sup_assoc a b c

/-- CvRDT condition 3: merge is idempotent. -/
theorem merge_idem (a : S) : merge a a = a := sup_idem a

/-- Merge is *inflationary*: a replica never moves down the lattice when it merges
in another replica's state. This is what makes delivery monotone. -/
theorem le_merge_left (a b : S) : a ≤ merge a b := le_sup_left

theorem le_merge_right (a b : S) : b ≤ merge a b := le_sup_right

variable [OrderBot S]

/-- The initial state `⊥` is the identity for merge. -/
theorem merge_bot (a : S) : merge a ⊥ = a := sup_bot_eq a

/-- A replica's observable state after delivering the finite set `updates` of
update-states is the join of all delivered states. The empty delivery is `⊥`. -/
def replicaState (updates : Finset S) : S := updates.sup id

@[simp] theorem replicaState_empty : replicaState (∅ : Finset S) = ⊥ := by
  simp [replicaState]

@[simp] theorem replicaState_insert [DecidableEq S] (a : S) (u : Finset S) :
    replicaState (insert a u) = merge a (replicaState u) := by
  simp [replicaState, Finset.sup_insert]

end Crdt
