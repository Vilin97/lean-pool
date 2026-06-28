/-
Copyright (c) 2026 crdt-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: crdt-lean contributors
-/
import LeanPool.CrdtLean.Crdt.Defs


/-!
# State-based CRDTs — convergence (Strong Eventual Consistency)

This file proves the headline guarantee for a state-based CRDT: **Strong Eventual
Consistency (SEC)**. Two replicas that have *delivered the same set of updates*
hold *identical state*, no matter the order in which the updates arrived or how
many times each was redelivered.

We model "applying a stream of update-states in some order" as a left/right fold of
`merge` over a `List S`, starting from the initial state `⊥`. The bridge lemma
`fold_merge_eq_replicaState` collapses any such fold to `replicaState l.toFinset`,
which depends only on the *set* of states delivered. SEC is then immediate.

We also record the lattice-theoretic content that justifies calling `replicaState`
"the" converged value: it is the **least upper bound** of the delivered states, it is
**monotone** in the delivered set, and merging two replicas equals the replica of the
union of their deliveries (the gossip step).
-/

namespace Crdt

variable {S : Type*} [SemilatticeSup S] [OrderBot S] [DecidableEq S]

/-- Folding `merge` over a delivery stream collapses to the join over the *set* of
delivered states. Order and multiplicity are quotiented away by associativity,
commutativity and idempotence of the join. -/
theorem fold_merge_eq_replicaState (l : List S) :
    l.foldr merge ⊥ = replicaState l.toFinset := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldr_cons, List.toFinset_cons, replicaState_insert, ih]

/-- **Strong Eventual Consistency.** If two replicas have delivered the same *set* of
update-states, their folded states are equal — independent of delivery order and of
how many times any update was redelivered. -/
theorem strong_eventual_consistency (l₁ l₂ : List S)
    (h : l₁.toFinset = l₂.toFinset) :
    l₁.foldr merge ⊥ = l₂.foldr merge ⊥ := by
  rw [fold_merge_eq_replicaState, fold_merge_eq_replicaState, h]

/-- Redelivering an already-delivered update is a no-op: idempotence at the set level. -/
theorem replicaState_redeliver (a : S) (u : Finset S) (ha : a ∈ u) :
    replicaState (insert a u) = replicaState u := by
  rw [Finset.insert_eq_self.mpr ha]

omit [DecidableEq S] in
/-- The converged state dominates every delivered update-state. -/
theorem le_replicaState {u : Finset S} {a : S} (ha : a ∈ u) :
    a ≤ replicaState u :=
  Finset.le_sup (f := id) ha

omit [DecidableEq S] in
/-- The converged state is the *least* upper bound: any state above all delivered
updates is above the merge. Together with `le_replicaState` this pins `replicaState`
as the join (LUB) of the delivered set. -/
theorem replicaState_le {u : Finset S} {b : S} (hb : ∀ a ∈ u, a ≤ b) :
    replicaState u ≤ b :=
  Finset.sup_le hb

omit [DecidableEq S] in
/-- Delivery is monotone: receiving more updates only moves a replica up the lattice. -/
theorem replicaState_mono {u v : Finset S} (h : u ⊆ v) :
    replicaState u ≤ replicaState v :=
  Finset.sup_mono h

/-- **Gossip step.** Merging two replicas equals the replica that has delivered the
union of both deliveries. This is why pairwise gossip converges the whole network. -/
theorem merge_replicaState (u v : Finset S) :
    merge (replicaState u) (replicaState v) = replicaState (u ∪ v) := by
  rw [merge_def, replicaState, replicaState, replicaState, Finset.sup_union]

/-- Network-level convergence: once two replicas have each delivered the union of all
updates (the gossip fixpoint), they hold identical state. Immediate from `merge_idem`
applied through `merge_replicaState`, but stated explicitly as the kernel guarantee. -/
theorem converged_states_agree (u v : Finset S) :
    replicaState (u ∪ v) = replicaState (v ∪ u) := by
  rw [Finset.union_comm]

end Crdt
