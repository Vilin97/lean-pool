/-
Copyright (c) 2026 crdt-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: crdt-lean contributors
-/
import LeanPool.CrdtLean.Crdt.Defs
import LeanPool.CrdtLean.Crdt.Convergence


/-!
# State-based CRDTs — liveness (the "Eventual" half of SEC)

`Crdt.Convergence` proves the **safety** half of Strong Eventual Consistency: replicas
that have delivered the *same set* of updates hold equal state. That theorem is silent
on whether the same set is ever actually delivered — it takes an already-delivered
`Finset`/`List`. This file supplies the missing **liveness** half.

You cannot prove a network delivers messages, so liveness is **conditional**: under an
explicit *fairness* assumption (every generated update eventually reaches every replica)
and *quiescence* (the set of generated updates is finite and fixed), every replica
eventually reaches — and thereafter holds — the join of all updates, and any two
replicas eventually agree. The fairness assumption is a hypothesis of `DeliverySystem`,
not something proved; that is the honest boundary between what Lean can certify and what
the network layer must guarantee.

The whole argument rests on one combinatorial lemma, `eventually_covers`: monotone
delivery plus "each element eventually arrives" forces "the whole finite set is
eventually present", by taking the max of finitely many arrival times.
-/

namespace Crdt

variable {S : Type*}

/-- **Core liveness lemma.** If a delivery history `d` is monotone in time and every
element of a finite set `s` is delivered at *some* time, then there is a *single* time
`T` by which the *entire* set `s` has been delivered. The proof inducts on `s`, taking
the max of the per-element arrival times. -/
theorem eventually_covers (d : ℕ → Finset S) (hmono : Monotone d) :
    ∀ s : Finset S, (∀ a ∈ s, ∃ t, a ∈ d t) → ∃ T, s ⊆ d T := by
  classical
  intro s
  induction s using Finset.induction with
  | empty => intro _; exact ⟨0, by simp⟩
  | @insert a s ha ih =>
    intro hfair
    obtain ⟨T₁, hT₁⟩ := ih (fun b hb => hfair b (Finset.mem_insert_of_mem hb))
    obtain ⟨ta, hta⟩ := hfair a (Finset.mem_insert_self a s)
    refine ⟨max T₁ ta, ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxs
    · exact hmono (le_max_right T₁ ta) hta
    · exact hmono (le_max_left T₁ ta) (hT₁ hxs)

variable [SemilatticeSup S] [OrderBot S] [DecidableEq S]

/-- A **delivery system**: a finite, fixed pool of generated update-states (quiescence)
gossiped to a family of replicas `ι`, where delivery is monotone, sound (no phantom
updates), and fair (every update eventually reaches every replica). The fairness field
is the honest network assumption: it is asserted, not derived. -/
structure DeliverySystem (ι : Type*) (S : Type*)
    [SemilatticeSup S] [OrderBot S] [DecidableEq S] where
  /-- All update-states ever generated. Finiteness encodes quiescence. -/
  allUpdates : Finset S
  /-- `delivered r t` = the set of update-states replica `r` has received by time `t`. -/
  delivered : ι → ℕ → Finset S
  /-- Delivery only ever accumulates: a replica never un-learns an update. -/
  mono : ∀ r, Monotone (delivered r)
  /-- No phantom updates: a replica only receives genuinely-generated states. -/
  sound : ∀ r t, delivered r t ⊆ allUpdates
  /-- **Fairness assumption.** Every generated update eventually reaches every replica. -/
  fair : ∀ r, ∀ a ∈ allUpdates, ∃ t, a ∈ delivered r t

variable {ι : Type*}

/-- **Per-replica convergence.** Under fairness + quiescence, each replica reaches the
full update set after some finite time and *stays* there: `delivered r t = allUpdates`
for all sufficiently large `t`. Soundness gives `⊆`, the liveness lemma gives `⊇`. -/
theorem DeliverySystem.converges (sys : DeliverySystem ι S) (r : ι) :
    ∃ T, ∀ t, T ≤ t → sys.delivered r t = sys.allUpdates := by
  obtain ⟨T, hT⟩ := eventually_covers (sys.delivered r) (sys.mono r) sys.allUpdates (sys.fair r)
  refine ⟨T, fun t hTt => Finset.Subset.antisymm (sys.sound r t) ?_⟩
  exact hT.trans (sys.mono r hTt)

/-- The quiescent converged value: the join of every generated update-state. -/
def DeliverySystem.convergedState (sys : DeliverySystem ι S) : S :=
  replicaState sys.allUpdates

/-- **Liveness: each replica reaches the converged state.** For all sufficiently large
`t`, a replica's observable state equals the join of all updates. -/
theorem DeliverySystem.reaches_converged (sys : DeliverySystem ι S) (r : ι) :
    ∃ T, ∀ t, T ≤ t → replicaState (sys.delivered r t) = sys.convergedState := by
  obtain ⟨T, hT⟩ := sys.converges r
  exact ⟨T, fun t hTt => by rw [hT t hTt, DeliverySystem.convergedState]⟩

/-- **Eventual agreement (the full SEC payoff).** Any two replicas eventually hold
identical state, forever after some finite time — combining the liveness lemma here with
the safety result `replicaState` is a function of the delivered set. Take the max of the
two convergence times. -/
theorem DeliverySystem.eventual_agreement (sys : DeliverySystem ι S) (r₁ r₂ : ι) :
    ∃ T, ∀ t, T ≤ t →
      replicaState (sys.delivered r₁ t) = replicaState (sys.delivered r₂ t) := by
  obtain ⟨T₁, h₁⟩ := sys.reaches_converged r₁
  obtain ⟨T₂, h₂⟩ := sys.reaches_converged r₂
  refine ⟨max T₁ T₂, fun t hTt => ?_⟩
  rw [h₁ t (le_of_max_le_left hTt), h₂ t (le_of_max_le_right hTt)]

end Crdt
