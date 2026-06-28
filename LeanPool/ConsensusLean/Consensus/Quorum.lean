/-
Copyright (c) 2026 consensus-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: consensus-lean contributors
-/
import Mathlib.Data.Finset.Basic

/-!
# Single-decree consensus — quorum safety

This file proves the **safety core of distributed consensus**: the property that at most
one value is ever *chosen*, which is what distinguishes consensus (the CP problem solved
by Paxos/Raft) from convergence (the AP property of CRDTs). CRDTs converge precisely by
*avoiding* consensus; here we do the opposite, and the load-bearing fact is **quorum
intersection**.

## Model

A `QuorumSystem` over an acceptor type `α` is a family of acceptor subsets (`IsQuorum`)
with the single defining condition that **any two quorums intersect**. A run is a vote
assignment `vote : α → Option V`: each acceptor votes for at most one value (single-valued
because it is a function). A value `v` is **chosen** when some quorum has *every* member
voting `v`.

## What is proved

* `agreement` — if `v` and `v'` are both chosen, then `v = v'`. The heart of Paxos
  safety: two quorums share an acceptor, that acceptor voted a single value, so the two
  chosen values coincide.
* `quorum_nonempty` — every quorum is nonempty, falling straight out of self-intersection.
* `validity` — a chosen value was actually voted by some acceptor (no value is chosen from
  thin air).

The abstraction is deliberate: `agreement` needs *only* intersection, so it holds for
majority quorums, weighted quorums, grid quorums, or any other intersecting family. The
concrete majority instance lives in `Consensus.Majority`.
-/

namespace Consensus

variable {α V : Type*}

/-- A quorum system over acceptors `α`: a family of acceptor subsets, any two of which
intersect. Intersection is the *only* structural condition, and it is exactly what consensus safety
needs. -/
structure QuorumSystem (α : Type*) where
  /-- Which acceptor subsets count as quorums. -/
  IsQuorum : Finset α → Prop
  /-- The defining property: any two quorums share at least one acceptor. -/
  inter : ∀ Q₁ Q₂, IsQuorum Q₁ → IsQuorum Q₂ → ∃ a, a ∈ Q₁ ∧ a ∈ Q₂

/-- A value is **chosen** when some quorum has every member voting for it. -/
def Chosen (qs : QuorumSystem α) (vote : α → Option V) (v : V) : Prop :=
  ∃ Q, qs.IsQuorum Q ∧ ∀ a ∈ Q, vote a = some v

/-- **Every quorum is nonempty.** A quorum intersects itself, and `Q ∩ Q = Q`. -/
theorem quorum_nonempty (qs : QuorumSystem α) {Q : Finset α} (hQ : qs.IsQuorum Q) :
    Q.Nonempty := by
  obtain ⟨a, ha, _⟩ := qs.inter Q Q hQ hQ
  exact ⟨a, ha⟩

/-- **Consensus agreement (safety).** If two values are both chosen, they are equal. The
two chosen quorums share an acceptor by intersection; that acceptor's vote is a single
value, so the two chosen values coincide. -/
theorem agreement (qs : QuorumSystem α) (vote : α → Option V) {v v' : V}
    (h : Chosen qs vote v) (h' : Chosen qs vote v') : v = v' := by
  obtain ⟨Q, hQ, hv⟩ := h
  obtain ⟨Q', hQ', hv'⟩ := h'
  obtain ⟨a, ha, ha'⟩ := qs.inter Q Q' hQ hQ'
  have e1 : vote a = some v := hv a ha
  have e2 : vote a = some v' := hv' a ha'
  rw [e1] at e2
  exact Option.some.inj e2

/-- **Validity.** A chosen value was actually voted by some acceptor — nothing is chosen
that no one voted for. Uses that quorums are nonempty. -/
theorem validity (qs : QuorumSystem α) (vote : α → Option V) {v : V}
    (h : Chosen qs vote v) : ∃ a, vote a = some v := by
  obtain ⟨Q, hQ, hv⟩ := h
  obtain ⟨a, ha⟩ := quorum_nonempty qs hQ
  exact ⟨a, hv a ha⟩

end Consensus
