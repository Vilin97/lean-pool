/-
Copyright (c) 2026 consensus-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: consensus-lean contributors
-/
import LeanPool.ConsensusLean.Consensus.Quorum
import LeanPool.ConsensusLean.Consensus.Majority

/-!
# Safe reconfiguration — agreement across changing membership

`Consensus.Quorum` proves agreement *within one fixed configuration*. But a live system's
membership and quorum rules change over time: agents join, leave, the roster rotates. The
danger is **split-brain across a reconfiguration** — two configurations whose quorums do
not overlap can each independently "choose" a different value, breaking agreement even
though each configuration is internally safe.

This file proves the condition that makes reconfiguration safe: **compatibility**, i.e.
every quorum of one configuration intersects every quorum of the other. Under
compatibility, agreement is preserved *across* the change. A `Transition` bundles two
configurations with the compatibility witness, so the seal admits a membership change only
when overlap is proven — the "constitution amendment" discipline: you may change the
guest list, but only via a process the old list overlaps and ratifies.

## Honest boundary

We model votes as a single per-acceptor assignment `vote : α → Option V` shared across
configurations — i.e. an acceptor never votes for two different values, *across epochs
included*. That single-vote discipline is exactly what a real reconfiguration protocol
(Vertical Paxos, Raft joint-consensus) must *enforce over time* by carrying chosen values
forward; here it is assumed, not derived. What is certified is the structural heart:
**compatible configurations cannot disagree.** Transitive safety across a long history
still requires either all-pairs compatibility (proved here) or per-step value
carry-forward (the protocol layer, not modelled).
-/

namespace Consensus

variable {α V : Type*}

/-- Two configurations are **compatible** when every quorum of one intersects every quorum
of the other. This is the cross-configuration intersection condition that makes a
reconfiguration from `c` to `d` safe. -/
def Compatible (c d : QuorumSystem α) : Prop :=
  ∀ Q₁ Q₂, c.IsQuorum Q₁ → d.IsQuorum Q₂ → ∃ a, a ∈ Q₁ ∧ a ∈ Q₂

/-- Compatibility is symmetric. -/
theorem Compatible.symm {c d : QuorumSystem α} (h : Compatible c d) : Compatible d c := by
  intro Q₁ Q₂ h₁ h₂
  obtain ⟨a, ha₁, ha₂⟩ := h Q₂ Q₁ h₂ h₁
  exact ⟨a, ha₂, ha₁⟩

/-- Every configuration is compatible with itself through its own intersection condition. So
within-configuration agreement is the `c = d` case of `agreement_cross`. -/
theorem Compatible.self (c : QuorumSystem α) : Compatible c c := c.inter

/-- **Cross-configuration agreement.** If `v` is chosen in configuration `c` and `v'` in a
compatible configuration `d` (under the same single-vote-per-acceptor assignment), then
`v = v'`. A shared acceptor exists by compatibility; its vote is one value; so the two
chosen values coincide. Reconfiguration preserves agreement exactly when the
configurations are compatible. -/
theorem agreement_cross (c d : QuorumSystem α) (hcd : Compatible c d)
    (vote : α → Option V) {v v' : V}
    (h : Chosen c vote v) (h' : Chosen d vote v') : v = v' := by
  obtain ⟨Q, hQ, hv⟩ := h
  obtain ⟨Q', hQ', hv'⟩ := h'
  obtain ⟨a, ha, ha'⟩ := hcd Q Q' hQ hQ'
  have e1 : vote a = some v := hv a ha
  have e2 : vote a = some v' := hv' a ha'
  rw [e1] at e2
  exact Option.some.inj e2

/-- A **reconfiguration step** from configuration `before` to `after`, carrying the proof
that the two are compatible (their quorums intersect). The seal admits a transition only
with this witness in hand: the constitution may be amended, but only by an overlapping,
ratified process. -/
structure Transition (α : Type*) where
  /-- The configuration in force before the change. -/
  before : QuorumSystem α
  /-- The configuration in force after the change. -/
  after : QuorumSystem α
  /-- The overlap witness: the two configurations are compatible. -/
  compatible : Compatible before after

/-- **A safe transition preserves agreement.** A value chosen under the old configuration
and a value chosen under the new configuration must agree. -/
theorem Transition.agreement_preserved (t : Transition α) (vote : α → Option V) {v v' : V}
    (h : Chosen t.before vote v) (h' : Chosen t.after vote v') : v = v' :=
  agreement_cross t.before t.after t.compatible vote h h'

/-- **Agreement across an entire reconfiguration history.** Given a timeline of
configurations `configs : ℕ → QuorumSystem α` that are pairwise compatible, a value chosen
in any epoch `i` agrees with a value chosen in any epoch `j`. The system can reconfigure
arbitrarily many times without ever admitting two conflicting decisions, provided every
pair of configurations overlaps. -/
theorem agreement_history (configs : ℕ → QuorumSystem α)
    (hcompat : ∀ i j, Compatible (configs i) (configs j))
    (vote : α → Option V) {i j : ℕ} {v v' : V}
    (h : Chosen (configs i) vote v) (h' : Chosen (configs j) vote v') : v = v' :=
  agreement_cross (configs i) (configs j) (hcompat i j) vote h h'

end Consensus

namespace Consensus

variable {α : Type*} [Fintype α]

/-- The majority configuration over a fixed acceptor population is self-compatible: any two
of its majority quorums intersect (this is just `majority_inter`). Cross-population
majority compatibility (different member sets) needs an explicit overlap bound on the
shared acceptors and is left to the protocol layer. -/
theorem majority_self_compatible : Compatible (majorityQuorums α) (majorityQuorums α) :=
  (majorityQuorums α).inter

end Consensus
