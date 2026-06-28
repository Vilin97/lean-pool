/-
Copyright (c) 2026 consensus-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: consensus-lean contributors
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Push
import LeanPool.ConsensusLean.Consensus.Quorum

/-!
# Majority quorums

The canonical quorum system: **strict-majority** sets over a finite acceptor population.
We prove the one thing required to be a `QuorumSystem` — that any two strict-majority sets
intersect — by a counting argument: if they were disjoint their sizes would sum to at most
the population, yet each exceeds half of it. Then consensus `agreement`, `validity`, and
quorum non-emptiness apply to majority consensus for free.
-/

namespace Consensus

variable {α : Type*} [Fintype α]

/-- A set is a strict-majority quorum when more than half the acceptors are in it. -/
def IsMajority (Q : Finset α) : Prop := 2 * Q.card > Fintype.card α

/-- **Any two strict-majority sets intersect.** If they were disjoint, their cardinalities
would sum to at most the population size, contradicting that each is more than half. -/
theorem majority_inter (Q₁ Q₂ : Finset α) (h₁ : IsMajority Q₁) (h₂ : IsMajority Q₂) :
    ∃ a, a ∈ Q₁ ∧ a ∈ Q₂ := by
  classical
  rw [IsMajority] at h₁ h₂
  by_contra hempty
  push Not at hempty
  have hdisj : Disjoint Q₁ Q₂ := by
    rw [Finset.disjoint_left]
    intro a ha₁ ha₂
    exact hempty a ha₁ ha₂
  have hsum : Q₁.card + Q₂.card ≤ Fintype.card α := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_univ _
  omega

/-- The majority quorum system over a finite acceptor population. -/
def majorityQuorums (α : Type*) [Fintype α] : QuorumSystem α where
  IsQuorum := IsMajority
  inter := majority_inter

/-- **Majority consensus agreement.** Under strict-majority quorums, at most one value is
ever chosen. -/
theorem majority_agreement {V : Type*} (vote : α → Option V) {v v' : V}
    (h : Chosen (majorityQuorums α) vote v) (h' : Chosen (majorityQuorums α) vote v') :
    v = v' :=
  agreement (majorityQuorums α) vote h h'

/-- **Majority consensus validity.** A chosen value was actually voted by some acceptor. -/
theorem majority_validity {V : Type*} (vote : α → Option V) {v : V}
    (h : Chosen (majorityQuorums α) vote v) : ∃ a, vote a = some v :=
  validity (majorityQuorums α) vote h

end Consensus
