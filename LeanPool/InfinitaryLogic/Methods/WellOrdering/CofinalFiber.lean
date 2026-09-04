/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.Cardinal.Regular

/-!
# The `ω₁` cofinal-fiber engine (issue #12, risky engine 1)

**A countable partition of `ω₁` has an unbounded fiber**: any assignment of countably many
labels to the countable ordinals takes some label unboundedly often below `ω₁`.

This is the single reusable pigeonhole behind *every* branching closure field of the
well-ordering consistency property — implication branching, positive disjunctions, and
negated conjunctions alike (audit v2, C4 engine): each `α < ω₁` chooses a branch, some branch
recurs unboundedly, and downward closure of the gap witness (`GapWitness.mono`) upgrades
"unboundedly many `α`" to "all `α`".

Proof: if every fiber were bounded, the supremum of countably many bounds would bound all of
`ω₁` — contradicting the regularity of `ℵ₁` (via `Ordinal.iSup_lt_omega_one`).
-/

namespace FirstOrder.Language

open Cardinal Ordinal

/-- **The cofinal-fiber lemma**: a countably-labelled assignment on the ordinals takes some
label unboundedly often below `ω₁ = (Cardinal.aleph 1).ord`. -/
theorem exists_unbounded_fiber {ι : Type} [Countable ι] [Nonempty ι]
    (f : Ordinal.{0} → ι) :
    ∃ i : ι, ∀ β : Ordinal.{0}, β < (Cardinal.aleph 1).ord →
      ∃ α : Ordinal.{0}, β ≤ α ∧ α < (Cardinal.aleph 1).ord ∧ f α = i := by
  simp only [Cardinal.ord_aleph]
  by_contra hcon
  push Not at hcon
  -- each label `i` has a bound `bnd i < ω₁` beyond which the fiber of `i` is empty
  choose bnd hbnd hmiss using hcon
  -- the countable supremum of the bounds stays below `ω₁`
  have hsup : (⨆ i, bnd i) < ω₁ := Ordinal.iSup_lt_omega_one hbnd
  -- one step past the supremum still lies below the limit ordinal `ω₁`
  have hlim : Order.IsSuccLimit (ω₁ : Ordinal.{0}) := by
    rw [← Cardinal.ord_aleph]
    exact Cardinal.isSuccLimit_ord (le_of_lt Cardinal.aleph0_lt_aleph_one)
  have hαlt : (⨆ i, bnd i) + 1 < ω₁ := hlim.add_one_lt hsup
  -- but that ordinal lies beyond the bound of its own label
  exact hmiss (f ((⨆ i, bnd i) + 1)) _
    (le_trans (Ordinal.le_iSup bnd _) (le_of_lt (lt_add_one _))) hαlt rfl

end FirstOrder.Language
