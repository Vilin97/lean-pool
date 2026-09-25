/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.StrongSeparator
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankOne
import Mathlib.Tactic

/-!
# Atanasov--Ranganathan rank-one reductions

This file records the non-metric logical core of Lemma 4.1 in
Atanasov--Ranganathan.  For an effective divisor, vertices in its support are
automatic rank-one tests.  Consequently Dhar calculations are needed only at
vertices outside the support.  Their seven pictured configurations are local
ways to establish precisely the remaining `Reaches` hypotheses below.
-/

namespace AtanasovRanganathan

open Utilities

open Certificate

variable {G : CFGraph}

/-- Formal core of the genus-four configuration lemma: an effective divisor
has rank at least one if it reaches every vertex where it has no chip. -/
theorem rank_ge_one_of_reaches_off_support
    (D : CFDiv G) (hEffective : effective D)
    (hOffSupport : ∀ vertex : G.V, D vertex = 0 →
      StrongSeparator.Reaches G D vertex) :
    rank G D ≥ 1 := by
  rw [rank_ge_one_iff_winnable_sub_one_chip]
  intro vertex
  by_cases hChip : 1 ≤ D vertex
  · apply winnable_of_effective
    intro other
    by_cases hOther : other = vertex
    · subst other
      simp only [Pi.sub_apply, oneChip, ↓reduceIte, Int.sub_nonneg]
      omega
    · simpa [oneChip, hOther] using hEffective other
  · have hZero : D vertex = 0 := by
      have := hEffective vertex
      omega
    exact hOffSupport vertex hZero

/-- Degree bookkeeping wrapper for an arbitrary rank-one pencil.  This is the
form needed both for the genus-four `g^1_3` and the genus-five `g^1_4` in the
Atanasov--Ranganathan argument. -/
theorem bnExists_one_of_reaches_off_support
    (D : CFDiv G) (hEffective : effective D) {degree : ℤ}
    (hDegree : deg D = degree)
    (hOffSupport : ∀ vertex : G.V, D vertex = 0 →
      StrongSeparator.Reaches G D vertex) :
    BNExists G 1 degree :=
  ⟨D, hDegree,
    rank_ge_one_of_reaches_off_support D hEffective hOffSupport⟩

/-- Genus-four specialization retained under its original name for existing
configuration proofs. -/
theorem bnExists_one_three_of_reaches_off_support
    (D : CFDiv G) (hEffective : effective D) (hDegree : deg D = 3)
    (hOffSupport : ∀ vertex : G.V, D vertex = 0 →
      StrongSeparator.Reaches G D vertex) :
    BNExists G 1 3 :=
  bnExists_one_of_reaches_off_support D hEffective hDegree hOffSupport

end AtanasovRanganathan
