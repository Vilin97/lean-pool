/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Transmission.RankZeroWitness
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankChipStep

/-!
# Support complexes of rank-zero divisors

The paper calls the vertices reachable by one chip from a divisor its support
complex.  Here it is expressed directly with the existing rank API.  The main
criterion is Lemma 3.1(2) of the paper, stated without choosing an effective
representative.
-/

namespace Bananas

open Utilities

/-- The support complex of `D`: vertices whose one-chip deletion is still
winnable (equivalently, has nonnegative rank). -/
def rankSupport (G : CFGraph) (D : CFDiv G) : Set G.V :=
  {x | 0 ≤ rank G (D - one_chip x)}

@[simp] theorem mem_rankSupport_iff (G : CFGraph) (D : CFDiv G) (x : G.V) :
    x ∈ rankSupport G D ↔ 0 ≤ rank G (D - one_chip x) := Iff.rfl

/-- Removing one chip cannot increase rank. -/
theorem rank_sub_one_chip_le_rank
    (G : CFGraph) (D : CFDiv G) (q : G.V) :
    rank G (D - one_chip q) ≤ rank G D := by
  by_contra hNot
  have hLower : rank G (D - one_chip q) ≥ rank G D + 1 := by omega
  have hAdded : rank G ((D - one_chip q) + one_chip q) ≥ rank G D + 1 :=
    rank_add_one_chip_ge (D - one_chip q) q (rank G D + 1) hLower
  have hSame : (D - one_chip q) + one_chip q = D := by abel
  rw [hSame] at hAdded
  omega

/-- For a rank-zero divisor, its support is precisely the set of vertices
whose deletion has rank zero. -/
theorem mem_rankSupport_iff_rank_eq_zero_of_rank_zero
    (G : CFGraph) (D : CFDiv G) (hD : rank G D = 0) (x : G.V) :
    x ∈ rankSupport G D ↔ rank G (D - one_chip x) = 0 := by
  rw [mem_rankSupport_iff]
  constructor
  · intro hNonneg
    have hUpper := rank_sub_one_chip_le_rank G D x
    omega
  · intro hZero
    omega

/-- **Rank-zero support criterion** (paper Lemma 3.1(2)).  At rank zero a
negative marked second difference is exactly the assertion that each mark is
reachable from `D`, but not after deleting the other mark. -/
theorem rankDelta_neg_iff_rankSupport_pattern
    (M : TwiceMarked) (D : CFDiv M.graph) (hD : rank M.graph D = 0) :
    rankDelta M D < 0 ↔
      (M.v ∈ rankSupport M.graph D ∧
        M.v ∉ rankSupport M.graph (D - one_chip M.u)) ∧
      (M.u ∈ rankSupport M.graph D ∧
        M.u ∉ rankSupport M.graph (D - one_chip M.v)) := by
  constructor
  · intro hNeg
    obtain ⟨hU, hV, hUV⟩ :=
      (rankDelta_neg_iff_rank_zero_deletions M D hD).mp hNeg
    constructor
    · refine ⟨(mem_rankSupport_iff_rank_eq_zero_of_rank_zero M.graph D hD M.v).mpr hV, ?_⟩
      intro hMem
      have hNonneg : 0 ≤ rank M.graph
          (D - one_chip M.u - one_chip M.v) := by
        simpa [rankSupport, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hMem
      omega
    · refine ⟨(mem_rankSupport_iff_rank_eq_zero_of_rank_zero M.graph D hD M.u).mpr hU, ?_⟩
      intro hMem
      have hNonneg : 0 ≤ rank M.graph
          (D - one_chip M.u - one_chip M.v) := by
        simpa [rankSupport, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hMem
      omega
  · rintro ⟨⟨hVD, hVNot⟩, ⟨hUD, _hUNot⟩⟩
    have hV : rank M.graph (D - one_chip M.v) = 0 :=
      (mem_rankSupport_iff_rank_eq_zero_of_rank_zero M.graph D hD M.v).mp hVD
    have hU : rank M.graph (D - one_chip M.u) = 0 :=
      (mem_rankSupport_iff_rank_eq_zero_of_rank_zero M.graph D hD M.u).mp hUD
    have hUVNot : ¬ 0 ≤ rank M.graph
        (D - one_chip M.u - one_chip M.v) := by
      intro hNonneg
      apply hVNot
      simpa [rankSupport, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hNonneg
    have hUVLower := rank_geq_neg_one M.graph
      (D - one_chip M.u - one_chip M.v)
    have hUV : rank M.graph (D - one_chip M.u - one_chip M.v) = -1 := by
      omega
    exact (rankDelta_neg_iff_rank_zero_deletions M D hD).mpr ⟨hU, hV, hUV⟩

end Bananas
