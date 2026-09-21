/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Foundations.Parameters

/-!
# Rank invariance under linear equivalence

The dependency library proves that winnability is invariant under linear
equivalence.  This module lifts that statement through the universal tests in
the definition of divisor rank.
-/

namespace Utilities

/-- Every rank lower bound is preserved under linear equivalence. -/
theorem rank_geq_of_linear_equiv
    (G : CFGraph) {D E : CFDiv G} (hDE : linear_equiv G D E) (k : ℤ)
    (hRank : rank_geq G D k) :
    rank_geq G E k := by
  intro A hA
  apply winnable_equiv_winnable G (D - A) (E - A) (hRank A hA)
  unfold linear_equiv at hDE ⊢
  have hDifference :
      (E - A) - (D - A) = E - D := by
    abel
  rw [hDifference]
  exact hDE

/-- Linearly equivalent divisors have equal rank. -/
theorem rank_eq_of_linear_equiv
    (G : CFGraph) {D E : CFDiv G} (hDE : linear_equiv G D E) :
    rank G D = rank G E := by
  apply le_antisymm
  · apply (rank_geq_iff G E (rank G D)).mp
    apply rank_geq_of_linear_equiv G hDE
    exact (rank_geq_iff G D (rank G D)).mpr le_rfl
  · apply (rank_geq_iff G D (rank G E)).mp
    apply rank_geq_of_linear_equiv G hDE.symm
    exact (rank_geq_iff G E (rank G E)).mpr le_rfl

/-- Adding an effective divisor preserves every rank lower bound. -/
theorem rank_add_effective_ge
    (G : CFGraph) (D E : CFDiv G) (hEffective : effective E) (r : ℤ)
    (hRank : rank G D ≥ r) :
    rank G (D + E) ≥ r := by
  apply (rank_geq_iff G (D + E) r).mp
  have hRankGeq : rank_geq G D r :=
    (rank_geq_iff G D r).mpr hRank
  intro A hA
  have hWinnable := winnable_add_winnable G (D - A) E
    (hRankGeq A hA) (winnable_of_effective G E hEffective)
  convert hWinnable using 1
  abel

/-- A Brill--Noether witness can be padded with effective chips to any larger
exact degree without decreasing its target rank. -/
theorem BNExists_mono_degree
    {G : CFGraph} {r d d' : ℤ} (hDegree : d ≤ d')
    (hExists : BNExists G r d) :
    BNExists G r d' := by
  obtain ⟨D, hDDegree, hDRank⟩ := hExists
  let v : G.V := Classical.arbitrary G.V
  let E : CFDiv G := (d' - d).toNat • one_chip v
  have hDifference : 0 ≤ d' - d := by omega
  have hEEffective : effective E := by
    exact (Eff G).nsmul_mem (eff_one_chip v) (d' - d).toNat
  have hEDegree : deg E = d' - d := by
    dsimp [E]
    simpa [Int.toNat_of_nonneg hDifference] using
      (AddMonoidHom.map_nsmul deg (d' - d).toNat (one_chip v))
  refine ⟨D + E, ?_, rank_add_effective_ge G D E hEEffective r hDRank⟩
  rw [deg.map_add, hDDegree, hEDegree]
  ring

end Utilities
