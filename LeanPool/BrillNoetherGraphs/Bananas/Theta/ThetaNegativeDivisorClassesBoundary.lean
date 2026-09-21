/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaNegativeDivisorClasses

/-!
# Boundary negative divisor classes on theta graphs

This extends the class-valued bijection in Theorem 3.4 to the first genuine
boundary family: the first mark is the raw initial endpoint and the second is
an interior point at least two steps before the terminal endpoint.  The two
excluded terminal-near positions are precisely the all-submodular cases of
Corollary 3.6.
-/

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-- Every exceptional position gives a negative divisor when the first mark
is the raw initial endpoint. -/
theorem rankDelta_path_pair_neg_of_mem_thetaExceptionalPositions_zero_left
    (B : Banana 2) (alpha : Fin 3)
    (j k : B.PathPosition alpha)
    (hj : B.IsInteriorPosition alpha j)
    (hjFar : j.val + 1 < B.length alpha)
    (hkExceptional : k ∈ thetaExceptionalPositions B alpha
      ⟨0, by omega⟩ j) :
    rankDelta
      (mark B.graph (B.pathVertex alpha ⟨0, by omega⟩)
        (B.pathVertex alpha j))
      (one_chip (B.pathVertex alpha k) +
        one_chip (B.pathVertex alpha ⟨0, by omega⟩)) < 0 := by
  rcases hkExceptional with ⟨hkReflect, hkj, hkLower, _hkUpper⟩
  have hkNotEnd : k.val ≠ B.length alpha := by
    intro hkEnd
    apply hkReflect
    push_cast
    omega
  have hkjNat : k.val ≠ j.val := by
    intro h
    apply hkj
    exact_mod_cast h
  have hkLower' : (j.val : ℤ) ≤ (k.val : ℤ) := by
    convert hkLower using 1
    all_goals norm_num
  have hjk : j.val < k.val := by
    have : j.val ≤ k.val := by exact_mod_cast hkLower'
    omega
  have hkInterior : B.IsInteriorPosition alpha k := by
    change 0 < k.val ∧ k.val < B.length alpha
    have hkBound := k.isLt
    omega
  let D : CFDiv B.graph :=
    one_chip (B.pathVertex alpha k) +
      one_chip (B.pathVertex alpha ⟨0, by omega⟩)
  have hRankD : rank B.graph D = 0 := by
    dsimp [D]
    apply rank_same_strand_pair_zero_of_not_reflection_generic
      (by omega : 2 ≤ 2) B alpha k ⟨0, by omega⟩
    omega
  have hRankU : rank B.graph
      (D - one_chip (B.pathVertex alpha ⟨0, by omega⟩)) = 0 := by
    have hCancel : D - one_chip (B.pathVertex alpha ⟨0, by omega⟩) =
        one_chip (G := B.graph) (B.pathVertex alpha k) := by
      dsimp [D]
      abel_nf
    rw [hCancel]
    exact rank_one_chip_zero_banana_two B _
  have hRankV : rank B.graph
      (D - one_chip (B.pathVertex alpha j)) = 0 := by
    have hPrin := prin_subinterval_reflection (spec := B) (star := alpha)
      (lo := 0) (hi := k.val) (target := j.val) hj.1 hjk (by omega)
    let q : B.PathPosition alpha := ⟨k.val - j.val, by omega⟩
    have hEquiv : linear_equiv B.graph
        (one_chip (B.pathVertex alpha ⟨0, by omega⟩) +
          one_chip (B.pathVertex alpha k) - one_chip (B.pathVertex alpha j))
        (one_chip (B.pathVertex alpha q)) := by
      unfold linear_equiv
      apply (principal_iff_eq_prin B.graph _).mpr
      refine ⟨segScript B alpha 0 k.val j.val, ?_⟩
      rw [hPrin]
      dsimp [q]
      abel_nf
    have hRankEq := rank_eq_of_linear_equiv B.graph hEquiv
    rw [rank_one_chip_zero_banana_two] at hRankEq
    have hRewrite : D - one_chip (B.pathVertex alpha j) =
        one_chip (B.pathVertex alpha ⟨0, by omega⟩) +
          one_chip (B.pathVertex alpha k) - one_chip (B.pathVertex alpha j) := by
      dsimp [D]
      abel_nf
    rw [hRewrite]
    exact hRankEq
  have hRankUV : rank B.graph
      (D - one_chip (B.pathVertex alpha ⟨0, by omega⟩) -
        one_chip (B.pathVertex alpha j)) = -1 := by
    have hVertices : B.pathVertex alpha k ≠ B.pathVertex alpha j := by
      intro h
      apply hkjNat
      exact congrArg Fin.val (B.pathVertex_injective alpha h)
    have hRank := rank_one_chip_sub_one_chip_eq_neg_one_of_ne_banana
      B (B.pathVertex alpha k) (B.pathVertex alpha j) hVertices
    have hCancel :
        D - one_chip (B.pathVertex alpha ⟨0, by omega⟩) -
            one_chip (B.pathVertex alpha j) =
          one_chip (B.pathVertex alpha k) - one_chip (B.pathVertex alpha j) := by
      dsimp [D]
      abel_nf
    rw [hCancel]
    exact hRank
  exact (rankDelta_neg_iff_rank_zero_deletions
    (mark B.graph (B.pathVertex alpha ⟨0, by omega⟩)
      (B.pathVertex alpha j)) D hRankD).mpr
        ⟨hRankU, hRankV, hRankUV⟩

/-- Every negative divisor for the raw-initial/interior boundary marking has
the exceptional representative asserted in Theorem 3.4. -/
theorem negative_path_pair_has_exceptional_representative_zero_left
    (B : Banana 2) (alpha : Fin 3) (j : B.PathPosition alpha)
    (hj : B.IsInteriorPosition alpha j)
    (_hjFar : j.val + 1 < B.length alpha)
    (D : CFDiv B.graph)
    (hNeg : rankDelta
      (mark B.graph (B.pathVertex alpha ⟨0, by omega⟩)
        (B.pathVertex alpha j)) D < 0) :
    ∃ k : B.PathPosition alpha,
      k ∈ thetaExceptionalPositions B alpha ⟨0, by omega⟩ j ∧
      linear_equiv B.graph D
        (one_chip (B.pathVertex alpha k) +
          one_chip (B.pathVertex alpha ⟨0, by omega⟩)) := by
  let i : B.PathPosition alpha := ⟨0, by omega⟩
  have hij : i.val < j.val := by
    dsimp [i]
    exact hj.1
  obtain ⟨w, hwv, hPair, hSub, hPairEquiv⟩ :=
    theta_negative_path_pair_auxiliary_rank_data B alpha i j hij D hNeg
  have hWonStrand : ∃ k : B.PathPosition alpha, w = B.pathVertex alpha k := by
    rcases w with e | ⟨gamma, offset⟩
    · rcases coreVertex_eq_pathVertex_zero_or_length B alpha e with h | h
      · exact ⟨⟨0, by omega⟩, h⟩
      · exact ⟨⟨B.length alpha, by omega⟩, h⟩
    · let k : B.PathPosition gamma := ⟨offset.val + 1, by
        have hoff := offset.isLt
        have hlen := B.length_pos gamma
        omega⟩
      have hk : B.IsInteriorPosition gamma k := by
        change 0 < offset.val + 1 ∧ offset.val + 1 < B.length gamma
        have hoff := offset.isLt
        have hlen := B.length_pos gamma
        omega
      have hwPath : B.interiorVertex gamma offset = B.pathVertex gamma k := by
        rw [B.pathVertex_eq_interiorVertex gamma k hk]
        congr 1
      have hwDef : (Sum.inr ⟨gamma, offset⟩ : B.graph.V) =
          B.interiorVertex gamma offset := rfl
      rw [hwDef] at hSub
      by_cases hgamma : gamma = alpha
      · subst gamma
        exact ⟨k, hwPath⟩
      · have hCore : B.pathVertex alpha i =
            B.coreVertex (B.core.tail alpha) := by
          dsimp [i]
          exact B.pathVertex_zero alpha
        have hNotRank := rank_coreVertex_add_distinct_interior_path_marks_ne_zero
          B (B.core.tail alpha) gamma alpha k j hk hj hgamma
        exfalso
        apply hNotRank
        rw [← hwPath, ← hCore]
        simpa [add_comm] using hSub
  obtain ⟨k, hwk⟩ := hWonStrand
  have hPair' : rank B.graph
      (one_chip (B.pathVertex alpha i) + one_chip (B.pathVertex alpha k)) = 0 := by
    rw [← hwk]
    simpa [add_comm] using hPair
  have hSub' : rank B.graph
      (one_chip (B.pathVertex alpha i) + one_chip (B.pathVertex alpha k) -
        one_chip (B.pathVertex alpha j)) = 0 := by
    rw [← hwk]
    simpa [add_comm] using hSub
  obtain ⟨hkReflect, hkLower, hkUpper⟩ :=
    same_strand_pair_sub_zero_forces_interval_general
      B alpha i j k hij hPair' hSub'
  have hkj : k.val ≠ j.val := by
    intro h
    apply hwv
    rw [hwk]
    exact congrArg (B.pathVertex alpha) (Fin.ext h)
  have hkExceptional : k ∈ thetaExceptionalPositions B alpha i j := by
    change (k.val : ℤ) ≠ (B.length alpha : ℤ) - (i.val : ℤ) ∧
      (k.val : ℤ) ≠ (j.val : ℤ) ∧
      (j.val : ℤ) - (i.val : ℤ) ≤ (k.val : ℤ) ∧
      (k.val : ℤ) ≤
        (j.val : ℤ) - (i.val : ℤ) + (B.length alpha : ℤ)
    constructor
    · intro h
      apply hkReflect
      omega
    constructor
    · intro h
      apply hkj
      omega
    constructor <;> omega
  have hWChip : one_chip w =
      (one_chip (B.pathVertex alpha k) : CFDiv B.graph) :=
    congrArg (one_chip (G := B.graph)) hwk
  have hPairEquiv' : linear_equiv B.graph D
      (one_chip (B.pathVertex alpha k) + one_chip (B.pathVertex alpha i)) := by
    simpa only [hWChip] using hPairEquiv
  exact ⟨k, hkExceptional, hPairEquiv'⟩

/-- **Theorem 3.4, class-valued bijection, raw initial-endpoint branch.** -/
theorem thetaPairDivisorClass_bijOn_negative_zero_left
    (B : Banana 2) (alpha : Fin 3) (j : B.PathPosition alpha)
    (hj : B.IsInteriorPosition alpha j)
    (hjFar : j.val + 1 < B.length alpha) :
    Set.BijOn (thetaPairDivisorClass B alpha ⟨0, by omega⟩)
      (thetaExceptionalPositions B alpha ⟨0, by omega⟩ j)
      (negativeRankDeltaClasses
        (mark B.graph (B.pathVertex alpha ⟨0, by omega⟩)
          (B.pathVertex alpha j))) := by
  refine ⟨?_, (thetaPairDivisorClass_injective B alpha
    ⟨0, by omega⟩).injOn, ?_⟩
  · intro k hk
    refine ⟨one_chip (B.pathVertex alpha k) +
      one_chip (B.pathVertex alpha ⟨0, by omega⟩), rfl, ?_⟩
    exact rankDelta_path_pair_neg_of_mem_thetaExceptionalPositions_zero_left
      B alpha j k hj hjFar hk
  · intro c hc
    obtain ⟨D, hClassD, hNeg⟩ := hc
    obtain ⟨k, hkExceptional, hPairEquiv⟩ :=
      negative_path_pair_has_exceptional_representative_zero_left
        B alpha j hj hjFar D hNeg
    refine ⟨k, hkExceptional, ?_⟩
    unfold thetaPairDivisorClass
    rw [← hClassD]
    exact (divisorClass_eq_iff_linearEquiv B.graph _ _).mpr hPairEquiv.symm

end Bananas
