/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaNegativeDivisorClassesBoundary

/-!
# Terminal-endpoint negative divisor classes on theta graphs

This is the reflected boundary family complementary to
`thetaPairDivisorClass_bijOn_negative_zero_left`: the second mark is the raw
terminal endpoint and the first is an interior point at least two steps from
the initial endpoint.
-/

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-- Every exceptional position gives a negative divisor when the second mark
is the raw terminal endpoint. -/
theorem rankDelta_path_pair_neg_of_mem_thetaExceptionalPositions_terminal_right
    (B : Banana 2) (alpha : Fin 3)
    (i k : B.PathPosition alpha)
    (hi : B.IsInteriorPosition alpha i)
    (hiFar : 1 < i.val)
    (hkExceptional : k ∈ thetaExceptionalPositions B alpha i
      ⟨B.length alpha, by omega⟩) :
    rankDelta
      (mark B.graph (B.pathVertex alpha i)
        (B.pathVertex alpha ⟨B.length alpha, by omega⟩))
      (one_chip (B.pathVertex alpha k) +
        one_chip (B.pathVertex alpha i)) < 0 := by
  rcases hkExceptional with ⟨hkReflect, hkj, hkLower, _hkUpper⟩
  have hkNotZero : k.val ≠ 0 := by
    intro hkZero
    dsimp at hkLower
    omega
  have hkNotTerminal : k.val ≠ B.length alpha := by
    intro h
    apply hkj
    dsimp
    exact_mod_cast h
  have hkInterior : B.IsInteriorPosition alpha k := by
    change 0 < k.val ∧ k.val < B.length alpha
    have hkBound := k.isLt
    omega
  have hSum : B.length alpha < i.val + k.val := by
    have hkLower' : (B.length alpha : ℤ) - (i.val : ℤ) ≤ (k.val : ℤ) := by
      simpa using hkLower
    have hWeak : B.length alpha ≤ i.val + k.val := by omega
    omega
  let terminal : B.PathPosition alpha := ⟨B.length alpha, by omega⟩
  let D : CFDiv B.graph :=
    one_chip (B.pathVertex alpha k) + one_chip (B.pathVertex alpha i)
  have hRankD : rank B.graph D = 0 := by
    dsimp [D]
    apply rank_same_strand_pair_zero_of_not_reflection_generic
      (by omega : 2 ≤ 2) B alpha k i
    intro h
    apply hkReflect
    omega
  have hRankU : rank B.graph
      (D - one_chip (B.pathVertex alpha i)) = 0 := by
    have hCancel : D - one_chip (B.pathVertex alpha i) =
        one_chip (G := B.graph) (B.pathVertex alpha k) := by
      dsimp [D]
      abel_nf
    rw [hCancel]
    exact rank_one_chip_zero_banana_two B _
  have hRankV : rank B.graph
      (D - one_chip (B.pathVertex alpha terminal)) = 0 := by
    have hSlide := path_pair_linearEquiv_head_excess
      B alpha k i hkInterior.2 hi.2 (by omega)
    have hShift := Certificate.StrongSeparator.linearEquiv_sub_one_chip
      hSlide (B.pathVertex alpha terminal)
    let q : B.PathPosition alpha :=
      ⟨k.val + i.val - B.length alpha, by omega⟩
    have hCancel :
        one_chip (B.pathVertex alpha q) +
              one_chip (B.coreVertex (B.core.head alpha)) -
            one_chip (B.pathVertex alpha terminal) =
          (one_chip (B.pathVertex alpha q) : CFDiv B.graph) := by
      rw [B.pathVertex_length]
      abel_nf
    have hRankEq := rank_eq_of_linear_equiv B.graph hShift
    rw [hCancel, rank_one_chip_zero_banana_two] at hRankEq
    have hRewrite :
        D - one_chip (B.pathVertex alpha terminal) =
          one_chip (B.pathVertex alpha k) + one_chip (B.pathVertex alpha i) -
            one_chip (B.pathVertex alpha terminal) := by
      rfl
    rw [hRewrite]
    exact hRankEq
  have hRankUV : rank B.graph
      (D - one_chip (B.pathVertex alpha i) -
        one_chip (B.pathVertex alpha terminal)) = -1 := by
    have hVertices : B.pathVertex alpha k ≠ B.pathVertex alpha terminal := by
      intro h
      apply hkNotTerminal
      exact congrArg Fin.val (B.pathVertex_injective alpha h)
    have hRank := rank_one_chip_sub_one_chip_eq_neg_one_of_ne_banana
      B (B.pathVertex alpha k) (B.pathVertex alpha terminal) hVertices
    have hCancel :
        D - one_chip (B.pathVertex alpha i) -
            one_chip (B.pathVertex alpha terminal) =
          one_chip (B.pathVertex alpha k) -
            one_chip (B.pathVertex alpha terminal) := by
      dsimp [D]
      abel_nf
    rw [hCancel]
    exact hRank
  exact (rankDelta_neg_iff_rank_zero_deletions
    (mark B.graph (B.pathVertex alpha i)
      (B.pathVertex alpha terminal)) D hRankD).mpr
        ⟨hRankU, hRankV, hRankUV⟩

/-- Every negative divisor for the interior/raw-terminal boundary marking has
the exceptional representative asserted in Theorem 3.4. -/
theorem negative_path_pair_has_exceptional_representative_terminal_right
    (B : Banana 2) (alpha : Fin 3) (i : B.PathPosition alpha)
    (hi : B.IsInteriorPosition alpha i)
    (hiFar : 1 < i.val)
    (D : CFDiv B.graph)
    (hNeg : rankDelta
      (mark B.graph (B.pathVertex alpha i)
        (B.pathVertex alpha ⟨B.length alpha, by omega⟩)) D < 0) :
    ∃ k : B.PathPosition alpha,
      k ∈ thetaExceptionalPositions B alpha i
        ⟨B.length alpha, by omega⟩ ∧
      linear_equiv B.graph D
        (one_chip (B.pathVertex alpha k) + one_chip (B.pathVertex alpha i)) := by
  let terminal : B.PathPosition alpha := ⟨B.length alpha, by omega⟩
  have hij : i.val < terminal.val := by
    dsimp [terminal]
    exact hi.2
  obtain ⟨w, hwv, hPair, hSub, hPairEquiv⟩ :=
    theta_negative_path_pair_auxiliary_rank_data
      B alpha i terminal hij D hNeg
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
      · obtain ⟨q, hq, hqVertex⟩ :=
          exists_interior_strandVertex B gamma offset
        let firstOffset : Fin (B.length alpha - 1) :=
          ⟨i.val - 1, by omega⟩
        have hiOffset : B.pathVertex alpha i =
            B.interiorVertex alpha firstOffset := by
          rw [B.pathVertex_eq_interiorVertex alpha i hi]
          congr 1
        obtain ⟨p, hp, hpVertex⟩ :=
          exists_interior_strandVertex B alpha firstOffset
        have hSub' : rank B.graph
            (one_chip (strandVertex B gamma q) +
              one_chip (strandVertex B alpha p) -
              one_chip (B.pathVertex alpha terminal)) = 0 := by
          rw [hqVertex, hpVertex, ← hiOffset]
          exact hSub
        have hSupport := rankSupport_two_interior_distinct_strands
          (by omega : 2 ≤ 2) B gamma alpha q p hq hp hgamma
        have hTerminalMem : B.pathVertex alpha terminal ∈
            rankSupport B.graph
              (one_chip (strandVertex B gamma q) +
                one_chip (strandVertex B alpha p)) := by
          exact hSub'.ge
        rw [hSupport] at hTerminalMem
        have hTerminalEndpoint : B.pathVertex alpha terminal =
            B.coreVertex (B.core.head alpha) := by
          dsimp [terminal]
          exact B.pathVertex_length alpha
        have hTerminalNeQ :
            B.pathVertex alpha terminal ≠ strandVertex B gamma q := by
          rw [hqVertex, hTerminalEndpoint]
          simp [SubdivisionGraph.Spec.coreVertex,
            SubdivisionGraph.Spec.interiorVertex]
        have hTerminalNeP :
            B.pathVertex alpha terminal ≠ strandVertex B alpha p := by
          rw [hpVertex, hTerminalEndpoint]
          simp [SubdivisionGraph.Spec.coreVertex,
            SubdivisionGraph.Spec.interiorVertex]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hTerminalMem
        exact (hTerminalMem.elim hTerminalNeQ hTerminalNeP).elim
  obtain ⟨k, hwk⟩ := hWonStrand
  have hPair' : rank B.graph
      (one_chip (B.pathVertex alpha i) + one_chip (B.pathVertex alpha k)) = 0 := by
    rw [← hwk]
    simpa [add_comm] using hPair
  have hSub' : rank B.graph
      (one_chip (B.pathVertex alpha i) + one_chip (B.pathVertex alpha k) -
        one_chip (B.pathVertex alpha terminal)) = 0 := by
    rw [← hwk]
    simpa [add_comm] using hSub
  obtain ⟨hkReflect, hkLower, hkUpper⟩ :=
    same_strand_pair_sub_zero_forces_interval_general
      B alpha i terminal k hij hPair' hSub'
  have hkj : k.val ≠ terminal.val := by
    intro h
    apply hwv
    rw [hwk]
    exact congrArg (B.pathVertex alpha) (Fin.ext h)
  have hkExceptional : k ∈ thetaExceptionalPositions B alpha i terminal := by
    change (k.val : ℤ) ≠ (B.length alpha : ℤ) - (i.val : ℤ) ∧
      (k.val : ℤ) ≠ (terminal.val : ℤ) ∧
      (terminal.val : ℤ) - (i.val : ℤ) ≤ (k.val : ℤ) ∧
      (k.val : ℤ) ≤
        (terminal.val : ℤ) - (i.val : ℤ) + (B.length alpha : ℤ)
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

/-- **Theorem 3.4, class-valued bijection, raw terminal-endpoint branch.** -/
theorem thetaPairDivisorClass_bijOn_negative_terminal_right
    (B : Banana 2) (alpha : Fin 3) (i : B.PathPosition alpha)
    (hi : B.IsInteriorPosition alpha i)
    (hiFar : 1 < i.val) :
    Set.BijOn (thetaPairDivisorClass B alpha i)
      (thetaExceptionalPositions B alpha i ⟨B.length alpha, by omega⟩)
      (negativeRankDeltaClasses
        (mark B.graph (B.pathVertex alpha i)
          (B.pathVertex alpha ⟨B.length alpha, by omega⟩))) := by
  refine ⟨?_, (thetaPairDivisorClass_injective B alpha i).injOn, ?_⟩
  · intro k hk
    refine ⟨one_chip (B.pathVertex alpha k) +
      one_chip (B.pathVertex alpha i), rfl, ?_⟩
    exact rankDelta_path_pair_neg_of_mem_thetaExceptionalPositions_terminal_right
      B alpha i k hi hiFar hk
  · intro c hc
    obtain ⟨D, hClassD, hNeg⟩ := hc
    obtain ⟨k, hkExceptional, hPairEquiv⟩ :=
      negative_path_pair_has_exceptional_representative_terminal_right
        B alpha i hi hiFar D hNeg
    refine ⟨k, hkExceptional, ?_⟩
    unfold thetaPairDivisorClass
    rw [← hClassD]
    exact (divisorClass_eq_iff_linearEquiv B.graph _ _).mpr hPairEquiv.symm

end Bananas
