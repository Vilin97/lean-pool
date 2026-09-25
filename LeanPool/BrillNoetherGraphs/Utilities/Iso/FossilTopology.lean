/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Iso.Fossil
import LeanPool.BrillNoetherGraphs.Utilities.Iso.GraphContractionFibreTree
import LeanPool.BrillNoetherGraphs.Utilities.Gonality.DivisorialGonality
import LeanPool.BrillNoetherGraphs.ChipFiringWithLean.RiemannRoch
import Mathlib.Tactic

/-!
# Topology and gonality of the fossil

The short library name `fossil` means the degree-one Abel--Jacobi image, or
2-edge-connectivization, of a connected graph.  This file packages the facts
needed by public applications: the fossil remains connected, has the same
cyclomatic genus and divisorial gonality, and has no one-edge cuts or leaves.
-/

namespace Utilities

open Finset
open Certificate.StrongSeparator
open Utilities.Gonality

universe u

/-- A connected graph has a connected fossil. -/
theorem graph_connected_fossil (G : CFGraph.{u})
    (hConnected : graphConnected G) : graphConnected (fossil G) :=
  (fossilContraction G).graphConnected (fossilContraction_valid G) hConnected

/-- The fossil has the same cyclomatic genus as a connected graph.

The proof avoids a separate edge-count analysis of the bridge forest.  Take a
divisor in the nonspecial range for both graphs.  Fossil pushforward preserves
its degree and rank, while Riemann--Roch says that this rank is `degree - genus`
on each side, forcing the genera to agree. -/
theorem genus_fossil (G : CFGraph.{u}) (hConnected : graphConnected G) :
    genus (fossil G) = genus G := by
  let n : ℤ := 2 * genus G + 2 * genus (fossil G) + 1
  let v : G.V := Classical.choice (inferInstance : Nonempty G.V)
  let D : CFDiv G := n • oneChip v
  have hFossilConnected : graphConnected (fossil G) :=
    graph_connected_fossil G hConnected
  have hGenusNonnegative : 0 ≤ genus G :=
    genus_nonneg_of_graph_connected G hConnected
  have hFossilGenusNonnegative : 0 ≤ genus (fossil G) :=
    genus_nonneg_of_graph_connected (fossil G) hFossilConnected
  have hDegree : deg D = n := by
    dsimp [D]
    rw [map_zsmul, deg_one_chip]
    ring
  have hSourceRange : deg D > 2 * genus G - 2 := by
    rw [hDegree]
    dsimp [n]
    omega
  have hTargetRange :
      deg (fossilPushforward G D) > 2 * genus (fossil G) - 2 := by
    rw [deg_fossilPushforward, hDegree]
    dsimp [n]
    omega
  have hSourceRank :=
    (rank_nonspecial_range hConnected D).2.2 hSourceRange
  have hTargetRank :=
    (rank_nonspecial_range hFossilConnected
      (fossilPushforward G D)).2.2 hTargetRange
  have hPreserved := rank_fossilPushforward G hConnected D
  rw [hSourceRank, hTargetRank, deg_fossilPushforward] at hPreserved
  omega

/-- A connected fossil has no one-edge cut.  If a proper cut had total
multiplicity one, its unique crossing occurrence would define a
`SeparatingEdgeCut`; its endpoints would then be equivalent one-chip classes,
contradicting that fossil vertices are already those classes. -/
theorem twoEdgeCutCondition_fossil (G : CFGraph.{u})
    (hConnected : graphConnected G) : TwoEdgeCutCondition (fossil G) := by
  let F := fossil G
  have hFConnected : graphConnected F := graph_connected_fossil G hConnected
  change TwoEdgeCutCondition F
  intro S hSNonempty hSProper
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    hFConnected S (by
      obtain ⟨p, hp⟩ := hSNonempty
      have hOutside : ∃ q : F.V, q ∉ S := by
        by_contra h
        push Not at h
        apply hSProper
        ext q
        simp [h q]
      obtain ⟨q, hq⟩ := hOutside
      exact ⟨p, q, hp, hq⟩)
  by_contra hCutSmall
  have hCutUpper : cutMultiplicity F S ≤ 1 := by omega
  have hEdgeLeOut : (numEdges F p q : ℤ) ≤ outdegreeSet F S p :=
    edge_le_outdeg_S hq
  have hOutNonnegative := outdeg_S_nonneg F S p
  have hOutLeCut : outdegreeSet F S p ≤ cutMultiplicity F S := by
    unfold cutMultiplicity
    exact Finset.single_le_sum
      (fun v _ => outdeg_S_nonneg F S v) hp
  have hpqCastPositive : 0 < (numEdges F p q : ℤ) := by
    exact_mod_cast hpq
  have hOutEq : outdegreeSet F S p = 1 := by omega
  have hCutEq : cutMultiplicity F S = 1 := by omega
  have hpqOne : numEdges F p q = 1 := by
    exact_mod_cast (show (numEdges F p q : ℤ) = 1 by omega)
  have hOtherOutZero : ∀ a ∈ S, a ≠ p → outdegreeSet F S a = 0 := by
    intro a ha hap
    have haErase : a ∈ S.erase p := by simp [ha, hap]
    have hRestNonnegative :
        0 ≤ ∑ v ∈ S.erase p, outdegreeSet F S v :=
      Finset.sum_nonneg fun v _ => outdeg_S_nonneg F S v
    have hDecompose := S.sum_erase_add (fun v => outdegreeSet F S v) hp
    have hRestZero : (∑ v ∈ S.erase p, outdegreeSet F S v) = 0 := by
      unfold cutMultiplicity at hCutEq
      omega
    have haLeRest : outdegreeSet F S a ≤
        ∑ v ∈ S.erase p, outdegreeSet F S v :=
      Finset.single_le_sum
        (fun v _ => outdeg_S_nonneg F S v) haErase
    have haNonnegative := outdeg_S_nonneg F S a
    omega
  have hOtherFromPZero : ∀ b ∉ S, b ≠ q → numEdges F p b = 0 := by
    intro b hb hbq
    have hqOutside : q ∈ Finset.univ \ S := by simp [hq]
    have hbOutside : b ∈ Finset.univ \ S := by simp [hb]
    have hbErase : b ∈ (Finset.univ \ S).erase q := by
      simp [hbOutside, hbq]
    have hDecompose := (Finset.univ \ S).sum_erase_add
      (fun w => (numEdges F p w : ℤ)) hqOutside
    have hRestNonnegative :
        0 ≤ ∑ w ∈ (Finset.univ \ S).erase q,
          (numEdges F p w : ℤ) :=
      Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
    have hRestZero :
        (∑ w ∈ (Finset.univ \ S).erase q,
          (numEdges F p w : ℤ)) = 0 := by
      unfold outdegreeSet at hOutEq
      have hpqCast : (numEdges F p q : ℤ) = 1 := by exact_mod_cast hpqOne
      omega
    have hEdgeLeRest : (numEdges F p b : ℤ) ≤
        ∑ w ∈ (Finset.univ \ S).erase q,
          (numEdges F p w : ℤ) :=
      Finset.single_le_sum
        (fun w _ => Int.natCast_nonneg (numEdges F p w)) hbErase
    exact_mod_cast (show (numEdges F p b : ℤ) = 0 by
      have hNonnegative : 0 ≤ (numEdges F p b : ℤ) := Int.natCast_nonneg _
      omega)
  let cut : SeparatingEdgeCut F p q :=
    { side := S
      left_mem := hp
      right_not_mem := hq
      cross_num_edges := by
        intro a b ha hb
        by_cases hap : a = p
        · subst a
          by_cases hbq : b = q
          · subst b
            simp [hpqOne]
          · simp [hbq, hOtherFromPZero b hb hbq]
        · have habZero : numEdges F a b = 0 := by
            have hEdgeLe := edge_le_outdeg_S (G := F) (A := S)
              (v := a) (x := b) hb
            have hNonnegative : 0 ≤ (numEdges F a b : ℤ) :=
              Int.natCast_nonneg _
            rw [hOtherOutZero a ha hap] at hEdgeLe
            exact_mod_cast (show (numEdges F a b : ℤ) = 0 by omega)
          simp [hap, habZero] }
  have hpqEqual : p = q :=
    (fossil_chipEquivalent_iff_eq G p q).mp cut.chipEquivalent
  exact hq (hpqEqual ▸ hp)

/-- In particular, a connected fossil has no degree-one vertices. -/
theorem fossil_vertex_degree_ne_one (G : CFGraph.{u})
    (hConnected : graphConnected G) (q : (fossil G).V) :
    vertexDegree (fossil G) q ≠ 1 :=
  vertex_degree_ne_one_of_twoEdgeCutCondition
    (twoEdgeCutCondition_fossil G hConnected) q

/-- Divisorial gonality is unchanged by passage to the fossil. -/
theorem divisorialGonality_fossil (G : CFGraph.{u})
    (hConnected : graphConnected G) :
    divisorialGonality (fossil G) = divisorialGonality G := by
  have hFossilConnected := graph_connected_fossil G hConnected
  apply Nat.le_antisymm
  · have hBN : BNExists (fossil G) 1 (divisorialGonality G : ℤ) :=
      (BNExists_fossil_iff G hConnected 1 _).mp
        (BNExists_one_divisorialGonality hConnected)
    exact_mod_cast divisorialGonality_le_of_BNExists hBN
  · have hBN : BNExists G 1 (divisorialGonality (fossil G) : ℤ) :=
      (BNExists_fossil_iff G hConnected 1 _).mpr
        (BNExists_one_divisorialGonality hFossilConnected)
    exact_mod_cast divisorialGonality_le_of_BNExists hBN

end Utilities
