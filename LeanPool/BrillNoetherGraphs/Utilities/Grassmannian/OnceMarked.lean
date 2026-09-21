/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.GetD
import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionCorner

/-!
# Once-marked Brill--Noether existence

This file records both the degree-free all-row rank-test definition of the
Pflueger--Solomon divisor census and its normalized finite form, together with
the exact graph-side interface with Grassmannian transmission.  A normalized
census witness has degree `genus G`.  If the rows of `lambda` are `lambda_i`,
the required finite inequalities are

`rank (D + (i - lambda_i) u) >= i`.

The auxiliary second mark in transmission disappears because every one of
these rows lies on the cut `b = 0`.
-/

namespace Utilities

universe uOnceMarked

/-- The recursive row-list construction has the expected number of cells. -/
private theorem card_cellsOfRowLens (rows : List ℕ) :
    (YoungDiagram.cellsOfRowLens rows).card = rows.sum := by
  induction rows with
  | nil => simp [YoungDiagram.cellsOfRowLens]
  | cons a rows ih =>
      rw [YoungDiagram.cellsOfRowLens]
      rw [Finset.card_union_of_disjoint]
      · simp [ih]
      · rw [Finset.disjoint_left]
        rintro ⟨i, j⟩ hij hright
        simp only [Finset.mem_product, Finset.mem_singleton,
          Finset.mem_range] at hij
        simp only [Finset.mem_map] at hright
        obtain ⟨⟨i', j'⟩, _hmem, heq⟩ := hright
        have hiSucc : i' + 1 = i := by
          simpa using congrArg Prod.fst heq
        omega

/-- The sum of the row lengths is the cardinality (number of boxes) of a
Young diagram. -/
theorem youngDiagram_rowLens_sum_eq_card (lambda : YoungDiagram) :
    lambda.rowLens.sum = lambda.card := by
  have hCells := congrArg YoungDiagram.cells
    (YoungDiagram.ofRowLens_to_rowLens_eq_self (μ := lambda))
  change YoungDiagram.cellsOfRowLens lambda.rowLens = lambda.cells at hCells
  calc
    lambda.rowLens.sum = (YoungDiagram.cellsOfRowLens lambda.rowLens).card :=
      (card_cellsOfRowLens lambda.rowLens).symm
    _ = lambda.cells.card := congrArg Finset.card hCells

/-- Transposition preserves the number of boxes. -/
@[simp] theorem youngDiagram_transpose_card (lambda : YoungDiagram) :
    lambda.transpose.card = lambda.card := by
  change lambda.transpose.cells.card = lambda.cells.card
  rw [YoungDiagram.transpose]
  exact Finset.card_map _

/-- The finite pointed rank rows encoded by a Young diagram.  We deliberately
retain every positive row.  Passing to the last row of each constant block is
an optional certificate compression, not part of the semantic definition. -/
def onceMarkedCorners (lambda : YoungDiagram) : List Corner :=
  lambda.rowLens.zipIdx.map fun p =>
    ((p.2 : ℤ) - (p.1 : ℤ), 0, (p.2 : ℤ))

/-- The `i`th part of a Young diagram, extended by zero beyond its positive
row list. -/
def onceMarkedPart (lambda : YoungDiagram) (i : ℕ) : ℕ :=
  lambda.rowLens.getD i 0

/-- The degree-free, all-row rank-test formulation of membership in the
Pflueger--Solomon divisor census.  It is the pole-order inequality
`lambda_i(D,u) ≥ lambda_i`, written without choosing minima:

`rank (D + (i + g - deg D - lambda_i)u) ≥ i` for every `i ≥ 0`.

For a connected graph this is equivalent to the finite normalized predicate
`OnceMarkedBNExists` below. -/
def OnceMarkedCensusContains (G : CFGraph) (u : G.V)
    (lambda : YoungDiagram) : Prop :=
  ∃ D : CFDiv G,
    ∀ i : ℕ,
      rank G
        (D + ((i : ℤ) + genus G - deg D - (onceMarkedPart lambda i : ℤ)) •
          one_chip u) ≥ (i : ℤ)

/-- The normalized form of membership of `lambda` in the divisor census of
the once-marked graph `(G,u)`. -/
def OnceMarkedBNExists (G : CFGraph) (u : G.V)
    (lambda : YoungDiagram) : Prop :=
  ∃ D : CFDiv G,
    deg D = genus G ∧
    ∀ c ∈ onceMarkedCorners lambda,
      rank G (D + c.1 • one_chip u) ≥ c.2.2

/-- Once-marked Brill--Noether existence for `(G,u)`: every Young diagram of
size at most the genus occurs in its divisor census. -/
def OnceMarkedBNExistence (G : CFGraph) (u : G.V) : Prop :=
  ∀ lambda : YoungDiagram,
    (lambda.card : ℤ) ≤ genus G →
      OnceMarkedBNExists G u lambda

/-- The once-marked Brill--Noether existence conjecture for finite connected
graphs. -/
def OnceMarkedBNConjecture : Prop :=
  ∀ (G : CFGraph.{uOnceMarked}), graph_connected G →
    ∀ u : G.V, OnceMarkedBNExistence G u

/-- Row-indexed form of `OnceMarkedBNExists`.  This is convenient both for
handwritten shape arguments and for generated finite catalogs. -/
theorem onceMarkedBNExists_iff_rank_rows
    (G : CFGraph) (u : G.V) (lambda : YoungDiagram) :
    OnceMarkedBNExists G u lambda ↔
      ∃ D : CFDiv G,
        deg D = genus G ∧
        ∀ (i : ℕ) (hi : i < lambda.rowLens.length),
          rank G
            (D + ((i : ℤ) - (lambda.rowLens[i] : ℤ)) • one_chip u) ≥
              (i : ℤ) := by
  unfold OnceMarkedBNExists onceMarkedCorners
  simp only [List.forall_mem_map, List.forall_mem_zipIdx']

/-! ## Marked Riemann--Roch duality -/

/-- Cellwise form of the pointed partition rank conditions.  A cell `(i,j)`
asks for rank at least `i` after twisting by `(i-j-1)u`.  This symmetric form
is the convenient interface for transposing a partition. -/
theorem onceMarkedBNExists_iff_rank_cells
    (G : CFGraph) (u : G.V) (lambda : YoungDiagram) :
    OnceMarkedBNExists G u lambda ↔
      ∃ D : CFDiv G,
        deg D = genus G ∧
        ∀ (i j : ℕ), (i, j) ∈ lambda →
          rank G
            (D + ((i : ℤ) - (j : ℤ) - 1) • one_chip u) ≥ (i : ℤ) := by
  rw [onceMarkedBNExists_iff_rank_rows]
  constructor
  · rintro ⟨D, hDegree, hRows⟩
    refine ⟨D, hDegree, ?_⟩
    intro i j hij
    have hiCell : (i, 0) ∈ lambda :=
      lambda.up_left_mem (le_refl i) (Nat.zero_le j) hij
    have hi : i < lambda.rowLens.length := by
      rw [YoungDiagram.length_rowLens]
      exact YoungDiagram.mem_iff_lt_colLen.mp hiCell
    have hj : j < lambda.rowLen i :=
      YoungDiagram.mem_iff_lt_rowLen.mp hij
    have hRowEq : lambda.rowLens[i] = lambda.rowLen i :=
      YoungDiagram.get_rowLens
    have hBase := hRows i hi
    rw [hRowEq] at hBase
    let k : ℕ := lambda.rowLen i - j - 1
    have hk : (k : ℤ) = (lambda.rowLen i : ℤ) - (j : ℤ) - 1 := by
      dsimp [k]
      omega
    have hTransport := rank_add_nsmul_one_chip_ge
      (D + ((i : ℤ) - (lambda.rowLen i : ℤ)) • one_chip u) u k
    have hRewrite :
        (D + ((i : ℤ) - (lambda.rowLen i : ℤ)) • one_chip u) +
            (k : ℤ) • one_chip u =
          D + ((i : ℤ) - (j : ℤ) - 1) • one_chip u := by
      funext v
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hk]
      ring
    rw [hRewrite] at hTransport
    exact hBase.trans hTransport
  · rintro ⟨D, hDegree, hCells⟩
    refine ⟨D, hDegree, ?_⟩
    intro i hi
    have hPos : 0 < lambda.rowLens[i] :=
      lambda.pos_of_mem_rowLens _ (List.getElem_mem hi)
    let j : ℕ := lambda.rowLens[i] - 1
    have hjCast : (j : ℤ) = (lambda.rowLens[i] : ℤ) - 1 := by
      dsimp [j]
      omega
    have hj : j < lambda.rowLen i := by
      rw [← YoungDiagram.get_rowLens (h := hi)]
      dsimp [j]
      omega
    have hCell := hCells i j (YoungDiagram.mem_iff_lt_rowLen.mpr hj)
    have hRewrite :
        D + ((i : ℤ) - (j : ℤ) - 1) • one_chip u =
          D + ((i : ℤ) - (lambda.rowLens[i] : ℤ)) • one_chip u := by
      funext v
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hjCast]
      ring
    rw [hRewrite] at hCell
    exact hCell

/-- The degree-`g` representative of the marked Riemann--Roch dual of `D`.
The extra `2u` normalizes the degree; twisting a divisor at the marked point
does not change its Weierstrass partition. -/
def onceMarkedDualDivisor (G : CFGraph) (u : G.V) (D : CFDiv G) : CFDiv G :=
  canonical_divisor G - D + (2 : ℤ) • one_chip u

@[simp] theorem deg_onceMarkedDualDivisor
    {G : CFGraph} (u : G.V) (D : CFDiv G)
    (hDegree : deg D = genus G) :
    deg (onceMarkedDualDivisor G u D) = genus G := by
  rw [onceMarkedDualDivisor, deg.map_add, deg.map_sub,
    degree_of_canonical_divisor, map_zsmul, deg_one_chip, hDegree]
  ring

/-- Exact marked Riemann--Roch identity for a normalized divisor. -/
theorem rank_onceMarkedDualDivisor_add_zsmul
    {G : CFGraph} (hG : graph_connected G) (u : G.V)
    (D : CFDiv G) (hDegree : deg D = genus G) (ell : ℤ) :
    rank G (onceMarkedDualDivisor G u D + ell • one_chip u) =
      rank G (D - (ell + 2) • one_chip u) + ell + 1 := by
  let X : CFDiv G := D - (ell + 2) • one_chip u
  have hXDegree : deg X = genus G - (ell + 2) := by
    dsimp [X]
    rw [deg.map_sub, map_zsmul, deg_one_chip, hDegree]
    ring
  have hComplement :
      canonical_divisor G - X =
        onceMarkedDualDivisor G u D + ell • one_chip u := by
    dsimp [X, onceMarkedDualDivisor]
    funext v
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hRR := riemann_roch_for_graphs hG X
  rw [hXDegree, hComplement] at hRR
  linarith

/-- A normalized witness for `lambda` dualizes to a normalized witness for
the transposed Young diagram. -/
theorem onceMarkedBNExists_transpose
    {G : CFGraph} (hG : graph_connected G) (u : G.V)
    (lambda : YoungDiagram) :
    OnceMarkedBNExists G u lambda →
      OnceMarkedBNExists G u lambda.transpose := by
  rw [onceMarkedBNExists_iff_rank_cells,
    onceMarkedBNExists_iff_rank_cells]
  rintro ⟨D, hDegree, hCells⟩
  refine ⟨onceMarkedDualDivisor G u D,
    deg_onceMarkedDualDivisor u D hDegree, ?_⟩
  intro i j hij
  have hSource :
      rank G (D + ((j : ℤ) - (i : ℤ) - 1) • one_chip u) ≥ (j : ℤ) :=
    hCells j i (by simpa using hij)
  have hRR := rank_onceMarkedDualDivisor_add_zsmul
    hG u D hDegree ((i : ℤ) - (j : ℤ) - 1)
  have hSourceRewrite :
      D - (((i : ℤ) - (j : ℤ) - 1) + 2) • one_chip u =
        D + ((j : ℤ) - (i : ℤ) - 1) • one_chip u := by
    funext v
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hSourceRewrite] at hRR
  rw [hRR]
  omega

/-- Once-marked Brill--Noether existence is invariant under transposing the
partition. -/
theorem onceMarkedBNExists_transpose_iff
    {G : CFGraph} (hG : graph_connected G) (u : G.V)
    (lambda : YoungDiagram) :
    OnceMarkedBNExists G u lambda ↔
      OnceMarkedBNExists G u lambda.transpose := by
  constructor
  · exact onceMarkedBNExists_transpose hG u lambda
  · intro hTranspose
    have h := onceMarkedBNExists_transpose hG u lambda.transpose hTranspose
    simpa using h

/-- On a connected graph, degree normalization and the Riemann tail identify
the original all-row census test with the finite positive-row test. -/
theorem onceMarkedCensusContains_iff_onceMarkedBNExists
    {G : CFGraph} (hG : graph_connected G) (u : G.V)
    (lambda : YoungDiagram) :
    OnceMarkedCensusContains G u lambda ↔
      OnceMarkedBNExists G u lambda := by
  rw [onceMarkedBNExists_iff_rank_rows]
  constructor
  · rintro ⟨E, hE⟩
    let D : CFDiv G := E + (genus G - deg E) • one_chip u
    refine ⟨D, ?_, ?_⟩
    · dsimp [D]
      rw [deg.map_add, map_zsmul, deg_one_chip]
      ring
    · intro i hi
      have hPart : onceMarkedPart lambda i = lambda.rowLens[i] := by
        exact List.getD_eq_getElem lambda.rowLens 0 hi
      have hRank := hE i
      have hTwist :
          D + ((i : ℤ) - (lambda.rowLens[i] : ℤ)) • one_chip u =
            E + ((i : ℤ) + genus G - deg E -
              (onceMarkedPart lambda i : ℤ)) • one_chip u := by
        rw [hPart]
        dsimp [D]
        funext v
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hTwist]
      exact hRank
  · rintro ⟨D, hDegree, hRows⟩
    refine ⟨D, ?_⟩
    intro i
    by_cases hi : i < lambda.rowLens.length
    · have hPart : onceMarkedPart lambda i = lambda.rowLens[i] := by
        exact List.getD_eq_getElem lambda.rowLens 0 hi
      have hRank := hRows i hi
      have hTwist :
          D + ((i : ℤ) + genus G - deg D -
              (onceMarkedPart lambda i : ℤ)) • one_chip u =
            D + ((i : ℤ) - (lambda.rowLens[i] : ℤ)) • one_chip u := by
        rw [hDegree, hPart]
        congr 2
        ring
      rw [hTwist]
      exact hRank
    · have hPart : onceMarkedPart lambda i = 0 := by
        exact List.getD_eq_default _ _ (Nat.le_of_not_gt hi)
      have hRank := rank_ge_deg_sub_genus hG
        (D + (i : ℤ) • one_chip u)
      have hTwist :
          D + ((i : ℤ) + genus G - deg D -
              (onceMarkedPart lambda i : ℤ)) • one_chip u =
            D + (i : ℤ) • one_chip u := by
        rw [hDegree, hPart]
        congr 2
        ring
      rw [hTwist]
      rw [deg.map_add, map_zsmul, deg_one_chip, hDegree] at hRank
      norm_num at hRank
      exact hRank

/-- The exact finite corner data needed for an ASP permutation to encode the
once-marked partition `lambda` at the cut `b = 0`.

For the Grassmannian permutation attached to `lambda`, these facts follow
from its essential-set formula.  Packaging them separately keeps the graph
side independent of the particular construction of that permutation. -/
def GrassmannianPartitionProfile (tau : AspPerm)
    (lambda : YoungDiagram) : Prop :=
  tau.χ = 0 ∧
  CornersDominate tau (onceMarkedCorners lambda) ∧
  ∀ c ∈ onceMarkedCorners lambda,
    c.2.2 ≤ tau.s (c.1 + 1) 0 - 1

/-- A Grassmannian partition profile makes its twice-marked transmission
existence condition exactly the once-marked divisor-census condition.  In
particular, the result is independent of the auxiliary second mark. -/
theorem transmissionExists_iff_onceMarkedBNExists
    {G : CFGraph} (hG : graph_connected G) (u v : G.V)
    (tau : AspPerm) (lambda : YoungDiagram)
    (hProfile : GrassmannianPartitionProfile tau lambda) :
    TransmissionExists G u v tau ↔ OnceMarkedBNExists G u lambda := by
  rcases hProfile with ⟨hChi, hDom, hThreshold⟩
  constructor
  · rintro ⟨D, hD⟩
    refine ⟨D, ?_, ?_⟩
    · rw [hD.1, hChi]
      simp
    · intro c hc
      have hRow := rank_twist_of_satisfiesTransmission hD c.1 0
      simp only [zero_smul, sub_zero] at hRow
      exact le_trans (hThreshold c hc) hRow
  · rintro ⟨D, hDegree, hCorners⟩
    refine ⟨D, satisfiesTransmission_of_corners hG u v tau D
      (onceMarkedCorners lambda) ?_ hDom ?_⟩
    · rw [hChi]
      simpa using hDegree
    · intro c hc
      have hcZero : c.2.1 = 0 := by
        rw [onceMarkedCorners, List.mem_map] at hc
        obtain ⟨p, _hp, rfl⟩ := hc
        rfl
      rw [hcZero, zero_smul, sub_zero]
      exact hCorners c hc

end Utilities
