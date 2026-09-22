/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Sections.SectionSixDefinitions
import LeanPool.BrillNoetherGraphs.Bananas.Basics.Definitions
import LeanPool.BrillNoetherGraphs.Utilities.Iso.GraphContractionFibreTree
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexWedgeRankFormula

/-!
# Once-marked Brill--Noether generality under vertex gluing

This file proves Proposition 6.14 (`prop:glueMarked`) of the paper.  The key
device is a finite piece of the Weierstrass partition attached to a pointed
divisor: its `i`th row is read from the first twist at which the divisor has
rank at least `i`.  Only the first `r+1` rows are needed for a wedge divisor
of rank `r`.

The construction is independent of the transmission-permutation identity of
Proposition 6.10.  It uses only the exact vertex-wedge rank formula and the
all-row definition `OnceMarkedCensusContains`.
-/

namespace Bananas

open Utilities

universe u v

/-! ## Pointed rank thresholds -/

/-- A sufficiently positive twist of a divisor on a connected graph has any
prescribed nonnegative rank.  The twist is normalized so that its degree is
the natural number being searched over. -/
private theorem exists_normalized_twist_rank_ge
    (G : CFGraph.{u}) (hG : graph_connected G) (D : CFDiv G) (q : G.V)
    (i : ℕ) :
    ∃ n : ℕ,
      rank G (D + ((n : ℤ) - deg D) • one_chip q) ≥ (i : ℤ) := by
  have hg : 0 ≤ genus G := genus_nonneg_of_graph_connected G hG
  let n : ℕ := (genus G).toNat + i
  refine ⟨n, ?_⟩
  have hn : (n : ℤ) = genus G + (i : ℤ) := by
    dsimp [n]
    rw [Int.toNat_of_nonneg hg]
  have hRank := rank_ge_deg_sub_genus hG
    (D + ((n : ℤ) - deg D) • one_chip q)
  have hDegree :
      deg (D + ((n : ℤ) - deg D) • one_chip q) = (n : ℤ) := by
    rw [deg.map_add, map_zsmul, deg_one_chip]
    ring
  rw [hDegree] at hRank
  have hNumeric : (i : ℤ) ≤ (n : ℤ) - genus G := by omega
  exact hNumeric.trans hRank

/-- The first integral twist at which `D` has rank at least `i`.  We search
from degree zero upward; every earlier twist has negative degree and hence
rank `-1`, so this is also the first twist among all integers. -/
noncomputable def pointedRankThreshold
    (G : CFGraph.{u}) (hG : graph_connected G) (D : CFDiv G) (q : G.V)
    (i : ℕ) : ℤ :=
  (Nat.find (exists_normalized_twist_rank_ge G hG D q i) : ℤ) - deg D

theorem rank_at_pointedRankThreshold_ge
    (G : CFGraph.{u}) (hG : graph_connected G) (D : CFDiv G) (q : G.V)
    (i : ℕ) :
    rank G (D + pointedRankThreshold G hG D q i • one_chip q) ≥
      (i : ℤ) := by
  exact Nat.find_spec (exists_normalized_twist_rank_ge G hG D q i)

/-- Minimality of the pointed rank threshold among all integral twists. -/
theorem pointedRankThreshold_le_of_rank_ge
    (G : CFGraph.{u}) (hG : graph_connected G) (D : CFDiv G) (q : G.V)
    (i : ℕ) (t : ℤ)
    (ht : rank G (D + t • one_chip q) ≥ (i : ℤ)) :
    pointedRankThreshold G hG D q i ≤ t := by
  have htDegree : 0 ≤ deg D + t := by
    by_contra hneg
    have hRankNeg : rank G (D + t • one_chip q) = -1 := by
      apply rank_neg_one_of_deg_neg
      rw [deg.map_add, map_zsmul, deg_one_chip]
      norm_num
      omega
    rw [hRankNeg] at ht
    omega
  let n : ℕ := (deg D + t).toNat
  have hn : (n : ℤ) = deg D + t := by
    dsimp [n]
    exact Int.toNat_of_nonneg htDegree
  have hTwist :
      D + ((n : ℤ) - deg D) • one_chip q = D + t • one_chip q := by
    rw [hn]
    congr 2
    ring
  have hnWitness :
      rank G (D + ((n : ℤ) - deg D) • one_chip q) ≥ (i : ℤ) := by
    rw [hTwist]
    exact ht
  have hFind := Nat.find_min'
    (exists_normalized_twist_rank_ge G hG D q i) hnWitness
  unfold pointedRankThreshold
  omega

/-- Immediately before the threshold, the desired rank has not yet been
reached. -/
theorem rank_before_pointedRankThreshold_lt
    (G : CFGraph.{u}) (hG : graph_connected G) (D : CFDiv G) (q : G.V)
    (i : ℕ) :
    rank G (D + (pointedRankThreshold G hG D q i - 1) • one_chip q) <
      (i : ℤ) := by
  by_contra hnot
  have hle := pointedRankThreshold_le_of_rank_ge G hG D q i
    (pointedRankThreshold G hG D q i - 1) (by omega)
  omega

/-- Successive pointed rank thresholds are separated by at least one twist.
This is the monotonicity that makes the associated row lengths weakly
decreasing. -/
theorem pointedRankThreshold_succ_le
    (G : CFGraph.{u}) (hG : graph_connected G) (D : CFDiv G) (q : G.V)
    (i : ℕ) :
    pointedRankThreshold G hG D q i + 1 ≤
      pointedRankThreshold G hG D q (i + 1) := by
  let t := pointedRankThreshold G hG D q (i + 1)
  have hAt := rank_at_pointedRankThreshold_ge G hG D q (i + 1)
  have hStep := (rank_add_zsmul_one_chip_step G D q (t - 1)).2
  have hPrev : rank G (D + (t - 1) • one_chip q) ≥ (i : ℤ) := by
    have hRewrite : D + ((t - 1) + 1) • one_chip q =
        D + t • one_chip q := by
      congr 2
      ring
    rw [hRewrite] at hStep
    dsimp [t] at hAt hStep ⊢
    omega
  have hMin := pointedRankThreshold_le_of_rank_ge G hG D q i (t - 1) hPrev
  omega

/-! ## Finite pointed diagrams -/

/-- The `i`th (truncated) Weierstrass row attached to a pointed divisor. -/
noncomputable def pointedRowLength
    (G : CFGraph.{u}) (hG : graph_connected G) (D : CFDiv G) (q : G.V)
    (i : ℕ) : ℕ :=
  Int.toNat ((i : ℤ) + genus G - deg D -
    pointedRankThreshold G hG D q i)

theorem pointedRowLength_anti
    (G : CFGraph.{u}) (hG : graph_connected G) (D : CFDiv G) (q : G.V)
    (i : ℕ) :
    pointedRowLength G hG D q (i + 1) ≤
      pointedRowLength G hG D q i := by
  unfold pointedRowLength
  apply Int.toNat_le_toNat
  have hThreshold := pointedRankThreshold_succ_le G hG D q i
  omega

/-- The first `r+1` pointed rows, sufficient for studying a divisor of rank
`r` on a vertex wedge. -/
noncomputable def finitePointedRows
    (G : CFGraph.{u}) (hG : graph_connected G) (D : CFDiv G) (q : G.V)
    (r : ℕ) : List ℕ :=
  List.ofFn fun i : Fin (r + 1) => pointedRowLength G hG D q i

theorem finitePointedRows_sorted
    (G : CFGraph.{u}) (hG : graph_connected G) (D : CFDiv G) (q : G.V)
    (r : ℕ) :
    (finitePointedRows G hG D q r).SortedGE := by
  rw [List.sortedGE_iff_pairwise, finitePointedRows, List.pairwise_ofFn]
  intro i j hij
  exact antitone_nat_of_succ_le (pointedRowLength_anti G hG D q) hij.le

/-- The finite Young diagram cut out by the first `r+1` pointed rows. -/
noncomputable def finitePointedDiagram
    (G : CFGraph.{u}) (hG : graph_connected G) (D : CFDiv G) (q : G.V)
    (r : ℕ) : YoungDiagram :=
  YoungDiagram.ofRowLens (finitePointedRows G hG D q r)
    (finitePointedRows_sorted G hG D q r)

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

theorem finitePointedDiagram_card
    (G : CFGraph.{u}) (hG : graph_connected G) (D : CFDiv G) (q : G.V)
    (r : ℕ) :
    (finitePointedDiagram G hG D q r).card =
      (finitePointedRows G hG D q r).sum := by
  exact card_cellsOfRowLens _
/-- Every finite pointed diagram belongs to the once-marked divisor census,
witnessed by the degree-`g` normalization of the original divisor. -/
theorem finitePointedDiagram_censusContains
    (G : CFGraph.{u}) (hG : graph_connected G) (D : CFDiv G) (q : G.V)
    (r : ℕ) :
    OnceMarkedCensusContains G q (finitePointedDiagram G hG D q r) := by
  rw [onceMarkedCensusContains_iff_onceMarkedBNExists hG]
  rw [onceMarkedBNExists_iff_rank_cells]
  let E : CFDiv G := D + (genus G - deg D) • one_chip q
  refine ⟨E, ?_, ?_⟩
  · dsimp [E]
    rw [deg.map_add, map_zsmul, deg_one_chip]
    ring
  · intro i j hij
    rw [finitePointedDiagram, YoungDiagram.mem_ofRowLens] at hij
    obtain ⟨hi, hj⟩ := hij
    have hiBound : i < r + 1 := by
      simpa [finitePointedRows] using hi
    have hjRow : j < pointedRowLength G hG D q i := by
      have hj' : j < (List.ofFn (fun k : Fin (r + 1) =>
          pointedRowLength G hG D q k))[i]'(by simpa using hiBound) := hj
      simpa only [List.getElem_ofFn] using hj'

    let raw : ℤ := (i : ℤ) + genus G - deg D -
      pointedRankThreshold G hG D q i
    have hrawPos : 0 < raw := by
      by_contra hnot
      have hzero : Int.toNat raw = 0 := Int.toNat_eq_zero.mpr (by omega)
      unfold pointedRowLength at hjRow
      change j < Int.toNat raw at hjRow
      rw [hzero] at hjRow
      omega
    have hjCast : (j : ℤ) < raw := by
      rw [← Int.toNat_of_nonneg (le_of_lt hrawPos)]
      exact_mod_cast hjRow
    have hExponent :
        pointedRankThreshold G hG D q i ≤
          genus G - deg D + (i : ℤ) - (j : ℤ) - 1 := by
      dsimp [raw] at hjCast
      omega
    have hAt := rank_at_pointedRankThreshold_ge G hG D q i
    let n : ℕ := (genus G - deg D + (i : ℤ) - (j : ℤ) - 1 -
      pointedRankThreshold G hG D q i).toNat
    have hn : (n : ℤ) =
        genus G - deg D + (i : ℤ) - (j : ℤ) - 1 -
          pointedRankThreshold G hG D q i := by
      dsimp [n]
      exact Int.toNat_of_nonneg (sub_nonneg.mpr hExponent)
    have hTransport := rank_add_nsmul_one_chip_ge
      (D + pointedRankThreshold G hG D q i • one_chip q) q n
    have hRewrite :
        (D + pointedRankThreshold G hG D q i • one_chip q) +
            (n : ℤ) • one_chip q =
          E + ((i : ℤ) - (j : ℤ) - 1) • one_chip q := by
      dsimp [E]
      funext z
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hn]
      ring
    rw [hRewrite] at hTransport
    exact hAt.trans hTransport

/-! ## Proposition 6.14 -/

/-- The wedge rank inequality forces complementary pointed thresholds to
sum to at most zero. -/
theorem pointedRankThreshold_add_le_zero_of_wedge_rank
    (G : CFGraph.{u}) (H : CFGraph.{v})
    (hG : graph_connected G) (hH : graph_connected H)
    (x : G.V) (y : H.V) (D : CFDiv G) (E : CFDiv H)
    (r : ℕ)
    (hRank : rank (vertexWedge G H x y)
      (wedgeAddDivisor G H x y D E) ≥ (r : ℤ))
    (i : ℕ) (hi : i ≤ r) :
    pointedRankThreshold G hG D x i +
      pointedRankThreshold H hH E y (r - i) ≤ 0 := by
  have hProfile := vertexWedge_rank_profile_inequality
    G H x y D E (r : ℤ) (by omega) hRank
  let s := pointedRankThreshold G hG D x i
  have hBefore := rank_before_pointedRankThreshold_lt G hG D x i
  have hAtPhase := hProfile (-s)
  have hLeftRewrite :
      D - (-s + 1) • one_chip x = D + (s - 1) • one_chip x := by
    funext z
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hLeftRewrite] at hAtPhase
  have hRight : rank H (E + (-s) • one_chip y) ≥ ((r - i : ℕ) : ℤ) := by
    dsimp [s] at hBefore hAtPhase ⊢
    omega
  have hMin := pointedRankThreshold_le_of_rank_ge H hH E y (r - i) (-s) hRight
  dsimp [s] at hMin ⊢
  omega

/-- Each complementary pair of pointed rows dominates the Brill--Noether
rectangle width of the wedge divisor. -/
theorem pointedRowLength_add_ge_wedge_width
    (G : CFGraph.{u}) (H : CFGraph.{v})
    (hG : graph_connected G) (hH : graph_connected H)
    (x : G.V) (y : H.V) (D : CFDiv G) (E : CFDiv H)
    (r : ℕ)
    (hRank : rank (vertexWedge G H x y)
      (wedgeAddDivisor G H x y D E) ≥ (r : ℤ))
    (i : ℕ) (hi : i ≤ r) :
    genus G + genus H - (deg D + deg E) + (r : ℤ) ≤
      (pointedRowLength G hG D x i : ℤ) +
        (pointedRowLength H hH E y (r - i) : ℤ) := by
  have hThreshold := pointedRankThreshold_add_le_zero_of_wedge_rank
    G H hG hH x y D E r hRank i hi
  unfold pointedRowLength
  rw [Int.ofNat_toNat, Int.ofNat_toNat]
  omega

/-- **Paper Proposition 6.14 (`prop:glueMarked`).**

Gluing the marked vertices of two once-marked Brill--Noether-general
connected graphs produces an unmarked Brill--Noether-general graph. -/
theorem onceMarkedBrillNoetherGeneral_vertexWedge
    (G : CFGraph.{u}) (H : CFGraph.{v})
    (hG : graph_connected G) (hH : graph_connected H)
    (x : G.V) (y : H.V)
    (hGeneralG : OnceMarkedBrillNoetherGeneral G x)
    (hGeneralH : OnceMarkedBrillNoetherGeneral H y) :
    BrillNoetherGeneral (vertexWedge G H x y) := by
  intro r d hr hExists
  rcases hExists with ⟨Q, hDegree, hRank⟩
  let D := wedgeRestrictLeftDivisor G H x y Q
  let E := wedgeRestrictRightDivisor G H x y Q
  have hQSplit : wedgeAddDivisor G H x y D E = Q := by
    exact wedgeAddDivisor_restrict G H x y Q
  have hDegrees : deg D + deg E = d := by
    rw [deg_wedgeRestrictions G H x y Q, hDegree]
  let rn : ℕ := r.toNat
  have hrCast : (rn : ℤ) = r := by
    dsimp [rn]
    exact Int.toNat_of_nonneg hr
  let lambdaG := finitePointedDiagram G hG D x rn
  let lambdaH := finitePointedDiagram H hH E y rn
  have hLambdaG : OnceMarkedCensusContains G x lambdaG :=
    finitePointedDiagram_censusContains G hG D x rn
  have hLambdaH : OnceMarkedCensusContains H y lambdaH :=
    finitePointedDiagram_censusContains H hH E y rn
  have hCardG : (lambdaG.card : ℤ) ≤ genus G :=
    hGeneralG lambdaG hLambdaG
  have hCardH : (lambdaH.card : ℤ) ≤ genus H :=
    hGeneralH lambdaH hLambdaH
  have hRankSplit : rank (vertexWedge G H x y)
      (wedgeAddDivisor G H x y D E) ≥ (rn : ℤ) := by
    rw [hQSplit, hrCast]
    exact hRank
  have hWidthRows : ∀ i : Fin (rn + 1),
      genus G + genus H - (deg D + deg E) + (rn : ℤ) ≤
        (pointedRowLength G hG D x i : ℤ) +
          (pointedRowLength H hH E y (rn - i) : ℤ) := by
    intro i
    exact pointedRowLength_add_ge_wedge_width G H hG hH x y D E rn
      hRankSplit i (Nat.le_of_lt_succ i.isLt)
  have hSumRows :
      ((rn + 1 : ℕ) : ℤ) *
          (genus G + genus H - (deg D + deg E) + (rn : ℤ)) ≤
        ((finitePointedRows G hG D x rn).sum : ℤ) +
          ((finitePointedRows H hH E y rn).sum : ℤ) := by
    have hSummed :
        ∑ _i : Fin (rn + 1),
            (genus G + genus H - (deg D + deg E) + (rn : ℤ)) ≤
          ∑ i : Fin (rn + 1),
            ((pointedRowLength G hG D x i : ℤ) +
              (pointedRowLength H hH E y (rn - i) : ℤ)) := by
      exact Finset.sum_le_sum (fun i _ => hWidthRows i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.sum_add_distrib] at hSummed
    have hReverse :
        ∑ i : Fin (rn + 1),
            (pointedRowLength H hH E y (rn - (i : ℕ)) : ℤ) =
          ∑ i : Fin (rn + 1),
            (pointedRowLength H hH E y i : ℤ) := by
      let e : Equiv.Perm (Fin (rn + 1)) := Fin.rev_involutive.toPerm
      have h := Equiv.sum_comp e
        (fun i : Fin (rn + 1) => (pointedRowLength H hH E y i : ℤ))
      simpa [e, Fin.rev] using h
    rw [hReverse] at hSummed
    simpa only [finitePointedRows, List.sum_ofFn, Nat.cast_sum] using hSummed
  have hCards :
      ((finitePointedRows G hG D x rn).sum : ℤ) +
          ((finitePointedRows H hH E y rn).sum : ℤ) ≤
        genus G + genus H := by
    rw [← finitePointedDiagram_card G hG D x rn,
      ← finitePointedDiagram_card H hH E y rn]
    change (lambdaG.card : ℤ) + (lambdaH.card : ℤ) ≤ _
    omega
  have hBound := hSumRows.trans hCards
  push_cast at hBound
  rw [hDegrees, hrCast] at hBound
  unfold bnNumber rectangleWidth
  rw [genus_vertexWedge]
  have := hBound
  omega

end Bananas
