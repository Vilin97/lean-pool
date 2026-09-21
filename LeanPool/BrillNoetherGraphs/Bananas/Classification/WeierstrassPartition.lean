/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TransmissionBridge
import LeanPool.BrillNoetherGraphs.Utilities.Grassmannian.OnceMarked
import LeanPool.BrillNoetherGraphs.Utilities.Iso.GraphContractionFibreTree

/-!
# Weierstrass partitions of pointed divisors

This file formalizes the pole orders and Weierstrass partition used in
Definition 1.6 and Proposition 6.10 of the twice-marked banana paper.

The definition is degree-independent.  For a divisor `D` on a connected
pointed graph `(G, v)`, the `i`th pole order is the least integer `ell` for
which `rank (D + ell * v) >= i`; the `i`th part is

`i + genus G - deg D - poleOrder G v D i`.

Riemann--Roch supplies an upper bound on the pole order, while the elementary
rank--degree inequality supplies a lower bound, so the integer infimum really
is a minimum.  The parts are weakly decreasing and vanish from row `genus G`
onward, hence define an honest finite `YoungDiagram`.
-/

namespace Bananas

open Utilities

/-- The integers at which the pointed rank has reached row `i`. -/
def poleOrderSet (G : CFGraph) (v : G.V) (D : CFDiv G) (i : ℕ) : Set ℤ :=
  {ell | (i : ℤ) ≤ rank G (D + ell • one_chip v)}

/-- Definition 1.6: the least twist at the marked point having rank at least
`i`. -/
noncomputable def poleOrder (G : CFGraph) (v : G.V) (D : CFDiv G)
    (i : ℕ) : ℤ :=
  sInf (poleOrderSet G v D i)

theorem poleOrderSet_nonempty {G : CFGraph} (hG : _root_.graph_connected G)
    (v : G.V) (D : CFDiv G) (i : ℕ) :
    (poleOrderSet G v D i).Nonempty := by
  refine ⟨(i : ℤ) + genus G - deg D, ?_⟩
  have hRank := rank_ge_deg_sub_genus hG
    (D + ((i : ℤ) + genus G - deg D) • one_chip v)
  have hDegree :
      deg (D + ((i : ℤ) + genus G - deg D) • one_chip v) - genus G =
        (i : ℤ) := by
    rw [deg.map_add, map_zsmul, deg_one_chip]
    norm_num
  simp only [poleOrderSet, Set.mem_ofPred_eq]
  rwa [hDegree] at hRank

theorem poleOrderSet_bddBelow (G : CFGraph) (v : G.V) (D : CFDiv G)
    (i : ℕ) : BddBelow (poleOrderSet G v D i) := by
  refine ⟨(i : ℤ) - deg D, ?_⟩
  intro ell hell
  have hRank : rank G (D + ell • one_chip v) ≥ (i : ℤ) := hell
  have hGeq : rank_geq G (D + ell • one_chip v) (i : ℤ) :=
    (rank_geq_iff G _ _).mpr hRank
  have hDegree := rank_le_degree G (D + ell • one_chip v) (i : ℤ)
    (by positivity) hGeq
  rw [deg.map_add, map_zsmul, deg_one_chip] at hDegree
  norm_num at hDegree
  linarith

theorem poleOrder_mem_set {G : CFGraph} (hG : _root_.graph_connected G)
    (v : G.V) (D : CFDiv G) (i : ℕ) :
    poleOrder G v D i ∈ poleOrderSet G v D i := by
  exact Int.csInf_mem (poleOrderSet_nonempty hG v D i)
    (poleOrderSet_bddBelow G v D i)

theorem poleOrder_rank_ge {G : CFGraph} (hG : _root_.graph_connected G)
    (v : G.V) (D : CFDiv G) (i : ℕ) :
    (i : ℤ) ≤ rank G (D + poleOrder G v D i • one_chip v) :=
  poleOrder_mem_set hG v D i

theorem poleOrder_le_of_rank_ge {G : CFGraph} (_hG : _root_.graph_connected G)
    (v : G.V) (D : CFDiv G) (i : ℕ) (ell : ℤ)
    (hRank : (i : ℤ) ≤ rank G (D + ell • one_chip v)) :
    poleOrder G v D i ≤ ell := by
  exact csInf_le (poleOrderSet_bddBelow G v D i) hRank

theorem rank_lt_of_lt_poleOrder {G : CFGraph} (hG : _root_.graph_connected G)
    (v : G.V) (D : CFDiv G) (i : ℕ) (ell : ℤ)
    (hell : ell < poleOrder G v D i) :
    rank G (D + ell • one_chip v) < (i : ℤ) := by
  by_contra h
  have hRank : (i : ℤ) ≤ rank G (D + ell • one_chip v) := by omega
  exact (not_le_of_gt hell) (poleOrder_le_of_rank_ge hG v D i ell hRank)

theorem poleOrder_le_riemannRoch {G : CFGraph} (hG : _root_.graph_connected G)
    (v : G.V) (D : CFDiv G) (i : ℕ) :
    poleOrder G v D i ≤ (i : ℤ) + genus G - deg D := by
  apply poleOrder_le_of_rank_ge hG
  have hRank := rank_ge_deg_sub_genus hG
    (D + ((i : ℤ) + genus G - deg D) • one_chip v)
  have hDegree :
      deg (D + ((i : ℤ) + genus G - deg D) • one_chip v) - genus G =
        (i : ℤ) := by
    rw [deg.map_add, map_zsmul, deg_one_chip]
    norm_num
  rwa [hDegree] at hRank

/-- The rank at the least pole order is exactly the row index. -/
theorem rank_poleOrder_eq {G : CFGraph} (hG : _root_.graph_connected G)
    (v : G.V) (D : CFDiv G) (i : ℕ) :
    rank G (D + poleOrder G v D i • one_chip v) = (i : ℤ) := by
  have hAt := poleOrder_rank_ge hG v D i
  have hBefore := rank_lt_of_lt_poleOrder hG v D i
    (poleOrder G v D i - 1) (by omega)
  have hStep := rank_sub_one_chip_ge_rank_sub_one
    (D + poleOrder G v D i • one_chip v) v
  have hRewrite :
      D + poleOrder G v D i • one_chip v - one_chip v =
        D + (poleOrder G v D i - 1) • one_chip v := by
    funext w
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hRewrite] at hStep
  omega

/-- Immediately before the `i`th pole, the rank is `i - 1`. -/
theorem rank_poleOrder_sub_one_eq {G : CFGraph}
    (hG : _root_.graph_connected G) (v : G.V) (D : CFDiv G) (i : ℕ) :
    rank G (D + (poleOrder G v D i - 1) • one_chip v) = (i : ℤ) - 1 := by
  have hBefore := rank_lt_of_lt_poleOrder hG v D i
    (poleOrder G v D i - 1) (by omega)
  have hStep := rank_sub_one_chip_ge_rank_sub_one
    (D + poleOrder G v D i • one_chip v) v
  have hAt := rank_poleOrder_eq hG v D i
  have hRewrite :
      D + poleOrder G v D i • one_chip v - one_chip v =
        D + (poleOrder G v D i - 1) • one_chip v := by
    funext w
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hRewrite, hAt] at hStep
  omega

/-- A one-step rank crossing characterizes the corresponding pole order. -/
theorem poleOrder_eq_of_rank_crossing {G : CFGraph}
    (hG : _root_.graph_connected G) (v : G.V) (D : CFDiv G)
    (i : ℕ) (ell : ℤ)
    (hAt : (i : ℤ) ≤ rank G (D + ell • one_chip v))
    (hBefore : rank G (D + (ell - 1) • one_chip v) < (i : ℤ)) :
    poleOrder G v D i = ell := by
  apply le_antisymm (poleOrder_le_of_rank_ge hG v D i ell hAt)
  by_contra hNot
  have hPoleLt : poleOrder G v D i < ell := by omega
  have hn : 0 ≤ ell - 1 - poleOrder G v D i := by omega
  let n : ℕ := (ell - 1 - poleOrder G v D i).toNat
  have hnCast : (n : ℤ) = ell - 1 - poleOrder G v D i := by
    dsimp [n]
    rw [Int.toNat_of_nonneg hn]
  have hTransport := rank_add_nsmul_one_chip_ge
    (D + poleOrder G v D i • one_chip v) v n
  have hRewrite :
      (D + poleOrder G v D i • one_chip v) + (n : ℤ) • one_chip v =
        D + (ell - 1) • one_chip v := by
    funext w
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hnCast]
    ring
  rw [hRewrite] at hTransport
  have hPoleRank := poleOrder_rank_ge hG v D i
  exact (not_le_of_gt hBefore) (hPoleRank.trans hTransport)

/-- Pole orders are strictly increasing with the rank row. -/
theorem poleOrder_strictMono {G : CFGraph}
    (hG : _root_.graph_connected G) (v : G.V) (D : CFDiv G) :
    StrictMono (poleOrder G v D) := by
  intro i j hij
  have hRankJ := rank_poleOrder_eq hG v D j
  have hLe := poleOrder_le_of_rank_ge hG v D i (poleOrder G v D j) (by
    rw [hRankJ]
    exact_mod_cast hij.le)
  apply lt_of_le_of_ne hLe
  intro hEq
  have hRankI := rank_poleOrder_eq hG v D i
  rw [hEq, hRankJ] at hRankI
  omega

/-- Consecutive pole orders differ by at least one. -/
theorem poleOrder_succ_le {G : CFGraph} (hG : _root_.graph_connected G)
    (v : G.V) (D : CFDiv G) (i : ℕ) :
    poleOrder G v D i + 1 ≤ poleOrder G v D (i + 1) := by
  have hPrev :
      rank G (D + (poleOrder G v D (i + 1) - 1) • one_chip v) = (i : ℤ) := by
    have hStep := rank_sub_one_chip_ge_rank_sub_one
      (D + poleOrder G v D (i + 1) • one_chip v) v
    have hAt := rank_poleOrder_eq hG v D (i + 1)
    have hBefore := rank_lt_of_lt_poleOrder hG v D (i + 1)
      (poleOrder G v D (i + 1) - 1) (by omega)
    have hRewrite :
        D + poleOrder G v D (i + 1) • one_chip v - one_chip v =
          D + (poleOrder G v D (i + 1) - 1) • one_chip v := by
      funext w
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hRewrite, hAt] at hStep
    omega
  have hMinimal := poleOrder_le_of_rank_ge hG v D i
    (poleOrder G v D (i + 1) - 1) (by rw [hPrev])
  omega

/-- The integer underlying the `i`th Weierstrass part. -/
noncomputable def weierstrassPartInt (G : CFGraph) (v : G.V) (D : CFDiv G)
    (i : ℕ) : ℤ :=
  (i : ℤ) + genus G - deg D - poleOrder G v D i

theorem weierstrassPartInt_nonneg {G : CFGraph} (hG : _root_.graph_connected G)
    (v : G.V) (D : CFDiv G) (i : ℕ) :
    0 ≤ weierstrassPartInt G v D i := by
  unfold weierstrassPartInt
  have := poleOrder_le_riemannRoch hG v D i
  omega

/-- Definition 1.6: the `i`th part of the Weierstrass partition. -/
noncomputable def weierstrassPart (G : CFGraph) (v : G.V) (D : CFDiv G)
    (i : ℕ) : ℕ :=
  (weierstrassPartInt G v D i).toNat

theorem weierstrassPart_cast {G : CFGraph} (hG : _root_.graph_connected G)
    (v : G.V) (D : CFDiv G) (i : ℕ) :
    (weierstrassPart G v D i : ℤ) = weierstrassPartInt G v D i := by
  rw [weierstrassPart, Int.toNat_of_nonneg
    (weierstrassPartInt_nonneg hG v D i)]

theorem weierstrassPart_anti {G : CFGraph} (hG : _root_.graph_connected G)
    (v : G.V) (D : CFDiv G) {i j : ℕ} (hij : i ≤ j) :
    weierstrassPart G v D j ≤ weierstrassPart G v D i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
      have hPole := poleOrder_succ_le hG v D j
      have hCastI := weierstrassPart_cast hG v D i
      have hCastJ := weierstrassPart_cast hG v D j
      have hCastSucc := weierstrassPart_cast hG v D (j + 1)
      apply Int.ofNat_le.mp
      rw [hCastI, hCastSucc]
      unfold weierstrassPartInt at *
      have ih' : (weierstrassPart G v D j : ℤ) ≤
          (weierstrassPart G v D i : ℤ) := by exact_mod_cast ih
      rw [hCastI, hCastJ] at ih'
      omega

theorem poleOrder_eq_riemannRoch_of_genus_le {G : CFGraph}
    (hG : _root_.graph_connected G) (v : G.V) (D : CFDiv G) (i : ℕ)
    (hi : (genus G).toNat ≤ i) :
    poleOrder G v D i = (i : ℤ) + genus G - deg D := by
  apply le_antisymm (poleOrder_le_riemannRoch hG v D i)
  let ell : ℤ := (i : ℤ) + genus G - deg D
  have hDegree :
      deg (D + (ell - 1) • one_chip v) = (i : ℤ) + genus G - 1 := by
    dsimp [ell]
    rw [deg.map_add, map_zsmul, deg_one_chip]
    ring
  have hg : 0 ≤ genus G := genus_nonneg_of_graph_connected G hG
  have hiCast : genus G ≤ (i : ℤ) := by
    rw [← Int.toNat_of_nonneg hg]
    exact_mod_cast hi
  have hLarge : deg (D + (ell - 1) • one_chip v) > 2 * genus G - 2 := by
    rw [hDegree]
    omega
  have hRankPrev := (rank_nonspecial_range hG
    (D + (ell - 1) • one_chip v)).2.2 hLarge
  rw [hDegree] at hRankPrev
  have hRankPrevEq : rank G (D + (ell - 1) • one_chip v) = (i : ℤ) - 1 := by
    linarith
  have hPoleMem := poleOrder_rank_ge hG v D i
  by_contra hNot
  have hlt : poleOrder G v D i < ell := by omega
  have hn : 0 ≤ ell - 1 - poleOrder G v D i := by omega
  let n : ℕ := (ell - 1 - poleOrder G v D i).toNat
  have hnCast : (n : ℤ) = ell - 1 - poleOrder G v D i := by
    dsimp [n]
    rw [Int.toNat_of_nonneg hn]
  have hTransport := rank_add_nsmul_one_chip_ge
    (D + poleOrder G v D i • one_chip v) v n
  have hRewrite :
      (D + poleOrder G v D i • one_chip v) + (n : ℤ) • one_chip v =
        D + (ell - 1) • one_chip v := by
    funext w
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hnCast]
    ring
  rw [hRewrite, hRankPrevEq] at hTransport
  omega

@[simp] theorem weierstrassPart_eq_zero_of_genus_le {G : CFGraph}
    (hG : _root_.graph_connected G) (v : G.V) (D : CFDiv G) (i : ℕ)
    (hi : (genus G).toNat ≤ i) :
    weierstrassPart G v D i = 0 := by
  apply Int.ofNat_eq_zero.mp
  rw [weierstrassPart_cast hG]
  unfold weierstrassPartInt
  rw [poleOrder_eq_riemannRoch_of_genus_le hG v D i hi]
  ring

/-- The finite row-list of the Weierstrass partition.  Zero trailing rows are
harmless to `YoungDiagram.ofRowLens`. -/
noncomputable def weierstrassRowLens (G : CFGraph) (v : G.V) (D : CFDiv G) :
    List ℕ :=
  (List.range (genus G).toNat).map (weierstrassPart G v D)

theorem weierstrassRowLens_sorted {G : CFGraph} (hG : _root_.graph_connected G)
    (v : G.V) (D : CFDiv G) :
    (weierstrassRowLens G v D).SortedGE := by
  unfold weierstrassRowLens
  have hPairwise : List.Pairwise (fun x y : ℕ => x ≥ y)
      ((List.range (genus G).toNat).map (weierstrassPart G v D)) :=
    List.pairwise_le_range.map _
      (fun _ _ hij => weierstrassPart_anti hG v D hij)
  exact hPairwise.sortedGE

/-- Definition 1.6 as an actual finite Young diagram. -/
noncomputable def weierstrassPartition {G : CFGraph} (hG : _root_.graph_connected G)
    (v : G.V) (D : CFDiv G) : YoungDiagram :=
  YoungDiagram.ofRowLens (weierstrassRowLens G v D)
    (weierstrassRowLens_sorted hG v D)

/-- `onceMarkedPart` is simply the row length of a Young diagram, including
the zero extension beyond its positive rows. -/
theorem onceMarkedPart_eq_rowLen (lambda : YoungDiagram) (i : ℕ) :
    onceMarkedPart lambda i = lambda.rowLen i := by
  by_cases hi : i < lambda.rowLens.length
  · rw [onceMarkedPart, List.getD_eq_getElem _ _ hi,
      YoungDiagram.get_rowLens]
  · have hPart : onceMarkedPart lambda i = 0 := by
      exact List.getD_eq_default _ _ (Nat.le_of_not_gt hi)
    rw [hPart]
    symm
    apply Nat.eq_zero_of_not_pos
    intro hPos
    have hCell : (i, 0) ∈ lambda :=
      YoungDiagram.mem_iff_lt_rowLen.mpr hPos
    have hi' : i < lambda.colLen 0 :=
      YoungDiagram.mem_iff_lt_colLen.mp hCell
    rw [← YoungDiagram.length_rowLens] at hi'
    exact hi hi'

theorem weierstrassPartition_rowLen {G : CFGraph}
    (hG : _root_.graph_connected G) (v : G.V) (D : CFDiv G) (i : ℕ) :
    (weierstrassPartition hG v D).rowLen i = weierstrassPart G v D i := by
  by_cases hi : i < (genus G).toNat
  · have hiList : i < (weierstrassRowLens G v D).length := by
      simp [weierstrassRowLens, hi]
    have hRow := YoungDiagram.rowLen_ofRowLens
      (w := weierstrassRowLens G v D)
      (hw := weierstrassRowLens_sorted hG v D) ⟨i, hiList⟩
    simpa [weierstrassPartition, weierstrassRowLens] using hRow
  · have hPart : weierstrassPart G v D i = 0 :=
      weierstrassPart_eq_zero_of_genus_le hG v D i (Nat.le_of_not_gt hi)
    rw [hPart]
    apply Nat.eq_zero_of_not_pos
    intro hPos
    have hCell : (i, 0) ∈ weierstrassPartition hG v D :=
      YoungDiagram.mem_iff_lt_rowLen.mpr hPos
    rw [weierstrassPartition, YoungDiagram.mem_ofRowLens] at hCell
    obtain ⟨hiList, _⟩ := hCell
    have hLength : (weierstrassRowLens G v D).length = (genus G).toNat := by
      simp [weierstrassRowLens]
    rw [hLength] at hiList
    exact hi hiList

theorem weierstrassPartition_part {G : CFGraph}
    (hG : _root_.graph_connected G) (v : G.V) (D : CFDiv G) (i : ℕ) :
    onceMarkedPart (weierstrassPartition hG v D) i =
      weierstrassPart G v D i := by
  rw [onceMarkedPart_eq_rowLen, weierstrassPartition_rowLen]

private theorem card_cellsOfRowLens (rows : List ℕ) :
    (YoungDiagram.cellsOfRowLens rows).card = rows.sum := by
  induction rows with
  | nil => simp [YoungDiagram.cellsOfRowLens]
  | cons a rows ih =>
      rw [YoungDiagram.cellsOfRowLens]
      rw [Finset.card_union_of_disjoint]
      · simp [ih]
      · rw [Finset.disjoint_left]
        rintro ⟨x, y⟩ hleft hright
        simp only [Finset.mem_product, Finset.mem_singleton,
          Finset.mem_range] at hleft
        simp only [Finset.mem_map] at hright
        obtain ⟨⟨x', y'⟩, _hmem, heq⟩ := hright
        have hxSucc : x' + 1 = x := by
          simpa using congrArg Prod.fst heq
        omega

/-- Definition 1.6: the finite size `|lambda(D,v)|`. -/
noncomputable def weierstrassSize {G : CFGraph}
    (hG : _root_.graph_connected G) (v : G.V) (D : CFDiv G) : ℕ :=
  (weierstrassPartition hG v D).card

theorem weierstrassSize_eq_sum {G : CFGraph}
    (hG : _root_.graph_connected G) (v : G.V) (D : CFDiv G) :
    weierstrassSize hG v D =
      ∑ i ∈ Finset.range (genus G).toNat, weierstrassPart G v D i := by
  rw [weierstrassSize, weierstrassPartition]
  change (YoungDiagram.cellsOfRowLens (weierstrassRowLens G v D)).card = _
  rw [card_cellsOfRowLens]
  unfold weierstrassRowLens
  have hSum : ∀ n : ℕ,
      ((List.range n).map (weierstrassPart G v D)).sum =
        ∑ i ∈ Finset.range n, weierstrassPart G v D i := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]
  exact hSum _

/-- The Weierstrass partition of `D` is literally an element of the
once-marked divisor census, witnessed by `D` itself. -/
theorem onceMarkedCensusContains_weierstrassPartition {G : CFGraph}
    (hG : _root_.graph_connected G) (v : G.V) (D : CFDiv G) :
    OnceMarkedCensusContains G v (weierstrassPartition hG v D) := by
  refine ⟨D, ?_⟩
  intro i
  rw [weierstrassPartition_part hG v D i]
  have hCast := weierstrassPart_cast hG v D i
  unfold weierstrassPartInt at hCast
  have hCoefficient :
      (i : ℤ) + genus G - deg D - (weierstrassPart G v D i : ℤ) =
        poleOrder G v D i := by
    omega
  rw [hCoefficient]
  exact poleOrder_rank_ge hG v D i

/-- A census partition witnessed by `D` is contained in the actual
Weierstrass partition of `D`.  This is the monotonicity bridge needed in
Section 6: the census definition asks only for a rank lower bound at each
row, whereas pole orders record the least such twist. -/
theorem census_partition_le_weierstrassPartition {G : CFGraph}
    (hG : _root_.graph_connected G) (v : G.V) (D : CFDiv G)
    (lambda : YoungDiagram)
    (hRows : ∀ i : ℕ,
      rank G (D + ((i : ℤ) + genus G - deg D -
        (onceMarkedPart lambda i : ℤ)) • one_chip v) ≥ (i : ℤ)) :
    lambda ≤ weierstrassPartition hG v D := by
  rw [← YoungDiagram.cells_subset_iff]
  intro cell hCell
  rcases cell with ⟨i, j⟩
  have hj : j < onceMarkedPart lambda i := by
    rw [onceMarkedPart_eq_rowLen]
    exact YoungDiagram.mem_iff_lt_rowLen.mp hCell
  have hPole := poleOrder_le_of_rank_ge hG v D i
    ((i : ℤ) + genus G - deg D - (onceMarkedPart lambda i : ℤ)) (hRows i)
  have hPartCast := weierstrassPart_cast hG v D i
  have hPart : onceMarkedPart lambda i ≤ weierstrassPart G v D i := by
    unfold weierstrassPartInt at hPartCast
    omega
  change (i, j) ∈ weierstrassPartition hG v D
  rw [YoungDiagram.mem_iff_lt_rowLen, weierstrassPartition_rowLen]
  exact lt_of_lt_of_le hj hPart

/-- Consequently every census partition is no larger than the Weierstrass
partition of its witness divisor. -/
theorem census_card_le_weierstrassSize {G : CFGraph}
    (hG : _root_.graph_connected G) (v : G.V) (lambda : YoungDiagram)
    (hCensus : OnceMarkedCensusContains G v lambda) :
    lambda.card ≤ weierstrassSize hG v (Classical.choose hCensus) := by
  classical
  let D : CFDiv G := Classical.choose hCensus
  have hRows : ∀ i : ℕ,
      rank G (D + ((i : ℤ) + genus G - deg D -
        (onceMarkedPart lambda i : ℤ)) • one_chip v) ≥ (i : ℤ) :=
    Classical.choose_spec hCensus
  change lambda.card ≤ weierstrassSize hG v D
  exact Finset.card_le_card
    (show lambda.cells ⊆ (weierstrassPartition hG v D).cells from
      (YoungDiagram.cells_subset_iff.mp
        (census_partition_le_weierstrassPartition hG v D lambda hRows)))

end Bananas
