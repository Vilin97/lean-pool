/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaBoundarySubmodularity
public import LeanPool.BrillNoetherGraphs.Bananas.Wedge.WedgeSubmodularity
public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.CycleRigidity
public import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionWedge
public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexWedgeGenusOne

/-!
# The same-loop branch for a chain of two loops

The graph is the vertex wedge of two positive two-path cycles.  This file
isolates the same-left-side argument in paper Proposition 3.7.
-/

@[expose] public section

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph

section Generic

/-- On a connected genus-one graph every positive-degree divisor has the
Riemann--Roch rank `deg D - 1`. -/
theorem genusOne_rank_eq_degree_sub_one
    {G : CFGraph} (hG : _root_.graphConnected G) (hGenus : genus G = 1)
    (D : CFDiv G) (hDegree : 0 < deg D) :
    rank G D = deg D - 1 := by
  have hDualDegree : deg (canonicalDivisor G - D) < 0 := by
    rw [deg.map_sub, degree_of_canonical_divisor, hGenus]
    omega
  have hDualRank := rank_neg_one_of_deg_neg G
    (canonicalDivisor G - D) hDualDegree
  have hRR := riemann_roch_for_graphs hG D
  rw [hDualRank, hGenus] at hRR
  omega

private theorem mark_difference_principal_of_two_residuals
    {G : CFGraph} {D U V : CFDiv G}
    (hU : linearEquiv G (D - U) 0)
    (hV : linearEquiv G (D - V) 0) :
    linearEquiv G (U - V) 0 := by
  unfold linearEquiv at hU hV ⊢
  have hSub := AddSubgroup.sub_mem (principalDivisors G) hV hU
  convert hSub using 1
  abel_nf

/-- Distinct degree-one classes on a connected genus-one graph make every
divisor submodular.  This is the factor-level submodularity input for the
opposite-side vertex-wedge branch of the genus-two classification. -/
theorem allSubmodular_of_connected_genus_one_distinct_classes
    {G : CFGraph} (hG : _root_.graphConnected G) (hGenus : genus G = 1)
    (u v : G.V)
    (hMarks : ¬ linearEquiv G (oneChip u - oneChip v) 0) :
    AllSubmodular (mark G u v) := by
  apply allSubmodular_mark_of_rankDelta_nonneg
  intro D
  let d := deg D
  have hDegU : deg (D - oneChip u) = d - 1 := by
    dsimp [d]
    rw [deg.map_sub, deg_one_chip]
  have hDegV : deg (D - oneChip v) = d - 1 := by
    dsimp [d]
    rw [deg.map_sub, deg_one_chip]
  have hDegUV : deg (D - oneChip u - oneChip v) = d - 2 := by
    dsimp [d]
    rw [deg.map_sub, deg.map_sub, deg_one_chip, deg_one_chip]
    omega
  by_cases hdNeg : d < 0
  · have hD := rank_neg_one_of_deg_neg G D (by simpa [d] using hdNeg)
    have hU := rank_neg_one_of_deg_neg G (D - oneChip u) (by omega)
    have hV := rank_neg_one_of_deg_neg G (D - oneChip v) (by omega)
    have hUV := rank_neg_one_of_deg_neg G
      (D - oneChip u - oneChip v) (by omega)
    unfold rankDelta mark
    rw [hD, hU, hV, hUV]
    norm_num
  · by_cases hdZero : d = 0
    · have hDich : rank G D = 0 ∨ rank G D = -1 := by
        have hLower := rank_geq_neg_one G D
        by_cases hNonneg : 0 ≤ rank G D
        · left
          have hUpper := rank_le_degree G D (rank G D) hNonneg
            ((rank_geq_iff G D (rank G D)).mpr le_rfl)
          dsimp [d] at hdZero
          omega
        · right
          omega
      have hU := rank_neg_one_of_deg_neg G (D - oneChip u) (by omega)
      have hV := rank_neg_one_of_deg_neg G (D - oneChip v) (by omega)
      have hUV := rank_neg_one_of_deg_neg G
        (D - oneChip u - oneChip v) (by omega)
      unfold rankDelta mark
      rcases hDich with hD | hD <;> rw [hD, hU, hV, hUV] <;> norm_num
    · by_cases hdOne : d = 1
      · have hD := genusOne_rank_eq_degree_sub_one hG hGenus D (by omega)
        have hDZero : rank G D = 0 := by
          rw [hD]
          dsimp [d] at hdOne
          omega
        have hDegUZero : deg (D - oneChip u) = 0 := by omega
        have hDegVZero : deg (D - oneChip v) = 0 := by omega
        have hUDich : rank G (D - oneChip u) = 0 ∨
            rank G (D - oneChip u) = -1 := by
          have hLower := rank_geq_neg_one G (D - oneChip u)
          by_cases hNonneg : 0 ≤ rank G (D - oneChip u)
          · left
            have hUpper := rank_le_degree G (D - oneChip u)
              (rank G (D - oneChip u)) hNonneg
              ((rank_geq_iff G _ _).mpr le_rfl)
            omega
          · right
            omega
        have hVDich : rank G (D - oneChip v) = 0 ∨
            rank G (D - oneChip v) = -1 := by
          have hLower := rank_geq_neg_one G (D - oneChip v)
          by_cases hNonneg : 0 ≤ rank G (D - oneChip v)
          · left
            have hUpper := rank_le_degree G (D - oneChip v)
              (rank G (D - oneChip v)) hNonneg
              ((rank_geq_iff G _ _).mpr le_rfl)
            omega
          · right
            omega
        have hUV := rank_neg_one_of_deg_neg G
          (D - oneChip u - oneChip v) (by omega)
        rcases hUDich with hU | hU <;> rcases hVDich with hV | hV
        · exfalso
          apply hMarks
          exact mark_difference_principal_of_two_residuals
            (linear_equiv_zero_of_winnable_deg_zero G _
              ((rank_nonneg_iff_winnable G _).mp
                ((rank_geq_iff G _ 0).mpr (by omega))) hDegUZero)
            (linear_equiv_zero_of_winnable_deg_zero G _
              ((rank_nonneg_iff_winnable G _).mp
                ((rank_geq_iff G _ 0).mpr (by omega))) hDegVZero)
        all_goals
          unfold rankDelta mark
          rw [hDZero, hU, hV, hUV]
          norm_num
      · by_cases hdTwo : d = 2
        · have hD := genusOne_rank_eq_degree_sub_one hG hGenus D (by omega)
          have hU := genusOne_rank_eq_degree_sub_one hG hGenus
            (D - oneChip u) (by omega)
          have hV := genusOne_rank_eq_degree_sub_one hG hGenus
            (D - oneChip v) (by omega)
          have hUVDich : rank G (D - oneChip u - oneChip v) = 0 ∨
              rank G (D - oneChip u - oneChip v) = -1 := by
            have hLower := rank_geq_neg_one G (D - oneChip u - oneChip v)
            by_cases hNonneg : 0 ≤ rank G (D - oneChip u - oneChip v)
            · left
              have hUpper := rank_le_degree G
                (D - oneChip u - oneChip v)
                (rank G (D - oneChip u - oneChip v)) hNonneg
                ((rank_geq_iff G _ _).mpr le_rfl)
              omega
            · right
              omega
          unfold rankDelta mark
          rcases hUVDich with hUV | hUV <;>
            rw [hD, hU, hV, hUV] <;> omega
        · have hD := genusOne_rank_eq_degree_sub_one hG hGenus D (by omega)
          have hU := genusOne_rank_eq_degree_sub_one hG hGenus
            (D - oneChip u) (by omega)
          have hV := genusOne_rank_eq_degree_sub_one hG hGenus
            (D - oneChip v) (by omega)
          have hUV := genusOne_rank_eq_degree_sub_one hG hGenus
            (D - oneChip u - oneChip v) (by omega)
          unfold rankDelta mark
          rw [hD, hU, hV, hUV]
          omega

private theorem rank_wedgeLiftLeft_eq_zero_of_rank_zero
    (G H : CFGraph) (x : G.V) (y : H.V)
    (hH : PointedGenusOneRigid H y) (D : CFDiv G)
    (hRank : rank G D = 0) :
    rank (vertexWedge G H x y) (wedgeLiftLeftDivisor G H x y D) = 0 := by
  have hWinG : winnable G D :=
    (rank_nonneg_iff_winnable G D).mp
      ((rank_geq_iff G D 0).mpr (by omega))
  have hWinH : winnable H (0 : CFDiv H) :=
    winnable_of_effective H 0 (by intro z; simp)
  have hWinW := winnable_wedgeAddDivisor G H x y D 0 hWinG hWinH
  have hNonneg : 0 ≤ rank (vertexWedge G H x y)
      (wedgeLiftLeftDivisor G H x y D) := by
    exact (rank_geq_iff _ _ 0).mp
      ((rank_nonneg_iff_winnable _ _).mpr hWinW)
  have hNotOne : ¬ rank (vertexWedge G H x y)
      (wedgeLiftLeftDivisor G H x y D) ≥ 1 := by
    intro hOne
    have hLeft := (rank_wedgeLiftLeft_ge_one_iff G H x y hH D).mp hOne
    omega
  omega

theorem wedge_left_difference
    (G H : CFGraph) (x : G.V) (y : H.V) (a b : G.V) :
    oneChip (G := vertexWedge G H x y) (Sum.inl a) -
        oneChip (G := vertexWedge G H x y) (Sum.inl b) =
      wedgeLiftLeftDivisor G H x y (oneChip a - oneChip b) := by
  rw [← wedgeAddDivisor_one_chip_left G H x y a,
    ← wedgeAddDivisor_one_chip_left G H x y b,
    wedgeAddDivisor_sub]
  rfl

/-- A pair of left-factor chips is the wedge lift of the corresponding
left-factor divisor. -/
theorem wedge_left_pair
    (G H : CFGraph) (x : G.V) (y : H.V) (a b : G.V) :
    oneChip (G := vertexWedge G H x y) (Sum.inl a) +
        oneChip (G := vertexWedge G H x y) (Sum.inl b) =
      wedgeLiftLeftDivisor G H x y (oneChip a + oneChip b) := by
  rw [← wedgeAddDivisor_one_chip_left G H x y a,
    ← wedgeAddDivisor_one_chip_left G H x y b,
    wedgeAddDivisor_add]
  rfl

theorem left_mark_difference_not_principal
    (G H : CFGraph) (x u : G.V) (y : H.V)
    (hG : PointedGenusOneRigid G x) (hu : u ≠ x) :
    ¬ linearEquiv (vertexWedge G H x y)
      (oneChip (Sum.inl x) - oneChip (Sum.inl u)) 0 := by
  intro hPrin
  have hWin : winnable (vertexWedge G H x y)
      (wedgeLiftLeftDivisor G H x y (oneChip x - oneChip u)) := by
    rw [← wedge_left_difference G H x y x u]
    exact winnable_equiv_winnable _ _ _
      (winnable_of_effective _ 0 (by intro z; simp)) hPrin.symm
  obtain ⟨t, hLeft, hRight⟩ :=
    (winnable_vertexWedge_iff_exists_chipShift G H x y
      (oneChip x - oneChip u) 0).mp hWin
  have htNonneg : 0 ≤ t := by
    have hDeg := deg_nonneg_of_winnable G _ hLeft
    rw [chipShift, deg.map_add, map_zsmul, deg.map_sub,
      deg_one_chip, deg_one_chip] at hDeg
    simp at hDeg
    omega
  have htNonpos : t ≤ 0 := by
    have hDeg := deg_nonneg_of_winnable H _ hRight
    rw [chipShift, deg.map_add, map_zsmul, deg_one_chip] at hDeg
    simp at hDeg
    omega
  have ht : t = 0 := by omega
  subst t
  have hLeftZero : linearEquiv G (oneChip x - oneChip u) 0 :=
    linear_equiv_zero_of_winnable_deg_zero G _
      (by simpa [chipShift] using hLeft)
      (by rw [deg.map_sub, deg_one_chip, deg_one_chip]; norm_num)
  exact hG.nontrivial u hu hLeftZero

private theorem swapped_difference_not_principal
    {G : CFGraph} (x u : G.V)
    (h : ¬ linearEquiv G (oneChip x - oneChip u) 0) :
    ¬ linearEquiv G (oneChip u - oneChip x) 0 := by
  intro hSwap
  apply h
  unfold linearEquiv at hSwap ⊢
  simpa [sub_eq_add_neg, add_comm] using
    AddSubgroup.neg_mem (principalDivisors G) hSwap

private theorem wedgeLiftLeft_not_winnable_of_degree_zero_not_principal
    (G H : CFGraph) (x : G.V) (y : H.V) (D : CFDiv G)
    (hDegree : deg D = 0) (hNotPrincipal : ¬ linearEquiv G D 0) :
    ¬ winnable (vertexWedge G H x y) (wedgeLiftLeftDivisor G H x y D) := by
  intro hWin
  obtain ⟨t, hLeft, hRight⟩ :=
    (winnable_vertexWedge_iff_exists_chipShift G H x y D 0).mp hWin
  have htNonneg : 0 ≤ t := by
    have hDeg := deg_nonneg_of_winnable G _ hLeft
    rw [chipShift, deg.map_add, map_zsmul, deg_one_chip, hDegree] at hDeg
    simp at hDeg
    omega
  have htNonpos : t ≤ 0 := by
    have hDeg := deg_nonneg_of_winnable H _ hRight
    rw [chipShift, deg.map_add, map_zsmul, deg_one_chip] at hDeg
    simp at hDeg
    omega
  have ht : t = 0 := by omega
  subst t
  apply hNotPrincipal
  exact linear_equiv_zero_of_winnable_deg_zero G D
    (by simpa [chipShift] using hLeft) hDegree

/-- If a genus-one left factor contains a third vertex besides the two marks,
the divisor consisting of the gluing mark and that third vertex has negative
marked second difference after attaching a rigid genus-one right factor. -/
theorem rankDelta_wedgeLiftLeft_pair_neg
    (G H : CFGraph) (x u w : G.V) (y : H.V)
    (hGconn : _root_.graphConnected G) (hGgenus : genus G = 1)
    (hGx : PointedGenusOneRigid G x) (hGu : PointedGenusOneRigid G u)
    (hH : PointedGenusOneRigid H y)
    (hwx : w ≠ x) (hwu : w ≠ u) :
    rankDelta
        (mark (vertexWedge G H x y) (Sum.inl x) (Sum.inl u))
        (wedgeLiftLeftDivisor G H x y (oneChip x + oneChip w)) < 0 := by
  let A : CFDiv G := oneChip x + oneChip w
  have hRankALeft : rank G A = 1 := by
    have h := genusOne_rank_eq_degree_sub_one hGconn hGgenus A (by
      dsimp [A]
      rw [deg.map_add, deg_one_chip, deg_one_chip]
      norm_num)
    rw [show deg A = 2 by
      dsimp [A]
      rw [deg.map_add, deg_one_chip, deg_one_chip]
      norm_num] at h
    exact h
  have hResidualEq : A - (2 : ℤ) • oneChip x = oneChip w - oneChip x := by
    dsimp [A]
    abel
  have hResidualNotPrincipal :
      ¬ linearEquiv G (oneChip w - oneChip x) 0 :=
    swapped_difference_not_principal x w (hGx.nontrivial w hwx)
  have hResidualNotWin : ¬ winnable G (A - (2 : ℤ) • oneChip x) := by
    rw [hResidualEq]
    intro hWin
    apply hResidualNotPrincipal
    exact linear_equiv_zero_of_winnable_deg_zero G _ hWin (by
      rw [deg.map_sub, deg_one_chip, deg_one_chip]
      norm_num)
  have hRankA : rank (vertexWedge G H x y)
      (wedgeLiftLeftDivisor G H x y A) = 0 := by
    have hNotOne : ¬ rank (vertexWedge G H x y)
        (wedgeLiftLeftDivisor G H x y A) ≥ 1 := by
      intro hOne
      exact hResidualNotWin
        ((rank_wedgeLiftLeft_ge_one_iff G H x y hH A).mp hOne).2
    have hEffectiveA : effective A := by
      intro z
      dsimp [A]
      exact add_nonneg (eff_one_chip x z) (eff_one_chip w z)
    have hEffectiveWedge : effective
        (wedgeLiftLeftDivisor G H x y A) :=
      (effective_wedgeLiftLeftDivisor_iff G H x y A).mpr hEffectiveA
    have hNonneg : 0 ≤ rank (vertexWedge G H x y)
        (wedgeLiftLeftDivisor G H x y A) := by
      exact (rank_geq_iff _ _ 0).mp
        ((rank_nonneg_iff_winnable _ _).mpr
          (winnable_of_effective _ _ hEffectiveWedge))
    omega
  let Ax : CFDiv G := A - oneChip x
  have hRankAxLeft : rank G Ax = 0 := by
    have h := genusOne_rank_eq_degree_sub_one hGconn hGgenus Ax (by
      dsimp [Ax, A]
      norm_num)
    rw [show deg Ax = 1 by
      dsimp [Ax, A]
      norm_num] at h
    exact h
  have hRankAx : rank (vertexWedge G H x y)
      (wedgeLiftLeftDivisor G H x y Ax) = 0 :=
    rank_wedgeLiftLeft_eq_zero_of_rank_zero G H x y hH Ax hRankAxLeft
  let Au : CFDiv G := A - oneChip u
  have hRankAuLeft : rank G Au = 0 := by
    have h := genusOne_rank_eq_degree_sub_one hGconn hGgenus Au (by
      dsimp [Au, A]
      norm_num)
    rw [show deg Au = 1 by
      dsimp [Au, A]
      norm_num] at h
    exact h
  have hRankAu : rank (vertexWedge G H x y)
      (wedgeLiftLeftDivisor G H x y Au) = 0 :=
    rank_wedgeLiftLeft_eq_zero_of_rank_zero G H x y hH Au hRankAuLeft
  let Axu : CFDiv G := A - oneChip x - oneChip u
  have hAxuEq : Axu = oneChip w - oneChip u := by
    dsimp [Axu, A]
    abel
  have hAxuDegree : deg Axu = 0 := by
    rw [hAxuEq, deg.map_sub, deg_one_chip, deg_one_chip]
    norm_num
  have hAxuNotPrincipal : ¬ linearEquiv G Axu 0 := by
    rw [hAxuEq]
    exact swapped_difference_not_principal u w (hGu.nontrivial w hwu)
  have hAxuNotWin := wedgeLiftLeft_not_winnable_of_degree_zero_not_principal
    G H x y Axu hAxuDegree hAxuNotPrincipal
  have hRankAxu : rank (vertexWedge G H x y)
      (wedgeLiftLeftDivisor G H x y Axu) = -1 := by
    have hLower := rank_geq_neg_one (vertexWedge G H x y)
      (wedgeLiftLeftDivisor G H x y Axu)
    have hNotNonneg : ¬ 0 ≤ rank (vertexWedge G H x y)
        (wedgeLiftLeftDivisor G H x y Axu) := by
      intro h
      apply hAxuNotWin
      exact (rank_nonneg_iff_winnable _ _).mp
        ((rank_geq_iff _ _ 0).mpr h)
    omega
  have hSubX :
      wedgeLiftLeftDivisor G H x y A - oneChip (Sum.inl x) =
        wedgeLiftLeftDivisor G H x y Ax := by
    exact wedgeLiftLeft_sub_left G H x y A x
  have hSubU :
      wedgeLiftLeftDivisor G H x y A - oneChip (Sum.inl u) =
        wedgeLiftLeftDivisor G H x y Au := by
    exact wedgeLiftLeft_sub_left G H x y A u
  have hSubXU :
      wedgeLiftLeftDivisor G H x y A - oneChip (Sum.inl x) -
          oneChip (Sum.inl u) =
        wedgeLiftLeftDivisor G H x y Axu := by
    rw [hSubX]
    exact wedgeLiftLeft_sub_left G H x y Ax u
  have hSubAxU :
      wedgeLiftLeftDivisor G H x y Ax - oneChip (Sum.inl u) =
        wedgeLiftLeftDivisor G H x y Axu := by
    exact wedgeLiftLeft_sub_left G H x y Ax u
  unfold rankDelta mark
  rw [hRankA, hSubX, hRankAx, hSubU, hRankAu, hSubAxU, hRankAxu]
  norm_num

/-- When neither mark is the gluing vertex, the gluing vertex itself supplies
the auxiliary chip in the paper's negative-second-difference witness. -/
theorem rankDelta_wedgeLiftLeft_mark_add_glue_neg
    (G H : CFGraph) (x p q : G.V) (y : H.V)
    (hGconn : _root_.graphConnected G) (hGgenus : genus G = 1)
    (hGx : PointedGenusOneRigid G x) (hGq : PointedGenusOneRigid G q)
    (hH : PointedGenusOneRigid H y)
    (hpx : p ≠ x) (hqx : q ≠ x) :
    rankDelta
        (mark (vertexWedge G H x y) (Sum.inl p) (Sum.inl q))
        (wedgeLiftLeftDivisor G H x y (oneChip p + oneChip x)) < 0 := by
  let A : CFDiv G := oneChip p + oneChip x
  have hRankALeft : rank G A = 1 := by
    have h := genusOne_rank_eq_degree_sub_one hGconn hGgenus A (by
      dsimp [A]
      norm_num)
    rw [show deg A = 2 by dsimp [A]; norm_num] at h
    exact h
  have hResidualEq : A - (2 : ℤ) • oneChip x = oneChip p - oneChip x := by
    dsimp [A]
    abel
  have hResidualNotWin : ¬ winnable G (A - (2 : ℤ) • oneChip x) := by
    rw [hResidualEq]
    intro hWin
    have hPrin := linear_equiv_zero_of_winnable_deg_zero G _ hWin (by
      rw [deg.map_sub, deg_one_chip, deg_one_chip]
      norm_num)
    exact (swapped_difference_not_principal x p (hGx.nontrivial p hpx)) hPrin
  have hRankA : rank (vertexWedge G H x y)
      (wedgeLiftLeftDivisor G H x y A) = 0 := by
    have hNotOne : ¬ rank (vertexWedge G H x y)
        (wedgeLiftLeftDivisor G H x y A) ≥ 1 := by
      intro hOne
      exact hResidualNotWin
        ((rank_wedgeLiftLeft_ge_one_iff G H x y hH A).mp hOne).2
    have hEffectiveA : effective A := by
      intro z
      dsimp [A]
      exact add_nonneg (eff_one_chip p z) (eff_one_chip x z)
    have hNonneg : 0 ≤ rank (vertexWedge G H x y)
        (wedgeLiftLeftDivisor G H x y A) := by
      exact (rank_geq_iff _ _ 0).mp
        ((rank_nonneg_iff_winnable _ _).mpr
          (winnable_of_effective _ _
            ((effective_wedgeLiftLeftDivisor_iff G H x y A).mpr hEffectiveA)))
    omega
  let Ap : CFDiv G := A - oneChip p
  have hRankApLeft : rank G Ap = 0 := by
    have h := genusOne_rank_eq_degree_sub_one hGconn hGgenus Ap (by
      dsimp [Ap, A]
      norm_num)
    rw [show deg Ap = 1 by dsimp [Ap, A]; norm_num] at h
    exact h
  have hRankAp : rank (vertexWedge G H x y)
      (wedgeLiftLeftDivisor G H x y Ap) = 0 :=
    rank_wedgeLiftLeft_eq_zero_of_rank_zero G H x y hH Ap hRankApLeft
  let Aq : CFDiv G := A - oneChip q
  have hRankAqLeft : rank G Aq = 0 := by
    have h := genusOne_rank_eq_degree_sub_one hGconn hGgenus Aq (by
      dsimp [Aq, A]
      norm_num)
    rw [show deg Aq = 1 by dsimp [Aq, A]; norm_num] at h
    exact h
  have hRankAq : rank (vertexWedge G H x y)
      (wedgeLiftLeftDivisor G H x y Aq) = 0 :=
    rank_wedgeLiftLeft_eq_zero_of_rank_zero G H x y hH Aq hRankAqLeft
  let Apq : CFDiv G := A - oneChip p - oneChip q
  have hApqEq : Apq = oneChip x - oneChip q := by
    dsimp [Apq, A]
    abel
  have hApqDegree : deg Apq = 0 := by
    rw [hApqEq, deg.map_sub, deg_one_chip, deg_one_chip]
    norm_num
  have hApqNotPrincipal : ¬ linearEquiv G Apq 0 := by
    rw [hApqEq]
    exact swapped_difference_not_principal q x
      (hGq.nontrivial x hqx.symm)
  have hApqNotWin := wedgeLiftLeft_not_winnable_of_degree_zero_not_principal
    G H x y Apq hApqDegree hApqNotPrincipal
  have hRankApq : rank (vertexWedge G H x y)
      (wedgeLiftLeftDivisor G H x y Apq) = -1 := by
    have hLower := rank_geq_neg_one (vertexWedge G H x y)
      (wedgeLiftLeftDivisor G H x y Apq)
    have hNotNonneg : ¬ 0 ≤ rank (vertexWedge G H x y)
        (wedgeLiftLeftDivisor G H x y Apq) := by
      intro h
      apply hApqNotWin
      exact (rank_nonneg_iff_winnable _ _).mp
        ((rank_geq_iff _ _ 0).mpr h)
    omega
  have hSubP :
      wedgeLiftLeftDivisor G H x y A - oneChip (Sum.inl p) =
        wedgeLiftLeftDivisor G H x y Ap :=
    wedgeLiftLeft_sub_left G H x y A p
  have hSubQ :
      wedgeLiftLeftDivisor G H x y A - oneChip (Sum.inl q) =
        wedgeLiftLeftDivisor G H x y Aq :=
    wedgeLiftLeft_sub_left G H x y A q
  have hSubApQ :
      wedgeLiftLeftDivisor G H x y Ap - oneChip (Sum.inl q) =
        wedgeLiftLeftDivisor G H x y Apq :=
    wedgeLiftLeft_sub_left G H x y Ap q
  unfold rankDelta mark
  rw [hRankA, hSubP, hRankAp, hSubQ, hRankAq, hSubApQ, hRankApq]
  norm_num

private theorem wedge_right_aux_pair
    (G H : CFGraph) (x u : G.V) (y : H.V)
    (b : {z : H.V // z ≠ y}) :
    oneChip (G := vertexWedge G H x y) (Sum.inr b) +
        oneChip (G := vertexWedge G H x y) (Sum.inl x) -
        oneChip (G := vertexWedge G H x y) (Sum.inl u) =
      wedgeAddDivisor G H x y (oneChip x - oneChip u) (oneChip b.1) := by
  rw [← wedgeRightVertex_unmarked G H x y b.1 b.2,
    ← wedgeAddDivisor_one_chip_right G H x y b.1,
    ← wedgeAddDivisor_one_chip_left G H x y x,
    ← wedgeAddDivisor_one_chip_left G H x y u,
    wedgeAddDivisor_add, wedgeAddDivisor_sub]
  simp

/-- A chip on the unmarked part of the right rigid factor cannot repair the
degree-zero left marked difference after wedging. -/
theorem wedge_right_aux_pair_not_winnable
    (G H : CFGraph) (x u : G.V) (y : H.V)
    (hG : PointedGenusOneRigid G x) (hH : PointedGenusOneRigid H y)
    (hu : u ≠ x) (b : {z : H.V // z ≠ y}) :
    ¬ winnable (vertexWedge G H x y)
      (oneChip (Sum.inr b) + oneChip (Sum.inl x) - oneChip (Sum.inl u)) := by
  rw [wedge_right_aux_pair G H x u y b]
  intro hWin
  obtain ⟨t, hLeft, hRight⟩ :=
    (winnable_vertexWedge_iff_exists_chipShift G H x y
      (oneChip x - oneChip u) (oneChip b.1)).mp hWin
  have htNonneg : 0 ≤ t := by
    have hDeg := deg_nonneg_of_winnable G _ hLeft
    rw [chipShift, deg.map_add, map_zsmul, deg.map_sub,
      deg_one_chip, deg_one_chip] at hDeg
    simp at hDeg
    omega
  have htLeOne : t ≤ 1 := by
    have hDeg := deg_nonneg_of_winnable H _ hRight
    rw [chipShift, deg.map_add, map_zsmul, deg_one_chip, deg_one_chip] at hDeg
    simp at hDeg
    omega
  by_cases ht : t = 0
  · subst t
    have hPrin : linearEquiv G (oneChip x - oneChip u) 0 :=
      linear_equiv_zero_of_winnable_deg_zero G _
        (by simpa [chipShift] using hLeft)
        (by rw [deg.map_sub, deg_one_chip, deg_one_chip]; norm_num)
    exact hG.nontrivial u hu hPrin
  · have htOne : t = 1 := by omega
    subst t
    have hPrin : linearEquiv H (oneChip b.1 - oneChip y) 0 :=
      linear_equiv_zero_of_winnable_deg_zero H _
        (by
          convert hRight using 1
          unfold chipShift
          abel)
        (by rw [deg.map_sub, deg_one_chip, deg_one_chip]; norm_num)
    exact (swapped_difference_not_principal y b.1
      (hH.nontrivial b.1 b.2)) hPrin

end Generic

private theorem twoPathCycle_card_vertices_eq_total
    (length : Fin 2 → ℕ) (hLength : ∀ edge, 0 < length edge) :
    Fintype.card (TwoPathCycle.spec length hLength).graph.V =
      length 0 + length 1 := by
  rw [(TwoPathCycle.spec length hLength).card_vertices]
  simp only [Fin.sum_univ_two]
  change 2 + ((length 0 - 1) + (length 1 - 1)) =
    length 0 + length 1
  have h0 := hLength 0
  have h1 := hLength 1
  omega

private theorem eq_of_ne_of_card_eq_two
    {X : Type} [Fintype X] [DecidableEq X]
    (hCard : Fintype.card X = 2) {x u w : X}
    (hxu : x ≠ u) (hwu : w ≠ u) : w = x := by
  by_contra hwx
  have hSubset : ({w, x, u} : Finset X) ⊆ Finset.univ := by simp
  have hThree : ({w, x, u} : Finset X).card = 3 := by
    simp [hwx, hwu, hxu]
  have hLe := Finset.card_le_card hSubset
  rw [hThree, Finset.card_univ, hCard] at hLe
  omega

theorem exists_ne_two_of_two_lt_card
    {X : Type} [Fintype X] (x u : X) (hCard : 2 < Fintype.card X) :
    ∃ w : X, w ≠ x ∧ w ≠ u := by
  let e := Fintype.equivFin X
  obtain ⟨k, hkx, hku⟩ :=
    Fin.exists_ne_and_ne_of_two_lt (e x) (e u) hCard
  refine ⟨e.symm k, ?_, ?_⟩
  · intro h
    apply hkx
    simpa using congrArg e h
  · intro h
    apply hku
    simpa using congrArg e h

/-! ## Proposition 3.7, same-loop branch -/

/-- On a vertex wedge of two positive subdivided cycles, with both marks on
the left cycle and one mark at the gluing vertex, every divisor is submodular
exactly when the marked cycle has total combinatorial length two. -/
theorem chainTwoLoops_allSubmodular_same_left_iff
    (leftLength rightLength : Fin 2 → ℕ)
    (hLeftLength : ∀ edge, 0 < leftLength edge)
    (hRightLength : ∀ edge, 0 < rightLength edge)
    (leftGlue u : (TwoPathCycle.spec leftLength hLeftLength).graph.V)
    (rightGlue : (TwoPathCycle.spec rightLength hRightLength).graph.V)
    (hu : u ≠ leftGlue) :
    AllSubmodular
        (mark
          (vertexWedge
            (TwoPathCycle.spec leftLength hLeftLength).graph
            (TwoPathCycle.spec rightLength hRightLength).graph
            leftGlue rightGlue)
          (Sum.inl leftGlue) (Sum.inl u)) ↔
      leftLength 0 + leftLength 1 = 2 := by
  let G := (TwoPathCycle.spec leftLength hLeftLength).graph
  let H := (TwoPathCycle.spec rightLength hRightLength).graph
  let W := vertexWedge G H leftGlue rightGlue
  have hGconn : _root_.graphConnected G :=
    TwoPathCycle.connected leftLength hLeftLength
  have hHconn : _root_.graphConnected H :=
    TwoPathCycle.connected rightLength hRightLength
  have hGgenus : genus G = 1 :=
    TwoPathCycle.genus_one leftLength hLeftLength
  have hHgenus : genus H = 1 :=
    TwoPathCycle.genus_one rightLength hRightLength
  have hWconn : _root_.graphConnected W :=
    graph_connected_vertexWedge G H leftGlue rightGlue hGconn hHconn
  have hWgenus : genus W = 2 := by
    dsimp [W]
    rw [genus_vertexWedge, hGgenus, hHgenus]
    norm_num
  have hGx : PointedGenusOneRigid G leftGlue :=
    TwoPathCycle.pointedGenusOneRigid leftLength hLeftLength leftGlue
  have hGu : PointedGenusOneRigid G u :=
    TwoPathCycle.pointedGenusOneRigid leftLength hLeftLength u
  have hH : PointedGenusOneRigid H rightGlue :=
    TwoPathCycle.pointedGenusOneRigid rightLength hRightLength rightGlue
  have hDistinct : ¬ linearEquiv W
      (oneChip (Sum.inl leftGlue) - oneChip (Sum.inl u)) 0 :=
    left_mark_difference_not_principal G H leftGlue u rightGlue hGx hu
  constructor
  · intro hSub
    change AllSubmodular (mark W (Sum.inl leftGlue) (Sum.inl u)) at hSub
    by_contra hNotTwo
    have hAtLeastTwo : 2 ≤ leftLength 0 + leftLength 1 := by
      have h0 := hLeftLength 0
      have h1 := hLeftLength 1
      omega
    have hCard : 2 < Fintype.card G.V := by
      rw [twoPathCycle_card_vertices_eq_total leftLength hLeftLength]
      omega
    obtain ⟨w, hwGlue, hwu⟩ :=
      exists_ne_two_of_two_lt_card leftGlue u hCard
    have hNeg := rankDelta_wedgeLiftLeft_pair_neg
      G H leftGlue u w rightGlue hGconn hGgenus hGx hGu hH hwGlue hwu
    change rankDelta (mark W (Sum.inl leftGlue) (Sum.inl u))
      (wedgeLiftLeftDivisor G H leftGlue rightGlue
        (oneChip leftGlue + oneChip w)) < 0 at hNeg
    have hNonneg := (allSubmodular_iff_rankDelta_nonneg
      (mark W (Sum.inl leftGlue) (Sum.inl u))).mp hSub
      (wedgeLiftLeftDivisor G H leftGlue rightGlue
        (oneChip leftGlue + oneChip w))
    omega
  · intro hLengthTwo
    change AllSubmodular (mark W (Sum.inl leftGlue) (Sum.inl u))
    rw [allSubmodular_iff_rankDelta_nonneg]
    intro D
    change CFDiv W at D
    by_contra hNotNonneg
    have hNeg : rankDelta
        (mark W (Sum.inl leftGlue) (Sum.inl u)) D < 0 := by omega
    have hRankD : rank W D = 0 :=
      rank_eq_zero_of_rankDelta_neg_genus_two
        (mark W (Sum.inl leftGlue) (Sum.inl u)) D
        hWconn hWgenus hDistinct hNeg
    obtain ⟨w, hRep, _hRed, hwu, hPair⟩ :=
      exists_vertex_rep_of_rankDelta_neg_genus_two W
        (Sum.inl leftGlue) (Sum.inl u) D
        hWconn hWgenus hDistinct hNeg
    cases w with
    | inl a =>
        have hau : a ≠ u := by
          intro h
          apply hwu
          exact congrArg Sum.inl h
        have hCardTwo : Fintype.card G.V = 2 := by
          rw [twoPathCycle_card_vertices_eq_total leftLength hLeftLength]
          exact hLengthTwo
        have ha : a = leftGlue :=
          eq_of_ne_of_card_eq_two hCardTwo hu.symm hau
        subst a
        have hDPair : linearEquiv W D
            (oneChip (Sum.inl leftGlue) + oneChip (Sum.inl leftGlue)) := by
          unfold linearEquiv at hRep ⊢
          have hEq :
              (oneChip (Sum.inl leftGlue) + oneChip (Sum.inl leftGlue) - D :
                CFDiv W) =
              oneChip (Sum.inl leftGlue) -
                (D - oneChip (Sum.inl leftGlue)) := by
            abel
          rw [hEq]
          exact hRep
        let A : CFDiv G := oneChip leftGlue + oneChip leftGlue
        have hRankALeft : rank G A = 1 := by
          have h := genusOne_rank_eq_degree_sub_one hGconn hGgenus A (by
            dsimp [A]
            norm_num)
          rw [show deg A = 2 by
            dsimp [A]
            norm_num] at h
          exact h
        have hResidual : winnable G (A - (2 : ℤ) • oneChip leftGlue) := by
          have hZero : A - (2 : ℤ) • oneChip leftGlue = 0 := by
            dsimp [A]
            abel
          rw [hZero]
          exact winnable_of_effective G 0 (by intro z; simp)
        have hRankPair : rank W
            (wedgeLiftLeftDivisor G H leftGlue rightGlue A) ≥ 1 :=
          (rank_wedgeLiftLeft_ge_one_iff G H leftGlue rightGlue hH A).mpr
            ⟨by omega, hResidual⟩
        have hPairEq :
            oneChip (G := W) (Sum.inl leftGlue) +
                oneChip (G := W) (Sum.inl leftGlue) =
              wedgeLiftLeftDivisor G H leftGlue rightGlue A := by
          exact wedge_left_pair G H leftGlue rightGlue leftGlue leftGlue
        have hRankEq := rank_eq_of_linear_equiv W hDPair
        rw [hRankD, hPairEq] at hRankEq
        omega
    | inr b =>
        have hNotWin := wedge_right_aux_pair_not_winnable
          G H leftGlue u rightGlue hGx hH hu b
        apply hNotWin
        exact (rank_nonneg_iff_winnable W _).mp
          ((rank_geq_iff W _ 0).mpr (by omega))

/-- Any two distinct vertices on a positive subdivided cycle define an
all-submodular twice-marking. -/
private theorem twoPathCycle_allSubmodular_of_ne
    (length : Fin 2 → ℕ) (hLength : ∀ edge, 0 < length edge)
    (u v : (TwoPathCycle.spec length hLength).graph.V) (huv : u ≠ v) :
    AllSubmodular (mark (TwoPathCycle.spec length hLength).graph u v) := by
  apply allSubmodular_of_connected_genus_one_distinct_classes
    (TwoPathCycle.connected length hLength)
    (TwoPathCycle.genus_one length hLength)
  have hRigid := TwoPathCycle.pointedGenusOneRigid length hLength v
  exact swapped_difference_not_principal v u (hRigid.nontrivial u huv)

/-- Distinct-loop clause of Proposition 3.7 for arbitrary non-gluing marks on
the two cycle factors. -/
theorem chainTwoLoops_allSubmodular_opposite
    (leftLength rightLength : Fin 2 → ℕ)
    (hLeftLength : ∀ edge, 0 < leftLength edge)
    (hRightLength : ∀ edge, 0 < rightLength edge)
    (leftGlue p : (TwoPathCycle.spec leftLength hLeftLength).graph.V)
    (rightGlue q : (TwoPathCycle.spec rightLength hRightLength).graph.V)
    (hp : p ≠ leftGlue) (hq : q ≠ rightGlue) :
    AllSubmodular
      (mark
        (vertexWedge
          (TwoPathCycle.spec leftLength hLeftLength).graph
          (TwoPathCycle.spec rightLength hRightLength).graph
          leftGlue rightGlue)
        (Sum.inl p)
        (wedgeRightVertex
          (TwoPathCycle.spec leftLength hLeftLength).graph
          (TwoPathCycle.spec rightLength hRightLength).graph
          leftGlue rightGlue q)) := by
  apply allSubmodular_vertexWedge_opposite
  · exact TwoPathCycle.connected leftLength hLeftLength
  · exact TwoPathCycle.connected rightLength hRightLength
  · exact twoPathCycle_allSubmodular_of_ne
      leftLength hLeftLength p leftGlue hp
  · exact twoPathCycle_allSubmodular_of_ne
      rightLength hRightLength rightGlue q hq.symm

/-- The missing arbitrary-mark negative direction of Proposition 3.7.  If a
left loop has at least three vertices, every pair of distinct marks on that
loop admits a negative-`rankDelta` divisor, whether or not either mark is the
gluing vertex. -/
theorem chainTwoLoops_not_allSubmodular_same_left_of_two_lt_length
    (leftLength rightLength : Fin 2 → ℕ)
    (hLeftLength : ∀ edge, 0 < leftLength edge)
    (hRightLength : ∀ edge, 0 < rightLength edge)
    (leftGlue p q : (TwoPathCycle.spec leftLength hLeftLength).graph.V)
    (rightGlue : (TwoPathCycle.spec rightLength hRightLength).graph.V)
    (hpq : p ≠ q) (hLength : 2 < leftLength 0 + leftLength 1) :
    ¬ AllSubmodular
        (mark
          (vertexWedge
            (TwoPathCycle.spec leftLength hLeftLength).graph
            (TwoPathCycle.spec rightLength hRightLength).graph
            leftGlue rightGlue)
          (Sum.inl p) (Sum.inl q)) := by
  let G := (TwoPathCycle.spec leftLength hLeftLength).graph
  let H := (TwoPathCycle.spec rightLength hRightLength).graph
  let W := vertexWedge G H leftGlue rightGlue
  intro hSub
  change AllSubmodular (mark W (Sum.inl p) (Sum.inl q)) at hSub
  by_cases hp : p = leftGlue
  · subst p
    have hNodeSub : AllSubmodular
        (mark W (Sum.inl leftGlue) (Sum.inl q)) := hSub
    have hTwo := (chainTwoLoops_allSubmodular_same_left_iff
      leftLength rightLength hLeftLength hRightLength leftGlue q rightGlue
      hpq.symm).mp hNodeSub
    omega
  · by_cases hq : q = leftGlue
    · subst q
      have hSwapped := allSubmodular_mark_swap W
        (Sum.inl p) (Sum.inl leftGlue) hSub
      have hTwo := (chainTwoLoops_allSubmodular_same_left_iff
        leftLength rightLength hLeftLength hRightLength leftGlue p rightGlue
        hpq).mp hSwapped
      omega
    · have hGconn : _root_.graphConnected G :=
        TwoPathCycle.connected leftLength hLeftLength
      have hGgenus : genus G = 1 :=
        TwoPathCycle.genus_one leftLength hLeftLength
      have hGx : PointedGenusOneRigid G leftGlue :=
        TwoPathCycle.pointedGenusOneRigid leftLength hLeftLength leftGlue
      have hGq : PointedGenusOneRigid G q :=
        TwoPathCycle.pointedGenusOneRigid leftLength hLeftLength q
      have hH : PointedGenusOneRigid H rightGlue :=
        TwoPathCycle.pointedGenusOneRigid rightLength hRightLength rightGlue
      have hNeg := rankDelta_wedgeLiftLeft_mark_add_glue_neg
        G H leftGlue p q rightGlue hGconn hGgenus hGx hGq hH hp hq
      change rankDelta (mark W (Sum.inl p) (Sum.inl q))
        (wedgeLiftLeftDivisor G H leftGlue rightGlue
          (oneChip p + oneChip leftGlue)) < 0 at hNeg
      have hNonneg := (allSubmodular_iff_rankDelta_nonneg
        (mark W (Sum.inl p) (Sum.inl q))).mp hSub
        (wedgeLiftLeftDivisor G H leftGlue rightGlue
          (oneChip p + oneChip leftGlue))
      omega

/-- Full same-loop clause of Proposition 3.7 for arbitrary distinct marks on
the left loop.  When the loop has length two, distinctness forces its two
vertices to be precisely the marks; at every larger length the preceding
explicit witness gives non-submodularity. -/
theorem chainTwoLoops_allSubmodular_same_left_arbitrary_iff
    (leftLength rightLength : Fin 2 → ℕ)
    (hLeftLength : ∀ edge, 0 < leftLength edge)
    (hRightLength : ∀ edge, 0 < rightLength edge)
    (leftGlue p q : (TwoPathCycle.spec leftLength hLeftLength).graph.V)
    (rightGlue : (TwoPathCycle.spec rightLength hRightLength).graph.V)
    (hpq : p ≠ q) :
    AllSubmodular
        (mark
          (vertexWedge
            (TwoPathCycle.spec leftLength hLeftLength).graph
            (TwoPathCycle.spec rightLength hRightLength).graph
            leftGlue rightGlue)
          (Sum.inl p) (Sum.inl q)) ↔
      leftLength 0 + leftLength 1 = 2 := by
  let G := (TwoPathCycle.spec leftLength hLeftLength).graph
  let H := (TwoPathCycle.spec rightLength hRightLength).graph
  let W := vertexWedge G H leftGlue rightGlue
  constructor
  · intro hSub
    have hAtLeastTwo : 2 ≤ leftLength 0 + leftLength 1 := by
      have h0 := hLeftLength 0
      have h1 := hLeftLength 1
      omega
    by_contra hNotTwo
    have hGreater : 2 < leftLength 0 + leftLength 1 := by omega
    exact (chainTwoLoops_not_allSubmodular_same_left_of_two_lt_length
      leftLength rightLength hLeftLength hRightLength leftGlue p q rightGlue
      hpq hGreater) hSub
  · intro hTwo
    have hCardTwo : Fintype.card G.V = 2 := by
      rw [twoPathCycle_card_vertices_eq_total leftLength hLeftLength]
      exact hTwo
    by_cases hp : p = leftGlue
    · subst p
      exact (chainTwoLoops_allSubmodular_same_left_iff
        leftLength rightLength hLeftLength hRightLength leftGlue q rightGlue
        hpq.symm).mpr hTwo
    · have hq : q = leftGlue := by
        have hxq : leftGlue = q :=
          eq_of_ne_of_card_eq_two hCardTwo hpq.symm (Ne.symm hp)
        exact hxq.symm
      subst q
      apply allSubmodular_mark_swap W
        (Sum.inl leftGlue) (Sum.inl p)
      exact (chainTwoLoops_allSubmodular_same_left_iff
        leftLength rightLength hLeftLength hRightLength leftGlue p rightGlue
        hp).mpr hTwo

end Bananas
