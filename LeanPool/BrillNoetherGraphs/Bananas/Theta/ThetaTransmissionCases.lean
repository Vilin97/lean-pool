/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Classification.GenusTwoDegreeTwo
import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffTransmission
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.GenericFarWitness

/-!
# Elementary rows in the theta transmission case table

This module starts the direct rank-difference portion of Proposition 4.5.
The remaining task is the exhaustive classification of the default case; the
exceptional rows below are graph-independent once their stated divisor-class
conditions hold.
-/

namespace Bananas

open Utilities

/-- The marked second rank difference of the zero divisor is one. -/
theorem rankDelta_zero_eq_one (M : TwiceMarked) :
    rankDelta M (0 : CFDiv M.graph) = 1 := by
  have hU : rank M.graph ((0 : CFDiv M.graph) - oneChip M.u) = -1 := by
    apply rank_neg_one_of_deg_neg
    rw [deg.map_sub, map_zero, deg_one_chip]
    norm_num
  have hV : rank M.graph ((0 : CFDiv M.graph) - oneChip M.v) = -1 := by
    apply rank_neg_one_of_deg_neg
    rw [deg.map_sub, map_zero, deg_one_chip]
    norm_num
  have hUV : rank M.graph
      ((0 : CFDiv M.graph) - oneChip M.u - oneChip M.v) = -1 := by
    apply rank_neg_one_of_deg_neg
    rw [deg.map_sub, deg.map_sub, map_zero, deg_one_chip, deg_one_chip]
    norm_num
  unfold rankDelta
  rw [zero_divisor_rank, hU, hV, hUV]
  norm_num

/-- The first row in Proposition 4.5: if the degree-two twist at `t` is
`2u`, then the transmission permutation takes `t` to `t - 2`. -/
theorem transmission_eq_sub_two_of_linearEquiv_two_u
    {M : TwiceMarked} {D : CFDiv M.graph} {tau : ℤ → ℤ} (t : ℤ)
    (hTau : IsTransmissionPermutation M D tau)
    (hClass : linearEquiv M.graph
      (D + t • (oneChip M.u - oneChip M.v))
      (2 • oneChip M.u)) :
    tau t = t - 2 := by
  apply transmission_value_of_linearEquiv_rankDelta_eq_one hTau
    (E := (0 : CFDiv M.graph))
  · unfold linearEquiv at hClass ⊢
    convert hClass using 1
    ext x
    simp only [Pi.zero_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    ring
  · exact rankDelta_zero_eq_one M

/-- A one-chip divisor has marked second difference one when its class is
different from both marked one-chip classes. -/
theorem rankDelta_one_chip_eq_one_of_distinct_mark_classes
    (B : Banana 2) (u v w : B.graph.V)
    (hwu : ¬ linearEquiv B.graph (oneChip w - oneChip u) 0)
    (hwv : ¬ linearEquiv B.graph (oneChip w - oneChip v) 0) :
    rankDelta (mark B.graph u v) (oneChip w) = 1 := by
  have hW : rank B.graph (oneChip w) = 0 := rank_one_chip_zero_banana_two B w
  have hWU : rank B.graph (oneChip w - oneChip u) = -1 := by
    have hLower := rank_geq_neg_one B.graph (oneChip w - oneChip u)
    by_contra hNot
    have hNonneg : 0 ≤ rank B.graph (oneChip w - oneChip u) := by omega
    exact hwu (linearEquiv_zero_of_rank_nonneg_degree_zero' B.graph _ hNonneg (by
      rw [deg.map_sub, deg_one_chip, deg_one_chip]
      norm_num))
  have hWV : rank B.graph (oneChip w - oneChip v) = -1 := by
    have hLower := rank_geq_neg_one B.graph (oneChip w - oneChip v)
    by_contra hNot
    have hNonneg : 0 ≤ rank B.graph (oneChip w - oneChip v) := by omega
    exact hwv (linearEquiv_zero_of_rank_nonneg_degree_zero' B.graph _ hNonneg (by
      rw [deg.map_sub, deg_one_chip, deg_one_chip]
      norm_num))
  have hWUV : rank B.graph (oneChip w - oneChip u - oneChip v) = -1 := by
    apply rank_neg_one_of_deg_neg
    rw [deg.map_sub, deg.map_sub, deg_one_chip, deg_one_chip, deg_one_chip]
    norm_num
  change rank B.graph (oneChip w) -
      rank B.graph (oneChip w - oneChip u) -
      rank B.graph (oneChip w - oneChip v) +
      rank B.graph (oneChip w - oneChip u - oneChip v) = 1
  rw [hW, hWU, hWV, hWUV]
  norm_num

/-- The second row in Proposition 4.5: if the degree-two twist at `t` is
`u+w` with `w` in neither marked one-chip class, then the transmission value
is `t - 1`. -/
theorem transmission_eq_sub_one_of_linearEquiv_u_add_one_chip
    (B : Banana 2) (u v w : B.graph.V) (D : CFDiv B.graph)
    (tau : ℤ → ℤ) (t : ℤ)
    (hTau : IsTransmissionPermutation (mark B.graph u v) D tau)
    (hClass : linearEquiv B.graph
      (D + t • (oneChip u - oneChip v))
      (oneChip u + oneChip w))
    (hwu : ¬ linearEquiv B.graph (oneChip w - oneChip u) 0)
    (hwv : ¬ linearEquiv B.graph (oneChip w - oneChip v) 0) :
    tau t = t - 1 := by
  apply transmission_value_of_linearEquiv_rankDelta_eq_one hTau
    (E := oneChip w)
  · unfold linearEquiv at hClass ⊢
    change oneChip w - (D + (t - 1) • oneChip u - t • oneChip v) ∈
      principalDivisors B.graph
    have hDiff :
        oneChip w - (D + (t - 1) • oneChip u - t • oneChip v) =
          (oneChip u + oneChip w) -
            (D + t • (oneChip u - oneChip v)) := by
      ext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      ring
    rw [hDiff]
    exact hClass
  · exact rankDelta_one_chip_eq_one_of_distinct_mark_classes B u v w hwu hwv

/-- An effective degree-two pair not in the canonical class has rank zero on
a theta graph. -/
theorem rank_pair_eq_zero_of_not_linearEquiv_canonical
    (B : Banana 2) (x y : B.graph.V)
    (hNotCanonical : ¬ linearEquiv B.graph
      (oneChip x + oneChip y) (canonicalDivisor B.graph)) :
    rank B.graph (oneChip x + oneChip y) = 0 := by
  have hWin : winnable B.graph (oneChip x + oneChip y) :=
    winnable_of_effective B.graph _ (effective_one_chip_add_one_chip x y)
  have hNonneg : 0 ≤ rank B.graph (oneChip x + oneChip y) :=
    (rank_geq_iff B.graph _ 0).mp
      ((rank_nonneg_iff_winnable B.graph _).mpr hWin)
  have hDegree : deg (oneChip x + oneChip y : CFDiv B.graph) = 2 := by
    rw [deg.map_add, deg_one_chip, deg_one_chip]
    norm_num
  have hUpper := rank_le_one_of_degree_two_genus_two
    (banana_graph_connected B) B.genus_graph _ hDegree
  by_contra hNotZero
  have hRankOne : rank B.graph (oneChip x + oneChip y) = 1 := by omega
  exact hNotCanonical
    (linearEquiv_canonical_of_rank_eq_one_degree_two_genus_two
      (banana_graph_connected B) B.genus_graph _ hDegree hRankOne)

/-- The third row in Proposition 4.5: if the degree-two twist at `t` is
`v+w`, and neither pair involving `w` is canonical, then the transmission
value is `t + 1`. -/
theorem transmission_eq_add_one_of_linearEquiv_v_add_one_chip
    (B : Banana 2) (u v w : B.graph.V) (D : CFDiv B.graph)
    (tau : ℤ → ℤ) (t : ℤ)
    (hTau : IsTransmissionPermutation (mark B.graph u v) D tau)
    (hClass : linearEquiv B.graph
      (D + t • (oneChip u - oneChip v))
      (oneChip v + oneChip w))
    (hUW : ¬ linearEquiv B.graph
      (oneChip u + oneChip w) (canonicalDivisor B.graph))
    (hVW : ¬ linearEquiv B.graph
      (oneChip v + oneChip w) (canonicalDivisor B.graph)) :
    tau t = t + 1 := by
  apply transmission_value_of_linearEquiv_rankDelta_eq_one hTau
    (E := oneChip u + oneChip v + oneChip w)
  · unfold linearEquiv at hClass ⊢
    change (oneChip u + oneChip v + oneChip w) -
        (D + (t + 1) • oneChip u - t • oneChip v) ∈
      principalDivisors B.graph
    have hDiff :
        (oneChip u + oneChip v + oneChip w) -
            (D + (t + 1) • oneChip u - t • oneChip v) =
          (oneChip v + oneChip w) -
            (D + t • (oneChip u - oneChip v)) := by
      ext z
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      ring
    rw [hDiff]
    exact hClass
  · rw [← markedRankDelta_eq_rankDelta B.graph u v
      (oneChip u + oneChip v + oneChip w)]
    unfold markedRankDelta
    have hDelU :
        oneChip u + oneChip v + oneChip w - oneChip u =
          (oneChip v + oneChip w : CFDiv B.graph) := by abel
    have hDelV :
        oneChip u + oneChip v + oneChip w - oneChip v =
          (oneChip u + oneChip w : CFDiv B.graph) := by abel
    have hDelUV :
        oneChip u + oneChip v + oneChip w - oneChip u - oneChip v =
          (oneChip w : CFDiv B.graph) := by abel
    have hDelVW : oneChip v + oneChip w - oneChip v =
        (oneChip w : CFDiv B.graph) := by abel
    have hTripleDegree : deg (oneChip u + oneChip v + oneChip w : CFDiv B.graph) = 3 := by
      rw [deg.map_add, deg.map_add, deg_one_chip, deg_one_chip, deg_one_chip]
      norm_num
    have hTripleRank : rank B.graph (oneChip u + oneChip v + oneChip w) = 1 := by
      have h := (rank_nonspecial_range (banana_graph_connected B)
        (oneChip u + oneChip v + oneChip w)).2.2 (by
          rw [hTripleDegree, B.genus_graph]
          omega)
      rw [hTripleDegree, B.genus_graph] at h
      exact h
    rw [hDelU, hDelV, hDelVW, hTripleRank,
      rank_pair_eq_zero_of_not_linearEquiv_canonical B v w hVW,
      rank_pair_eq_zero_of_not_linearEquiv_canonical B u w hUW,
      rank_one_chip_zero_banana_two]
    norm_num

/-- The fourth row in Proposition 4.5: writing the reflected class of `u` as
`K-u`, a twist equivalent to `v + (K-u)` forces transmission value `t + 2`. -/
theorem transmission_eq_add_two_of_linearEquiv_canonical_sub_u_add_v
    (B : Banana 2) (u v : B.graph.V) (D : CFDiv B.graph)
    (tau : ℤ → ℤ) (t : ℤ)
    (hTau : IsTransmissionPermutation (mark B.graph u v) D tau)
    (hClass : linearEquiv B.graph
      (D + t • (oneChip u - oneChip v))
      (canonicalDivisor B.graph - oneChip u + oneChip v)) :
    tau t = t + 2 := by
  apply transmission_value_of_linearEquiv_rankDelta_eq_one hTau
    (E := canonicalDivisor B.graph + oneChip u + oneChip v)
  · unfold linearEquiv at hClass ⊢
    change (canonicalDivisor B.graph + oneChip u + oneChip v) -
        (D + (t + 2) • oneChip u - t • oneChip v) ∈
      principalDivisors B.graph
    have hDiff :
        (canonicalDivisor B.graph + oneChip u + oneChip v) -
            (D + (t + 2) • oneChip u - t • oneChip v) =
          (canonicalDivisor B.graph - oneChip u + oneChip v) -
            (D + t • (oneChip u - oneChip v)) := by
      ext z
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      ring
    rw [hDiff]
    exact hClass
  · rw [← markedRankDelta_eq_rankDelta B.graph u v
      (canonicalDivisor B.graph + oneChip u + oneChip v)]
    unfold markedRankDelta
    have hDelU : canonicalDivisor B.graph + oneChip u + oneChip v - oneChip u =
        canonicalDivisor B.graph + oneChip v := by abel
    have hDelV : canonicalDivisor B.graph + oneChip u + oneChip v - oneChip v =
        canonicalDivisor B.graph + oneChip u := by abel
    have hDelUV : canonicalDivisor B.graph + oneChip u + oneChip v - oneChip u - oneChip v =
        canonicalDivisor B.graph := by abel
    have hDelVV : canonicalDivisor B.graph + oneChip v - oneChip v =
        canonicalDivisor B.graph := by abel
    have hRank (X : CFDiv B.graph) (hDeg : deg X > 2 * genus B.graph - 2) :
        rank B.graph X = deg X - genus B.graph :=
      (rank_nonspecial_range (banana_graph_connected B) X).2.2 hDeg
    have hDegBig : deg (canonicalDivisor B.graph + oneChip u + oneChip v) = 4 := by
      rw [deg.map_add, deg.map_add, degree_of_canonical_divisor, B.genus_graph,
        deg_one_chip, deg_one_chip]
      norm_num
    have hDegU : deg (canonicalDivisor B.graph + oneChip u) = 3 := by
      rw [deg.map_add, degree_of_canonical_divisor, B.genus_graph, deg_one_chip]
      norm_num
    have hDegV : deg (canonicalDivisor B.graph + oneChip v) = 3 := by
      rw [deg.map_add, degree_of_canonical_divisor, B.genus_graph, deg_one_chip]
      norm_num
    have hRankBig : rank B.graph (canonicalDivisor B.graph + oneChip u + oneChip v) = 2 := by
      have h := hRank _ (by rw [hDegBig, B.genus_graph]; norm_num)
      rw [hDegBig, B.genus_graph] at h
      exact h
    have hRankU : rank B.graph (canonicalDivisor B.graph + oneChip u) = 1 := by
      have h := hRank _ (by rw [hDegU, B.genus_graph]; norm_num)
      rw [hDegU, B.genus_graph] at h
      exact h
    have hRankV : rank B.graph (canonicalDivisor B.graph + oneChip v) = 1 := by
      have h := hRank _ (by rw [hDegV, B.genus_graph]; norm_num)
      rw [hDegV, B.genus_graph] at h
      exact h
    rw [hDelU, hDelV, hDelVV, hRankBig, hRankU, hRankV,
      rank_canonical_eq_one_of_genus_two (banana_graph_connected B) B.genus_graph]
    norm_num

/-! ## The exhaustive default row -/

/-- Proposition 4.5's `t - 2` exceptional class, stated independently of a
chosen transmission permutation. -/
def ThetaTransmissionSubTwoCase
    (B : Banana 2) (u : B.graph.V) (X : CFDiv B.graph) : Prop :=
  linearEquiv B.graph X (2 • oneChip u)

/-- Proposition 4.5's `t - 1` exceptional class.  The two inequalities in
the paper mean that the residual chip belongs to neither marked degree-one
class. -/
def ThetaTransmissionSubOneCase
    (B : Banana 2) (u v : B.graph.V) (X : CFDiv B.graph) : Prop :=
  ∃ w : B.graph.V,
    linearEquiv B.graph X (oneChip u + oneChip w) ∧
    ¬ linearEquiv B.graph (oneChip w - oneChip u) 0 ∧
    ¬ linearEquiv B.graph (oneChip w - oneChip v) 0

/-- Proposition 4.5's `t + 1` exceptional class.  Saying that `w` is
neither reflected marked point is precisely saying that neither marked pair
with `w` is canonical. -/
def ThetaTransmissionAddOneCase
    (B : Banana 2) (u v : B.graph.V) (X : CFDiv B.graph) : Prop :=
  ∃ w : B.graph.V,
    linearEquiv B.graph X (oneChip v + oneChip w) ∧
    ¬ linearEquiv B.graph
      (oneChip u + oneChip w) (canonicalDivisor B.graph) ∧
    ¬ linearEquiv B.graph
      (oneChip v + oneChip w) (canonicalDivisor B.graph)

/-- Proposition 4.5's `t + 2` exceptional class, with the reflected class
`bar u` written coordinate-freely as `K-u`. -/
def ThetaTransmissionAddTwoCase
    (B : Banana 2) (u v : B.graph.V) (X : CFDiv B.graph) : Prop :=
  linearEquiv B.graph X
    (canonicalDivisor B.graph - oneChip u + oneChip v)

private theorem linearEquiv_one_chips_of_sub_zero
    {G : CFGraph} {x y : G.V}
    (h : linearEquiv G (oneChip x - oneChip y) 0) :
    linearEquiv G (oneChip x) (oneChip y) := by
  unfold linearEquiv at h ⊢
  simpa using h

/-- Under rigidity, the marked pair itself is caught by one of the two
positive exceptional rows.  If `2u` is canonical it is the `+2` row;
otherwise it is the `+1` row with residual chip `u`. -/
private theorem addOneCase_or_addTwoCase_of_linearEquiv_mark_pair
    (B : Banana 2) (u v : B.graph.V) (X : CFDiv B.graph)
    (hRigid : ¬ linearEquiv B.graph
      (oneChip u + oneChip v) (canonicalDivisor B.graph))
    (hPair : linearEquiv B.graph X (oneChip u + oneChip v)) :
    ThetaTransmissionAddOneCase B u v X ∨
      ThetaTransmissionAddTwoCase B u v X := by
  by_cases hUU : linearEquiv B.graph
      (oneChip u + oneChip u) (canonicalDivisor B.graph)
  · right
    unfold ThetaTransmissionAddTwoCase
    apply hPair.trans
    unfold linearEquiv at hUU ⊢
    convert hUU using 1
    abel
  · left
    refine ⟨u, ?_, hUU, ?_⟩
    · convert hPair using 1
      abel
    · simpa [add_comm] using hRigid

/-- A canonical degree-two class is necessarily caught by the `-2` or `-1`
row.  The residual chip in the latter case is an effective representative
of the degree-one class `K-u`. -/
private theorem subTwoCase_or_subOneCase_of_linearEquiv_canonical
    (B : Banana 2) (u v : B.graph.V) (X : CFDiv B.graph)
    (hRigid : ¬ linearEquiv B.graph
      (oneChip u + oneChip v) (canonicalDivisor B.graph))
    (hCanonical : linearEquiv B.graph X (canonicalDivisor B.graph)) :
    ThetaTransmissionSubTwoCase B u X ∨
      ThetaTransmissionSubOneCase B u v X := by
  by_cases hTwoU : linearEquiv B.graph
      (2 • oneChip u) (canonicalDivisor B.graph)
  · left
    exact hCanonical.trans hTwoU.symm
  · right
    have hDualRank :
        rank B.graph (canonicalDivisor B.graph - oneChip u) = 0 := by
      have hRR := riemann_roch_for_graphs (banana_graph_connected B) (oneChip u)
      rw [deg_one_chip, B.genus_graph, rank_one_chip_zero_banana_two] at hRR
      omega
    obtain ⟨w, hw⟩ := exists_one_chip_representative_of_rank_zero_degree_one
      B.graph (canonicalDivisor B.graph - oneChip u) hDualRank (by
        rw [deg.map_sub, degree_of_canonical_divisor, B.genus_graph, deg_one_chip]
        norm_num)
    have hKPair : linearEquiv B.graph (canonicalDivisor B.graph)
        (oneChip u + oneChip w) := by
      unfold linearEquiv at hw ⊢
      convert hw using 1
      abel
    refine ⟨w, hCanonical.trans hKPair, ?_, ?_⟩
    · intro hWU
      have hWU' := linearEquiv_one_chips_of_sub_zero hWU
      have hAdd := linearEquiv_add_left_of_linearEquiv
        (C := oneChip u) hWU'
      apply hTwoU
      convert hAdd.symm.trans hKPair.symm using 1
      abel
    · intro hWV
      have hWV' := linearEquiv_one_chips_of_sub_zero hWV
      have hAdd := linearEquiv_add_left_of_linearEquiv
        (C := oneChip u) hWV'
      apply hRigid
      exact (hKPair.trans hAdd).symm

/-- The fifth row of Proposition 4.5 at the rank-theoretic level.  On a
rigid theta graph, a degree-two class outside the four exceptional classes
has rank pattern `(0,-1,-1,-1)` after deleting neither, either, or both
marked chips. -/
theorem thetaTransmission_default_rank_pattern
    (B : Banana 2) (u v : B.graph.V) (X : CFDiv B.graph)
    (hDegree : deg X = 2)
    (hRigid : ¬ linearEquiv B.graph
      (oneChip u + oneChip v) (canonicalDivisor B.graph))
    (hNotSubTwo : ¬ ThetaTransmissionSubTwoCase B u X)
    (hNotSubOne : ¬ ThetaTransmissionSubOneCase B u v X)
    (hNotAddOne : ¬ ThetaTransmissionAddOneCase B u v X)
    (hNotAddTwo : ¬ ThetaTransmissionAddTwoCase B u v X) :
    rank B.graph X = 0 ∧
      rank B.graph (X - oneChip u) = -1 ∧
      rank B.graph (X - oneChip v) = -1 ∧
      rank B.graph (X - oneChip u - oneChip v) = -1 := by
  have catchMarkPair
      (hPair : linearEquiv B.graph X (oneChip u + oneChip v)) : False := by
    rcases addOneCase_or_addTwoCase_of_linearEquiv_mark_pair
      B u v X hRigid hPair with h | h
    · exact hNotAddOne h
    · exact hNotAddTwo h
  have catchCanonical
      (hCanonical : linearEquiv B.graph X (canonicalDivisor B.graph)) : False := by
    rcases subTwoCase_or_subOneCase_of_linearEquiv_canonical
      B u v X hRigid hCanonical with h | h
    · exact hNotSubTwo h
    · exact hNotSubOne h
  have hXNonneg : 0 ≤ rank B.graph X := by
    have hRR := riemann_roch_for_graphs (banana_graph_connected B) X
    have hDualLower := rank_geq_neg_one B.graph (canonicalDivisor B.graph - X)
    rw [B.genus_graph, hDegree] at hRR
    omega
  have hXUpper := rank_le_one_of_degree_two_genus_two
    (banana_graph_connected B) B.genus_graph X hDegree
  have hX : rank B.graph X = 0 := by
    by_contra hNe
    have hOne : rank B.graph X = 1 := by omega
    exact catchCanonical
      (linearEquiv_canonical_of_rank_eq_one_degree_two_genus_two
        (banana_graph_connected B) B.genus_graph X hDegree hOne)
  have hXu : rank B.graph (X - oneChip u) = -1 := by
    by_contra hNe
    have hNonneg : 0 ≤ rank B.graph (X - oneChip u) := by
      have hLower := rank_geq_neg_one B.graph (X - oneChip u)
      omega
    have hRankZero := rank_eq_zero_of_deg_one_rank_nonneg_banana_two B
      (X - oneChip u) (by rw [deg.map_sub, hDegree, deg_one_chip]; norm_num) hNonneg
    obtain ⟨w, hw⟩ := exists_one_chip_representative_of_rank_zero_degree_one
      B.graph (X - oneChip u) hRankZero (by
        rw [deg.map_sub, hDegree, deg_one_chip]
        norm_num)
    have hAdd := linearEquiv_add_left_of_linearEquiv (C := oneChip u) hw
    have hXPair : linearEquiv B.graph X (oneChip u + oneChip w) := by
      convert hAdd using 1
      abel
    by_cases hWU : linearEquiv B.graph (oneChip w - oneChip u) 0
    · have hWU' := linearEquiv_one_chips_of_sub_zero hWU
      have hPair := linearEquiv_add_left_of_linearEquiv (C := oneChip u) hWU'
      apply hNotSubTwo
      unfold ThetaTransmissionSubTwoCase
      apply hXPair.trans
      convert hPair using 1
      abel
    · by_cases hWV : linearEquiv B.graph (oneChip w - oneChip v) 0
      · have hWV' := linearEquiv_one_chips_of_sub_zero hWV
        have hPair := linearEquiv_add_left_of_linearEquiv (C := oneChip u) hWV'
        apply catchMarkPair
        exact hXPair.trans hPair
      · exact hNotSubOne ⟨w, hXPair, hWU, hWV⟩
  have hXv : rank B.graph (X - oneChip v) = -1 := by
    by_contra hNe
    have hNonneg : 0 ≤ rank B.graph (X - oneChip v) := by
      have hLower := rank_geq_neg_one B.graph (X - oneChip v)
      omega
    have hRankZero := rank_eq_zero_of_deg_one_rank_nonneg_banana_two B
      (X - oneChip v) (by rw [deg.map_sub, hDegree, deg_one_chip]; norm_num) hNonneg
    obtain ⟨w, hw⟩ := exists_one_chip_representative_of_rank_zero_degree_one
      B.graph (X - oneChip v) hRankZero (by
        rw [deg.map_sub, hDegree, deg_one_chip]
        norm_num)
    have hAdd := linearEquiv_add_left_of_linearEquiv (C := oneChip v) hw
    have hXPair : linearEquiv B.graph X (oneChip v + oneChip w) := by
      convert hAdd using 1
      abel
    by_cases hUW : linearEquiv B.graph
        (oneChip u + oneChip w) (canonicalDivisor B.graph)
    · apply hNotAddTwo
      unfold ThetaTransmissionAddTwoCase
      apply hXPair.trans
      unfold linearEquiv at hUW ⊢
      convert hUW using 1
      abel
    · by_cases hVW : linearEquiv B.graph
          (oneChip v + oneChip w) (canonicalDivisor B.graph)
      · exact catchCanonical (hXPair.trans hVW)
      · exact hNotAddOne ⟨w, hXPair, hUW, hVW⟩
  have hXuv : rank B.graph (X - oneChip u - oneChip v) = -1 := by
    by_contra hNe
    have hNonneg : 0 ≤ rank B.graph (X - oneChip u - oneChip v) := by
      have hLower := rank_geq_neg_one B.graph (X - oneChip u - oneChip v)
      omega
    have hZero : linearEquiv B.graph
        (X - oneChip u - oneChip v) 0 :=
      linearEquiv_zero_of_rank_nonneg_degree_zero' B.graph _ hNonneg (by
        rw [deg.map_sub, deg.map_sub, hDegree, deg_one_chip, deg_one_chip]
        norm_num)
    apply catchMarkPair
    unfold linearEquiv at hZero ⊢
    convert hZero using 1
    abel
  exact ⟨hX, hXu, hXv, hXuv⟩

/-- The exhaustive default row of Proposition 4.5: if the degree-two twist
at `t` belongs to none of the four exceptional divisor classes, its
transmission value is `t`. -/
theorem transmission_eq_self_of_no_theta_exception
    (B : Banana 2) (u v : B.graph.V) (D : CFDiv B.graph)
    (tau : ℤ → ℤ) (t : ℤ)
    (hTau : IsTransmissionPermutation (mark B.graph u v) D tau)
    (hDegree : deg D = 2)
    (hRigid : ¬ linearEquiv B.graph
      (oneChip u + oneChip v) (canonicalDivisor B.graph))
    (hNotSubTwo : ¬ ThetaTransmissionSubTwoCase B u
      (D + t • (oneChip u - oneChip v)))
    (hNotSubOne : ¬ ThetaTransmissionSubOneCase B u v
      (D + t • (oneChip u - oneChip v)))
    (hNotAddOne : ¬ ThetaTransmissionAddOneCase B u v
      (D + t • (oneChip u - oneChip v)))
    (hNotAddTwo : ¬ ThetaTransmissionAddTwoCase B u v
      (D + t • (oneChip u - oneChip v))) :
    tau t = t := by
  let X : CFDiv B.graph := D + t • (oneChip u - oneChip v)
  have hXDegree : deg X = 2 := by
    dsimp [X]
    rw [deg.map_add, map_zsmul, deg.map_sub, deg_one_chip, deg_one_chip, hDegree]
    ring
  obtain ⟨hX, hXu, hXv, hXuv⟩ := thetaTransmission_default_rank_pattern
    B u v X hXDegree hRigid hNotSubTwo hNotSubOne hNotAddOne hNotAddTwo
  have hTwist :
      D + t • oneChip u - t • oneChip v = X := by
    dsimp [X]
    rw [smul_sub]
    abel
  have hDelta : rankDelta (mark B.graph u v)
      (D + t • oneChip u - t • oneChip v : CFDiv B.graph) = 1 := by
    rw [← markedRankDelta_eq_rankDelta B.graph u v]
    unfold markedRankDelta
    rw [hTwist, hX, hXu, hXv, hXuv]
    norm_num
  exact transmission_value_of_rankDelta_eq_one hTau hDelta

/-- TeX label: `prop-thetaTransChar` (Proposition 4.5).

The complete rowwise transmission table for a rigid theta marking.  The four
exception predicates are the coordinate-free versions of the paper's classes
`2u`, `u+w`, `v+w`, and `v+\bar u`; the final implication is the exhaustive
default row.  Their mutual exclusivity is not needed to state or use the
table, since each implication is proved directly from the corresponding rank
difference. -/
theorem theta_transmission_characteristic_rows
    (B : Banana 2) (u v : B.graph.V) (D : CFDiv B.graph)
    (tau : ℤ → ℤ) (t : ℤ)
    (hTau : IsTransmissionPermutation (mark B.graph u v) D tau)
    (hDegree : deg D = 2)
    (hRigid : ¬ linearEquiv B.graph
      (oneChip u + oneChip v) (canonicalDivisor B.graph)) :
    (ThetaTransmissionSubTwoCase B u
        (D + t • (oneChip u - oneChip v)) → tau t = t - 2) ∧
    (ThetaTransmissionSubOneCase B u v
        (D + t • (oneChip u - oneChip v)) → tau t = t - 1) ∧
    (ThetaTransmissionAddOneCase B u v
        (D + t • (oneChip u - oneChip v)) → tau t = t + 1) ∧
    (ThetaTransmissionAddTwoCase B u v
        (D + t • (oneChip u - oneChip v)) → tau t = t + 2) ∧
    (¬ ThetaTransmissionSubTwoCase B u
        (D + t • (oneChip u - oneChip v)) →
      ¬ ThetaTransmissionSubOneCase B u v
        (D + t • (oneChip u - oneChip v)) →
      ¬ ThetaTransmissionAddOneCase B u v
        (D + t • (oneChip u - oneChip v)) →
      ¬ ThetaTransmissionAddTwoCase B u v
        (D + t • (oneChip u - oneChip v)) → tau t = t) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact transmission_eq_sub_two_of_linearEquiv_two_u t hTau h
  · rintro ⟨w, hClass, hwu, hwv⟩
    exact transmission_eq_sub_one_of_linearEquiv_u_add_one_chip
      B u v w D tau t hTau hClass hwu hwv
  · rintro ⟨w, hClass, hUW, hVW⟩
    exact transmission_eq_add_one_of_linearEquiv_v_add_one_chip
      B u v w D tau t hTau hClass hUW hVW
  · intro h
    exact transmission_eq_add_two_of_linearEquiv_canonical_sub_u_add_v
      B u v D tau t hTau h
  · intro hSubTwo hSubOne hAddOne hAddTwo
    exact transmission_eq_self_of_no_theta_exception
      B u v D tau t hTau hDegree hRigid hSubTwo hSubOne hAddOne hAddTwo

end Bananas
