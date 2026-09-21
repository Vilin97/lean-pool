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
  have hU : rank M.graph ((0 : CFDiv M.graph) - one_chip M.u) = -1 := by
    apply rank_neg_one_of_deg_neg
    rw [deg.map_sub, map_zero, deg_one_chip]
    norm_num
  have hV : rank M.graph ((0 : CFDiv M.graph) - one_chip M.v) = -1 := by
    apply rank_neg_one_of_deg_neg
    rw [deg.map_sub, map_zero, deg_one_chip]
    norm_num
  have hUV : rank M.graph
      ((0 : CFDiv M.graph) - one_chip M.u - one_chip M.v) = -1 := by
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
    (hClass : linear_equiv M.graph
      (D + t • (one_chip M.u - one_chip M.v))
      (2 • one_chip M.u)) :
    tau t = t - 2 := by
  apply transmission_value_of_linearEquiv_rankDelta_eq_one hTau
    (E := (0 : CFDiv M.graph))
  · unfold linear_equiv at hClass ⊢
    convert hClass using 1
    ext x
    simp only [Pi.zero_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    ring
  · exact rankDelta_zero_eq_one M

/-- A one-chip divisor has marked second difference one when its class is
different from both marked one-chip classes. -/
theorem rankDelta_one_chip_eq_one_of_distinct_mark_classes
    (B : Banana 2) (u v w : B.graph.V)
    (hwu : ¬ linear_equiv B.graph (one_chip w - one_chip u) 0)
    (hwv : ¬ linear_equiv B.graph (one_chip w - one_chip v) 0) :
    rankDelta (mark B.graph u v) (one_chip w) = 1 := by
  have hW : rank B.graph (one_chip w) = 0 := rank_one_chip_zero_banana_two B w
  have hWU : rank B.graph (one_chip w - one_chip u) = -1 := by
    have hLower := rank_geq_neg_one B.graph (one_chip w - one_chip u)
    by_contra hNot
    have hNonneg : 0 ≤ rank B.graph (one_chip w - one_chip u) := by omega
    exact hwu (linearEquiv_zero_of_rank_nonneg_degree_zero' B.graph _ hNonneg (by
      rw [deg.map_sub, deg_one_chip, deg_one_chip]
      norm_num))
  have hWV : rank B.graph (one_chip w - one_chip v) = -1 := by
    have hLower := rank_geq_neg_one B.graph (one_chip w - one_chip v)
    by_contra hNot
    have hNonneg : 0 ≤ rank B.graph (one_chip w - one_chip v) := by omega
    exact hwv (linearEquiv_zero_of_rank_nonneg_degree_zero' B.graph _ hNonneg (by
      rw [deg.map_sub, deg_one_chip, deg_one_chip]
      norm_num))
  have hWUV : rank B.graph (one_chip w - one_chip u - one_chip v) = -1 := by
    apply rank_neg_one_of_deg_neg
    rw [deg.map_sub, deg.map_sub, deg_one_chip, deg_one_chip, deg_one_chip]
    norm_num
  change rank B.graph (one_chip w) -
      rank B.graph (one_chip w - one_chip u) -
      rank B.graph (one_chip w - one_chip v) +
      rank B.graph (one_chip w - one_chip u - one_chip v) = 1
  rw [hW, hWU, hWV, hWUV]
  norm_num

/-- The second row in Proposition 4.5: if the degree-two twist at `t` is
`u+w` with `w` in neither marked one-chip class, then the transmission value
is `t - 1`. -/
theorem transmission_eq_sub_one_of_linearEquiv_u_add_one_chip
    (B : Banana 2) (u v w : B.graph.V) (D : CFDiv B.graph)
    (tau : ℤ → ℤ) (t : ℤ)
    (hTau : IsTransmissionPermutation (mark B.graph u v) D tau)
    (hClass : linear_equiv B.graph
      (D + t • (one_chip u - one_chip v))
      (one_chip u + one_chip w))
    (hwu : ¬ linear_equiv B.graph (one_chip w - one_chip u) 0)
    (hwv : ¬ linear_equiv B.graph (one_chip w - one_chip v) 0) :
    tau t = t - 1 := by
  apply transmission_value_of_linearEquiv_rankDelta_eq_one hTau
    (E := one_chip w)
  · unfold linear_equiv at hClass ⊢
    change one_chip w - (D + (t - 1) • one_chip u - t • one_chip v) ∈
      principal_divisors B.graph
    have hDiff :
        one_chip w - (D + (t - 1) • one_chip u - t • one_chip v) =
          (one_chip u + one_chip w) -
            (D + t • (one_chip u - one_chip v)) := by
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
    (hNotCanonical : ¬ linear_equiv B.graph
      (one_chip x + one_chip y) (canonical_divisor B.graph)) :
    rank B.graph (one_chip x + one_chip y) = 0 := by
  have hWin : winnable B.graph (one_chip x + one_chip y) :=
    winnable_of_effective B.graph _ (effective_one_chip_add_one_chip x y)
  have hNonneg : 0 ≤ rank B.graph (one_chip x + one_chip y) :=
    (rank_geq_iff B.graph _ 0).mp
      ((rank_nonneg_iff_winnable B.graph _).mpr hWin)
  have hDegree : deg (one_chip x + one_chip y : CFDiv B.graph) = 2 := by
    rw [deg.map_add, deg_one_chip, deg_one_chip]
    norm_num
  have hUpper := rank_le_one_of_degree_two_genus_two
    (banana_graph_connected B) B.genus_graph _ hDegree
  by_contra hNotZero
  have hRankOne : rank B.graph (one_chip x + one_chip y) = 1 := by omega
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
    (hClass : linear_equiv B.graph
      (D + t • (one_chip u - one_chip v))
      (one_chip v + one_chip w))
    (hUW : ¬ linear_equiv B.graph
      (one_chip u + one_chip w) (canonical_divisor B.graph))
    (hVW : ¬ linear_equiv B.graph
      (one_chip v + one_chip w) (canonical_divisor B.graph)) :
    tau t = t + 1 := by
  apply transmission_value_of_linearEquiv_rankDelta_eq_one hTau
    (E := one_chip u + one_chip v + one_chip w)
  · unfold linear_equiv at hClass ⊢
    change (one_chip u + one_chip v + one_chip w) -
        (D + (t + 1) • one_chip u - t • one_chip v) ∈
      principal_divisors B.graph
    have hDiff :
        (one_chip u + one_chip v + one_chip w) -
            (D + (t + 1) • one_chip u - t • one_chip v) =
          (one_chip v + one_chip w) -
            (D + t • (one_chip u - one_chip v)) := by
      ext z
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      ring
    rw [hDiff]
    exact hClass
  · rw [← markedRankDelta_eq_rankDelta B.graph u v
      (one_chip u + one_chip v + one_chip w)]
    unfold markedRankDelta
    have hDelU :
        one_chip u + one_chip v + one_chip w - one_chip u =
          (one_chip v + one_chip w : CFDiv B.graph) := by abel
    have hDelV :
        one_chip u + one_chip v + one_chip w - one_chip v =
          (one_chip u + one_chip w : CFDiv B.graph) := by abel
    have hDelUV :
        one_chip u + one_chip v + one_chip w - one_chip u - one_chip v =
          (one_chip w : CFDiv B.graph) := by abel
    have hDelVW : one_chip v + one_chip w - one_chip v =
        (one_chip w : CFDiv B.graph) := by abel
    have hTripleDegree : deg (one_chip u + one_chip v + one_chip w : CFDiv B.graph) = 3 := by
      rw [deg.map_add, deg.map_add, deg_one_chip, deg_one_chip, deg_one_chip]
      norm_num
    have hTripleRank : rank B.graph (one_chip u + one_chip v + one_chip w) = 1 := by
      have h := (rank_nonspecial_range (banana_graph_connected B)
        (one_chip u + one_chip v + one_chip w)).2.2 (by
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
    (hClass : linear_equiv B.graph
      (D + t • (one_chip u - one_chip v))
      (canonical_divisor B.graph - one_chip u + one_chip v)) :
    tau t = t + 2 := by
  apply transmission_value_of_linearEquiv_rankDelta_eq_one hTau
    (E := canonical_divisor B.graph + one_chip u + one_chip v)
  · unfold linear_equiv at hClass ⊢
    change (canonical_divisor B.graph + one_chip u + one_chip v) -
        (D + (t + 2) • one_chip u - t • one_chip v) ∈
      principal_divisors B.graph
    have hDiff :
        (canonical_divisor B.graph + one_chip u + one_chip v) -
            (D + (t + 2) • one_chip u - t • one_chip v) =
          (canonical_divisor B.graph - one_chip u + one_chip v) -
            (D + t • (one_chip u - one_chip v)) := by
      ext z
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      ring
    rw [hDiff]
    exact hClass
  · rw [← markedRankDelta_eq_rankDelta B.graph u v
      (canonical_divisor B.graph + one_chip u + one_chip v)]
    unfold markedRankDelta
    have hDelU : canonical_divisor B.graph + one_chip u + one_chip v - one_chip u =
        canonical_divisor B.graph + one_chip v := by abel
    have hDelV : canonical_divisor B.graph + one_chip u + one_chip v - one_chip v =
        canonical_divisor B.graph + one_chip u := by abel
    have hDelUV : canonical_divisor B.graph + one_chip u + one_chip v - one_chip u - one_chip v =
        canonical_divisor B.graph := by abel
    have hDelVV : canonical_divisor B.graph + one_chip v - one_chip v =
        canonical_divisor B.graph := by abel
    have hRank (X : CFDiv B.graph) (hDeg : deg X > 2 * genus B.graph - 2) :
        rank B.graph X = deg X - genus B.graph :=
      (rank_nonspecial_range (banana_graph_connected B) X).2.2 hDeg
    have hDegBig : deg (canonical_divisor B.graph + one_chip u + one_chip v) = 4 := by
      rw [deg.map_add, deg.map_add, degree_of_canonical_divisor, B.genus_graph,
        deg_one_chip, deg_one_chip]
      norm_num
    have hDegU : deg (canonical_divisor B.graph + one_chip u) = 3 := by
      rw [deg.map_add, degree_of_canonical_divisor, B.genus_graph, deg_one_chip]
      norm_num
    have hDegV : deg (canonical_divisor B.graph + one_chip v) = 3 := by
      rw [deg.map_add, degree_of_canonical_divisor, B.genus_graph, deg_one_chip]
      norm_num
    have hRankBig : rank B.graph (canonical_divisor B.graph + one_chip u + one_chip v) = 2 := by
      have h := hRank _ (by rw [hDegBig, B.genus_graph]; norm_num)
      rw [hDegBig, B.genus_graph] at h
      exact h
    have hRankU : rank B.graph (canonical_divisor B.graph + one_chip u) = 1 := by
      have h := hRank _ (by rw [hDegU, B.genus_graph]; norm_num)
      rw [hDegU, B.genus_graph] at h
      exact h
    have hRankV : rank B.graph (canonical_divisor B.graph + one_chip v) = 1 := by
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
  linear_equiv B.graph X (2 • one_chip u)

/-- Proposition 4.5's `t - 1` exceptional class.  The two inequalities in
the paper mean that the residual chip belongs to neither marked degree-one
class. -/
def ThetaTransmissionSubOneCase
    (B : Banana 2) (u v : B.graph.V) (X : CFDiv B.graph) : Prop :=
  ∃ w : B.graph.V,
    linear_equiv B.graph X (one_chip u + one_chip w) ∧
    ¬ linear_equiv B.graph (one_chip w - one_chip u) 0 ∧
    ¬ linear_equiv B.graph (one_chip w - one_chip v) 0

/-- Proposition 4.5's `t + 1` exceptional class.  Saying that `w` is
neither reflected marked point is precisely saying that neither marked pair
with `w` is canonical. -/
def ThetaTransmissionAddOneCase
    (B : Banana 2) (u v : B.graph.V) (X : CFDiv B.graph) : Prop :=
  ∃ w : B.graph.V,
    linear_equiv B.graph X (one_chip v + one_chip w) ∧
    ¬ linear_equiv B.graph
      (one_chip u + one_chip w) (canonical_divisor B.graph) ∧
    ¬ linear_equiv B.graph
      (one_chip v + one_chip w) (canonical_divisor B.graph)

/-- Proposition 4.5's `t + 2` exceptional class, with the reflected class
`bar u` written coordinate-freely as `K-u`. -/
def ThetaTransmissionAddTwoCase
    (B : Banana 2) (u v : B.graph.V) (X : CFDiv B.graph) : Prop :=
  linear_equiv B.graph X
    (canonical_divisor B.graph - one_chip u + one_chip v)

private theorem linearEquiv_one_chips_of_sub_zero
    {G : CFGraph} {x y : G.V}
    (h : linear_equiv G (one_chip x - one_chip y) 0) :
    linear_equiv G (one_chip x) (one_chip y) := by
  unfold linear_equiv at h ⊢
  simpa using h

/-- Under rigidity, the marked pair itself is caught by one of the two
positive exceptional rows.  If `2u` is canonical it is the `+2` row;
otherwise it is the `+1` row with residual chip `u`. -/
private theorem addOneCase_or_addTwoCase_of_linearEquiv_mark_pair
    (B : Banana 2) (u v : B.graph.V) (X : CFDiv B.graph)
    (hRigid : ¬ linear_equiv B.graph
      (one_chip u + one_chip v) (canonical_divisor B.graph))
    (hPair : linear_equiv B.graph X (one_chip u + one_chip v)) :
    ThetaTransmissionAddOneCase B u v X ∨
      ThetaTransmissionAddTwoCase B u v X := by
  by_cases hUU : linear_equiv B.graph
      (one_chip u + one_chip u) (canonical_divisor B.graph)
  · right
    unfold ThetaTransmissionAddTwoCase
    apply hPair.trans
    unfold linear_equiv at hUU ⊢
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
    (hRigid : ¬ linear_equiv B.graph
      (one_chip u + one_chip v) (canonical_divisor B.graph))
    (hCanonical : linear_equiv B.graph X (canonical_divisor B.graph)) :
    ThetaTransmissionSubTwoCase B u X ∨
      ThetaTransmissionSubOneCase B u v X := by
  by_cases hTwoU : linear_equiv B.graph
      (2 • one_chip u) (canonical_divisor B.graph)
  · left
    exact hCanonical.trans hTwoU.symm
  · right
    have hDualRank :
        rank B.graph (canonical_divisor B.graph - one_chip u) = 0 := by
      have hRR := riemann_roch_for_graphs (banana_graph_connected B) (one_chip u)
      rw [deg_one_chip, B.genus_graph, rank_one_chip_zero_banana_two] at hRR
      omega
    obtain ⟨w, hw⟩ := exists_one_chip_representative_of_rank_zero_degree_one
      B.graph (canonical_divisor B.graph - one_chip u) hDualRank (by
        rw [deg.map_sub, degree_of_canonical_divisor, B.genus_graph, deg_one_chip]
        norm_num)
    have hKPair : linear_equiv B.graph (canonical_divisor B.graph)
        (one_chip u + one_chip w) := by
      unfold linear_equiv at hw ⊢
      convert hw using 1
      abel
    refine ⟨w, hCanonical.trans hKPair, ?_, ?_⟩
    · intro hWU
      have hWU' := linearEquiv_one_chips_of_sub_zero hWU
      have hAdd := linearEquiv_add_left_of_linearEquiv
        (C := one_chip u) hWU'
      apply hTwoU
      convert hAdd.symm.trans hKPair.symm using 1
      abel
    · intro hWV
      have hWV' := linearEquiv_one_chips_of_sub_zero hWV
      have hAdd := linearEquiv_add_left_of_linearEquiv
        (C := one_chip u) hWV'
      apply hRigid
      exact (hKPair.trans hAdd).symm

/-- The fifth row of Proposition 4.5 at the rank-theoretic level.  On a
rigid theta graph, a degree-two class outside the four exceptional classes
has rank pattern `(0,-1,-1,-1)` after deleting neither, either, or both
marked chips. -/
theorem thetaTransmission_default_rank_pattern
    (B : Banana 2) (u v : B.graph.V) (X : CFDiv B.graph)
    (hDegree : deg X = 2)
    (hRigid : ¬ linear_equiv B.graph
      (one_chip u + one_chip v) (canonical_divisor B.graph))
    (hNotSubTwo : ¬ ThetaTransmissionSubTwoCase B u X)
    (hNotSubOne : ¬ ThetaTransmissionSubOneCase B u v X)
    (hNotAddOne : ¬ ThetaTransmissionAddOneCase B u v X)
    (hNotAddTwo : ¬ ThetaTransmissionAddTwoCase B u v X) :
    rank B.graph X = 0 ∧
      rank B.graph (X - one_chip u) = -1 ∧
      rank B.graph (X - one_chip v) = -1 ∧
      rank B.graph (X - one_chip u - one_chip v) = -1 := by
  have catchMarkPair
      (hPair : linear_equiv B.graph X (one_chip u + one_chip v)) : False := by
    rcases addOneCase_or_addTwoCase_of_linearEquiv_mark_pair
      B u v X hRigid hPair with h | h
    · exact hNotAddOne h
    · exact hNotAddTwo h
  have catchCanonical
      (hCanonical : linear_equiv B.graph X (canonical_divisor B.graph)) : False := by
    rcases subTwoCase_or_subOneCase_of_linearEquiv_canonical
      B u v X hRigid hCanonical with h | h
    · exact hNotSubTwo h
    · exact hNotSubOne h
  have hXNonneg : 0 ≤ rank B.graph X := by
    have hRR := riemann_roch_for_graphs (banana_graph_connected B) X
    have hDualLower := rank_geq_neg_one B.graph (canonical_divisor B.graph - X)
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
  have hXu : rank B.graph (X - one_chip u) = -1 := by
    by_contra hNe
    have hNonneg : 0 ≤ rank B.graph (X - one_chip u) := by
      have hLower := rank_geq_neg_one B.graph (X - one_chip u)
      omega
    have hRankZero := rank_eq_zero_of_deg_one_rank_nonneg_banana_two B
      (X - one_chip u) (by rw [deg.map_sub, hDegree, deg_one_chip]; norm_num) hNonneg
    obtain ⟨w, hw⟩ := exists_one_chip_representative_of_rank_zero_degree_one
      B.graph (X - one_chip u) hRankZero (by
        rw [deg.map_sub, hDegree, deg_one_chip]
        norm_num)
    have hAdd := linearEquiv_add_left_of_linearEquiv (C := one_chip u) hw
    have hXPair : linear_equiv B.graph X (one_chip u + one_chip w) := by
      convert hAdd using 1
      abel
    by_cases hWU : linear_equiv B.graph (one_chip w - one_chip u) 0
    · have hWU' := linearEquiv_one_chips_of_sub_zero hWU
      have hPair := linearEquiv_add_left_of_linearEquiv (C := one_chip u) hWU'
      apply hNotSubTwo
      unfold ThetaTransmissionSubTwoCase
      apply hXPair.trans
      convert hPair using 1
      abel
    · by_cases hWV : linear_equiv B.graph (one_chip w - one_chip v) 0
      · have hWV' := linearEquiv_one_chips_of_sub_zero hWV
        have hPair := linearEquiv_add_left_of_linearEquiv (C := one_chip u) hWV'
        apply catchMarkPair
        exact hXPair.trans hPair
      · exact hNotSubOne ⟨w, hXPair, hWU, hWV⟩
  have hXv : rank B.graph (X - one_chip v) = -1 := by
    by_contra hNe
    have hNonneg : 0 ≤ rank B.graph (X - one_chip v) := by
      have hLower := rank_geq_neg_one B.graph (X - one_chip v)
      omega
    have hRankZero := rank_eq_zero_of_deg_one_rank_nonneg_banana_two B
      (X - one_chip v) (by rw [deg.map_sub, hDegree, deg_one_chip]; norm_num) hNonneg
    obtain ⟨w, hw⟩ := exists_one_chip_representative_of_rank_zero_degree_one
      B.graph (X - one_chip v) hRankZero (by
        rw [deg.map_sub, hDegree, deg_one_chip]
        norm_num)
    have hAdd := linearEquiv_add_left_of_linearEquiv (C := one_chip v) hw
    have hXPair : linear_equiv B.graph X (one_chip v + one_chip w) := by
      convert hAdd using 1
      abel
    by_cases hUW : linear_equiv B.graph
        (one_chip u + one_chip w) (canonical_divisor B.graph)
    · apply hNotAddTwo
      unfold ThetaTransmissionAddTwoCase
      apply hXPair.trans
      unfold linear_equiv at hUW ⊢
      convert hUW using 1
      abel
    · by_cases hVW : linear_equiv B.graph
          (one_chip v + one_chip w) (canonical_divisor B.graph)
      · exact catchCanonical (hXPair.trans hVW)
      · exact hNotAddOne ⟨w, hXPair, hUW, hVW⟩
  have hXuv : rank B.graph (X - one_chip u - one_chip v) = -1 := by
    by_contra hNe
    have hNonneg : 0 ≤ rank B.graph (X - one_chip u - one_chip v) := by
      have hLower := rank_geq_neg_one B.graph (X - one_chip u - one_chip v)
      omega
    have hZero : linear_equiv B.graph
        (X - one_chip u - one_chip v) 0 :=
      linearEquiv_zero_of_rank_nonneg_degree_zero' B.graph _ hNonneg (by
        rw [deg.map_sub, deg.map_sub, hDegree, deg_one_chip, deg_one_chip]
        norm_num)
    apply catchMarkPair
    unfold linear_equiv at hZero ⊢
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
    (hRigid : ¬ linear_equiv B.graph
      (one_chip u + one_chip v) (canonical_divisor B.graph))
    (hNotSubTwo : ¬ ThetaTransmissionSubTwoCase B u
      (D + t • (one_chip u - one_chip v)))
    (hNotSubOne : ¬ ThetaTransmissionSubOneCase B u v
      (D + t • (one_chip u - one_chip v)))
    (hNotAddOne : ¬ ThetaTransmissionAddOneCase B u v
      (D + t • (one_chip u - one_chip v)))
    (hNotAddTwo : ¬ ThetaTransmissionAddTwoCase B u v
      (D + t • (one_chip u - one_chip v))) :
    tau t = t := by
  let X : CFDiv B.graph := D + t • (one_chip u - one_chip v)
  have hXDegree : deg X = 2 := by
    dsimp [X]
    rw [deg.map_add, map_zsmul, deg.map_sub, deg_one_chip, deg_one_chip, hDegree]
    ring
  obtain ⟨hX, hXu, hXv, hXuv⟩ := thetaTransmission_default_rank_pattern
    B u v X hXDegree hRigid hNotSubTwo hNotSubOne hNotAddOne hNotAddTwo
  have hTwist :
      D + t • one_chip u - t • one_chip v = X := by
    dsimp [X]
    rw [smul_sub]
    abel
  have hDelta : rankDelta (mark B.graph u v)
      (D + t • one_chip u - t • one_chip v : CFDiv B.graph) = 1 := by
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
    (hRigid : ¬ linear_equiv B.graph
      (one_chip u + one_chip v) (canonical_divisor B.graph)) :
    (ThetaTransmissionSubTwoCase B u
        (D + t • (one_chip u - one_chip v)) → tau t = t - 2) ∧
    (ThetaTransmissionSubOneCase B u v
        (D + t • (one_chip u - one_chip v)) → tau t = t - 1) ∧
    (ThetaTransmissionAddOneCase B u v
        (D + t • (one_chip u - one_chip v)) → tau t = t + 1) ∧
    (ThetaTransmissionAddTwoCase B u v
        (D + t • (one_chip u - one_chip v)) → tau t = t + 2) ∧
    (¬ ThetaTransmissionSubTwoCase B u
        (D + t • (one_chip u - one_chip v)) →
      ¬ ThetaTransmissionSubOneCase B u v
        (D + t • (one_chip u - one_chip v)) →
      ¬ ThetaTransmissionAddOneCase B u v
        (D + t • (one_chip u - one_chip v)) →
      ¬ ThetaTransmissionAddTwoCase B u v
        (D + t • (one_chip u - one_chip v)) → tau t = t) := by
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
