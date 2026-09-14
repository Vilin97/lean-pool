/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.RationalChord
public import LeanPool.Besicovitch.SixPoint.RootEdge
public import LeanPool.Besicovitch.SixPoint.SiblingIncidenceLedger

/-!
# The root--edge stage of the six-point failure tree

After the sibling supports choose the coincident endpoint `B11`, the two root--edge supports use
the opposite children. This file connects their geometric packings to the root--edge minimax and
records the elementary reductions shared by the two color directions.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

/-- The endpoint diameter target for the red root--second-child support. -/
def redRootEdgeTarget (configuration : SixPointConfiguration) : ℝ :=
  barC * (dist (configuration .red .root) (configuration .red .right) +
    rootedTriangleTotalRadius configuration .blue)

/-- The endpoint diameter target for the blue root--second-child support. -/
def blueRootEdgeTarget (configuration : SixPointConfiguration) : ℝ :=
  barC * (dist (configuration .blue .root) (configuration .blue .right) +
    rootedTriangleTotalRadius configuration .red)

/-- Support `57`, with the red root--second-child radius split at `x`. -/
def redRootEdgePackingAtEndpoint (configuration : SixPointConfiguration)
    (h : configuration.IsAdmissibleAt barS) (x : ℝ)
    (hxZero : 0 ≤ x)
    (hxEdge : x ≤ dist (configuration .red .root) (configuration .red .right)) :
    SixPointPacking configuration :=
  redRootEdgeBlueTrianglePacking configuration .right (by simp) rfl
    (h.child_distance .red .right (by simp)) hxZero hxEdge
    (h.child_distance .blue .left (by simp)) (h.child_distance .blue .right (by simp))

/-- Support `75`, with the blue root--second-child radius split at `x`. -/
def blueRootEdgePackingAtEndpoint (configuration : SixPointConfiguration)
    (h : configuration.IsAdmissibleAt barS) (x : ℝ)
    (hxZero : 0 ≤ x)
    (hxEdge : x ≤ dist (configuration .blue .root) (configuration .blue .right)) :
    SixPointPacking configuration :=
  blueRootEdgeRedTrianglePacking configuration .right (by simp) rfl
    (h.child_distance .blue .right (by simp)) hxZero hxEdge
    (h.child_distance .red .left (by simp)) (h.child_distance .red .right (by simp))

/-- A feasible red root--edge split below its target gives nonnegative score. -/
theorem redRootEdgePackingAtEndpoint_score_nonnegative
    (configuration : SixPointConfiguration) (h : configuration.IsAdmissibleAt barS) (x : ℝ)
    (hxZero : 0 ≤ x)
    (hxEdge : x ≤ dist (configuration .red .root) (configuration .red .right))
    (hdiameter : rootEdgeSplitDiameter
      (dist (configuration .red .root) (configuration .red .right))
      (dist (configuration .blue .left) (configuration .blue .right)) x
      (redRootBlueTriangleReach configuration)
      (redChildBlueTriangleReach configuration .right) ≤ redRootEdgeTarget configuration) :
    0 ≤ (redRootEdgePackingAtEndpoint configuration h x hxZero hxEdge).score barS := by
  have hblueOne : 1 ≤ dist (configuration .blue .left) (configuration .blue .right) :=
    one_lt_barC_and_barC_lt_two.1.le.trans
      (sibling_distance_mem_endpoint_interval h .blue).1
  simp only [redRootEdgePackingAtEndpoint, SixPointPacking.score]
  rw [redRootEdgeBlueTrianglePacking_totalRadius,
    redRootEdgeBlueTrianglePacking_virtualDiameter (hMdist := rfl) (hM := hblueOne)]
  simp only [barS]
  rw [show 2 * (barC / 2) = barC by ring]
  rw [sub_nonneg, div_le_iff₀ barC_pos]
  simpa [redRootEdgeTarget, rootedTriangleTotalRadius, mul_comm] using hdiameter

/-- A feasible blue root--edge split below its target gives nonnegative score. -/
theorem blueRootEdgePackingAtEndpoint_score_nonnegative
    (configuration : SixPointConfiguration) (h : configuration.IsAdmissibleAt barS) (x : ℝ)
    (hxZero : 0 ≤ x)
    (hxEdge : x ≤ dist (configuration .blue .root) (configuration .blue .right))
    (hdiameter : rootEdgeSplitDiameter
      (dist (configuration .blue .root) (configuration .blue .right))
      (dist (configuration .red .left) (configuration .red .right)) x
      (blueRootRedTriangleReach configuration)
      (blueChildRedTriangleReach configuration .right) ≤ blueRootEdgeTarget configuration) :
    0 ≤ (blueRootEdgePackingAtEndpoint configuration h x hxZero hxEdge).score barS := by
  have hredOne : 1 ≤ dist (configuration .red .left) (configuration .red .right) :=
    one_lt_barC_and_barC_lt_two.1.le.trans
      (sibling_distance_mem_endpoint_interval h .red).1
  simp only [blueRootEdgePackingAtEndpoint, SixPointPacking.score]
  rw [blueRootEdgeRedTrianglePacking_totalRadius,
    blueRootEdgeRedTrianglePacking_virtualDiameter (hLdist := rfl) (hL := hredOne)]
  simp only [barS]
  rw [show 2 * (barC / 2) = barC by ring]
  rw [sub_nonneg, div_le_iff₀ barC_pos]
  simpa [blueRootEdgeTarget, rootedTriangleTotalRadius, mul_comm] using hdiameter

/-- Every feasible split of support `57` has negative score. -/
def RedRootEdgeFails (configuration : SixPointConfiguration)
    (h : configuration.IsAdmissibleAt barS) : Prop :=
  ∀ (x : ℝ) (hxZero : 0 ≤ x)
    (hxEdge : x ≤ dist (configuration .red .root) (configuration .red .right)),
    (redRootEdgePackingAtEndpoint configuration h x hxZero hxEdge).score barS < 0

/-- Every feasible split of support `75` has negative score. -/
def BlueRootEdgeFails (configuration : SixPointConfiguration)
    (h : configuration.IsAdmissibleAt barS) : Prop :=
  ∀ (x : ℝ) (hxZero : 0 ≤ x)
    (hxEdge : x ≤ dist (configuration .blue .root) (configuration .blue .right)),
    (blueRootEdgePackingAtEndpoint configuration h x hxZero hxEdge).score barS < 0

/-- Failure of support `57` makes every feasible root--edge split exceed its target. -/
theorem redRootEdge_split_failure
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hfailure : RedRootEdgeFails configuration h) :
    ∀ (x : ℝ) (_hxZero : 0 ≤ x)
      (_hxEdge : x ≤ dist (configuration .red .root) (configuration .red .right)),
      redRootEdgeTarget configuration < rootEdgeSplitDiameter
        (dist (configuration .red .root) (configuration .red .right))
        (dist (configuration .blue .left) (configuration .blue .right)) x
        (redRootBlueTriangleReach configuration)
        (redChildBlueTriangleReach configuration .right) := by
  intro x hxZero hxEdge
  exact lt_of_not_ge fun hdiameter ↦
    (not_lt_of_ge (redRootEdgePackingAtEndpoint_score_nonnegative configuration h x hxZero hxEdge
      hdiameter)) (hfailure x hxZero hxEdge)

/-- Failure of support `75` makes every feasible root--edge split exceed its target. -/
theorem blueRootEdge_split_failure
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hfailure : BlueRootEdgeFails configuration h) :
    ∀ (x : ℝ) (_hxZero : 0 ≤ x)
      (_hxEdge : x ≤ dist (configuration .blue .root) (configuration .blue .right)),
      blueRootEdgeTarget configuration < rootEdgeSplitDiameter
        (dist (configuration .blue .root) (configuration .blue .right))
        (dist (configuration .red .left) (configuration .red .right)) x
        (blueRootRedTriangleReach configuration)
        (blueChildRedTriangleReach configuration .right) := by
  intro x hxZero hxEdge
  exact lt_of_not_ge fun hdiameter ↦
    (not_lt_of_ge (blueRootEdgePackingAtEndpoint_score_nonnegative configuration h x hxZero hxEdge
      hdiameter)) (hfailure x hxZero hxEdge)

private theorem barC_rootEdge_child_gap_pos : 0 < barC ^ 2 + barC - 3 := by
  have hc := barC_mem_isolation_box.1
  norm_num at hc ⊢
  nlinarith [sq_nonneg (barC - 1)]

private theorem barC_rootEdge_order_gap_pos : 2 < 4 * barC * (barC - 1) := by
  have hc := barC_mem_isolation_box.1
  norm_num at hc ⊢
  nlinarith [sq_nonneg (barC - 1)]

/-- The selected matching and blue coincident endpoint exclude the blue internal primitive. -/
theorem SixPointConfiguration.blueRootEdgeInternalSlack_neg_of_matching_endpoint
    (configuration : SixPointConfiguration) (h : configuration.IsAdmissibleAt barS)
    (hmatching : 0 ≤ matchingFailureSlack barC
      (dist (configuration .red .left) (configuration .red .right))
      (dist (configuration .blue .left) (configuration .blue .right))
      (dist (configuration .red .left) (configuration .blue .left))
      (dist (configuration .red .right) (configuration .blue .right)))
    (hendpoint : 0 ≤ blueEndpointFailureSlack barC
      (dist (configuration .red .left) (configuration .red .right))
      (dist (configuration .blue .left) (configuration .blue .right))
      (dist (configuration .red .root) (configuration .red .left))
      (dist (configuration .red .root) (configuration .red .right))
      (dist (configuration .red .left) (configuration .blue .left))) :
    blueRootEdgeInternalSlack barC
      (dist (configuration .red .left) (configuration .red .right))
      (dist (configuration .blue .root) (configuration .blue .right))
      (dist (configuration .red .root) (configuration .red .left))
      (dist (configuration .red .root) (configuration .red .right)) < 0 := by
  let e := configuration.rootDisplacement
  let p₁ := configuration.redDisplacement .left
  let p₂ := configuration.redDisplacement .right
  let w₁ := configuration.bluePullback .left
  let w₂ := configuration.bluePullback .right
  have hL : ‖p₁ - p₂‖ =
      dist (configuration .red .left) (configuration .red .right) := by
    rw [← dist_eq_norm, configuration.dist_redDisplacement]
  have hM : ‖w₁ - w₂‖ =
      dist (configuration .blue .left) (configuration .blue .right) := by
    rw [← dist_eq_norm, configuration.dist_bluePullback]
  have hb₂ : ‖w₂‖ = dist (configuration .blue .root) (configuration .blue .right) := by
    simp [w₂, SixPointConfiguration.bluePullback, dist_eq_norm]
  have hr₁ : ‖p₁‖ = dist (configuration .red .root) (configuration .red .left) := by
    simp [p₁, SixPointConfiguration.redDisplacement, dist_eq_norm, norm_sub_rev]
  have hr₂ : ‖p₂‖ = dist (configuration .red .root) (configuration .red .right) := by
    simp [p₂, SixPointConfiguration.redDisplacement, dist_eq_norm, norm_sub_rev]
  have hB₁₁ : ‖e - p₁ - w₁‖ =
      dist (configuration .red .left) (configuration .blue .left) := by
    exact (configuration.dist_red_blue_eq_norm .left .left).symm
  have hB₂₂ : ‖e - p₂ - w₂‖ =
      dist (configuration .red .right) (configuration .blue .right) := by
    exact (configuration.dist_red_blue_eq_norm .right .right).symm
  have hredSeparation : barC ≤ ‖p₁ - p₂‖ := by
    have hsibling := configuration.two_mul_le_dist_redDisplacement h
    rw [barS, show 2 * (barC / 2) = barC by ring, dist_eq_norm] at hsibling
    exact hsibling
  have hblueSeparation : barC ≤ ‖w₁ - w₂‖ := by
    have hsibling := configuration.two_mul_le_dist_bluePullback h
    rw [barS, show 2 * (barC / 2) = barC by ring, dist_eq_norm] at hsibling
    exact hsibling
  have hnegative := blueRootEdgeInternalSlack_neg e p₁ p₂ w₁ w₂
    (configuration.norm_rootDisplacement h)
    (configuration.norm_redDisplacement_le_one h (by simp))
    (configuration.norm_redDisplacement_le_one h (by simp))
    (configuration.norm_bluePullback_le_one h (by simp))
    (configuration.norm_bluePullback_le_one h (by simp)) hredSeparation hblueSeparation
    (by simpa only [hL, hM, hB₁₁, hB₂₂] using hmatching)
    (by simpa only [hL, hM, hr₁, hr₂, hB₁₁] using hendpoint)
  simpa only [hL, hb₂, hr₁, hr₂] using hnegative

/-- On the selected endpoint branch, failure of the red root--edge support can only use one of
the two child-labelled balanced terms. -/
theorem redRootEdge_failure_routes_to_child_balanced
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration)
    (hendpoint : redSiblingTriangleFailure configuration (.endpoint 0))
    (hfailure : RedRootEdgeFails configuration h) :
    2 * redRootEdgeTarget configuration <
        dist (configuration .red .root) (configuration .red .right) +
          redRootBlueTriangleReach configuration .left +
          redChildBlueTriangleReach configuration .right .left ∨
      2 * redRootEdgeTarget configuration <
        dist (configuration .red .root) (configuration .red .right) +
          redRootBlueTriangleReach configuration .left +
          redChildBlueTriangleReach configuration .right .right := by
  let R := dist (configuration .red .root) (configuration .red .right)
  let L := dist (configuration .red .left) (configuration .red .right)
  let M := dist (configuration .blue .left) (configuration .blue .right)
  let r₁ := dist (configuration .red .root) (configuration .red .left)
  let b₁ := dist (configuration .blue .root) (configuration .blue .left)
  let b₂ := dist (configuration .blue .root) (configuration .blue .right)
  have hcOne : 1 < barC := one_lt_barC_and_barC_lt_two.1
  have hcTwo : barC < 2 := one_lt_barC_and_barC_lt_two.2
  have hLLower : barC ≤ L := by
    simpa [L] using (sibling_distance_mem_endpoint_interval h .red).1
  have hMLower : barC ≤ M := by
    simpa [M] using (sibling_distance_mem_endpoint_interval h .blue).1
  have hROne : R ≤ 1 := by
    simpa [R] using h.child_distance .red .right (by simp)
  have hr₁One : r₁ ≤ 1 := by
    simpa [r₁] using h.child_distance .red .left (by simp)
  have hb₁One : b₁ ≤ 1 := by
    simpa [b₁] using h.child_distance .blue .left (by simp)
  have hb₂One : b₂ ≤ 1 := by
    simpa [b₂] using h.child_distance .blue .right (by simp)
  have hRTriangle : L ≤ r₁ + R := by
    calc
      L ≤ dist (configuration .red .left) (configuration .red .root) + R := by
        simpa [L, R] using dist_triangle (configuration .red .left)
          (configuration .red .root) (configuration .red .right)
      _ = r₁ + R := by rw [dist_comm]
  have hRLower : barC - 1 ≤ R := by linarith
  have hRPos : 0 < R := by linarith
  have hBlueTriangle : M ≤ b₁ + b₂ := by
    calc
      M ≤ dist (configuration .blue .left) (configuration .blue .root) + b₂ := by
        simpa [M, b₂] using dist_triangle (configuration .blue .left)
          (configuration .blue .root) (configuration .blue .right)
      _ = b₁ + b₂ := by rw [dist_comm]
  have hRootRoot :
      redRootBlueTriangleReach configuration .root ≤ redRootEdgeTarget configuration - R := by
    have hRScaled := mul_le_mul_of_nonneg_left hRLower (by linarith : 0 ≤ barC - 1)
    have hBlueScaled := mul_le_mul_of_nonneg_left hBlueTriangle
      (by linarith : 0 ≤ (barC - 1) / 2)
    have hMScaled := mul_le_mul_of_nonneg_left hMLower barC_pos.le
    simp [redRootBlueTriangleReach, redRootEdgeTarget, rootedTriangleTotalRadius,
      canonicalTriangleRadius, R, h.root_distance]
    nlinarith
  have hChildRoot :
      redChildBlueTriangleReach configuration .right .root ≤
        redRootEdgeTarget configuration - R := by
    have hcross : dist (configuration .red .right) (configuration .blue .root) ≤ R + 1 := by
      calc
        _ ≤ dist (configuration .red .right) (configuration .red .root) +
            dist (configuration .red .root) (configuration .blue .root) :=
          dist_triangle _ _ _
        _ = R + 1 := by rw [dist_comm, h.root_distance]
    have hRScaled := mul_le_mul_of_nonpos_left hROne (by linarith : barC - 2 ≤ 0)
    have hBlueScaled := mul_le_mul_of_nonneg_left hBlueTriangle
      (by linarith : 0 ≤ (barC - 1) / 2)
    have hMScaled := mul_le_mul_of_nonneg_left hMLower barC_pos.le
    simp [redChildBlueTriangleReach, redRootEdgeTarget, rootedTriangleTotalRadius,
      canonicalTriangleRadius, R]
    nlinarith [barC_rootEdge_child_gap_pos]
  have hLeftLower : redRootEdgeTarget configuration - R ≤
      redRootBlueTriangleReach configuration .left := by
    have hB₁₁Triangle :
        dist (configuration .red .left) (configuration .blue .left) ≤ r₁ +
          dist (configuration .red .root) (configuration .blue .left) := by
      calc
        _ ≤ dist (configuration .red .left) (configuration .red .root) +
            dist (configuration .red .root) (configuration .blue .left) :=
          dist_triangle _ _ _
        _ = _ := by rw [dist_comm]
    have hLRLower : barC - 1 ≤ L - R := by linarith
    have hLRScaled := mul_le_mul_of_nonneg_left hLRLower
      (by linarith : 0 ≤ barC - 1)
    simp [redSiblingTriangleFailure, siblingTriangleWitnessExceeds, incidenceFirst,
      incidenceSecond, incidenceChild, redSiblingTriangleTarget, rootedTriangleTotalRadius,
      redSiblingBlueTriangleReach, canonicalTriangleRadius, redRootEdgeTarget,
      redRootBlueTriangleReach, R] at hendpoint ⊢
    nlinarith
  have hLeftLargest : redRootBlueTriangleReach configuration .right <
      redRootBlueTriangleReach configuration .left := by
    by_contra hnot
    have hreachOrder : redRootBlueTriangleReach configuration .left ≤
        redRootBlueTriangleReach configuration .right := not_lt.mp hnot
    have hRootLeft :
        dist (configuration .red .root) (configuration .blue .left) ≤ 1 + b₁ := by
      calc
        _ ≤ dist (configuration .red .root) (configuration .blue .root) +
            dist (configuration .blue .root) (configuration .blue .left) :=
          dist_triangle _ _ _
        _ = _ := by rw [h.root_distance]
    have hRootRight :
        dist (configuration .red .root) (configuration .blue .right) ≤ 1 + b₂ := by
      calc
        _ ≤ dist (configuration .red .root) (configuration .blue .root) +
            dist (configuration .blue .root) (configuration .blue .right) :=
          dist_triangle _ _ _
        _ = _ := by rw [h.root_distance]
    have hB₁₁Triangle :
        dist (configuration .red .left) (configuration .blue .left) ≤ r₁ +
          dist (configuration .red .root) (configuration .blue .left) := by
      calc
        _ ≤ dist (configuration .red .left) (configuration .red .root) +
            dist (configuration .red .root) (configuration .blue .left) :=
          dist_triangle _ _ _
        _ = _ := by rw [dist_comm]
    have hLScaled := mul_le_mul_of_nonneg_left hLLower
      (by linarith : 0 ≤ barC - 1)
    have hSumLower : 2 * barC ≤ b₁ + b₂ + M := by linarith
    have hSumScaled := mul_le_mul_of_nonneg_left hSumLower
      (by linarith : 0 ≤ barC - 1)
    simp [redSiblingTriangleFailure, siblingTriangleWitnessExceeds, incidenceFirst,
      incidenceSecond, incidenceChild, redSiblingTriangleTarget, rootedTriangleTotalRadius,
      redSiblingBlueTriangleReach, canonicalTriangleRadius,
      redRootBlueTriangleReach] at hendpoint hreachOrder ⊢
    nlinarith [barC_rootEdge_order_gap_pos]
  have hClose : ∀ label, label ≠ .root →
      redRootBlueTriangleReach configuration label - R ≤
        redChildBlueTriangleReach configuration .right label := by
    intro label hlabel
    have htriangle := dist_triangle (configuration .red .root)
      (configuration .red .right) (configuration .blue label)
    simp only [redRootBlueTriangleReach, redChildBlueTriangleReach]
    dsimp only [R] at htriangle ⊢
    linarith
  have hroute := rootEdge_failure_routing hRPos.le (redRootEdge_split_failure h hfailure)
  rcases rootEdge_failure_reduces_to_three_types hRPos hRootRoot hChildRoot hLeftLower
      hLeftLargest hClose hroute with hinternal | hleft | hright
  · have hmatchingSlack : 0 ≤ matchingFailureSlack barC L M
        (dist (configuration .red .left) (configuration .blue .left))
        (dist (configuration .red .right) (configuration .blue .right)) := by
      simpa [SelectedDiagonalMatchingFails, matchingFailureSlack, incidenceCrossDistance,
        incidenceChild, L, M] using hmatching
    have hendpointSlack : 0 ≤ redEndpointFailureSlack barC L M b₁ b₂
        (dist (configuration .red .left) (configuration .blue .left)) := by
      simp [redSiblingTriangleFailure,
        siblingTriangleWitnessExceeds, incidenceFirst, incidenceSecond, incidenceChild,
        redSiblingTriangleTarget, rootedTriangleTotalRadius, redSiblingBlueTriangleReach,
        canonicalTriangleRadius] at hendpoint
      simp only [redEndpointFailureSlack]
      dsimp only [L, M, b₁, b₂]
      linarith
    have hnegative := configuration.redRootEdgeInternalSlack_neg_of_matching_endpoint h
      hmatchingSlack hendpointSlack
    have hnegative' : 2 * M - barC *
        (R + (b₁ + b₂ + M) / 2) < 0 := by
      simpa [redRootEdgeInternalSlack, R, M, b₁, b₂] using hnegative
    have hinternal' : barC * (R + (b₁ + b₂ + M) / 2) < 2 * M := by
      simpa [redRootEdgeTarget, rootedTriangleTotalRadius, R, M, b₁, b₂] using hinternal
    exfalso
    linarith
  · dsimp only [R] at hleft
    exact Or.inl hleft
  · dsimp only [R] at hright
    exact Or.inr hright

/-- The color-reversed root--edge failure has the same two surviving balanced terms. -/
theorem blueRootEdge_failure_routes_to_child_balanced
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration)
    (hendpoint : blueSiblingTriangleFailure configuration (.endpoint 0))
    (hfailure : BlueRootEdgeFails configuration h) :
    2 * blueRootEdgeTarget configuration <
        dist (configuration .blue .root) (configuration .blue .right) +
          blueRootRedTriangleReach configuration .left +
          blueChildRedTriangleReach configuration .right .left ∨
      2 * blueRootEdgeTarget configuration <
        dist (configuration .blue .root) (configuration .blue .right) +
          blueRootRedTriangleReach configuration .left +
          blueChildRedTriangleReach configuration .right .right := by
  let R := dist (configuration .blue .root) (configuration .blue .right)
  let L := dist (configuration .red .left) (configuration .red .right)
  let M := dist (configuration .blue .left) (configuration .blue .right)
  let b₁ := dist (configuration .blue .root) (configuration .blue .left)
  let r₁ := dist (configuration .red .root) (configuration .red .left)
  let r₂ := dist (configuration .red .root) (configuration .red .right)
  have hcOne : 1 < barC := one_lt_barC_and_barC_lt_two.1
  have hcTwo : barC < 2 := one_lt_barC_and_barC_lt_two.2
  have hrootReverse :
      dist (configuration .blue .root) (configuration .red .root) = 1 := by
    simpa [dist_comm] using h.root_distance
  have hLLower : barC ≤ L := by
    simpa [L] using (sibling_distance_mem_endpoint_interval h .red).1
  have hMLower : barC ≤ M := by
    simpa [M] using (sibling_distance_mem_endpoint_interval h .blue).1
  have hROne : R ≤ 1 := by
    simpa [R] using h.child_distance .blue .right (by simp)
  have hb₁One : b₁ ≤ 1 := by
    simpa [b₁] using h.child_distance .blue .left (by simp)
  have hr₁One : r₁ ≤ 1 := by
    simpa [r₁] using h.child_distance .red .left (by simp)
  have hr₂One : r₂ ≤ 1 := by
    simpa [r₂] using h.child_distance .red .right (by simp)
  have hBlueTriangle : M ≤ b₁ + R := by
    calc
      M ≤ dist (configuration .blue .left) (configuration .blue .root) + R := by
        simpa [M, R] using dist_triangle (configuration .blue .left)
          (configuration .blue .root) (configuration .blue .right)
      _ = b₁ + R := by rw [dist_comm]
  have hRLower : barC - 1 ≤ R := by linarith
  have hRPos : 0 < R := by linarith
  have hRedTriangle : L ≤ r₁ + r₂ := by
    calc
      L ≤ dist (configuration .red .left) (configuration .red .root) + r₂ := by
        simpa [L, r₂] using dist_triangle (configuration .red .left)
          (configuration .red .root) (configuration .red .right)
      _ = r₁ + r₂ := by rw [dist_comm]
  have hRootRoot :
      blueRootRedTriangleReach configuration .root ≤ blueRootEdgeTarget configuration - R := by
    have hRScaled := mul_le_mul_of_nonneg_left hRLower (by linarith : 0 ≤ barC - 1)
    have hRedScaled := mul_le_mul_of_nonneg_left hRedTriangle
      (by linarith : 0 ≤ (barC - 1) / 2)
    have hLScaled := mul_le_mul_of_nonneg_left hLLower barC_pos.le
    simp [blueRootRedTriangleReach, blueRootEdgeTarget, rootedTriangleTotalRadius,
      canonicalTriangleRadius, R, hrootReverse]
    nlinarith
  have hChildRoot :
      blueChildRedTriangleReach configuration .right .root ≤
        blueRootEdgeTarget configuration - R := by
    have hcross : dist (configuration .blue .right) (configuration .red .root) ≤ R + 1 := by
      calc
        _ ≤ dist (configuration .blue .right) (configuration .blue .root) +
            dist (configuration .blue .root) (configuration .red .root) :=
          dist_triangle _ _ _
        _ = R + 1 := by rw [dist_comm (configuration .blue .right), hrootReverse]
    have hRScaled := mul_le_mul_of_nonpos_left hROne (by linarith : barC - 2 ≤ 0)
    have hRedScaled := mul_le_mul_of_nonneg_left hRedTriangle
      (by linarith : 0 ≤ (barC - 1) / 2)
    have hLScaled := mul_le_mul_of_nonneg_left hLLower barC_pos.le
    simp [blueChildRedTriangleReach, blueRootEdgeTarget, rootedTriangleTotalRadius,
      canonicalTriangleRadius, R]
    nlinarith [barC_rootEdge_child_gap_pos]
  have hLeftLower : blueRootEdgeTarget configuration - R ≤
      blueRootRedTriangleReach configuration .left := by
    have hB₁₁Triangle :
        dist (configuration .blue .left) (configuration .red .left) ≤ b₁ +
          dist (configuration .blue .root) (configuration .red .left) := by
      calc
        _ ≤ dist (configuration .blue .left) (configuration .blue .root) +
            dist (configuration .blue .root) (configuration .red .left) :=
          dist_triangle _ _ _
        _ = _ := by rw [dist_comm (configuration .blue .left)]
    have hMRLower : barC - 1 ≤ M - R := by linarith
    have hMRScaled := mul_le_mul_of_nonneg_left hMRLower
      (by linarith : 0 ≤ barC - 1)
    simp [blueSiblingTriangleFailure, transposeBlueEndpointWitness, transposeEndpointCode,
      siblingTriangleWitnessExceeds, incidenceFirst, incidenceSecond, incidenceChild,
      blueSiblingTriangleTarget, rootedTriangleTotalRadius, blueSiblingRedTriangleReach,
      canonicalTriangleRadius, blueRootEdgeTarget, blueRootRedTriangleReach, R] at hendpoint ⊢
    nlinarith
  have hLeftLargest : blueRootRedTriangleReach configuration .right <
      blueRootRedTriangleReach configuration .left := by
    by_contra hnot
    have hreachOrder : blueRootRedTriangleReach configuration .left ≤
        blueRootRedTriangleReach configuration .right := not_lt.mp hnot
    have hRootLeft :
        dist (configuration .blue .root) (configuration .red .left) ≤ 1 + r₁ := by
      calc
        _ ≤ dist (configuration .blue .root) (configuration .red .root) +
            dist (configuration .red .root) (configuration .red .left) :=
          dist_triangle _ _ _
        _ = _ := by rw [hrootReverse]
    have hRootRight :
        dist (configuration .blue .root) (configuration .red .right) ≤ 1 + r₂ := by
      calc
        _ ≤ dist (configuration .blue .root) (configuration .red .root) +
            dist (configuration .red .root) (configuration .red .right) :=
          dist_triangle _ _ _
        _ = _ := by rw [hrootReverse]
    have hB₁₁Triangle :
        dist (configuration .blue .left) (configuration .red .left) ≤ b₁ +
          dist (configuration .blue .root) (configuration .red .left) := by
      calc
        _ ≤ dist (configuration .blue .left) (configuration .blue .root) +
            dist (configuration .blue .root) (configuration .red .left) :=
          dist_triangle _ _ _
        _ = _ := by rw [dist_comm (configuration .blue .left)]
    have hMScaled := mul_le_mul_of_nonneg_left hMLower
      (by linarith : 0 ≤ barC - 1)
    have hSumLower : 2 * barC ≤ r₁ + r₂ + L := by linarith
    have hSumScaled := mul_le_mul_of_nonneg_left hSumLower
      (by linarith : 0 ≤ barC - 1)
    simp [blueSiblingTriangleFailure, transposeBlueEndpointWitness, transposeEndpointCode,
      siblingTriangleWitnessExceeds, incidenceFirst, incidenceSecond, incidenceChild,
      blueSiblingTriangleTarget, rootedTriangleTotalRadius, blueSiblingRedTriangleReach,
      canonicalTriangleRadius, blueRootRedTriangleReach] at hendpoint hreachOrder ⊢
    nlinarith [barC_rootEdge_order_gap_pos]
  have hClose : ∀ label, label ≠ .root →
      blueRootRedTriangleReach configuration label - R ≤
        blueChildRedTriangleReach configuration .right label := by
    intro label hlabel
    have htriangle := dist_triangle (configuration .blue .root)
      (configuration .blue .right) (configuration .red label)
    simp only [blueRootRedTriangleReach, blueChildRedTriangleReach]
    dsimp only [R] at htriangle ⊢
    linarith
  have hroute := rootEdge_failure_routing hRPos.le (blueRootEdge_split_failure h hfailure)
  rcases rootEdge_failure_reduces_to_three_types hRPos hRootRoot hChildRoot hLeftLower
      hLeftLargest hClose hroute with hinternal | hleft | hright
  · have hmatchingSlack : 0 ≤ matchingFailureSlack barC L M
        (dist (configuration .red .left) (configuration .blue .left))
        (dist (configuration .red .right) (configuration .blue .right)) := by
      simpa [SelectedDiagonalMatchingFails, matchingFailureSlack, incidenceCrossDistance,
        incidenceChild, L, M] using hmatching
    have hendpointSlack : 0 ≤ blueEndpointFailureSlack barC L M r₁ r₂
        (dist (configuration .red .left) (configuration .blue .left)) := by
      simp [blueSiblingTriangleFailure, transposeBlueEndpointWitness, transposeEndpointCode,
        siblingTriangleWitnessExceeds, incidenceFirst, incidenceSecond, incidenceChild,
        blueSiblingTriangleTarget, rootedTriangleTotalRadius, blueSiblingRedTriangleReach,
        canonicalTriangleRadius] at hendpoint
      rw [dist_comm (configuration .blue .left) (configuration .red .left)] at hendpoint
      simp only [blueEndpointFailureSlack]
      dsimp only [L, M, r₁, r₂]
      linarith
    have hnegative := configuration.blueRootEdgeInternalSlack_neg_of_matching_endpoint h
      hmatchingSlack hendpointSlack
    have hnegative' : 2 * L - barC *
        (R + (r₁ + r₂ + L) / 2) < 0 := by
      simpa [blueRootEdgeInternalSlack, R, L, r₁, r₂] using hnegative
    have hinternal' : barC * (R + (r₁ + r₂ + L) / 2) < 2 * L := by
      simpa [blueRootEdgeTarget, rootedTriangleTotalRadius, R, L, r₁, r₂] using hinternal
    exfalso
    linarith
  · dsimp only [R] at hleft
    exact Or.inl hleft
  · dsimp only [R] at hright
    exact Or.inr hright

end LeanPool.Besicovitch
