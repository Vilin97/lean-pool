/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.RationalChord
public import LeanPool.Besicovitch.SixPoint.SiblingTriangle
public import LeanPool.Besicovitch.SixPoint.SiblingTangent

/-!
# Incidences in the sibling--triangle branch

This file encodes the finite incidence ledger for simultaneous failures of supports `67` and
`76`. Endpoint and balanced witnesses use the four codes from the paper, and the orbit types
are exactly the six, eight, and seven cases left by the fixed diagonal matching.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

/-- The child at one coordinate of an incidence code. -/
def incidenceChild : Fin 2 → SixPointLabel
  | 0 => .left
  | 1 => .right

/-- The other child index. -/
def otherChild : Fin 2 → Fin 2
  | 0 => 1
  | 1 => 0

/-- The first child coordinate in the code `2 i + j`. -/
def incidenceFirst : Fin 4 → Fin 2
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1

/-- The second child coordinate in the code `2 i + j`. -/
def incidenceSecond : Fin 4 → Fin 2
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 1

/-- A sibling--triangle failure is witnessed by an endpoint or a balanced pair of terms. -/
inductive SiblingTriangleWitness
  | endpoint (code : Fin 4)
  | balanced (code : Fin 4)
  deriving DecidableEq

/-- Simultaneously swapping the two children sends an endpoint code `a` to `3 - a`. -/
def swapEndpointCode : Fin 4 → Fin 4
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0

/-- Transposing the two colors transposes an endpoint's two coordinates. -/
def transposeEndpointCode : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 3

/-- Put a blue endpoint witness into the common `(red child, blue child)` code convention. -/
def transposeBlueEndpointWitness : SiblingTriangleWitness → SiblingTriangleWitness
  | .endpoint code => .endpoint (transposeEndpointCode code)
  | .balanced code => .balanced code

/-- Simultaneously swapping the children exchanges balanced codes `0` and `3`. -/
def swapBalancedCode : Fin 4 → Fin 4
  | 0 => 3
  | 1 => 1
  | 2 => 2
  | 3 => 0

/-- The six endpoint--endpoint orbits relative to the diagonal matching. -/
inductive EndpointEndpointOrbit
  | matchedCoincident
  | offMatchingCoincident
  | adjacentFirst
  | adjacentSecond
  | matchingDisjoint
  | offMatchingDisjoint
  deriving DecidableEq

/-- The eight endpoint--balanced orbits after orienting the endpoint from red to blue. -/
inductive EndpointBalancedOrbit
  | e0s0
  | e0s1
  | e0s2
  | e0s3
  | e1s0
  | e1s1
  | e1s2
  | e1s3
  deriving DecidableEq

/-- The seven balanced--balanced orbits relative to the diagonal matching. -/
inductive BalancedBalancedOrbit
  | s0s0
  | s0s3
  | s0s1
  | s0s2
  | s1s1
  | s1s2
  | s2s2
  deriving DecidableEq

/-- Classify an ordered pair of endpoint codes under child swap and color transposition. -/
def endpointEndpointOrbit : Fin 4 → Fin 4 → EndpointEndpointOrbit
  | 0, 0 | 3, 3 => .matchedCoincident
  | 1, 1 | 2, 2 => .offMatchingCoincident
  | 0, 1 | 3, 2 | 2, 0 | 1, 3 => .adjacentFirst
  | 0, 2 | 3, 1 | 1, 0 | 2, 3 => .adjacentSecond
  | 0, 3 | 3, 0 => .matchingDisjoint
  | 1, 2 | 2, 1 => .offMatchingDisjoint

/-- Classify an endpoint code and a balanced code under simultaneous child swap. -/
def endpointBalancedOrbit : Fin 4 → Fin 4 → EndpointBalancedOrbit
  | 0, 0 | 3, 3 => .e0s0
  | 0, 1 | 3, 1 => .e0s1
  | 0, 2 | 3, 2 => .e0s2
  | 0, 3 | 3, 0 => .e0s3
  | 1, 0 | 2, 3 => .e1s0
  | 1, 1 | 2, 1 => .e1s1
  | 1, 2 | 2, 2 => .e1s2
  | 1, 3 | 2, 0 => .e1s3

/-- Classify an ordered pair of balanced codes under child swap and color transposition. -/
def balancedBalancedOrbit : Fin 4 → Fin 4 → BalancedBalancedOrbit
  | 0, 0 | 3, 3 => .s0s0
  | 0, 3 | 3, 0 => .s0s3
  | 0, 1 | 3, 1 | 1, 0 | 1, 3 => .s0s1
  | 0, 2 | 3, 2 | 2, 0 | 2, 3 => .s0s2
  | 1, 1 => .s1s1
  | 1, 2 | 2, 1 => .s1s2
  | 2, 2 => .s2s2

/-- The matched coincident orbit consists exactly of the two diagonal coincidences. -/
theorem endpointEndpointOrbit_eq_matchedCoincident_iff (redCode blueCode : Fin 4) :
    endpointEndpointOrbit redCode blueCode = .matchedCoincident ↔
      (redCode = 0 ∧ blueCode = 0) ∨ (redCode = 3 ∧ blueCode = 3) := by
  fin_cases redCode <;> fin_cases blueCode <;> simp [endpointEndpointOrbit]

/-- The endpoint--endpoint classifier is unchanged by simultaneous child swap. -/
@[simp] theorem endpointEndpointOrbit_swap (redCode blueCode : Fin 4) :
    endpointEndpointOrbit (swapEndpointCode redCode) (swapEndpointCode blueCode) =
      endpointEndpointOrbit redCode blueCode := by
  fin_cases redCode <;> fin_cases blueCode <;>
    rfl

/-- The endpoint--endpoint classifier is unchanged by color transposition. -/
@[simp] theorem endpointEndpointOrbit_transpose (redCode blueCode : Fin 4) :
    endpointEndpointOrbit (transposeEndpointCode blueCode)
      (transposeEndpointCode redCode) = endpointEndpointOrbit redCode blueCode := by
  fin_cases redCode <;> fin_cases blueCode <;>
    rfl

/-- The endpoint--balanced classifier is unchanged by simultaneous child swap. -/
@[simp] theorem endpointBalancedOrbit_swap (endpointCode balancedCode : Fin 4) :
    endpointBalancedOrbit (swapEndpointCode endpointCode) (swapBalancedCode balancedCode) =
      endpointBalancedOrbit endpointCode balancedCode := by
  fin_cases endpointCode <;> fin_cases balancedCode <;>
    rfl

/-- The balanced--balanced classifier is unchanged by simultaneous child swap. -/
@[simp] theorem balancedBalancedOrbit_swap (redCode blueCode : Fin 4) :
    balancedBalancedOrbit (swapBalancedCode redCode) (swapBalancedCode blueCode) =
      balancedBalancedOrbit redCode blueCode := by
  fin_cases redCode <;> fin_cases blueCode <;>
    rfl

/-- The balanced--balanced classifier is unchanged by color transposition. -/
theorem balancedBalancedOrbit_transpose (redCode blueCode : Fin 4) :
    balancedBalancedOrbit blueCode redCode = balancedBalancedOrbit redCode blueCode := by
  fin_cases redCode <;> fin_cases blueCode <;>
    rfl

/-- The threshold inequality selected by an endpoint or balanced sibling witness. -/
def siblingTriangleWitnessExceeds (L T : ℝ) (leftReach rightReach : SixPointLabel → ℝ) :
    SiblingTriangleWitness → Prop
  | .endpoint code =>
      let reach := if incidenceFirst code = 0 then leftReach else rightReach
      T < L - 1 + reach (incidenceChild (incidenceSecond code))
  | .balanced code =>
      2 * T < L + leftReach (incidenceChild (incidenceFirst code)) +
        rightReach (incidenceChild (incidenceSecond code))

/-- Removing root-labelled primitives turns the minimax route into one of the eight incidences. -/
theorem exists_siblingTriangleWitnessExceeds_of_failure
    {L M T : ℝ} {leftReach rightReach : SixPointLabel → ℝ}
    (hL : L ≤ 2) (hsameL : 2 * L ≤ T) (hsameM : 2 * M ≤ T)
    (hleftRoot : L - 1 + leftReach .root ≤ T)
    (hrightRoot : L - 1 + rightReach .root ≤ T)
    (hbalancedRoot : ∀ leftLabel rightLabel,
      leftLabel = .root ∨ rightLabel = .root →
        L + leftReach leftLabel + rightReach rightLabel ≤ 2 * T)
    (hfail : ∀ x : ℝ, L - 1 ≤ x → x ≤ 1 →
      T < siblingTriangleSplitDiameter L M x leftReach rightReach) :
    ∃ witness, siblingTriangleWitnessExceeds L T leftReach rightReach witness := by
  rcases siblingTriangle_failure_routing hL hsameL hsameM hfail with
    ⟨label, hlabel⟩ | ⟨label, hlabel⟩ | ⟨leftLabel, rightLabel, hlabels⟩
  · cases label with
    | root => exact (not_lt_of_ge hleftRoot hlabel).elim
    | left => exact ⟨.endpoint 0, hlabel⟩
    | right => exact ⟨.endpoint 1, hlabel⟩
  · cases label with
    | root => exact (not_lt_of_ge hrightRoot hlabel).elim
    | left => exact ⟨.endpoint 2, hlabel⟩
    | right => exact ⟨.endpoint 3, hlabel⟩
  · cases leftLabel <;> cases rightLabel
    · exact (not_lt_of_ge (hbalancedRoot .root .root (Or.inl rfl)) hlabels).elim
    · exact (not_lt_of_ge (hbalancedRoot .root .left (Or.inl rfl)) hlabels).elim
    · exact (not_lt_of_ge (hbalancedRoot .root .right (Or.inl rfl)) hlabels).elim
    · exact (not_lt_of_ge (hbalancedRoot .left .root (Or.inr rfl)) hlabels).elim
    · exact ⟨.balanced 0, hlabels⟩
    · exact ⟨.balanced 1, hlabels⟩
    · exact (not_lt_of_ge (hbalancedRoot .right .root (Or.inr rfl)) hlabels).elim
    · exact ⟨.balanced 2, hlabels⟩
    · exact ⟨.balanced 3, hlabels⟩

/-- The total canonical radius of one color's rooted triangle. -/
def rootedTriangleTotalRadius (configuration : SixPointConfiguration)
    (color : SixPointColor) : ℝ :=
  (dist (configuration color .root) (configuration color .left) +
    dist (configuration color .root) (configuration color .right) +
    dist (configuration color .left) (configuration color .right)) / 2

/-- The diameter threshold for support `67` at the exact endpoint. -/
def redSiblingTriangleTarget (configuration : SixPointConfiguration) : ℝ :=
  barC * (dist (configuration .red .left) (configuration .red .right) +
    rootedTriangleTotalRadius configuration .blue)

/-- The diameter threshold for support `76` at the exact endpoint. -/
def blueSiblingTriangleTarget (configuration : SixPointConfiguration) : ℝ :=
  barC * (dist (configuration .blue .left) (configuration .blue .right) +
    rootedTriangleTotalRadius configuration .red)

/-- The exact endpoint or balanced failure inequality for support `67`. -/
def redSiblingTriangleFailure (configuration : SixPointConfiguration) :
    SiblingTriangleWitness → Prop :=
  siblingTriangleWitnessExceeds
    (dist (configuration .red .left) (configuration .red .right))
    (redSiblingTriangleTarget configuration)
    (redSiblingBlueTriangleReach configuration .left)
    (redSiblingBlueTriangleReach configuration .right)

/-- The exact endpoint or balanced failure inequality for support `76`. -/
def blueSiblingTriangleFailure (configuration : SixPointConfiguration) :
    SiblingTriangleWitness → Prop :=
  fun witness ↦ siblingTriangleWitnessExceeds
    (dist (configuration .blue .left) (configuration .blue .right))
    (blueSiblingTriangleTarget configuration)
    (blueSiblingRedTriangleReach configuration .left)
    (blueSiblingRedTriangleReach configuration .right)
    (transposeBlueEndpointWitness witness)

/-- The average of the two root-to-child distances at a matched child index. -/
def matchedChildAverage (configuration : SixPointConfiguration) (child : Fin 2) : ℝ :=
  (dist (configuration .red .root) (configuration .red (incidenceChild child)) +
    dist (configuration .blue .root) (configuration .blue (incidenceChild child))) / 2

private theorem barC_internal_gap_pos : 0 < barC ^ 2 + 2 * barC - 4 := by
  have hc := barC_mem_isolation_box.1
  norm_num at hc ⊢
  nlinarith [sq_nonneg (barC - 1)]

private theorem barC_root_endpoint_gap_pos : 0 < 2 * barC ^ 2 - barC / 2 - 2 := by
  have hc := barC_mem_isolation_box.1
  norm_num at hc ⊢
  nlinarith [sq_nonneg (barC - 1)]

private theorem barC_balanced_root_gap_pos : 6 < 4 * barC ^ 2 - barC := by
  have hc := barC_mem_isolation_box.1
  norm_num at hc ⊢
  nlinarith [sq_nonneg (barC - 1)]

private theorem barC_disjoint_gap_neg : 2 + 4 * barC - 4 * barC ^ 2 < 0 := by
  have hc := barC_mem_isolation_box.1
  norm_num at hc ⊢
  nlinarith [sq_nonneg (barC - 1)]

private theorem sibling_internal_terms_le_target {L M U : ℝ}
    (hL : barC ≤ L ∧ L ≤ 2) (hM : barC ≤ M ∧ M ≤ 2) (hMU : M ≤ U) :
    2 * L ≤ barC * (L + U) ∧ 2 * M ≤ barC * (L + U) := by
  have hc_two : barC - 2 ≤ 0 := by linarith [one_lt_barC_and_barC_lt_two.2]
  have hc_nonneg : 0 ≤ barC := barC_pos.le
  have htarget : barC * (L + M) ≤ barC * (L + U) := by
    apply mul_le_mul_of_nonneg_left _ hc_nonneg
    linarith
  have hLM := mul_le_mul_of_nonneg_left hM.1 hc_nonneg
  have hML := mul_le_mul_of_nonneg_left hL.1 hc_nonneg
  have hLnegative := mul_le_mul_of_nonpos_left hL.2 hc_two
  have hMnegative := mul_le_mul_of_nonpos_left hM.2 hc_two
  constructor
  · apply le_trans (le_of_lt ?_) htarget
    nlinarith [barC_internal_gap_pos]
  · apply le_trans (le_of_lt ?_) htarget
    nlinarith [barC_internal_gap_pos]

private theorem root_endpoint_le_target {L M U reach : ℝ}
    (hL : barC ≤ L) (hM : barC ≤ M) (hMU : M ≤ U)
    (hreach : reach ≤ 3 - M / 2) : L - 1 + reach ≤ barC * (L + U) := by
  have hc_nonneg : 0 ≤ barC := barC_pos.le
  have hc_sub_one : 0 ≤ barC - 1 := by linarith [one_lt_barC_and_barC_lt_two.1]
  have hc_add_half : 0 ≤ barC + 1 / 2 := by positivity
  have hLscaled := mul_le_mul_of_nonneg_left hL hc_sub_one
  have hMscaled := mul_le_mul_of_nonneg_left hM hc_add_half
  have htarget : barC * (L + M) ≤ barC * (L + U) := by
    apply mul_le_mul_of_nonneg_left _ hc_nonneg
    linarith
  nlinarith [barC_root_endpoint_gap_pos]

private theorem balanced_root_le_target {L M U reachSum : ℝ}
    (hL : barC ≤ L) (hM : barC ≤ M) (hMU : M ≤ U)
    (hreach : reachSum ≤ 6) : L + reachSum ≤ 2 * (barC * (L + U)) := by
  have hc_nonneg : 0 ≤ barC := barC_pos.le
  have htwoCSubOne : 0 ≤ 2 * barC - 1 := by nlinarith [one_lt_barC_and_barC_lt_two.1]
  have htwoC : 0 ≤ 2 * barC := by positivity
  have hLscaled := mul_le_mul_of_nonneg_left hL htwoCSubOne
  have hMscaled := mul_le_mul_of_nonneg_left hM htwoC
  have htarget : barC * (L + M) ≤ barC * (L + U) := by
    apply mul_le_mul_of_nonneg_left _ hc_nonneg
    linarith
  nlinarith [barC_balanced_root_gap_pos]

/-- Each sibling length in an endpoint-admissible configuration lies between `barC` and two. -/
theorem sibling_distance_mem_endpoint_interval {configuration : SixPointConfiguration}
    (h : configuration.IsAdmissibleAt barS) (color : SixPointColor) :
    barC ≤ dist (configuration color .left) (configuration color .right) ∧
      dist (configuration color .left) (configuration color .right) ≤ 2 := by
  constructor
  · have hsibling := h.sibling_distance color
    rw [barS] at hsibling
    linarith
  · calc
      dist (configuration color .left) (configuration color .right) ≤
          dist (configuration color .left) (configuration color .root) +
            dist (configuration color .root) (configuration color .right) :=
        dist_triangle _ _ _
      _ ≤ 1 + 1 := add_le_add (by simpa [dist_comm] using h.child_distance color .left (by simp))
        (h.child_distance color .right (by simp))
      _ = 2 := by norm_num

/-- The canonical triangle total lies between its sibling side and two. -/
theorem rootedTriangleTotalRadius_mem_endpoint_interval
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (color : SixPointColor) :
    dist (configuration color .left) (configuration color .right) ≤
        rootedTriangleTotalRadius configuration color ∧
      rootedTriangleTotalRadius configuration color ≤ 2 := by
  have hleft := h.child_distance color .left (by simp)
  have hright := h.child_distance color .right (by simp)
  have hsibling := (sibling_distance_mem_endpoint_interval h color).2
  have htriangle := dist_triangle (configuration color .left) (configuration color .root)
    (configuration color .right)
  rw [dist_comm (configuration color .left) (configuration color .root)] at htriangle
  simp only [rootedTriangleTotalRadius]
  constructor <;> nlinarith

private theorem red_child_blue_root_distance_le_two {configuration : SixPointConfiguration}
    (h : configuration.IsAdmissibleAt barS) (redLabel : SixPointLabel)
    (hred : redLabel ≠ .root) :
    dist (configuration .red redLabel) (configuration .blue .root) ≤ 2 := by
  calc
    _ ≤ dist (configuration .red redLabel) (configuration .red .root) +
        dist (configuration .red .root) (configuration .blue .root) := dist_triangle _ _ _
    _ ≤ 1 + 1 := add_le_add (by simpa [dist_comm] using h.child_distance .red redLabel hred)
      h.root_distance.le
    _ = 2 := by norm_num

private theorem blue_child_red_root_distance_le_two {configuration : SixPointConfiguration}
    (h : configuration.IsAdmissibleAt barS) (blueLabel : SixPointLabel)
    (hblue : blueLabel ≠ .root) :
    dist (configuration .blue blueLabel) (configuration .red .root) ≤ 2 := by
  calc
    _ ≤ dist (configuration .blue blueLabel) (configuration .blue .root) +
        dist (configuration .blue .root) (configuration .red .root) := dist_triangle _ _ _
    _ ≤ 1 + 1 := add_le_add (by simpa [dist_comm] using h.child_distance .blue blueLabel hblue)
      (by simpa [dist_comm] using h.root_distance.le)
    _ = 2 := by norm_num

private theorem cross_child_distance_le_three {configuration : SixPointConfiguration}
    (h : configuration.IsAdmissibleAt barS) (redLabel blueLabel : SixPointLabel)
    (hred : redLabel ≠ .root) (hblue : blueLabel ≠ .root) :
    dist (configuration .red redLabel) (configuration .blue blueLabel) ≤ 3 := by
  calc
    _ ≤ dist (configuration .red redLabel) (configuration .blue .root) +
        dist (configuration .blue .root) (configuration .blue blueLabel) := dist_triangle _ _ _
    _ ≤ 2 + 1 := add_le_add (red_child_blue_root_distance_le_two h redLabel hred)
      (h.child_distance .blue blueLabel hblue)
    _ = 3 := by norm_num

private theorem cross_child_distance_le_one_add_root_distances
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (redLabel blueLabel : SixPointLabel) :
    dist (configuration .red redLabel) (configuration .blue blueLabel) ≤
      1 + dist (configuration .red .root) (configuration .red redLabel) +
        dist (configuration .blue .root) (configuration .blue blueLabel) := by
  calc
    _ ≤ dist (configuration .red redLabel) (configuration .red .root) +
        dist (configuration .red .root) (configuration .blue blueLabel) := dist_triangle _ _ _
    _ ≤ dist (configuration .red redLabel) (configuration .red .root) +
        (dist (configuration .red .root) (configuration .blue .root) +
          dist (configuration .blue .root) (configuration .blue blueLabel)) := by
      have htriangle := dist_triangle (configuration .red .root)
        (configuration .blue .root) (configuration .blue blueLabel)
      linarith
    _ = _ := by rw [h.root_distance, dist_comm (configuration .red redLabel)]; ring

private theorem red_reach_root_le {configuration : SixPointConfiguration}
    (h : configuration.IsAdmissibleAt barS) (redLabel : SixPointLabel)
    (hred : redLabel ≠ .root) :
    redSiblingBlueTriangleReach configuration redLabel .root ≤
      3 - dist (configuration .blue .left) (configuration .blue .right) / 2 := by
  have hleft := h.child_distance .blue .left (by simp)
  have hright := h.child_distance .blue .right (by simp)
  have hdist := red_child_blue_root_distance_le_two h redLabel hred
  simp only [redSiblingBlueTriangleReach, canonicalTriangleRadius]
  nlinarith

private theorem blue_reach_root_le {configuration : SixPointConfiguration}
    (h : configuration.IsAdmissibleAt barS) (blueLabel : SixPointLabel)
    (hblue : blueLabel ≠ .root) :
    blueSiblingRedTriangleReach configuration blueLabel .root ≤
      3 - dist (configuration .red .left) (configuration .red .right) / 2 := by
  have hleft := h.child_distance .red .left (by simp)
  have hright := h.child_distance .red .right (by simp)
  have hdist := blue_child_red_root_distance_le_two h blueLabel hblue
  simp only [blueSiblingRedTriangleReach, canonicalTriangleRadius]
  nlinarith

private theorem red_balanced_root_reaches_le_six {configuration : SixPointConfiguration}
    (h : configuration.IsAdmissibleAt barS) (leftTarget rightTarget : SixPointLabel)
    (hroot : leftTarget = .root ∨ rightTarget = .root) :
    redSiblingBlueTriangleReach configuration .left leftTarget +
      redSiblingBlueTriangleReach configuration .right rightTarget ≤ 6 := by
  cases leftTarget <;> cases rightTarget
  · have hleft := red_child_blue_root_distance_le_two h .left (by simp)
    have hright := red_child_blue_root_distance_le_two h .right (by simp)
    have hradius := canonicalTriangleRadius_root_le_average (configuration .blue .root)
      (configuration .blue .left) (configuration .blue .right)
    have hblueLeft := h.child_distance .blue .left (by simp)
    have hblueRight := h.child_distance .blue .right (by simp)
    simp only [redSiblingBlueTriangleReach]
    nlinarith
  · have hleft := red_child_blue_root_distance_le_two h .left (by simp)
    have hright := cross_child_distance_le_three h .right .left (by simp) (by simp)
    have hradius := canonicalTriangleRadius_root_add_left (configuration .blue .root)
      (configuration .blue .left) (configuration .blue .right)
    have hblue := h.child_distance .blue .left (by simp)
    simp only [redSiblingBlueTriangleReach]
    nlinarith
  · have hleft := red_child_blue_root_distance_le_two h .left (by simp)
    have hright := cross_child_distance_le_three h .right .right (by simp) (by simp)
    have hradius := canonicalTriangleRadius_root_add_right (configuration .blue .root)
      (configuration .blue .left) (configuration .blue .right)
    have hblue := h.child_distance .blue .right (by simp)
    simp only [redSiblingBlueTriangleReach]
    nlinarith
  · have hleft := cross_child_distance_le_three h .left .left (by simp) (by simp)
    have hright := red_child_blue_root_distance_le_two h .right (by simp)
    have hradius := canonicalTriangleRadius_root_add_left (configuration .blue .root)
      (configuration .blue .left) (configuration .blue .right)
    have hblue := h.child_distance .blue .left (by simp)
    simp only [redSiblingBlueTriangleReach]
    nlinarith
  · simp at hroot
  · simp at hroot
  · have hleft := cross_child_distance_le_three h .left .right (by simp) (by simp)
    have hright := red_child_blue_root_distance_le_two h .right (by simp)
    have hradius := canonicalTriangleRadius_root_add_right (configuration .blue .root)
      (configuration .blue .left) (configuration .blue .right)
    have hblue := h.child_distance .blue .right (by simp)
    simp only [redSiblingBlueTriangleReach]
    nlinarith
  · simp at hroot
  · simp at hroot

private theorem blue_balanced_root_reaches_le_six {configuration : SixPointConfiguration}
    (h : configuration.IsAdmissibleAt barS) (leftTarget rightTarget : SixPointLabel)
    (hroot : leftTarget = .root ∨ rightTarget = .root) :
    blueSiblingRedTriangleReach configuration .left leftTarget +
      blueSiblingRedTriangleReach configuration .right rightTarget ≤ 6 := by
  cases leftTarget <;> cases rightTarget
  · have hleft := blue_child_red_root_distance_le_two h .left (by simp)
    have hright := blue_child_red_root_distance_le_two h .right (by simp)
    have hradius := canonicalTriangleRadius_root_le_average (configuration .red .root)
      (configuration .red .left) (configuration .red .right)
    have hredLeft := h.child_distance .red .left (by simp)
    have hredRight := h.child_distance .red .right (by simp)
    simp only [blueSiblingRedTriangleReach]
    nlinarith
  · have hleft := blue_child_red_root_distance_le_two h .left (by simp)
    have hright : dist (configuration .blue .right) (configuration .red .left) ≤ 3 := by
      simpa [dist_comm] using cross_child_distance_le_three h .left .right (by simp) (by simp)
    have hradius := canonicalTriangleRadius_root_add_left (configuration .red .root)
      (configuration .red .left) (configuration .red .right)
    have hred := h.child_distance .red .left (by simp)
    simp only [blueSiblingRedTriangleReach]
    nlinarith
  · have hleft := blue_child_red_root_distance_le_two h .left (by simp)
    have hright : dist (configuration .blue .right) (configuration .red .right) ≤ 3 := by
      simpa [dist_comm] using cross_child_distance_le_three h .right .right (by simp) (by simp)
    have hradius := canonicalTriangleRadius_root_add_right (configuration .red .root)
      (configuration .red .left) (configuration .red .right)
    have hred := h.child_distance .red .right (by simp)
    simp only [blueSiblingRedTriangleReach]
    nlinarith
  · have hleft : dist (configuration .blue .left) (configuration .red .left) ≤ 3 := by
      simpa [dist_comm] using cross_child_distance_le_three h .left .left (by simp) (by simp)
    have hright := blue_child_red_root_distance_le_two h .right (by simp)
    have hradius := canonicalTriangleRadius_root_add_left (configuration .red .root)
      (configuration .red .left) (configuration .red .right)
    have hred := h.child_distance .red .left (by simp)
    simp only [blueSiblingRedTriangleReach]
    nlinarith
  · simp at hroot
  · simp at hroot
  · have hleft : dist (configuration .blue .left) (configuration .red .right) ≤ 3 := by
      simpa [dist_comm] using cross_child_distance_le_three h .right .left (by simp) (by simp)
    have hright := blue_child_red_root_distance_le_two h .right (by simp)
    have hradius := canonicalTriangleRadius_root_add_right (configuration .red .root)
      (configuration .red .left) (configuration .red .right)
    have hred := h.child_distance .red .right (by simp)
    simp only [blueSiblingRedTriangleReach]
    nlinarith
  · simp at hroot
  · simp at hroot

/-- Failure of every radius split in support `67` has a child-labelled incidence witness. -/
theorem exists_redSiblingTriangleFailure_of_split_failure
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hfail : ∀ x : ℝ,
      dist (configuration .red .left) (configuration .red .right) - 1 ≤ x → x ≤ 1 →
        redSiblingTriangleTarget configuration <
          siblingTriangleSplitDiameter
            (dist (configuration .red .left) (configuration .red .right))
            (dist (configuration .blue .left) (configuration .blue .right)) x
            (redSiblingBlueTriangleReach configuration .left)
            (redSiblingBlueTriangleReach configuration .right)) :
    ∃ witness, redSiblingTriangleFailure configuration witness := by
  have hred := sibling_distance_mem_endpoint_interval h .red
  have hblue := sibling_distance_mem_endpoint_interval h .blue
  have hblueTotal := rootedTriangleTotalRadius_mem_endpoint_interval h .blue
  have hinternal := sibling_internal_terms_le_target hred hblue hblueTotal.1
  have hleftRoot := root_endpoint_le_target hred.1 hblue.1 hblueTotal.1
    (red_reach_root_le h .left (by simp))
  have hrightRoot := root_endpoint_le_target hred.1 hblue.1 hblueTotal.1
    (red_reach_root_le h .right (by simp))
  have hbalancedRoot (leftTarget rightTarget : SixPointLabel)
      (hroot : leftTarget = .root ∨ rightTarget = .root) :=
    balanced_root_le_target hred.1 hblue.1 hblueTotal.1
      (red_balanced_root_reaches_le_six h leftTarget rightTarget hroot)
  apply exists_siblingTriangleWitnessExceeds_of_failure hred.2
    (T := redSiblingTriangleTarget configuration)
    (leftReach := redSiblingBlueTriangleReach configuration .left)
    (rightReach := redSiblingBlueTriangleReach configuration .right)
  · simpa [redSiblingTriangleTarget] using hinternal.1
  · simpa [redSiblingTriangleTarget] using hinternal.2
  · simpa [redSiblingTriangleTarget] using hleftRoot
  · simpa [redSiblingTriangleTarget] using hrightRoot
  · intro leftTarget rightTarget hroot
    simpa [redSiblingTriangleTarget, add_assoc] using
      hbalancedRoot leftTarget rightTarget hroot
  · exact hfail

/-- Failure of every radius split in support `76` has a child-labelled incidence witness. -/
theorem exists_blueSiblingTriangleFailure_of_split_failure
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hfail : ∀ y : ℝ,
      dist (configuration .blue .left) (configuration .blue .right) - 1 ≤ y → y ≤ 1 →
        blueSiblingTriangleTarget configuration <
          siblingTriangleSplitDiameter
            (dist (configuration .blue .left) (configuration .blue .right))
            (dist (configuration .red .left) (configuration .red .right)) y
            (blueSiblingRedTriangleReach configuration .left)
            (blueSiblingRedTriangleReach configuration .right)) :
    ∃ witness, blueSiblingTriangleFailure configuration witness := by
  have hblue := sibling_distance_mem_endpoint_interval h .blue
  have hred := sibling_distance_mem_endpoint_interval h .red
  have hredTotal := rootedTriangleTotalRadius_mem_endpoint_interval h .red
  have hinternal := sibling_internal_terms_le_target hblue hred hredTotal.1
  have hleftRoot := root_endpoint_le_target hblue.1 hred.1 hredTotal.1
    (blue_reach_root_le h .left (by simp))
  have hrightRoot := root_endpoint_le_target hblue.1 hred.1 hredTotal.1
    (blue_reach_root_le h .right (by simp))
  have hbalancedRoot (leftTarget rightTarget : SixPointLabel)
      (hroot : leftTarget = .root ∨ rightTarget = .root) :=
    balanced_root_le_target hblue.1 hred.1 hredTotal.1
      (blue_balanced_root_reaches_le_six h leftTarget rightTarget hroot)
  have hexists : ∃ witness, siblingTriangleWitnessExceeds
      (dist (configuration .blue .left) (configuration .blue .right))
      (blueSiblingTriangleTarget configuration)
      (blueSiblingRedTriangleReach configuration .left)
      (blueSiblingRedTriangleReach configuration .right) witness := by
    apply exists_siblingTriangleWitnessExceeds_of_failure hblue.2
      (M := dist (configuration .red .left) (configuration .red .right))
    · simpa [blueSiblingTriangleTarget] using hinternal.1
    · simpa [blueSiblingTriangleTarget] using hinternal.2
    · simpa [blueSiblingTriangleTarget] using hleftRoot
    · simpa [blueSiblingTriangleTarget] using hrightRoot
    · intro leftTarget rightTarget hroot
      simpa [blueSiblingTriangleTarget, add_assoc] using
        hbalancedRoot leftTarget rightTarget hroot
    · exact hfail
  obtain ⟨witness, hwitness⟩ := hexists
  cases witness with
  | endpoint code =>
      refine ⟨.endpoint (transposeEndpointCode code), ?_⟩
      fin_cases code <;> exact hwitness
  | balanced code => exact ⟨.balanced code, hwitness⟩

/-- The support `67` packing with its actual sibling length at the exact endpoint. -/
def redSiblingTrianglePackingAtEndpoint (configuration : SixPointConfiguration)
    (h : configuration.IsAdmissibleAt barS) (x : ℝ)
    (hxLower : dist (configuration .red .left) (configuration .red .right) - 1 ≤ x)
    (hxUpper : x ≤ 1) : SixPointPacking configuration :=
  redSiblingBlueTrianglePacking configuration rfl
    (one_lt_barC_and_barC_lt_two.1.le.trans
      (sibling_distance_mem_endpoint_interval h .red).1)
    hxLower hxUpper (h.child_distance .blue .left (by simp))
    (h.child_distance .blue .right (by simp))

/-- The support `76` packing with its actual sibling length at the exact endpoint. -/
def blueSiblingTrianglePackingAtEndpoint (configuration : SixPointConfiguration)
    (h : configuration.IsAdmissibleAt barS) (y : ℝ)
    (hyLower : dist (configuration .blue .left) (configuration .blue .right) - 1 ≤ y)
    (hyUpper : y ≤ 1) : SixPointPacking configuration :=
  blueSiblingRedTrianglePacking configuration rfl
    (one_lt_barC_and_barC_lt_two.1.le.trans
      (sibling_distance_mem_endpoint_interval h .blue).1)
    hyLower hyUpper (h.child_distance .red .left (by simp))
    (h.child_distance .red .right (by simp))

/-- Every feasible support `67` radius split has negative endpoint score. -/
def RedSiblingTriangleFails (configuration : SixPointConfiguration)
    (h : configuration.IsAdmissibleAt barS) : Prop :=
  ∀ (x : ℝ)
    (hxLower : dist (configuration .red .left) (configuration .red .right) - 1 ≤ x)
    (hxUpper : x ≤ 1),
    (redSiblingTrianglePackingAtEndpoint configuration h x hxLower hxUpper).score barS < 0

/-- Every feasible support `76` radius split has negative endpoint score. -/
def BlueSiblingTriangleFails (configuration : SixPointConfiguration)
    (h : configuration.IsAdmissibleAt barS) : Prop :=
  ∀ (y : ℝ)
    (hyLower : dist (configuration .blue .left) (configuration .blue .right) - 1 ≤ y)
    (hyUpper : y ≤ 1),
    (blueSiblingTrianglePackingAtEndpoint configuration h y hyLower hyUpper).score barS < 0

/-- Negative score for every support `67` split yields a child-labelled failure witness. -/
theorem exists_redSiblingTriangleFailure_of_score_failure
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hfailure : RedSiblingTriangleFails configuration h) :
    ∃ witness, redSiblingTriangleFailure configuration witness := by
  apply exists_redSiblingTriangleFailure_of_split_failure h
  intro x hxLower hxUpper
  have hscore := hfailure x hxLower hxUpper
  have hredOne : 1 ≤ dist (configuration .red .left) (configuration .red .right) :=
    one_lt_barC_and_barC_lt_two.1.le.trans
      (sibling_distance_mem_endpoint_interval h .red).1
  have hblueOne : 1 ≤ dist (configuration .blue .left) (configuration .blue .right) :=
    one_lt_barC_and_barC_lt_two.1.le.trans
      (sibling_distance_mem_endpoint_interval h .blue).1
  simp only [redSiblingTrianglePackingAtEndpoint, SixPointPacking.score] at hscore
  rw [redSiblingBlueTrianglePacking_totalRadius,
    redSiblingBlueTrianglePacking_virtualDiameter (hM := hblueOne) (hMdist := rfl)] at hscore
  rw [barS] at hscore
  rw [show 2 * (barC / 2) = barC by ring] at hscore
  have hquotient :
      dist (configuration .red .left) (configuration .red .right) +
          rootedTriangleTotalRadius configuration .blue <
        siblingTriangleSplitDiameter
            (dist (configuration .red .left) (configuration .red .right))
            (dist (configuration .blue .left) (configuration .blue .right)) x
            (redSiblingBlueTriangleReach configuration .left)
            (redSiblingBlueTriangleReach configuration .right) / barC := by
    simp only [rootedTriangleTotalRadius]
    linarith
  rw [redSiblingTriangleTarget]
  nlinarith [(lt_div_iff₀ barC_pos).1 hquotient]

/-- Negative score for every support `76` split yields a child-labelled failure witness. -/
theorem exists_blueSiblingTriangleFailure_of_score_failure
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hfailure : BlueSiblingTriangleFails configuration h) :
    ∃ witness, blueSiblingTriangleFailure configuration witness := by
  apply exists_blueSiblingTriangleFailure_of_split_failure h
  intro y hyLower hyUpper
  have hscore := hfailure y hyLower hyUpper
  have hblueOne : 1 ≤ dist (configuration .blue .left) (configuration .blue .right) :=
    one_lt_barC_and_barC_lt_two.1.le.trans
      (sibling_distance_mem_endpoint_interval h .blue).1
  have hredOne : 1 ≤ dist (configuration .red .left) (configuration .red .right) :=
    one_lt_barC_and_barC_lt_two.1.le.trans
      (sibling_distance_mem_endpoint_interval h .red).1
  simp only [blueSiblingTrianglePackingAtEndpoint, SixPointPacking.score] at hscore
  rw [blueSiblingRedTrianglePacking_totalRadius,
    blueSiblingRedTrianglePacking_virtualDiameter (hL := hredOne) (hLdist := rfl)] at hscore
  rw [barS] at hscore
  rw [show 2 * (barC / 2) = barC by ring] at hscore
  have hquotient :
      dist (configuration .blue .left) (configuration .blue .right) +
          rootedTriangleTotalRadius configuration .red <
        siblingTriangleSplitDiameter
            (dist (configuration .blue .left) (configuration .blue .right))
            (dist (configuration .red .left) (configuration .red .right)) y
            (blueSiblingRedTriangleReach configuration .left)
            (blueSiblingRedTriangleReach configuration .right) / barC := by
    simp only [rootedTriangleTotalRadius]
    linarith
  rw [blueSiblingTriangleTarget]
  nlinarith [(lt_div_iff₀ barC_pos).1 hquotient]

/-- Coincident endpoint failures at `B11` imply the first exact `q2` inequality. -/
theorem q2_strict_of_matched_endpoint_zero {configuration : SixPointConfiguration}
    (h : configuration.IsAdmissibleAt barS)
    (hred : redSiblingTriangleFailure configuration (.endpoint 0))
    (hblue : blueSiblingTriangleFailure configuration (.endpoint 0)) :
    ((barC - 1) * matchedChildAverage configuration 0 +
        (barC + 1) * matchedChildAverage configuration 1 +
        3 * barC ^ 2 - 3 * barC + 2) / 2 <
      dist (configuration .red .left) (configuration .blue .left) := by
  have hL := (sibling_distance_mem_endpoint_interval h .red).1
  have hM := (sibling_distance_mem_endpoint_interval h .blue).1
  have hcoefficient : 0 ≤ 3 * (barC - 1) / 2 := by
    nlinarith [one_lt_barC_and_barC_lt_two.1]
  have hsiblingSum := mul_le_mul_of_nonneg_left (show 2 * barC ≤
      dist (configuration .red .left) (configuration .red .right) +
        dist (configuration .blue .left) (configuration .blue .right) by linarith)
    hcoefficient
  simp [redSiblingTriangleFailure, blueSiblingTriangleFailure,
    transposeBlueEndpointWitness, transposeEndpointCode,
    siblingTriangleWitnessExceeds, incidenceFirst, incidenceSecond, incidenceChild,
    redSiblingTriangleTarget, blueSiblingTriangleTarget, rootedTriangleTotalRadius,
    redSiblingBlueTriangleReach, blueSiblingRedTriangleReach, canonicalTriangleRadius,
    matchedChildAverage] at hred hblue ⊢
  rw [dist_comm (configuration .blue .left) (configuration .red .left)] at hblue
  nlinarith

/-- Coincident endpoint failures at `B22` imply the child-swapped exact `q2` inequality. -/
theorem q2_strict_of_matched_endpoint_three {configuration : SixPointConfiguration}
    (h : configuration.IsAdmissibleAt barS)
    (hred : redSiblingTriangleFailure configuration (.endpoint 3))
    (hblue : blueSiblingTriangleFailure configuration (.endpoint 3)) :
    ((barC - 1) * matchedChildAverage configuration 1 +
        (barC + 1) * matchedChildAverage configuration 0 +
        3 * barC ^ 2 - 3 * barC + 2) / 2 <
      dist (configuration .red .right) (configuration .blue .right) := by
  have hL := (sibling_distance_mem_endpoint_interval h .red).1
  have hM := (sibling_distance_mem_endpoint_interval h .blue).1
  have hcoefficient : 0 ≤ 3 * (barC - 1) / 2 := by
    nlinarith [one_lt_barC_and_barC_lt_two.1]
  have hsiblingSum := mul_le_mul_of_nonneg_left (show 2 * barC ≤
      dist (configuration .red .left) (configuration .red .right) +
        dist (configuration .blue .left) (configuration .blue .right) by linarith)
    hcoefficient
  simp [redSiblingTriangleFailure, blueSiblingTriangleFailure,
    transposeBlueEndpointWitness, transposeEndpointCode,
    siblingTriangleWitnessExceeds, incidenceFirst, incidenceSecond, incidenceChild,
    redSiblingTriangleTarget, blueSiblingTriangleTarget, rootedTriangleTotalRadius,
    redSiblingBlueTriangleReach, blueSiblingRedTriangleReach, canonicalTriangleRadius,
    matchedChildAverage] at hred hblue ⊢
  rw [dist_comm (configuration .blue .right) (configuration .red .right)] at hblue
  nlinarith

/-- The selected-matching disjoint endpoint incidence is impossible. -/
theorem not_redEndpoint_zero_and_blueEndpoint_three
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS) :
    ¬ (redSiblingTriangleFailure configuration (.endpoint 0) ∧
      blueSiblingTriangleFailure configuration (.endpoint 3)) := by
  rintro ⟨hred, hblue⟩
  have hL := (sibling_distance_mem_endpoint_interval h .red).1
  have hM := (sibling_distance_mem_endpoint_interval h .blue).1
  have hredTriangle := dist_triangle (configuration .red .left) (configuration .red .root)
    (configuration .red .right)
  have hblueTriangle := dist_triangle (configuration .blue .left)
    (configuration .blue .root) (configuration .blue .right)
  rw [dist_comm (configuration .red .left) (configuration .red .root)] at hredTriangle
  rw [dist_comm (configuration .blue .left) (configuration .blue .root)] at hblueTriangle
  have hselected :
      dist (configuration .red .root) (configuration .red .right) +
          dist (configuration .blue .root) (configuration .blue .left) ≤ 2 := by
    have hredRight := h.child_distance .red .right (by simp)
    have hblueLeft := h.child_distance .blue .left (by simp)
    linarith
  have hB11 := cross_child_distance_le_one_add_root_distances h .left .left
  have hB22 := cross_child_distance_le_one_add_root_distances h .right .right
  have hsum :
      dist (configuration .red .left) (configuration .red .right) +
          dist (configuration .blue .left) (configuration .blue .right) ≤
        (dist (configuration .red .root) (configuration .red .right) +
            dist (configuration .blue .root) (configuration .blue .left)) +
          (dist (configuration .red .root) (configuration .red .left) +
            dist (configuration .blue .root) (configuration .blue .right)) := by
    linarith
  have hsumScaled := mul_le_mul_of_nonpos_left hsum
    (show (1 - barC) / 2 ≤ 0 by nlinarith [one_lt_barC_and_barC_lt_two.1])
  have hPscaled := mul_le_mul_of_nonpos_left (show 2 * barC ≤
      dist (configuration .red .left) (configuration .red .right) +
        dist (configuration .blue .left) (configuration .blue .right) by linarith)
    (show 2 * (1 - barC) ≤ 0 by nlinarith [one_lt_barC_and_barC_lt_two.1])
  simp [redSiblingTriangleFailure, blueSiblingTriangleFailure,
    transposeBlueEndpointWitness, transposeEndpointCode,
    siblingTriangleWitnessExceeds, incidenceFirst, incidenceSecond, incidenceChild,
    redSiblingTriangleTarget, blueSiblingTriangleTarget, rootedTriangleTotalRadius,
    redSiblingBlueTriangleReach, blueSiblingRedTriangleReach, canonicalTriangleRadius]
    at hred hblue
  rw [dist_comm (configuration .blue .right) (configuration .red .right)] at hblue
  nlinarith [barC_disjoint_gap_neg]

/-- The off-matching disjoint endpoint incidence is impossible. -/
theorem not_redEndpoint_one_and_blueEndpoint_two
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS) :
    ¬ (redSiblingTriangleFailure configuration (.endpoint 1) ∧
      blueSiblingTriangleFailure configuration (.endpoint 2)) := by
  rintro ⟨hred, hblue⟩
  have hL := (sibling_distance_mem_endpoint_interval h .red).1
  have hM := (sibling_distance_mem_endpoint_interval h .blue).1
  have hredTriangle := dist_triangle (configuration .red .left) (configuration .red .root)
    (configuration .red .right)
  have hblueTriangle := dist_triangle (configuration .blue .left)
    (configuration .blue .root) (configuration .blue .right)
  rw [dist_comm (configuration .red .left) (configuration .red .root)] at hredTriangle
  rw [dist_comm (configuration .blue .left) (configuration .blue .root)] at hblueTriangle
  have hselected :
      dist (configuration .red .root) (configuration .red .right) +
          dist (configuration .blue .root) (configuration .blue .right) ≤ 2 := by
    have hredRight := h.child_distance .red .right (by simp)
    have hblueRight := h.child_distance .blue .right (by simp)
    linarith
  have hB12 := cross_child_distance_le_one_add_root_distances h .left .right
  have hB21 := cross_child_distance_le_one_add_root_distances h .right .left
  have hsum :
      dist (configuration .red .left) (configuration .red .right) +
          dist (configuration .blue .left) (configuration .blue .right) ≤
        (dist (configuration .red .root) (configuration .red .right) +
            dist (configuration .blue .root) (configuration .blue .right)) +
          (dist (configuration .red .root) (configuration .red .left) +
            dist (configuration .blue .root) (configuration .blue .left)) := by
    linarith
  have hsumScaled := mul_le_mul_of_nonpos_left hsum
    (show (1 - barC) / 2 ≤ 0 by nlinarith [one_lt_barC_and_barC_lt_two.1])
  have hPscaled := mul_le_mul_of_nonpos_left (show 2 * barC ≤
      dist (configuration .red .left) (configuration .red .right) +
        dist (configuration .blue .left) (configuration .blue .right) by linarith)
    (show 2 * (1 - barC) ≤ 0 by nlinarith [one_lt_barC_and_barC_lt_two.1])
  simp [redSiblingTriangleFailure, blueSiblingTriangleFailure,
    transposeBlueEndpointWitness, transposeEndpointCode,
    siblingTriangleWitnessExceeds, incidenceFirst, incidenceSecond, incidenceChild,
    redSiblingTriangleTarget, blueSiblingTriangleTarget, rootedTriangleTotalRadius,
    redSiblingBlueTriangleReach, blueSiblingRedTriangleReach, canonicalTriangleRadius]
    at hred hblue
  rw [dist_comm (configuration .blue .left) (configuration .red .right)] at hblue
  nlinarith [barC_disjoint_gap_neg]

/-- The analytic exclusions required by the complete sibling-incidence ledger. -/
structure SiblingIncidenceExclusions
    (redFailure blueFailure : SiblingTriangleWitness → Prop) : Prop where
  endpointEndpoint : ∀ redCode blueCode,
    endpointEndpointOrbit redCode blueCode ≠ .matchedCoincident →
      ¬ (redFailure (.endpoint redCode) ∧ blueFailure (.endpoint blueCode))
  endpointBalanced : ∀ endpointCode balancedCode,
    ¬ (redFailure (.endpoint endpointCode) ∧ blueFailure (.balanced balancedCode))
  balancedEndpoint : ∀ balancedCode endpointCode,
    ¬ (redFailure (.balanced balancedCode) ∧ blueFailure (.endpoint endpointCode))
  balancedBalanced : ∀ redCode blueCode,
    ¬ (redFailure (.balanced redCode) ∧ blueFailure (.balanced blueCode))

/-- Complete incidence routing: the only simultaneous failures select one diagonal endpoint. -/
theorem exists_matched_endpoint_of_siblingIncidenceExclusions
    {redFailure blueFailure : SiblingTriangleWitness → Prop}
    (hexclusions : SiblingIncidenceExclusions redFailure blueFailure)
    (hred : ∃ witness, redFailure witness) (hblue : ∃ witness, blueFailure witness) :
    ∃ code : Fin 4, (code = 0 ∨ code = 3) ∧
      redFailure (.endpoint code) ∧ blueFailure (.endpoint code) := by
  obtain ⟨redWitness, hred⟩ := hred
  obtain ⟨blueWitness, hblue⟩ := hblue
  cases redWitness with
  | endpoint redCode =>
      cases blueWitness with
      | endpoint blueCode =>
          have horbit : endpointEndpointOrbit redCode blueCode = .matchedCoincident := by
            by_contra hne
            exact hexclusions.endpointEndpoint redCode blueCode hne ⟨hred, hblue⟩
          rcases (endpointEndpointOrbit_eq_matchedCoincident_iff redCode blueCode).1 horbit with
            hzero | hthree
          · exact ⟨0, Or.inl rfl, hzero.1 ▸ hred, hzero.2 ▸ hblue⟩
          · exact ⟨3, Or.inr rfl, hthree.1 ▸ hred, hthree.2 ▸ hblue⟩
      | balanced blueCode =>
          exact (hexclusions.endpointBalanced redCode blueCode ⟨hred, hblue⟩).elim
  | balanced redCode =>
      cases blueWitness with
      | endpoint blueCode =>
          exact (hexclusions.balancedEndpoint redCode blueCode ⟨hred, hblue⟩).elim
      | balanced blueCode =>
          exact (hexclusions.balancedBalanced redCode blueCode ⟨hred, hblue⟩).elim

/-- If supports `67` and `76` both fail, the incidence ledger selects one diagonal endpoint. -/
theorem exists_matched_endpoint_of_siblingTriangle_score_failures
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hred : RedSiblingTriangleFails configuration h)
    (hblue : BlueSiblingTriangleFails configuration h)
    (hexclusions : SiblingIncidenceExclusions (redSiblingTriangleFailure configuration)
      (blueSiblingTriangleFailure configuration)) :
    ∃ code : Fin 4, (code = 0 ∨ code = 3) ∧
      redSiblingTriangleFailure configuration (.endpoint code) ∧
      blueSiblingTriangleFailure configuration (.endpoint code) :=
  exists_matched_endpoint_of_siblingIncidenceExclusions hexclusions
    (exists_redSiblingTriangleFailure_of_score_failure h hred)
    (exists_blueSiblingTriangleFailure_of_score_failure h hblue)

/-- Simultaneous `67` and `76` failures force the exact `q2` inequality at one matched child. -/
theorem q2_strict_of_siblingTriangle_score_failures
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hred : RedSiblingTriangleFails configuration h)
    (hblue : BlueSiblingTriangleFails configuration h)
    (hexclusions : SiblingIncidenceExclusions (redSiblingTriangleFailure configuration)
      (blueSiblingTriangleFailure configuration)) :
    ((barC - 1) * matchedChildAverage configuration 0 +
          (barC + 1) * matchedChildAverage configuration 1 +
          3 * barC ^ 2 - 3 * barC + 2) / 2 <
        dist (configuration .red .left) (configuration .blue .left) ∨
      ((barC - 1) * matchedChildAverage configuration 1 +
          (barC + 1) * matchedChildAverage configuration 0 +
          3 * barC ^ 2 - 3 * barC + 2) / 2 <
        dist (configuration .red .right) (configuration .blue .right) := by
  obtain ⟨code, hcode, hredCode, hblueCode⟩ :=
    exists_matched_endpoint_of_siblingTriangle_score_failures h hred hblue hexclusions
  rcases hcode with rfl | rfl
  · exact Or.inl (q2_strict_of_matched_endpoint_zero h hredCode hblueCode)
  · exact Or.inr (q2_strict_of_matched_endpoint_three h hredCode hblueCode)

end LeanPool.Besicovitch
