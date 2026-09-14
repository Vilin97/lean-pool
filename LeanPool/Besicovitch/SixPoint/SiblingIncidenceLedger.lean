/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.RationalChord
public import LeanPool.Besicovitch.SixPoint.SiblingIncidence

/-!
# Geometric sibling-incidence exclusions

This file connects the exact rational tangent certificates to the endpoint and balanced
failure witnesses. The only remaining analytic inputs are the five named lens inequalities.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

/-- Swap the two child labels while fixing the root. -/
def swapChildLabel : SixPointLabel → SixPointLabel
  | .root => .root
  | .left => .right
  | .right => .left

/-- Simultaneously swap the two children of both colors. -/
def swapConfigurationChildren (configuration : SixPointConfiguration) : SixPointConfiguration :=
  fun color label ↦ configuration color (swapChildLabel label)

/-- Interchange the red and blue colors. -/
def transposeConfigurationColors (configuration : SixPointConfiguration) : SixPointConfiguration
  | .red => configuration .blue
  | .blue => configuration .red

/-- Simultaneous child swap preserves endpoint admissibility. -/
theorem IsAdmissibleAt.swapChildren {configuration : SixPointConfiguration} {s : ℝ}
    (h : configuration.IsAdmissibleAt s) :
    (swapConfigurationChildren configuration).IsAdmissibleAt s where
  root_distance := h.root_distance
  child_distance color label hlabel := by
    cases label with
    | root => simp at hlabel
    | left => exact h.child_distance color .right (by simp)
    | right => exact h.child_distance color .left (by simp)
  sibling_distance color := by
    simpa [swapConfigurationChildren, swapChildLabel, dist_comm] using h.sibling_distance color

/-- Color transposition preserves endpoint admissibility. -/
theorem IsAdmissibleAt.transposeColors {configuration : SixPointConfiguration} {s : ℝ}
    (h : configuration.IsAdmissibleAt s) :
    (transposeConfigurationColors configuration).IsAdmissibleAt s where
  root_distance := by
    simpa [transposeConfigurationColors, dist_comm] using h.root_distance
  child_distance color label hlabel := by
    cases color <;>
      simpa [transposeConfigurationColors] using h.child_distance _ label hlabel
  sibling_distance color := by
    cases color <;>
      simpa [transposeConfigurationColors] using h.sibling_distance _

/-- The distance between a chosen red child and a chosen blue child. -/
def incidenceCrossDistance (configuration : SixPointConfiguration) (redChild blueChild : Fin 2) :
    ℝ :=
  dist (configuration .red (incidenceChild redChild))
    (configuration .blue (incidenceChild blueChild))

/-- The root-to-child radius at a chosen color and child. -/
def incidenceChildRadius (configuration : SixPointConfiguration) (color : SixPointColor)
    (child : Fin 2) : ℝ :=
  dist (configuration color .root) (configuration color (incidenceChild child))

/-- A child radius is the norm of its red displacement vector. -/
theorem incidenceChildRadius_red_eq_norm (configuration : SixPointConfiguration) (child : Fin 2) :
    incidenceChildRadius configuration .red child =
      ‖configuration.redDisplacement (incidenceChild child)‖ := by
  simp [incidenceChildRadius, SixPointConfiguration.redDisplacement, dist_eq_norm, norm_sub_rev]

/-- A child radius is the norm of its pulled-back blue displacement vector. -/
theorem incidenceChildRadius_blue_eq_norm (configuration : SixPointConfiguration) (child : Fin 2) :
    incidenceChildRadius configuration .blue child =
      ‖configuration.bluePullback (incidenceChild child)‖ := by
  simp [incidenceChildRadius, SixPointConfiguration.bluePullback, dist_eq_norm]

/-- A cross distance is the norm of its endpoint-geometry displacement. -/
theorem incidenceCrossDistance_eq_norm (configuration : SixPointConfiguration)
    (redChild blueChild : Fin 2) :
    incidenceCrossDistance configuration redChild blueChild =
      ‖configuration.rootDisplacement -
        configuration.redDisplacement (incidenceChild redChild) -
        configuration.bluePullback (incidenceChild blueChild)‖ := by
  exact configuration.dist_red_blue_eq_norm _ _

/-- The radial penalty in a reduced balanced incidence slack. -/
def balancedIncidencePenalty (code : Fin 4) (firstRadius secondRadius : ℝ) : ℝ :=
  match code with
  | 0 => ((barC - 1) * firstRadius + (barC + 1) * secondRadius) / 2
  | 1 | 2 => barC * (firstRadius + secondRadius) / 2
  | 3 => ((barC + 1) * firstRadius + (barC - 1) * secondRadius) / 2

/-- The reduced matching slack retained from the four-child branch. -/
def diagonalMatchingReducedSlack (configuration : SixPointConfiguration) : ℝ :=
  incidenceCrossDistance configuration 0 0 + incidenceCrossDistance configuration 1 1 -
    2 * barC * (2 * barC - 1)

/-- The selected diagonal matching alternative from the four-child minimax. -/
def SelectedDiagonalMatchingFails (configuration : SixPointConfiguration) : Prop :=
  (2 * barC - 1) *
      (dist (configuration .red .left) (configuration .red .right) +
        dist (configuration .blue .left) (configuration .blue .right)) ≤
    incidenceCrossDistance configuration 0 0 + incidenceCrossDistance configuration 1 1

/-- The selected diagonal matching is unchanged by simultaneous child swap. -/
theorem selectedDiagonalMatchingFails_swapChildren (configuration : SixPointConfiguration) :
    SelectedDiagonalMatchingFails (swapConfigurationChildren configuration) ↔
      SelectedDiagonalMatchingFails configuration := by
  simp only [SelectedDiagonalMatchingFails, incidenceCrossDistance, incidenceChild,
    swapConfigurationChildren, swapChildLabel]
  constructor <;> intro h <;>
    simpa [add_comm, dist_comm] using h

/-- The selected diagonal matching is unchanged by color transposition. -/
theorem selectedDiagonalMatchingFails_transposeColors (configuration : SixPointConfiguration) :
    SelectedDiagonalMatchingFails (transposeConfigurationColors configuration) ↔
      SelectedDiagonalMatchingFails configuration := by
  simp only [SelectedDiagonalMatchingFails, incidenceCrossDistance, incidenceChild,
    transposeConfigurationColors]
  constructor <;> intro h <;>
    simpa [add_comm, dist_comm] using h

/-- Red endpoint failures respect simultaneous child swap. -/
theorem redEndpointFailure_swapChildren (configuration : SixPointConfiguration) (code : Fin 4) :
    redSiblingTriangleFailure (swapConfigurationChildren configuration)
        (.endpoint (swapEndpointCode code)) ↔
      redSiblingTriangleFailure configuration (.endpoint code) := by
  fin_cases code <;>
    simp [redSiblingTriangleFailure, siblingTriangleWitnessExceeds,
      redSiblingTriangleTarget, rootedTriangleTotalRadius, redSiblingBlueTriangleReach,
      canonicalTriangleRadius, swapEndpointCode, swapConfigurationChildren, swapChildLabel,
      incidenceFirst, incidenceSecond, incidenceChild, dist_comm, add_comm]

/-- Blue endpoint failures respect simultaneous child swap. -/
theorem blueEndpointFailure_swapChildren (configuration : SixPointConfiguration) (code : Fin 4) :
    blueSiblingTriangleFailure (swapConfigurationChildren configuration)
        (.endpoint (swapEndpointCode code)) ↔
      blueSiblingTriangleFailure configuration (.endpoint code) := by
  fin_cases code <;>
    simp [blueSiblingTriangleFailure, transposeBlueEndpointWitness, transposeEndpointCode,
      siblingTriangleWitnessExceeds, blueSiblingTriangleTarget, rootedTriangleTotalRadius,
      blueSiblingRedTriangleReach, canonicalTriangleRadius, swapEndpointCode,
      swapConfigurationChildren, swapChildLabel, incidenceFirst, incidenceSecond,
      incidenceChild, dist_comm, add_comm]

/-- Red balanced failures respect simultaneous child swap. -/
theorem redBalancedFailure_swapChildren (configuration : SixPointConfiguration) (code : Fin 4) :
    redSiblingTriangleFailure (swapConfigurationChildren configuration)
        (.balanced (swapBalancedCode code)) ↔
      redSiblingTriangleFailure configuration (.balanced code) := by
  fin_cases code <;>
    simp [redSiblingTriangleFailure, siblingTriangleWitnessExceeds,
      redSiblingTriangleTarget, rootedTriangleTotalRadius, redSiblingBlueTriangleReach,
      canonicalTriangleRadius, swapBalancedCode, swapConfigurationChildren, swapChildLabel,
      incidenceFirst, incidenceSecond, incidenceChild, dist_comm, add_comm] <;>
    constructor <;> intro h <;> nlinarith

/-- Blue balanced failures respect simultaneous child swap. -/
theorem blueBalancedFailure_swapChildren (configuration : SixPointConfiguration) (code : Fin 4) :
    blueSiblingTriangleFailure (swapConfigurationChildren configuration)
        (.balanced (swapBalancedCode code)) ↔
      blueSiblingTriangleFailure configuration (.balanced code) := by
  fin_cases code <;>
    simp [blueSiblingTriangleFailure, transposeBlueEndpointWitness,
      siblingTriangleWitnessExceeds, blueSiblingTriangleTarget, rootedTriangleTotalRadius,
      blueSiblingRedTriangleReach, canonicalTriangleRadius, swapBalancedCode,
      swapConfigurationChildren, swapChildLabel, incidenceFirst, incidenceSecond,
      incidenceChild, dist_comm, add_comm] <;>
    constructor <;> intro h <;> nlinarith

/-- Red endpoint failures become blue endpoint failures under color transposition. -/
theorem redEndpointFailure_transposeColors (configuration : SixPointConfiguration) (code : Fin 4) :
    redSiblingTriangleFailure (transposeConfigurationColors configuration)
        (.endpoint (transposeEndpointCode code)) ↔
      blueSiblingTriangleFailure configuration (.endpoint code) := by
  fin_cases code <;>
    simp [redSiblingTriangleFailure, blueSiblingTriangleFailure,
      transposeBlueEndpointWitness, transposeEndpointCode, siblingTriangleWitnessExceeds,
      redSiblingTriangleTarget, blueSiblingTriangleTarget, rootedTriangleTotalRadius,
      redSiblingBlueTriangleReach, blueSiblingRedTriangleReach, canonicalTriangleRadius,
      transposeConfigurationColors, incidenceFirst, incidenceSecond, incidenceChild,
      dist_comm, add_comm]

/-- Blue endpoint failures become red endpoint failures under color transposition. -/
theorem blueEndpointFailure_transposeColors (configuration : SixPointConfiguration) (code : Fin 4) :
    blueSiblingTriangleFailure (transposeConfigurationColors configuration)
        (.endpoint (transposeEndpointCode code)) ↔
      redSiblingTriangleFailure configuration (.endpoint code) := by
  fin_cases code <;>
    simp [redSiblingTriangleFailure, blueSiblingTriangleFailure,
      transposeBlueEndpointWitness, transposeEndpointCode, siblingTriangleWitnessExceeds,
      redSiblingTriangleTarget, blueSiblingTriangleTarget, rootedTriangleTotalRadius,
      redSiblingBlueTriangleReach, blueSiblingRedTriangleReach, canonicalTriangleRadius,
      transposeConfigurationColors, incidenceFirst, incidenceSecond, incidenceChild,
      dist_comm, add_comm]

/-- Red balanced failures become blue balanced failures under color transposition. -/
theorem redBalancedFailure_transposeColors (configuration : SixPointConfiguration) (code : Fin 4) :
    redSiblingTriangleFailure (transposeConfigurationColors configuration) (.balanced code) ↔
      blueSiblingTriangleFailure configuration (.balanced code) := by
  fin_cases code <;>
    simp [redSiblingTriangleFailure, blueSiblingTriangleFailure,
      transposeBlueEndpointWitness, siblingTriangleWitnessExceeds,
      redSiblingTriangleTarget, blueSiblingTriangleTarget, rootedTriangleTotalRadius,
      redSiblingBlueTriangleReach, blueSiblingRedTriangleReach, canonicalTriangleRadius,
      transposeConfigurationColors, incidenceFirst, incidenceSecond, incidenceChild,
      dist_comm, add_comm]

/-- Blue balanced failures become red balanced failures under color transposition. -/
theorem blueBalancedFailure_transposeColors (configuration : SixPointConfiguration) (code : Fin 4) :
    blueSiblingTriangleFailure (transposeConfigurationColors configuration) (.balanced code) ↔
      redSiblingTriangleFailure configuration (.balanced code) := by
  fin_cases code <;>
    simp [redSiblingTriangleFailure, blueSiblingTriangleFailure,
      transposeBlueEndpointWitness, siblingTriangleWitnessExceeds,
      redSiblingTriangleTarget, blueSiblingTriangleTarget, rootedTriangleTotalRadius,
      redSiblingBlueTriangleReach, blueSiblingRedTriangleReach, canonicalTriangleRadius,
      transposeConfigurationColors, incidenceFirst, incidenceSecond, incidenceChild,
      dist_comm, add_comm]

/-- The reduced upper slack for a red endpoint incidence. -/
def redEndpointReducedSlack (configuration : SixPointConfiguration) (code : Fin 4) : ℝ :=
  let blueChild := incidenceSecond code
  incidenceCrossDistance configuration (incidenceFirst code) blueChild -
    (1 + 3 * barC * (barC - 1) / 2) -
    ((barC - 1) * incidenceChildRadius configuration .blue blueChild +
      (barC + 1) * incidenceChildRadius configuration .blue (otherChild blueChild)) / 2

/-- The reduced upper slack for a blue endpoint incidence. -/
def blueEndpointReducedSlack (configuration : SixPointConfiguration) (code : Fin 4) : ℝ :=
  let redChild := incidenceFirst code
  incidenceCrossDistance configuration redChild (incidenceSecond code) -
    (1 + 3 * barC * (barC - 1) / 2) -
    ((barC - 1) * incidenceChildRadius configuration .red redChild +
      (barC + 1) * incidenceChildRadius configuration .red (otherChild redChild)) / 2

/-- The reduced upper slack for a red balanced incidence. -/
def redBalancedReducedSlack (configuration : SixPointConfiguration) (code : Fin 4) : ℝ :=
  (incidenceCrossDistance configuration 0 (incidenceFirst code) +
      incidenceCrossDistance configuration 1 (incidenceSecond code)) / 2 +
    barC - 3 * barC ^ 2 / 2 -
    balancedIncidencePenalty code (incidenceChildRadius configuration .blue 0)
      (incidenceChildRadius configuration .blue 1)

/-- The reduced upper slack for a blue balanced incidence. -/
def blueBalancedReducedSlack (configuration : SixPointConfiguration) (code : Fin 4) : ℝ :=
  (incidenceCrossDistance configuration (incidenceFirst code) 0 +
      incidenceCrossDistance configuration (incidenceSecond code) 1) / 2 +
    barC - 3 * barC ^ 2 / 2 -
    balancedIncidencePenalty code (incidenceChildRadius configuration .red 0)
      (incidenceChildRadius configuration .red 1)

/-- The selected matching alternative makes its reduced slack nonnegative. -/
theorem diagonalMatchingReducedSlack_nonneg {configuration : SixPointConfiguration}
    (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) :
    0 ≤ diagonalMatchingReducedSlack configuration := by
  have hL := (sibling_distance_mem_endpoint_interval h .red).1
  have hM := (sibling_distance_mem_endpoint_interval h .blue).1
  have hcoefficient : 0 ≤ 2 * barC - 1 := by
    nlinarith [one_lt_barC_and_barC_lt_two.1]
  have hscaled := mul_le_mul_of_nonneg_left (show 2 * barC ≤
      dist (configuration .red .left) (configuration .red .right) +
        dist (configuration .blue .left) (configuration .blue .right) by linarith)
    hcoefficient
  apply sub_nonneg.mpr
  simpa [mul_comm] using hscaled.trans hmatching

/-- A red endpoint failure makes the corresponding reduced endpoint slack positive. -/
theorem redEndpointReducedSlack_pos {configuration : SixPointConfiguration}
    (h : configuration.IsAdmissibleAt barS) (code : Fin 4)
    (hfailure : redSiblingTriangleFailure configuration (.endpoint code)) :
    0 < redEndpointReducedSlack configuration code := by
  have hL := (sibling_distance_mem_endpoint_interval h .red).1
  have hM := (sibling_distance_mem_endpoint_interval h .blue).1
  have hcoefficient : 1 - barC ≤ 0 := by
    nlinarith [one_lt_barC_and_barC_lt_two.1]
  have hLscaled := mul_le_mul_of_nonpos_left hL hcoefficient
  have hMscaled := mul_le_mul_of_nonpos_left hM hcoefficient
  fin_cases code <;>
    simp [redSiblingTriangleFailure, siblingTriangleWitnessExceeds,
      redSiblingTriangleTarget, rootedTriangleTotalRadius, redSiblingBlueTriangleReach,
      canonicalTriangleRadius, redEndpointReducedSlack, incidenceFirst, incidenceSecond,
      incidenceChild, incidenceCrossDistance, incidenceChildRadius, otherChild] at hfailure ⊢ <;>
    nlinarith

/-- A blue endpoint failure makes the corresponding reduced endpoint slack positive. -/
theorem blueEndpointReducedSlack_pos {configuration : SixPointConfiguration}
    (h : configuration.IsAdmissibleAt barS) (code : Fin 4)
    (hfailure : blueSiblingTriangleFailure configuration (.endpoint code)) :
    0 < blueEndpointReducedSlack configuration code := by
  have hL := (sibling_distance_mem_endpoint_interval h .red).1
  have hM := (sibling_distance_mem_endpoint_interval h .blue).1
  have hcoefficient : 1 - barC ≤ 0 := by
    nlinarith [one_lt_barC_and_barC_lt_two.1]
  have hLscaled := mul_le_mul_of_nonpos_left hL hcoefficient
  have hMscaled := mul_le_mul_of_nonpos_left hM hcoefficient
  fin_cases code <;>
    simp [blueSiblingTriangleFailure, transposeBlueEndpointWitness, transposeEndpointCode,
      siblingTriangleWitnessExceeds, blueSiblingTriangleTarget, rootedTriangleTotalRadius,
      blueSiblingRedTriangleReach, canonicalTriangleRadius, blueEndpointReducedSlack,
      incidenceFirst, incidenceSecond, incidenceChild, incidenceCrossDistance,
      incidenceChildRadius, otherChild] at hfailure ⊢ <;>
    rw [dist_comm (configuration .blue _) (configuration .red _)] at hfailure <;>
    nlinarith

/-- A red balanced failure makes the corresponding reduced balanced slack positive. -/
theorem redBalancedReducedSlack_pos {configuration : SixPointConfiguration}
    (h : configuration.IsAdmissibleAt barS) (code : Fin 4)
    (hfailure : redSiblingTriangleFailure configuration (.balanced code)) :
    0 < redBalancedReducedSlack configuration code := by
  have hL := (sibling_distance_mem_endpoint_interval h .red).1
  have hM := (sibling_distance_mem_endpoint_interval h .blue).1
  have hcoefficientL : 1 / 2 - barC ≤ 0 := by
    nlinarith [one_lt_barC_and_barC_lt_two.1]
  have hcoefficientM : (1 - barC) / 2 ≤ 0 := by
    nlinarith [one_lt_barC_and_barC_lt_two.1]
  have hLscaled := mul_le_mul_of_nonpos_left hL hcoefficientL
  have hMscaled := mul_le_mul_of_nonpos_left hM hcoefficientM
  fin_cases code <;>
    simp [redSiblingTriangleFailure, siblingTriangleWitnessExceeds,
      redSiblingTriangleTarget, rootedTriangleTotalRadius, redSiblingBlueTriangleReach,
      canonicalTriangleRadius, redBalancedReducedSlack, balancedIncidencePenalty,
      incidenceFirst, incidenceSecond, incidenceChild, incidenceCrossDistance,
      incidenceChildRadius] at hfailure ⊢ <;>
    nlinarith

/-- A blue balanced failure makes the corresponding reduced balanced slack positive. -/
theorem blueBalancedReducedSlack_pos {configuration : SixPointConfiguration}
    (h : configuration.IsAdmissibleAt barS) (code : Fin 4)
    (hfailure : blueSiblingTriangleFailure configuration (.balanced code)) :
    0 < blueBalancedReducedSlack configuration code := by
  have hL := (sibling_distance_mem_endpoint_interval h .red).1
  have hM := (sibling_distance_mem_endpoint_interval h .blue).1
  have hcoefficientL : 1 / 2 - barC ≤ 0 := by
    nlinarith [one_lt_barC_and_barC_lt_two.1]
  have hcoefficientM : (1 - barC) / 2 ≤ 0 := by
    nlinarith [one_lt_barC_and_barC_lt_two.1]
  have hLscaled := mul_le_mul_of_nonpos_left hL hcoefficientM
  have hMscaled := mul_le_mul_of_nonpos_left hM hcoefficientL
  fin_cases code <;>
    simp [blueSiblingTriangleFailure, transposeBlueEndpointWitness,
      siblingTriangleWitnessExceeds, blueSiblingTriangleTarget, rootedTriangleTotalRadius,
      blueSiblingRedTriangleReach, canonicalTriangleRadius, blueBalancedReducedSlack,
      balancedIncidencePenalty, incidenceFirst, incidenceSecond, incidenceChild,
      incidenceCrossDistance, incidenceChildRadius] at hfailure ⊢ <;>
    simp only [dist_comm (configuration .blue .left) (configuration .red .left),
      dist_comm (configuration .blue .left) (configuration .red .right),
      dist_comm (configuration .blue .right) (configuration .red .left),
      dist_comm (configuration .blue .right) (configuration .red .right)] at hfailure <;>
    nlinarith

/-- The `E0/S1` red-endpoint/blue-balanced representative is impossible. -/
theorem not_redEndpoint_zero_and_blueBalanced_one
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) :
    ¬ (redSiblingTriangleFailure configuration (.endpoint 0) ∧
      blueSiblingTriangleFailure configuration (.balanced 1)) := by
  rintro ⟨hred, hblue⟩
  have hpsep := SixPointConfiguration.two_mul_le_dist_redDisplacement h
  have hwsep := SixPointConfiguration.two_mul_le_dist_bluePullback h
  rw [barS, dist_eq_norm] at hpsep hwsep
  have hcertificate := tangentCertificate_e0s1 configuration.rootDisplacement
    (configuration.redDisplacement .left) (configuration.redDisplacement .right)
    (configuration.bluePullback .left) (configuration.bluePullback .right)
    (SixPointConfiguration.norm_rootDisplacement h)
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp)) (by linarith) (by linarith)
  have hmatchingSlack := diagonalMatchingReducedSlack_nonneg h hmatching
  have hredSlack := redEndpointReducedSlack_pos h 0 hred
  have hblueSlack := blueBalancedReducedSlack_pos h 1 hblue
  have hpositive : 0 < diagonalMatchingReducedSlack configuration +
      7 * redEndpointReducedSlack configuration 0 +
      13 * blueBalancedReducedSlack configuration 1 := by
    nlinarith
  simp only [diagonalMatchingReducedSlack, redEndpointReducedSlack,
    blueBalancedReducedSlack, balancedIncidencePenalty, incidenceCrossDistance_eq_norm,
    incidenceChildRadius_red_eq_norm, incidenceChildRadius_blue_eq_norm] at hpositive
  norm_num [incidenceFirst, incidenceSecond, incidenceChild, otherChild] at hpositive
  nlinarith

/-- The `E0/S2` red-endpoint/blue-balanced representative is impossible. -/
theorem not_redEndpoint_zero_and_blueBalanced_two
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) :
    ¬ (redSiblingTriangleFailure configuration (.endpoint 0) ∧
      blueSiblingTriangleFailure configuration (.balanced 2)) := by
  rintro ⟨hred, hblue⟩
  have hpsep := SixPointConfiguration.two_mul_le_dist_redDisplacement h
  have hwsep := SixPointConfiguration.two_mul_le_dist_bluePullback h
  rw [barS, dist_eq_norm] at hpsep hwsep
  have hcertificate := tangentCertificate_e0s2 configuration.rootDisplacement
    (configuration.redDisplacement .left) (configuration.redDisplacement .right)
    (configuration.bluePullback .left) (configuration.bluePullback .right)
    (SixPointConfiguration.norm_rootDisplacement h)
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp)) (by linarith) (by linarith)
  have hmatchingSlack := diagonalMatchingReducedSlack_nonneg h hmatching
  have hredSlack := redEndpointReducedSlack_pos h 0 hred
  have hblueSlack := blueBalancedReducedSlack_pos h 2 hblue
  have hpositive : 0 < diagonalMatchingReducedSlack configuration +
      2 * redEndpointReducedSlack configuration 0 +
      3 * blueBalancedReducedSlack configuration 2 := by
    nlinarith
  simp only [diagonalMatchingReducedSlack, redEndpointReducedSlack,
    blueBalancedReducedSlack, balancedIncidencePenalty, incidenceCrossDistance_eq_norm,
    incidenceChildRadius_red_eq_norm, incidenceChildRadius_blue_eq_norm] at hpositive
  norm_num [incidenceFirst, incidenceSecond, incidenceChild, otherChild] at hpositive
  nlinarith

/-- The `E0/S3` red-endpoint/blue-balanced representative is impossible. -/
theorem not_redEndpoint_zero_and_blueBalanced_three
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) :
    ¬ (redSiblingTriangleFailure configuration (.endpoint 0) ∧
      blueSiblingTriangleFailure configuration (.balanced 3)) := by
  rintro ⟨hred, hblue⟩
  have hpsep := SixPointConfiguration.two_mul_le_dist_redDisplacement h
  have hwsep := SixPointConfiguration.two_mul_le_dist_bluePullback h
  rw [barS, dist_eq_norm] at hpsep hwsep
  have hcertificate := tangentCertificate_e0s3 configuration.rootDisplacement
    (configuration.redDisplacement .left) (configuration.redDisplacement .right)
    (configuration.bluePullback .left) (configuration.bluePullback .right)
    (SixPointConfiguration.norm_rootDisplacement h)
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp)) (by linarith) (by linarith)
  have hmatchingSlack := diagonalMatchingReducedSlack_nonneg h hmatching
  have hredSlack := redEndpointReducedSlack_pos h 0 hred
  have hblueSlack := blueBalancedReducedSlack_pos h 3 hblue
  have hpositive : 0 < 5 * diagonalMatchingReducedSlack configuration +
      41 * redEndpointReducedSlack configuration 0 +
      54 * blueBalancedReducedSlack configuration 3 := by
    nlinarith
  simp only [diagonalMatchingReducedSlack, redEndpointReducedSlack,
    blueBalancedReducedSlack, balancedIncidencePenalty, incidenceCrossDistance_eq_norm,
    incidenceChildRadius_red_eq_norm, incidenceChildRadius_blue_eq_norm] at hpositive
  norm_num [incidenceFirst, incidenceSecond, incidenceChild, otherChild] at hpositive
  nlinarith

/-- The `E1/S1` red-endpoint/blue-balanced representative is impossible. -/
theorem not_redEndpoint_one_and_blueBalanced_one
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) :
    ¬ (redSiblingTriangleFailure configuration (.endpoint 1) ∧
      blueSiblingTriangleFailure configuration (.balanced 1)) := by
  rintro ⟨hred, hblue⟩
  have hpsep := SixPointConfiguration.two_mul_le_dist_redDisplacement h
  have hwsep := SixPointConfiguration.two_mul_le_dist_bluePullback h
  rw [barS, dist_eq_norm] at hpsep hwsep
  have hcertificate := tangentCertificate_e1s1 configuration.rootDisplacement
    (configuration.redDisplacement .left) (configuration.redDisplacement .right)
    (configuration.bluePullback .left) (configuration.bluePullback .right)
    (SixPointConfiguration.norm_rootDisplacement h)
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp)) (by linarith) (by linarith)
  have hmatchingSlack := diagonalMatchingReducedSlack_nonneg h hmatching
  have hredSlack := redEndpointReducedSlack_pos h 1 hred
  have hblueSlack := blueBalancedReducedSlack_pos h 1 hblue
  have hpositive : 0 < diagonalMatchingReducedSlack configuration +
      7 * redEndpointReducedSlack configuration 1 +
      12 * blueBalancedReducedSlack configuration 1 := by
    nlinarith
  simp only [diagonalMatchingReducedSlack, redEndpointReducedSlack,
    blueBalancedReducedSlack, balancedIncidencePenalty, incidenceCrossDistance_eq_norm,
    incidenceChildRadius_red_eq_norm, incidenceChildRadius_blue_eq_norm] at hpositive
  norm_num [incidenceFirst, incidenceSecond, incidenceChild, otherChild] at hpositive
  nlinarith

/-- The `E1/S2` red-endpoint/blue-balanced representative is impossible. -/
theorem not_redEndpoint_one_and_blueBalanced_two
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS) :
    ¬ (redSiblingTriangleFailure configuration (.endpoint 1) ∧
      blueSiblingTriangleFailure configuration (.balanced 2)) := by
  rintro ⟨hred, hblue⟩
  have hpsep := SixPointConfiguration.two_mul_le_dist_redDisplacement h
  have hwsep := SixPointConfiguration.two_mul_le_dist_bluePullback h
  rw [barS, dist_eq_norm] at hpsep hwsep
  have hcertificate := tangentCertificate_e1s2 configuration.rootDisplacement
    (configuration.redDisplacement .left) (configuration.redDisplacement .right)
    (configuration.bluePullback .left) (configuration.bluePullback .right)
    (SixPointConfiguration.norm_rootDisplacement h)
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp)) (by linarith) (by linarith)
  have hredSlack := redEndpointReducedSlack_pos h 1 hred
  have hblueSlack := blueBalancedReducedSlack_pos h 2 hblue
  have hpositive : 0 < 3 * redEndpointReducedSlack configuration 1 +
      7 * blueBalancedReducedSlack configuration 2 := by
    nlinarith
  simp only [redEndpointReducedSlack, blueBalancedReducedSlack,
    balancedIncidencePenalty, incidenceCrossDistance_eq_norm,
    incidenceChildRadius_red_eq_norm, incidenceChildRadius_blue_eq_norm] at hpositive
  norm_num [incidenceFirst, incidenceSecond, incidenceChild, otherChild] at hpositive
  nlinarith

/-- The `E1/S3` red-endpoint/blue-balanced representative is impossible. -/
theorem not_redEndpoint_one_and_blueBalanced_three
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) :
    ¬ (redSiblingTriangleFailure configuration (.endpoint 1) ∧
      blueSiblingTriangleFailure configuration (.balanced 3)) := by
  rintro ⟨hred, hblue⟩
  have hpsep := SixPointConfiguration.two_mul_le_dist_redDisplacement h
  have hwsep := SixPointConfiguration.two_mul_le_dist_bluePullback h
  rw [barS, dist_eq_norm] at hpsep hwsep
  have hcertificate := tangentCertificate_e1s3 configuration.rootDisplacement
    (configuration.redDisplacement .left) (configuration.redDisplacement .right)
    (configuration.bluePullback .left) (configuration.bluePullback .right)
    (SixPointConfiguration.norm_rootDisplacement h)
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp)) (by linarith) (by linarith)
  have hmatchingSlack := diagonalMatchingReducedSlack_nonneg h hmatching
  have hredSlack := redEndpointReducedSlack_pos h 1 hred
  have hblueSlack := blueBalancedReducedSlack_pos h 3 hblue
  have hpositive : 0 < 3 * diagonalMatchingReducedSlack configuration +
      11 * redEndpointReducedSlack configuration 1 +
      16 * blueBalancedReducedSlack configuration 3 := by
    nlinarith
  simp only [diagonalMatchingReducedSlack, redEndpointReducedSlack,
    blueBalancedReducedSlack, balancedIncidencePenalty, incidenceCrossDistance_eq_norm,
    incidenceChildRadius_red_eq_norm, incidenceChildRadius_blue_eq_norm] at hpositive
  norm_num [incidenceFirst, incidenceSecond, incidenceChild, otherChild] at hpositive
  nlinarith

/-- The `S0/S1` balanced/balanced representative is impossible. -/
theorem not_redBalanced_zero_and_blueBalanced_one
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS) :
    ¬ (redSiblingTriangleFailure configuration (.balanced 0) ∧
      blueSiblingTriangleFailure configuration (.balanced 1)) := by
  rintro ⟨hred, hblue⟩
  have hpsep := SixPointConfiguration.two_mul_le_dist_redDisplacement h
  have hwsep := SixPointConfiguration.two_mul_le_dist_bluePullback h
  rw [barS, dist_eq_norm] at hpsep hwsep
  have hcertificate := tangentCertificate_s0s1 configuration.rootDisplacement
    (configuration.redDisplacement .left) (configuration.redDisplacement .right)
    (configuration.bluePullback .left) (configuration.bluePullback .right)
    (SixPointConfiguration.norm_rootDisplacement h)
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp)) (by linarith) (by linarith)
  have hredSlack := redBalancedReducedSlack_pos h 0 hred
  have hblueSlack := blueBalancedReducedSlack_pos h 1 hblue
  have hpositive : 0 < 2 * redBalancedReducedSlack configuration 0 +
      5 * blueBalancedReducedSlack configuration 1 := by
    nlinarith
  simp only [redBalancedReducedSlack, blueBalancedReducedSlack,
    balancedIncidencePenalty, incidenceCrossDistance_eq_norm,
    incidenceChildRadius_red_eq_norm, incidenceChildRadius_blue_eq_norm] at hpositive
  norm_num [incidenceFirst, incidenceSecond, incidenceChild] at hpositive
  nlinarith

/-- The `S0/S2` balanced/balanced representative is impossible. -/
theorem not_redBalanced_zero_and_blueBalanced_two
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS) :
    ¬ (redSiblingTriangleFailure configuration (.balanced 0) ∧
      blueSiblingTriangleFailure configuration (.balanced 2)) := by
  rintro ⟨hred, hblue⟩
  have hpsep := SixPointConfiguration.two_mul_le_dist_redDisplacement h
  have hwsep := SixPointConfiguration.two_mul_le_dist_bluePullback h
  rw [barS, dist_eq_norm] at hpsep hwsep
  have hcertificate := tangentCertificate_s0s2 configuration.rootDisplacement
    (configuration.redDisplacement .left) (configuration.redDisplacement .right)
    (configuration.bluePullback .left) (configuration.bluePullback .right)
    (SixPointConfiguration.norm_rootDisplacement h)
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp)) (by linarith) (by linarith)
  have hredSlack := redBalancedReducedSlack_pos h 0 hred
  have hblueSlack := blueBalancedReducedSlack_pos h 2 hblue
  have hpositive : 0 < 2 * redBalancedReducedSlack configuration 0 +
      5 * blueBalancedReducedSlack configuration 2 := by
    nlinarith
  simp only [redBalancedReducedSlack, blueBalancedReducedSlack,
    balancedIncidencePenalty, incidenceCrossDistance_eq_norm,
    incidenceChildRadius_red_eq_norm, incidenceChildRadius_blue_eq_norm] at hpositive
  norm_num [incidenceFirst, incidenceSecond, incidenceChild] at hpositive
  nlinarith

/-- The `S1/S1` balanced/balanced representative is impossible. -/
theorem not_redBalanced_one_and_blueBalanced_one
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) :
    ¬ (redSiblingTriangleFailure configuration (.balanced 1) ∧
      blueSiblingTriangleFailure configuration (.balanced 1)) := by
  rintro ⟨hred, hblue⟩
  have hpsep := SixPointConfiguration.two_mul_le_dist_redDisplacement h
  have hwsep := SixPointConfiguration.two_mul_le_dist_bluePullback h
  rw [barS, dist_eq_norm] at hpsep hwsep
  have hcertificate := tangentCertificate_s1s1 configuration.rootDisplacement
    (configuration.redDisplacement .left) (configuration.redDisplacement .right)
    (configuration.bluePullback .left) (configuration.bluePullback .right)
    (SixPointConfiguration.norm_rootDisplacement h)
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp)) (by linarith) (by linarith)
  have hmatchingSlack := diagonalMatchingReducedSlack_nonneg h hmatching
  have hredSlack := redBalancedReducedSlack_pos h 1 hred
  have hblueSlack := blueBalancedReducedSlack_pos h 1 hblue
  have hpositive : 0 < diagonalMatchingReducedSlack configuration +
      12 * redBalancedReducedSlack configuration 1 +
      12 * blueBalancedReducedSlack configuration 1 := by
    nlinarith
  simp only [diagonalMatchingReducedSlack, redBalancedReducedSlack,
    blueBalancedReducedSlack, balancedIncidencePenalty, incidenceCrossDistance_eq_norm,
    incidenceChildRadius_red_eq_norm, incidenceChildRadius_blue_eq_norm] at hpositive
  norm_num [incidenceFirst, incidenceSecond, incidenceChild] at hpositive
  nlinarith

/-- The `S1/S2` balanced/balanced representative is impossible. -/
theorem not_redBalanced_one_and_blueBalanced_two
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS) :
    ¬ (redSiblingTriangleFailure configuration (.balanced 1) ∧
      blueSiblingTriangleFailure configuration (.balanced 2)) := by
  rintro ⟨hred, hblue⟩
  have hpsep := SixPointConfiguration.two_mul_le_dist_redDisplacement h
  have hwsep := SixPointConfiguration.two_mul_le_dist_bluePullback h
  rw [barS, dist_eq_norm] at hpsep hwsep
  have hcertificate := tangentCertificate_s1s2 configuration.rootDisplacement
    (configuration.redDisplacement .left) (configuration.redDisplacement .right)
    (configuration.bluePullback .left) (configuration.bluePullback .right)
    (SixPointConfiguration.norm_rootDisplacement h)
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp)) (by linarith) (by linarith)
  have hredSlack := redBalancedReducedSlack_pos h 1 hred
  have hblueSlack := blueBalancedReducedSlack_pos h 2 hblue
  have hpositive : 0 < 2 * redBalancedReducedSlack configuration 1 +
      5 * blueBalancedReducedSlack configuration 2 := by
    nlinarith
  simp only [redBalancedReducedSlack, blueBalancedReducedSlack,
    balancedIncidencePenalty, incidenceCrossDistance_eq_norm,
    incidenceChildRadius_red_eq_norm, incidenceChildRadius_blue_eq_norm] at hpositive
  norm_num [incidenceFirst, incidenceSecond, incidenceChild] at hpositive
  nlinarith

/-- The `S2/S2` balanced/balanced representative is impossible. -/
theorem not_redBalanced_two_and_blueBalanced_two
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) :
    ¬ (redSiblingTriangleFailure configuration (.balanced 2) ∧
      blueSiblingTriangleFailure configuration (.balanced 2)) := by
  rintro ⟨hred, hblue⟩
  have hpsep := SixPointConfiguration.two_mul_le_dist_redDisplacement h
  have hwsep := SixPointConfiguration.two_mul_le_dist_bluePullback h
  rw [barS, dist_eq_norm] at hpsep hwsep
  have hcertificate := tangentCertificate_s2s2 configuration.rootDisplacement
    (configuration.redDisplacement .left) (configuration.redDisplacement .right)
    (configuration.bluePullback .left) (configuration.bluePullback .right)
    (SixPointConfiguration.norm_rootDisplacement h)
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp)) (by linarith) (by linarith)
  have hmatchingSlack := diagonalMatchingReducedSlack_nonneg h hmatching
  have hredSlack := redBalancedReducedSlack_pos h 2 hred
  have hblueSlack := blueBalancedReducedSlack_pos h 2 hblue
  have hpositive : 0 < diagonalMatchingReducedSlack configuration +
      8 * redBalancedReducedSlack configuration 2 +
      8 * blueBalancedReducedSlack configuration 2 := by
    nlinarith
  simp only [diagonalMatchingReducedSlack, redBalancedReducedSlack,
    blueBalancedReducedSlack, balancedIncidencePenalty, incidenceCrossDistance_eq_norm,
    incidenceChildRadius_red_eq_norm, incidenceChildRadius_blue_eq_norm] at hpositive
  norm_num [incidenceFirst, incidenceSecond, incidenceChild] at hpositive
  nlinarith

/-- The first adjacent endpoint representative is impossible. -/
theorem not_redEndpoint_zero_and_blueEndpoint_one
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) :
    ¬ (redSiblingTriangleFailure configuration (.endpoint 0) ∧
      blueSiblingTriangleFailure configuration (.endpoint 1)) := by
  rintro ⟨hred, hblue⟩
  have hpsep := SixPointConfiguration.two_mul_le_dist_redDisplacement h
  have hwsep := SixPointConfiguration.two_mul_le_dist_bluePullback h
  rw [barS, dist_eq_norm] at hpsep hwsep
  have hcertificate := tangentCertificate_adjacentFirst configuration.rootDisplacement
    (configuration.redDisplacement .left) (configuration.redDisplacement .right)
    (configuration.bluePullback .left) (configuration.bluePullback .right)
    (SixPointConfiguration.norm_rootDisplacement h)
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp)) (by linarith) (by linarith)
  have hmatchingSlack := diagonalMatchingReducedSlack_nonneg h hmatching
  have hredSlack := redEndpointReducedSlack_pos h 0 hred
  have hblueSlack := blueEndpointReducedSlack_pos h 1 hblue
  have hpositive : 0 < diagonalMatchingReducedSlack configuration +
      7 / 4 * (redEndpointReducedSlack configuration 0 +
        blueEndpointReducedSlack configuration 1) := by
    nlinarith
  simp only [diagonalMatchingReducedSlack, redEndpointReducedSlack,
    blueEndpointReducedSlack, incidenceCrossDistance_eq_norm,
    incidenceChildRadius_red_eq_norm, incidenceChildRadius_blue_eq_norm] at hpositive
  norm_num [incidenceFirst, incidenceSecond, incidenceChild, otherChild] at hpositive
  nlinarith

/-- The second adjacent endpoint representative is impossible. -/
theorem not_redEndpoint_zero_and_blueEndpoint_two
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) :
    ¬ (redSiblingTriangleFailure configuration (.endpoint 0) ∧
      blueSiblingTriangleFailure configuration (.endpoint 2)) := by
  rintro ⟨hred, hblue⟩
  have hpsep := SixPointConfiguration.two_mul_le_dist_redDisplacement h
  have hwsep := SixPointConfiguration.two_mul_le_dist_bluePullback h
  rw [barS, dist_eq_norm] at hpsep hwsep
  have hcertificate := tangentCertificate_adjacentSecond configuration.rootDisplacement
    (configuration.redDisplacement .left) (configuration.redDisplacement .right)
    (configuration.bluePullback .left) (configuration.bluePullback .right)
    (SixPointConfiguration.norm_rootDisplacement h)
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp)) (by linarith) (by linarith)
  have hmatchingSlack := diagonalMatchingReducedSlack_nonneg h hmatching
  have hredSlack := redEndpointReducedSlack_pos h 0 hred
  have hblueSlack := blueEndpointReducedSlack_pos h 2 hblue
  have hpositive : 0 < diagonalMatchingReducedSlack configuration +
      7 / 4 * (redEndpointReducedSlack configuration 0 +
        blueEndpointReducedSlack configuration 2) := by
    nlinarith
  simp only [diagonalMatchingReducedSlack, redEndpointReducedSlack,
    blueEndpointReducedSlack, incidenceCrossDistance_eq_norm,
    incidenceChildRadius_red_eq_norm, incidenceChildRadius_blue_eq_norm] at hpositive
  norm_num [incidenceFirst, incidenceSecond, incidenceChild, otherChild] at hpositive
  nlinarith

/-- The exact scalar lens bound for the off-matching coincident endpoint cell. -/
def OffMatchingCoincidentLensBound (configuration : SixPointConfiguration) : Prop :=
  6 * diagonalMatchingReducedSlack configuration +
      7 * redEndpointReducedSlack configuration 1 +
      7 * blueEndpointReducedSlack configuration 1 < 0

/-- The exact scalar lens bound for the `E0/S0` endpoint/balanced cell. -/
def EndpointBalancedE0S0LensBound (configuration : SixPointConfiguration) : Prop :=
  5 * diagonalMatchingReducedSlack configuration +
      9 * redEndpointReducedSlack configuration 0 +
      6 * blueBalancedReducedSlack configuration 0 < 0

/-- The exact scalar lens bound for the `E1/S0` endpoint/balanced cell. -/
def EndpointBalancedE1S0LensBound (configuration : SixPointConfiguration) : Prop :=
  13 * diagonalMatchingReducedSlack configuration +
      24 * redEndpointReducedSlack configuration 1 +
      15 * blueBalancedReducedSlack configuration 0 < 0

/-- The exact scalar lens bound for the `S0/S0` balanced/balanced cell. -/
def BalancedBalancedS0S0LensBound (configuration : SixPointConfiguration) : Prop :=
  2 * diagonalMatchingReducedSlack configuration +
      5 * redBalancedReducedSlack configuration 0 +
      5 * blueBalancedReducedSlack configuration 0 < 0

/-- The exact scalar lens bound for the `S0/S3` balanced/balanced cell. -/
def BalancedBalancedS0S3LensBound (configuration : SixPointConfiguration) : Prop :=
  7 * diagonalMatchingReducedSlack configuration +
      20 * redBalancedReducedSlack configuration 0 +
      20 * blueBalancedReducedSlack configuration 3 < 0

/-- The off-matching scalar lens bound excludes its endpoint representative. -/
theorem offMatchingCoincident_excluded_of_lensBound
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration)
    (hlens : OffMatchingCoincidentLensBound configuration) :
    ¬ (redSiblingTriangleFailure configuration (.endpoint 1) ∧
      blueSiblingTriangleFailure configuration (.endpoint 1)) := by
  rintro ⟨hred, hblue⟩
  have hmatchingSlack := diagonalMatchingReducedSlack_nonneg h hmatching
  have hredSlack := redEndpointReducedSlack_pos h 1 hred
  have hblueSlack := blueEndpointReducedSlack_pos h 1 hblue
  exact (not_lt_of_ge (by positivity : 0 ≤
    6 * diagonalMatchingReducedSlack configuration +
      7 * redEndpointReducedSlack configuration 1 +
      7 * blueEndpointReducedSlack configuration 1)) hlens

/-- The `E0/S0` scalar lens bound excludes its endpoint/balanced representative. -/
theorem endpointBalancedE0S0_excluded_of_lensBound
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration)
    (hlens : EndpointBalancedE0S0LensBound configuration) :
    ¬ (redSiblingTriangleFailure configuration (.endpoint 0) ∧
      blueSiblingTriangleFailure configuration (.balanced 0)) := by
  rintro ⟨hred, hblue⟩
  have hmatchingSlack := diagonalMatchingReducedSlack_nonneg h hmatching
  have hredSlack := redEndpointReducedSlack_pos h 0 hred
  have hblueSlack := blueBalancedReducedSlack_pos h 0 hblue
  exact (not_lt_of_ge (by positivity : 0 ≤
    5 * diagonalMatchingReducedSlack configuration +
      9 * redEndpointReducedSlack configuration 0 +
      6 * blueBalancedReducedSlack configuration 0)) hlens

/-- The `E1/S0` scalar lens bound excludes its endpoint/balanced representative. -/
theorem endpointBalancedE1S0_excluded_of_lensBound
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration)
    (hlens : EndpointBalancedE1S0LensBound configuration) :
    ¬ (redSiblingTriangleFailure configuration (.endpoint 1) ∧
      blueSiblingTriangleFailure configuration (.balanced 0)) := by
  rintro ⟨hred, hblue⟩
  have hmatchingSlack := diagonalMatchingReducedSlack_nonneg h hmatching
  have hredSlack := redEndpointReducedSlack_pos h 1 hred
  have hblueSlack := blueBalancedReducedSlack_pos h 0 hblue
  exact (not_lt_of_ge (by positivity : 0 ≤
    13 * diagonalMatchingReducedSlack configuration +
      24 * redEndpointReducedSlack configuration 1 +
      15 * blueBalancedReducedSlack configuration 0)) hlens

/-- The `S0/S0` scalar lens bound excludes its balanced representative. -/
theorem balancedBalancedS0S0_excluded_of_lensBound
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration)
    (hlens : BalancedBalancedS0S0LensBound configuration) :
    ¬ (redSiblingTriangleFailure configuration (.balanced 0) ∧
      blueSiblingTriangleFailure configuration (.balanced 0)) := by
  rintro ⟨hred, hblue⟩
  have hmatchingSlack := diagonalMatchingReducedSlack_nonneg h hmatching
  have hredSlack := redBalancedReducedSlack_pos h 0 hred
  have hblueSlack := blueBalancedReducedSlack_pos h 0 hblue
  exact (not_lt_of_ge (by positivity : 0 ≤
    2 * diagonalMatchingReducedSlack configuration +
      5 * redBalancedReducedSlack configuration 0 +
      5 * blueBalancedReducedSlack configuration 0)) hlens

/-- The `S0/S3` scalar lens bound excludes its balanced representative. -/
theorem balancedBalancedS0S3_excluded_of_lensBound
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration)
    (hlens : BalancedBalancedS0S3LensBound configuration) :
    ¬ (redSiblingTriangleFailure configuration (.balanced 0) ∧
      blueSiblingTriangleFailure configuration (.balanced 3)) := by
  rintro ⟨hred, hblue⟩
  have hmatchingSlack := diagonalMatchingReducedSlack_nonneg h hmatching
  have hredSlack := redBalancedReducedSlack_pos h 0 hred
  have hblueSlack := blueBalancedReducedSlack_pos h 3 hblue
  exact (not_lt_of_ge (by positivity : 0 ≤
    7 * diagonalMatchingReducedSlack configuration +
      20 * redBalancedReducedSlack configuration 0 +
      20 * blueBalancedReducedSlack configuration 3)) hlens

/-- Every endpoint/endpoint cell outside the matched and off-matching lens orbits is excluded. -/
theorem endpointEndpoint_excluded_outside_lens
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) (redCode blueCode : Fin 4)
    (hnotMatched : endpointEndpointOrbit redCode blueCode ≠ .matchedCoincident)
    (hnotLens : endpointEndpointOrbit redCode blueCode ≠ .offMatchingCoincident) :
    ¬ (redSiblingTriangleFailure configuration (.endpoint redCode) ∧
      blueSiblingTriangleFailure configuration (.endpoint blueCode)) := by
  fin_cases redCode <;> fin_cases blueCode
  · exact (hnotMatched rfl).elim
  · exact not_redEndpoint_zero_and_blueEndpoint_one h hmatching
  · exact not_redEndpoint_zero_and_blueEndpoint_two h hmatching
  · exact not_redEndpoint_zero_and_blueEndpoint_three h
  · intro failures
    apply not_redEndpoint_zero_and_blueEndpoint_two (IsAdmissibleAt.transposeColors h)
      ((selectedDiagonalMatchingFails_transposeColors configuration).2 hmatching)
    exact ⟨(redEndpointFailure_transposeColors configuration 0).2 failures.2,
      (blueEndpointFailure_transposeColors configuration 1).2 failures.1⟩
  · exact (hnotLens rfl).elim
  · exact not_redEndpoint_one_and_blueEndpoint_two h
  · intro failures
    let transposed := transposeConfigurationColors configuration
    apply not_redEndpoint_zero_and_blueEndpoint_one
      (IsAdmissibleAt.swapChildren (IsAdmissibleAt.transposeColors h))
      ((selectedDiagonalMatchingFails_swapChildren transposed).2
        ((selectedDiagonalMatchingFails_transposeColors configuration).2 hmatching))
    exact ⟨(redEndpointFailure_swapChildren transposed 3).2
        ((redEndpointFailure_transposeColors configuration 3).2 failures.2),
      (blueEndpointFailure_swapChildren transposed 2).2
        ((blueEndpointFailure_transposeColors configuration 1).2 failures.1)⟩
  · intro failures
    apply not_redEndpoint_zero_and_blueEndpoint_one (IsAdmissibleAt.transposeColors h)
      ((selectedDiagonalMatchingFails_transposeColors configuration).2 hmatching)
    exact ⟨(redEndpointFailure_transposeColors configuration 0).2 failures.2,
      (blueEndpointFailure_transposeColors configuration 2).2 failures.1⟩
  · intro failures
    apply not_redEndpoint_one_and_blueEndpoint_two (IsAdmissibleAt.swapChildren h)
    exact ⟨(redEndpointFailure_swapChildren configuration 2).2 failures.1,
      (blueEndpointFailure_swapChildren configuration 1).2 failures.2⟩
  · exact (hnotLens rfl).elim
  · intro failures
    let transposed := transposeConfigurationColors configuration
    apply not_redEndpoint_zero_and_blueEndpoint_two
      (IsAdmissibleAt.swapChildren (IsAdmissibleAt.transposeColors h))
      ((selectedDiagonalMatchingFails_swapChildren transposed).2
        ((selectedDiagonalMatchingFails_transposeColors configuration).2 hmatching))
    exact ⟨(redEndpointFailure_swapChildren transposed 3).2
        ((redEndpointFailure_transposeColors configuration 3).2 failures.2),
      (blueEndpointFailure_swapChildren transposed 1).2
        ((blueEndpointFailure_transposeColors configuration 2).2 failures.1)⟩
  · intro failures
    apply not_redEndpoint_zero_and_blueEndpoint_three (IsAdmissibleAt.swapChildren h)
    exact ⟨(redEndpointFailure_swapChildren configuration 3).2 failures.1,
      (blueEndpointFailure_swapChildren configuration 0).2 failures.2⟩
  · intro failures
    apply not_redEndpoint_zero_and_blueEndpoint_two (IsAdmissibleAt.swapChildren h)
      ((selectedDiagonalMatchingFails_swapChildren configuration).2 hmatching)
    exact ⟨(redEndpointFailure_swapChildren configuration 3).2 failures.1,
      (blueEndpointFailure_swapChildren configuration 1).2 failures.2⟩
  · intro failures
    apply not_redEndpoint_zero_and_blueEndpoint_one (IsAdmissibleAt.swapChildren h)
      ((selectedDiagonalMatchingFails_swapChildren configuration).2 hmatching)
    exact ⟨(redEndpointFailure_swapChildren configuration 3).2 failures.1,
      (blueEndpointFailure_swapChildren configuration 2).2 failures.2⟩
  · exact (hnotMatched rfl).elim

/-- Every endpoint/balanced cell outside the two lens orbits is excluded. -/
theorem endpointBalanced_excluded_outside_lenses
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) (endpointCode balancedCode : Fin 4)
    (hnotE0S0 : endpointBalancedOrbit endpointCode balancedCode ≠ .e0s0)
    (hnotE1S0 : endpointBalancedOrbit endpointCode balancedCode ≠ .e1s0) :
    ¬ (redSiblingTriangleFailure configuration (.endpoint endpointCode) ∧
      blueSiblingTriangleFailure configuration (.balanced balancedCode)) := by
  fin_cases endpointCode <;> fin_cases balancedCode
  · exact (hnotE0S0 rfl).elim
  · exact not_redEndpoint_zero_and_blueBalanced_one h hmatching
  · exact not_redEndpoint_zero_and_blueBalanced_two h hmatching
  · exact not_redEndpoint_zero_and_blueBalanced_three h hmatching
  · exact (hnotE1S0 rfl).elim
  · exact not_redEndpoint_one_and_blueBalanced_one h hmatching
  · exact not_redEndpoint_one_and_blueBalanced_two h
  · exact not_redEndpoint_one_and_blueBalanced_three h hmatching
  · intro failures
    apply not_redEndpoint_one_and_blueBalanced_three (IsAdmissibleAt.swapChildren h)
      ((selectedDiagonalMatchingFails_swapChildren configuration).2 hmatching)
    exact ⟨(redEndpointFailure_swapChildren configuration 2).2 failures.1,
      (blueBalancedFailure_swapChildren configuration 0).2 failures.2⟩
  · intro failures
    apply not_redEndpoint_one_and_blueBalanced_one (IsAdmissibleAt.swapChildren h)
      ((selectedDiagonalMatchingFails_swapChildren configuration).2 hmatching)
    exact ⟨(redEndpointFailure_swapChildren configuration 2).2 failures.1,
      (blueBalancedFailure_swapChildren configuration 1).2 failures.2⟩
  · intro failures
    apply not_redEndpoint_one_and_blueBalanced_two (IsAdmissibleAt.swapChildren h)
    exact ⟨(redEndpointFailure_swapChildren configuration 2).2 failures.1,
      (blueBalancedFailure_swapChildren configuration 2).2 failures.2⟩
  · exact (hnotE1S0 rfl).elim
  · intro failures
    apply not_redEndpoint_zero_and_blueBalanced_three (IsAdmissibleAt.swapChildren h)
      ((selectedDiagonalMatchingFails_swapChildren configuration).2 hmatching)
    exact ⟨(redEndpointFailure_swapChildren configuration 3).2 failures.1,
      (blueBalancedFailure_swapChildren configuration 0).2 failures.2⟩
  · intro failures
    apply not_redEndpoint_zero_and_blueBalanced_one (IsAdmissibleAt.swapChildren h)
      ((selectedDiagonalMatchingFails_swapChildren configuration).2 hmatching)
    exact ⟨(redEndpointFailure_swapChildren configuration 3).2 failures.1,
      (blueBalancedFailure_swapChildren configuration 1).2 failures.2⟩
  · intro failures
    apply not_redEndpoint_zero_and_blueBalanced_two (IsAdmissibleAt.swapChildren h)
      ((selectedDiagonalMatchingFails_swapChildren configuration).2 hmatching)
    exact ⟨(redEndpointFailure_swapChildren configuration 3).2 failures.1,
      (blueBalancedFailure_swapChildren configuration 2).2 failures.2⟩
  · exact (hnotE0S0 rfl).elim

/-- The color-reversed endpoint/balanced cells outside the two lens orbits are excluded. -/
theorem balancedEndpoint_excluded_outside_lenses
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) (balancedCode endpointCode : Fin 4)
    (hnotE0S0 : endpointBalancedOrbit (transposeEndpointCode endpointCode) balancedCode ≠ .e0s0)
    (hnotE1S0 : endpointBalancedOrbit (transposeEndpointCode endpointCode) balancedCode ≠ .e1s0) :
    ¬ (redSiblingTriangleFailure configuration (.balanced balancedCode) ∧
      blueSiblingTriangleFailure configuration (.endpoint endpointCode)) := by
  intro failures
  apply endpointBalanced_excluded_outside_lenses (IsAdmissibleAt.transposeColors h)
    ((selectedDiagonalMatchingFails_transposeColors configuration).2 hmatching)
    (transposeEndpointCode endpointCode) balancedCode hnotE0S0 hnotE1S0
  exact ⟨(redEndpointFailure_transposeColors configuration endpointCode).2 failures.2,
    (blueBalancedFailure_transposeColors configuration balancedCode).2 failures.1⟩

/-- Every balanced/balanced cell outside the two lens orbits is excluded. -/
theorem balancedBalanced_excluded_outside_lenses
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) (redCode blueCode : Fin 4)
    (hnotS0S0 : balancedBalancedOrbit redCode blueCode ≠ .s0s0)
    (hnotS0S3 : balancedBalancedOrbit redCode blueCode ≠ .s0s3) :
    ¬ (redSiblingTriangleFailure configuration (.balanced redCode) ∧
      blueSiblingTriangleFailure configuration (.balanced blueCode)) := by
  fin_cases redCode <;> fin_cases blueCode
  · exact (hnotS0S0 rfl).elim
  · exact not_redBalanced_zero_and_blueBalanced_one h
  · exact not_redBalanced_zero_and_blueBalanced_two h
  · exact (hnotS0S3 rfl).elim
  · intro failures
    apply not_redBalanced_zero_and_blueBalanced_one (IsAdmissibleAt.transposeColors h)
    exact ⟨(redBalancedFailure_transposeColors configuration 0).2 failures.2,
      (blueBalancedFailure_transposeColors configuration 1).2 failures.1⟩
  · exact not_redBalanced_one_and_blueBalanced_one h hmatching
  · exact not_redBalanced_one_and_blueBalanced_two h
  · intro failures
    let transposed := transposeConfigurationColors configuration
    apply not_redBalanced_zero_and_blueBalanced_one
      (IsAdmissibleAt.swapChildren (IsAdmissibleAt.transposeColors h))
    exact ⟨(redBalancedFailure_swapChildren transposed 3).2
        ((redBalancedFailure_transposeColors configuration 3).2 failures.2),
      (blueBalancedFailure_swapChildren transposed 1).2
        ((blueBalancedFailure_transposeColors configuration 1).2 failures.1)⟩
  · intro failures
    apply not_redBalanced_zero_and_blueBalanced_two (IsAdmissibleAt.transposeColors h)
    exact ⟨(redBalancedFailure_transposeColors configuration 0).2 failures.2,
      (blueBalancedFailure_transposeColors configuration 2).2 failures.1⟩
  · intro failures
    apply not_redBalanced_one_and_blueBalanced_two (IsAdmissibleAt.transposeColors h)
    exact ⟨(redBalancedFailure_transposeColors configuration 1).2 failures.2,
      (blueBalancedFailure_transposeColors configuration 2).2 failures.1⟩
  · exact not_redBalanced_two_and_blueBalanced_two h hmatching
  · intro failures
    let transposed := transposeConfigurationColors configuration
    apply not_redBalanced_zero_and_blueBalanced_two
      (IsAdmissibleAt.swapChildren (IsAdmissibleAt.transposeColors h))
    exact ⟨(redBalancedFailure_swapChildren transposed 3).2
        ((redBalancedFailure_transposeColors configuration 3).2 failures.2),
      (blueBalancedFailure_swapChildren transposed 2).2
        ((blueBalancedFailure_transposeColors configuration 2).2 failures.1)⟩
  · exact (hnotS0S3 rfl).elim
  · intro failures
    apply not_redBalanced_zero_and_blueBalanced_one (IsAdmissibleAt.swapChildren h)
    exact ⟨(redBalancedFailure_swapChildren configuration 3).2 failures.1,
      (blueBalancedFailure_swapChildren configuration 1).2 failures.2⟩
  · intro failures
    apply not_redBalanced_zero_and_blueBalanced_two (IsAdmissibleAt.swapChildren h)
    exact ⟨(redBalancedFailure_swapChildren configuration 3).2 failures.1,
      (blueBalancedFailure_swapChildren configuration 2).2 failures.2⟩
  · exact (hnotS0S0 rfl).elim

/-- The five possible outcomes after all tangent and direct incidence exclusions. -/
def SiblingIncidenceOutcome (configuration : SixPointConfiguration) : Prop :=
  (∃ code : Fin 4, (code = 0 ∨ code = 3) ∧
      redSiblingTriangleFailure configuration (.endpoint code) ∧
      blueSiblingTriangleFailure configuration (.endpoint code)) ∨
    (∃ redCode blueCode, endpointEndpointOrbit redCode blueCode = .offMatchingCoincident ∧
      redSiblingTriangleFailure configuration (.endpoint redCode) ∧
      blueSiblingTriangleFailure configuration (.endpoint blueCode)) ∨
    (∃ endpointCode balancedCode,
      (endpointBalancedOrbit endpointCode balancedCode = .e0s0 ∨
        endpointBalancedOrbit endpointCode balancedCode = .e1s0) ∧
      redSiblingTriangleFailure configuration (.endpoint endpointCode) ∧
      blueSiblingTriangleFailure configuration (.balanced balancedCode)) ∨
    (∃ balancedCode endpointCode,
      (endpointBalancedOrbit (transposeEndpointCode endpointCode) balancedCode = .e0s0 ∨
        endpointBalancedOrbit (transposeEndpointCode endpointCode) balancedCode = .e1s0) ∧
      redSiblingTriangleFailure configuration (.balanced balancedCode) ∧
      blueSiblingTriangleFailure configuration (.endpoint endpointCode)) ∨
    (∃ redCode blueCode,
      (balancedBalancedOrbit redCode blueCode = .s0s0 ∨
        balancedBalancedOrbit redCode blueCode = .s0s3) ∧
      redSiblingTriangleFailure configuration (.balanced redCode) ∧
      blueSiblingTriangleFailure configuration (.balanced blueCode))

/-- Simultaneous sibling-triangle witnesses route to a matched endpoint or one lens orbit. -/
theorem siblingIncidence_route
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration)
    (hred : ∃ witness, redSiblingTriangleFailure configuration witness)
    (hblue : ∃ witness, blueSiblingTriangleFailure configuration witness) :
    SiblingIncidenceOutcome configuration := by
  obtain ⟨redWitness, hred⟩ := hred
  obtain ⟨blueWitness, hblue⟩ := hblue
  unfold SiblingIncidenceOutcome
  cases redWitness with
  | endpoint redCode =>
      cases blueWitness with
      | endpoint blueCode =>
          by_cases hmatched : endpointEndpointOrbit redCode blueCode = .matchedCoincident
          · rcases (endpointEndpointOrbit_eq_matchedCoincident_iff redCode blueCode).1
              hmatched with
              ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inl ⟨0, Or.inl rfl, hred, hblue⟩
            · exact Or.inl ⟨3, Or.inr rfl, hred, hblue⟩
          · by_cases hlens : endpointEndpointOrbit redCode blueCode = .offMatchingCoincident
            · exact Or.inr (Or.inl ⟨redCode, blueCode, hlens, hred, hblue⟩)
            · exact (endpointEndpoint_excluded_outside_lens h hmatching redCode blueCode
                hmatched hlens ⟨hred, hblue⟩).elim
      | balanced blueCode =>
          by_cases hzero : endpointBalancedOrbit redCode blueCode = .e0s0
          · exact Or.inr (Or.inr (Or.inl ⟨redCode, blueCode, Or.inl hzero, hred, hblue⟩))
          · by_cases hone : endpointBalancedOrbit redCode blueCode = .e1s0
            · exact Or.inr (Or.inr (Or.inl ⟨redCode, blueCode, Or.inr hone, hred, hblue⟩))
            · exact (endpointBalanced_excluded_outside_lenses h hmatching redCode blueCode
                hzero hone ⟨hred, hblue⟩).elim
  | balanced redCode =>
      cases blueWitness with
      | endpoint blueCode =>
          by_cases hzero :
              endpointBalancedOrbit (transposeEndpointCode blueCode) redCode = .e0s0
          · exact Or.inr (Or.inr (Or.inr (Or.inl
              ⟨redCode, blueCode, Or.inl hzero, hred, hblue⟩)))
          · by_cases hone :
                endpointBalancedOrbit (transposeEndpointCode blueCode) redCode = .e1s0
            · exact Or.inr (Or.inr (Or.inr (Or.inl
                ⟨redCode, blueCode, Or.inr hone, hred, hblue⟩)))
            · exact (balancedEndpoint_excluded_outside_lenses h hmatching redCode blueCode
                hzero hone ⟨hred, hblue⟩).elim
      | balanced blueCode =>
          by_cases hzero : balancedBalancedOrbit redCode blueCode = .s0s0
          · exact Or.inr (Or.inr (Or.inr (Or.inr
              ⟨redCode, blueCode, Or.inl hzero, hred, hblue⟩)))
          · by_cases hthree : balancedBalancedOrbit redCode blueCode = .s0s3
            · exact Or.inr (Or.inr (Or.inr (Or.inr
                ⟨redCode, blueCode, Or.inr hthree, hred, hblue⟩)))
            · exact (balancedBalanced_excluded_outside_lenses h hmatching redCode blueCode
                hzero hthree ⟨hred, hblue⟩).elim

/-- If supports `67` and `76` both fail, their witnesses route to the five residual outcomes. -/
theorem siblingTriangle_score_failure_route
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration)
    (hred : RedSiblingTriangleFails configuration h)
    (hblue : BlueSiblingTriangleFails configuration h) :
    SiblingIncidenceOutcome configuration :=
  siblingIncidence_route h hmatching
    (exists_redSiblingTriangleFailure_of_score_failure h hred)
    (exists_blueSiblingTriangleFailure_of_score_failure h hblue)

end LeanPool.Besicovitch
