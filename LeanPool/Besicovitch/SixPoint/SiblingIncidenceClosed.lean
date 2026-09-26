/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.RationalChord
public import LeanPool.Besicovitch.SixPoint.LensEndpointBalancedE0S0
public import LeanPool.Besicovitch.SixPoint.SiblingFailureTree
public import LeanPool.Besicovitch.SixPoint.SiblingLensE1S0
public import LeanPool.Besicovitch.SixPoint.SiblingLensS0S0
public import LeanPool.Besicovitch.SixPoint.SiblingLensS0S3

/-!
# The closed sibling-incidence ledger

The five lens separators, together with the direct outside-orbit exclusions, rule out every
simultaneous sibling failure except the two matched endpoint coincidences.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

private theorem endpointEndpoint_offMatching_excluded_aux
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) {redCode blueCode : Fin 4}
    (horbit : endpointEndpointOrbit redCode blueCode = .offMatchingCoincident) :
    ¬ (redSiblingTriangleFailure configuration (.endpoint redCode) ∧
      blueSiblingTriangleFailure configuration (.endpoint blueCode)) := by
  fin_cases redCode <;> fin_cases blueCode <;> simp [endpointEndpointOrbit] at horbit
  · exact not_redEndpoint_one_and_blueEndpoint_one h hmatching
  · intro failures
    apply not_redEndpoint_one_and_blueEndpoint_one (IsAdmissibleAt.swapChildren h)
      ((selectedDiagonalMatchingFails_swapChildren configuration).2 hmatching)
    exact ⟨(redEndpointFailure_swapChildren configuration 2).2 failures.1,
      (blueEndpointFailure_swapChildren configuration 2).2 failures.2⟩

private theorem endpointBalanced_e0s0_excluded_aux
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) {endpointCode balancedCode : Fin 4}
    (horbit : endpointBalancedOrbit endpointCode balancedCode = .e0s0) :
    ¬ (redSiblingTriangleFailure configuration (.endpoint endpointCode) ∧
      blueSiblingTriangleFailure configuration (.balanced balancedCode)) := by
  fin_cases endpointCode <;> fin_cases balancedCode <;> simp [endpointBalancedOrbit] at horbit
  · exact endpointBalancedE0S0_excluded_of_lensBound h hmatching
      (endpointBalancedE0S0LensBound_of_admissible h)
  · intro failures
    apply endpointBalancedE0S0_excluded_of_lensBound (IsAdmissibleAt.swapChildren h)
      ((selectedDiagonalMatchingFails_swapChildren configuration).2 hmatching)
      (endpointBalancedE0S0LensBound_of_admissible (IsAdmissibleAt.swapChildren h))
    exact ⟨(redEndpointFailure_swapChildren configuration 3).2 failures.1,
      (blueBalancedFailure_swapChildren configuration 3).2 failures.2⟩

private theorem endpointBalanced_e1s0_excluded_aux
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) {endpointCode balancedCode : Fin 4}
    (horbit : endpointBalancedOrbit endpointCode balancedCode = .e1s0) :
    ¬ (redSiblingTriangleFailure configuration (.endpoint endpointCode) ∧
      blueSiblingTriangleFailure configuration (.balanced balancedCode)) := by
  fin_cases endpointCode <;> fin_cases balancedCode <;> simp [endpointBalancedOrbit] at horbit
  · exact not_redEndpoint_one_and_blueBalanced_zero h hmatching
  · intro failures
    apply not_redEndpoint_one_and_blueBalanced_zero (IsAdmissibleAt.swapChildren h)
      ((selectedDiagonalMatchingFails_swapChildren configuration).2 hmatching)
    exact ⟨(redEndpointFailure_swapChildren configuration 2).2 failures.1,
      (blueBalancedFailure_swapChildren configuration 3).2 failures.2⟩

private theorem balancedEndpoint_e0s0_excluded_aux
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) {balancedCode endpointCode : Fin 4}
    (horbit : endpointBalancedOrbit (transposeEndpointCode endpointCode) balancedCode = .e0s0) :
    ¬ (redSiblingTriangleFailure configuration (.balanced balancedCode) ∧
      blueSiblingTriangleFailure configuration (.endpoint endpointCode)) := by
  intro failures
  apply endpointBalanced_e0s0_excluded_aux
    (configuration := transposeConfigurationColors configuration)
    (endpointCode := transposeEndpointCode endpointCode) (balancedCode := balancedCode)
    (IsAdmissibleAt.transposeColors h)
    ((selectedDiagonalMatchingFails_transposeColors configuration).2 hmatching) horbit
  exact ⟨(redEndpointFailure_transposeColors configuration endpointCode).2 failures.2,
    (blueBalancedFailure_transposeColors configuration balancedCode).2 failures.1⟩

private theorem balancedEndpoint_e1s0_excluded_aux
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) {balancedCode endpointCode : Fin 4}
    (horbit : endpointBalancedOrbit (transposeEndpointCode endpointCode) balancedCode = .e1s0) :
    ¬ (redSiblingTriangleFailure configuration (.balanced balancedCode) ∧
      blueSiblingTriangleFailure configuration (.endpoint endpointCode)) := by
  intro failures
  apply endpointBalanced_e1s0_excluded_aux
    (configuration := transposeConfigurationColors configuration)
    (endpointCode := transposeEndpointCode endpointCode) (balancedCode := balancedCode)
    (IsAdmissibleAt.transposeColors h)
    ((selectedDiagonalMatchingFails_transposeColors configuration).2 hmatching) horbit
  exact ⟨(redEndpointFailure_transposeColors configuration endpointCode).2 failures.2,
    (blueBalancedFailure_transposeColors configuration balancedCode).2 failures.1⟩

private theorem balancedBalanced_s0s0_excluded_aux
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) {redCode blueCode : Fin 4}
    (horbit : balancedBalancedOrbit redCode blueCode = .s0s0) :
    ¬ (redSiblingTriangleFailure configuration (.balanced redCode) ∧
      blueSiblingTriangleFailure configuration (.balanced blueCode)) := by
  fin_cases redCode <;> fin_cases blueCode <;> simp [balancedBalancedOrbit] at horbit
  · exact not_redBalanced_zero_and_blueBalanced_zero h hmatching
  · intro failures
    apply not_redBalanced_zero_and_blueBalanced_zero (IsAdmissibleAt.swapChildren h)
      ((selectedDiagonalMatchingFails_swapChildren configuration).2 hmatching)
    exact ⟨(redBalancedFailure_swapChildren configuration 3).2 failures.1,
      (blueBalancedFailure_swapChildren configuration 3).2 failures.2⟩

private theorem balancedBalanced_s0s3_excluded_aux
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) {redCode blueCode : Fin 4}
    (horbit : balancedBalancedOrbit redCode blueCode = .s0s3) :
    ¬ (redSiblingTriangleFailure configuration (.balanced redCode) ∧
      blueSiblingTriangleFailure configuration (.balanced blueCode)) := by
  fin_cases redCode <;> fin_cases blueCode <;> simp [balancedBalancedOrbit] at horbit
  · exact not_redBalanced_zero_and_blueBalanced_three h hmatching
  · intro failures
    apply not_redBalanced_zero_and_blueBalanced_three (IsAdmissibleAt.swapChildren h)
      ((selectedDiagonalMatchingFails_swapChildren configuration).2 hmatching)
    exact ⟨(redBalancedFailure_swapChildren configuration 3).2 failures.1,
      (blueBalancedFailure_swapChildren configuration 0).2 failures.2⟩

/-- Every non-matched sibling-incidence cell is excluded at the exact endpoint. -/
theorem siblingIncidenceExclusions_of_admissible
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) :
    SiblingIncidenceExclusions (redSiblingTriangleFailure configuration)
      (blueSiblingTriangleFailure configuration) where
  endpointEndpoint redCode blueCode hnotMatched := by
    by_cases horbit : endpointEndpointOrbit redCode blueCode = .offMatchingCoincident
    · exact endpointEndpoint_offMatching_excluded_aux h hmatching horbit
    · exact endpointEndpoint_excluded_outside_lens h hmatching redCode blueCode
        hnotMatched horbit
  endpointBalanced endpointCode balancedCode := by
    by_cases hzero : endpointBalancedOrbit endpointCode balancedCode = .e0s0
    · exact endpointBalanced_e0s0_excluded_aux h hmatching hzero
    · by_cases hone : endpointBalancedOrbit endpointCode balancedCode = .e1s0
      · exact endpointBalanced_e1s0_excluded_aux h hmatching hone
      · exact endpointBalanced_excluded_outside_lenses h hmatching endpointCode balancedCode
          hzero hone
  balancedEndpoint balancedCode endpointCode := by
    by_cases hzero :
        endpointBalancedOrbit (transposeEndpointCode endpointCode) balancedCode = .e0s0
    · exact balancedEndpoint_e0s0_excluded_aux h hmatching hzero
    · by_cases hone :
          endpointBalancedOrbit (transposeEndpointCode endpointCode) balancedCode = .e1s0
      · exact balancedEndpoint_e1s0_excluded_aux h hmatching hone
      · exact balancedEndpoint_excluded_outside_lenses h hmatching balancedCode endpointCode
          hzero hone
  balancedBalanced redCode blueCode := by
    by_cases hzero : balancedBalancedOrbit redCode blueCode = .s0s0
    · exact balancedBalanced_s0s0_excluded_aux h hmatching hzero
    · by_cases hthree : balancedBalancedOrbit redCode blueCode = .s0s3
      · exact balancedBalanced_s0s3_excluded_aux h hmatching hthree
      · exact balancedBalanced_excluded_outside_lenses h hmatching redCode blueCode
          hzero hthree

private theorem siblingIncidenceOutcome_failures_aux {configuration : SixPointConfiguration}
    (houtcome : SiblingIncidenceOutcome configuration) :
    (∃ witness, redSiblingTriangleFailure configuration witness) ∧
      ∃ witness, blueSiblingTriangleFailure configuration witness := by
  rcases houtcome with hmatched | hoffMatching | hendpointBalanced | hbalancedEndpoint |
    hbalancedBalanced
  · rcases hmatched with ⟨code, _, hred, hblue⟩
    exact ⟨⟨.endpoint code, hred⟩, ⟨.endpoint code, hblue⟩⟩
  · rcases hoffMatching with ⟨redCode, blueCode, _, hred, hblue⟩
    exact ⟨⟨.endpoint redCode, hred⟩, ⟨.endpoint blueCode, hblue⟩⟩
  · rcases hendpointBalanced with ⟨endpointCode, balancedCode, _, hred, hblue⟩
    exact ⟨⟨.endpoint endpointCode, hred⟩, ⟨.balanced balancedCode, hblue⟩⟩
  · rcases hbalancedEndpoint with ⟨balancedCode, endpointCode, _, hred, hblue⟩
    exact ⟨⟨.balanced balancedCode, hred⟩, ⟨.endpoint endpointCode, hblue⟩⟩
  · rcases hbalancedBalanced with ⟨redCode, blueCode, _, hred, hblue⟩
    exact ⟨⟨.balanced redCode, hred⟩, ⟨.balanced blueCode, hblue⟩⟩

/-- The sibling supports either give a nonnegative packing or fail at one matched endpoint. -/
theorem exists_nonnegative_score_or_matched_sibling_endpoint
    (configuration : SixPointConfiguration) (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) :
    (∃ packing : SixPointPacking configuration, 0 ≤ packing.score barS) ∨
      ∃ code : Fin 4, (code = 0 ∨ code = 3) ∧
        redSiblingTriangleFailure configuration (.endpoint code) ∧
        blueSiblingTriangleFailure configuration (.endpoint code) := by
  rcases exists_nonnegative_score_or_siblingIncidenceOutcome configuration h hmatching with
    hpacking | houtcome
  · exact Or.inl hpacking
  · rcases siblingIncidenceOutcome_failures_aux houtcome with ⟨hred, hblue⟩
    exact Or.inr <| exists_matched_endpoint_of_siblingIncidenceExclusions
      (siblingIncidenceExclusions_of_admissible h hmatching) hred hblue

end LeanPool.Besicovitch
