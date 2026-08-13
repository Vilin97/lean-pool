/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/

import LeanPool.FrontierMathOpenHypergraphs.Uniform.FrameDefs

/-!
# Booster-frame validations
-/

namespace HypergraphLowerBound

-- Stable names let the exposition replay reject these already-loaded certificates before
-- recomputing their expensive Boolean validations. Lean and doc-gen treat the `proof_n`
-- declarations as implementation details, so only the final certificates enter the public API.
namespace BoosterValidation
/-- Validation certificate booster_0_valid. -/
theorem booster_0_valid :
    (boosters.get ⟨0, by decide⟩).IsValid := by
  exact (boosters.get ⟨0, by decide⟩).rawCheckValid_sound rfl

private def booster1Spec : FrameSpec :=
  boosters.get ⟨1, by decide⟩

/-- Validation certificate proof_1_0. -/
theorem proof_1_0 :
    checkMasksDown booster1Spec 7 0 0 = true := rfl

/-- Validation certificate proof_1_1. -/
theorem proof_1_1 :
    checkMasksDown booster1Spec 7 (((1 : Nat) <<< 7)) 0 = true := rfl

/-- Validation certificate proof_1_2. -/
theorem proof_1_2 :
    checkMasksDown booster1Spec 7 (((1 : Nat) <<< 7)) (((1 : Nat) <<< 7)) = true := rfl

/-- Validation certificate proof_1_9. -/
theorem proof_1_9 :
    booster1Spec.rawCheckValid = true := by
  unfold FrameSpec.rawCheckValid
  change checkMasksDown booster1Spec 8 0 0 = true
  exact
    checkMasksDown_step_true booster1Spec 7 0 0
      proof_1_0 proof_1_1 proof_1_2

/-- Validation certificate booster_1_valid. -/
theorem booster_1_valid :
    (boosters.get ⟨1, by decide⟩).IsValid := by
  simpa [booster1Spec] using
    booster1Spec.rawCheckValid_sound proof_1_9

/-- Validation certificate booster_2_valid. -/
theorem booster_2_valid :
    (boosters.get ⟨2, by decide⟩).IsValid := by
  exact (boosters.get ⟨2, by decide⟩).rawCheckValid_sound rfl

/-- Validation certificate booster_3_valid. -/
theorem booster_3_valid :
    (boosters.get ⟨3, by decide⟩).IsValid := by
  exact (boosters.get ⟨3, by decide⟩).rawCheckValid_sound rfl

private def booster4Spec : FrameSpec :=
  boosters.get ⟨4, by decide⟩

/-- Validation certificate proof_4_00. -/
theorem proof_4_00 :
    checkMasksDown booster4Spec 6 0 0 = true := rfl

/-- Validation certificate proof_4_01. -/
theorem proof_4_01 :
    checkMasksDown booster4Spec 6 (((1 : Nat) <<< 6)) 0 = true := rfl

/-- Validation certificate proof_4_02. -/
theorem proof_4_02 :
    checkMasksDown booster4Spec 6 (((1 : Nat) <<< 6)) (((1 : Nat) <<< 6)) = true := rfl

/-- Validation certificate proof_4_0. -/
theorem proof_4_0 :
    checkMasksDown booster4Spec 7 0 0 = true := by
  exact checkMasksDown_step_true booster4Spec 6 0 0
    proof_4_00 proof_4_01 proof_4_02

/-- Validation certificate proof_4_10. -/
theorem proof_4_10 :
    checkMasksDown booster4Spec 6 (((1 : Nat) <<< 7)) 0 = true := rfl

/-- Validation certificate proof_4_11. -/
theorem proof_4_11 :
    checkMasksDown booster4Spec 6 ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6))) 0 = true := rfl

/-- Validation certificate proof_4_12. -/
theorem proof_4_12 :
    checkMasksDown booster4Spec 6 ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      (((1 : Nat) <<< 6)) = true := rfl

/-- Validation certificate proof_4_1. -/
theorem proof_4_1 :
    checkMasksDown booster4Spec 7 (((1 : Nat) <<< 7)) 0 = true := by
  exact checkMasksDown_step_true booster4Spec 6 (((1 : Nat) <<< 7)) 0
    proof_4_10 proof_4_11 proof_4_12

/-- Validation certificate proof_4_20. -/
theorem proof_4_20 :
    checkMasksDown booster4Spec 6 (((1 : Nat) <<< 7)) (((1 : Nat) <<< 7)) = true := rfl

/-- Validation certificate proof_4_21. -/
theorem proof_4_21 :
    checkMasksDown booster4Spec 6 ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      (((1 : Nat) <<< 7)) = true := rfl

/-- Validation certificate proof_4_22. -/
theorem proof_4_22 :
    checkMasksDown booster4Spec 6 ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6))) = true := rfl

/-- Validation certificate proof_4_2. -/
theorem proof_4_2 :
    checkMasksDown booster4Spec 7 (((1 : Nat) <<< 7)) (((1 : Nat) <<< 7)) = true := by
  exact checkMasksDown_step_true booster4Spec 6 (((1 : Nat) <<< 7)) (((1 : Nat) <<< 7))
    proof_4_20 proof_4_21 proof_4_22

/-- Validation certificate proof_4_9. -/
theorem proof_4_9 :
    booster4Spec.rawCheckValid = true := by
  unfold FrameSpec.rawCheckValid
  change checkMasksDown booster4Spec 8 0 0 = true
  exact
    checkMasksDown_step_true booster4Spec 7 0 0
      proof_4_0 proof_4_1 proof_4_2

/-- Validation certificate booster_4_valid. -/
theorem booster_4_valid :
    (boosters.get ⟨4, by decide⟩).IsValid := by
  simpa [booster4Spec] using
    booster4Spec.rawCheckValid_sound proof_4_9

private def booster5Spec : FrameSpec :=
  boosters.get ⟨5, by decide⟩

/-- Validation certificate proof_5_00. -/
theorem proof_5_00 :
    checkMasksDown booster5Spec 6 0 0 = true := rfl

/-- Validation certificate proof_5_01. -/
theorem proof_5_01 :
    checkMasksDown booster5Spec 6 (((1 : Nat) <<< 6)) 0 = true := rfl

/-- Validation certificate proof_5_02. -/
theorem proof_5_02 :
    checkMasksDown booster5Spec 6 (((1 : Nat) <<< 6)) (((1 : Nat) <<< 6)) = true := rfl

/-- Validation certificate proof_5_0. -/
theorem proof_5_0 :
    checkMasksDown booster5Spec 7 0 0 = true := by
  exact checkMasksDown_step_true booster5Spec 6 0 0
    proof_5_00 proof_5_01 proof_5_02

/-- Validation certificate proof_5_10. -/
theorem proof_5_10 :
    checkMasksDown booster5Spec 6 (((1 : Nat) <<< 7)) 0 = true := rfl

/-- Validation certificate proof_5_11. -/
theorem proof_5_11 :
    checkMasksDown booster5Spec 6 ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6))) 0 = true := rfl

/-- Validation certificate proof_5_12. -/
theorem proof_5_12 :
    checkMasksDown booster5Spec 6 ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      (((1 : Nat) <<< 6)) = true := rfl

/-- Validation certificate proof_5_1. -/
theorem proof_5_1 :
    checkMasksDown booster5Spec 7 (((1 : Nat) <<< 7)) 0 = true := by
  exact checkMasksDown_step_true booster5Spec 6 (((1 : Nat) <<< 7)) 0
    proof_5_10 proof_5_11 proof_5_12

/-- Validation certificate proof_5_20. -/
theorem proof_5_20 :
    checkMasksDown booster5Spec 6 (((1 : Nat) <<< 7)) (((1 : Nat) <<< 7)) = true := rfl

/-- Validation certificate proof_5_21. -/
theorem proof_5_21 :
    checkMasksDown booster5Spec 6 ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      (((1 : Nat) <<< 7)) = true := rfl

/-- Validation certificate proof_5_22. -/
theorem proof_5_22 :
    checkMasksDown booster5Spec 6 ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6))) = true := rfl

/-- Validation certificate proof_5_2. -/
theorem proof_5_2 :
    checkMasksDown booster5Spec 7 (((1 : Nat) <<< 7)) (((1 : Nat) <<< 7)) = true := by
  exact checkMasksDown_step_true booster5Spec 6 (((1 : Nat) <<< 7)) (((1 : Nat) <<< 7))
    proof_5_20 proof_5_21 proof_5_22

/-- Validation certificate proof_5_9. -/
theorem proof_5_9 :
    booster5Spec.rawCheckValid = true := by
  unfold FrameSpec.rawCheckValid
  change checkMasksDown booster5Spec 8 0 0 = true
  exact
    checkMasksDown_step_true booster5Spec 7 0 0
      proof_5_0 proof_5_1 proof_5_2

/-- Validation certificate booster_5_valid. -/
theorem booster_5_valid :
    (boosters.get ⟨5, by decide⟩).IsValid := by
  simpa [booster5Spec] using
    booster5Spec.rawCheckValid_sound proof_5_9

private def booster6Spec : FrameSpec :=
  boosters.get ⟨6, by decide⟩

/-- Validation certificate proof_6_000. -/
theorem proof_6_000 :
    checkMasksDown booster6Spec 6 0 0 = true := rfl

/-- Validation certificate proof_6_001. -/
theorem proof_6_001 :
    checkMasksDown booster6Spec 6 (((1 : Nat) <<< 6)) 0 = true := rfl

/-- Validation certificate proof_6_002. -/
theorem proof_6_002 :
    checkMasksDown booster6Spec 6 (((1 : Nat) <<< 6)) (((1 : Nat) <<< 6)) = true := rfl

/-- Validation certificate proof_6_00. -/
theorem proof_6_00 :
    checkMasksDown booster6Spec 7 0 0 = true := by
  exact checkMasksDown_step_true booster6Spec 6 0 0
    proof_6_000 proof_6_001 proof_6_002

/-- Validation certificate proof_6_010. -/
theorem proof_6_010 :
    checkMasksDown booster6Spec 6 (((1 : Nat) <<< 7)) 0 = true := rfl

/-- Validation certificate proof_6_011. -/
theorem proof_6_011 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6))) 0 = true := rfl

/-- Validation certificate proof_6_012. -/
theorem proof_6_012 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      (((1 : Nat) <<< 6)) = true := rfl

/-- Validation certificate proof_6_01. -/
theorem proof_6_01 :
    checkMasksDown booster6Spec 7 (((1 : Nat) <<< 7)) 0 = true := by
  exact checkMasksDown_step_true booster6Spec 6 (((1 : Nat) <<< 7)) 0
    proof_6_010 proof_6_011 proof_6_012

/-- Validation certificate proof_6_020. -/
theorem proof_6_020 :
    checkMasksDown booster6Spec 6 (((1 : Nat) <<< 7)) (((1 : Nat) <<< 7)) = true := rfl

/-- Validation certificate proof_6_021. -/
theorem proof_6_021 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      (((1 : Nat) <<< 7)) = true := rfl

/-- Validation certificate proof_6_022. -/
theorem proof_6_022 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6))) = true := rfl

/-- Validation certificate proof_6_02. -/
theorem proof_6_02 :
    checkMasksDown booster6Spec 7 (((1 : Nat) <<< 7)) (((1 : Nat) <<< 7)) = true := by
  exact checkMasksDown_step_true booster6Spec 6 (((1 : Nat) <<< 7)) (((1 : Nat) <<< 7))
    proof_6_020 proof_6_021 proof_6_022

/-- Validation certificate proof_6_100. -/
theorem proof_6_100 :
    checkMasksDown booster6Spec 6 (((1 : Nat) <<< 8)) 0 = true := rfl

/-- Validation certificate proof_6_101. -/
theorem proof_6_101 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 6))) 0 = true := rfl

/-- Validation certificate proof_6_102. -/
theorem proof_6_102 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 6)))
      (((1 : Nat) <<< 6)) = true := rfl

/-- Validation certificate proof_6_10. -/
theorem proof_6_10 :
    checkMasksDown booster6Spec 7 (((1 : Nat) <<< 8)) 0 = true := by
  exact checkMasksDown_step_true booster6Spec 6 (((1 : Nat) <<< 8)) 0
    proof_6_100 proof_6_101 proof_6_102

/-- Validation certificate proof_6_110. -/
theorem proof_6_110 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7))) 0 = true := rfl

/-- Validation certificate proof_6_111. -/
theorem proof_6_111 :
    checkMasksDown booster6Spec 6
      ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6))) 0 =
        true := rfl

/-- Validation certificate proof_6_112. -/
theorem proof_6_112 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      (((1 : Nat) <<< 6)) = true := rfl

/-- Validation certificate proof_6_11. -/
theorem proof_6_11 :
    checkMasksDown booster6Spec 7 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7))) 0 = true := by
  exact checkMasksDown_step_true booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7))) 0
    proof_6_110 proof_6_111 proof_6_112

/-- Validation certificate proof_6_120. -/
theorem proof_6_120 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7)))
      (((1 : Nat) <<< 7)) = true := rfl

/-- Validation certificate proof_6_121. -/
theorem proof_6_121 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      (((1 : Nat) <<< 7)) = true := rfl

/-- Validation certificate proof_6_122. -/
theorem proof_6_122 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6))) = true := rfl

/-- Validation certificate proof_6_12. -/
theorem proof_6_12 :
    checkMasksDown booster6Spec 7 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7)))
      (((1 : Nat) <<< 7)) = true := by
  exact checkMasksDown_step_true booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7)))
    (((1 : Nat) <<< 7)) proof_6_120 proof_6_121 proof_6_122

/-- Validation certificate proof_6_200. -/
theorem proof_6_200 :
    checkMasksDown booster6Spec 6 (((1 : Nat) <<< 8)) (((1 : Nat) <<< 8)) = true := rfl

/-- Validation certificate proof_6_201. -/
theorem proof_6_201 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 6)))
      (((1 : Nat) <<< 8)) = true := rfl

/-- Validation certificate proof_6_202. -/
theorem proof_6_202 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 6)))
      ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 6))) = true := rfl

/-- Validation certificate proof_6_20. -/
theorem proof_6_20 :
    checkMasksDown booster6Spec 7 (((1 : Nat) <<< 8)) (((1 : Nat) <<< 8)) = true := by
  exact checkMasksDown_step_true booster6Spec 6 (((1 : Nat) <<< 8)) (((1 : Nat) <<< 8))
    proof_6_200 proof_6_201 proof_6_202

/-- Validation certificate proof_6_210. -/
theorem proof_6_210 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7)))
      (((1 : Nat) <<< 8)) = true := rfl

/-- Validation certificate proof_6_211. -/
theorem proof_6_211 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      (((1 : Nat) <<< 8)) = true := rfl

/-- Validation certificate proof_6_212. -/
theorem proof_6_212 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 6))) = true := rfl

/-- Validation certificate proof_6_21. -/
theorem proof_6_21 :
    checkMasksDown booster6Spec 7 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7)))
      (((1 : Nat) <<< 8)) = true := by
  exact checkMasksDown_step_true booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7)))
    (((1 : Nat) <<< 8)) proof_6_210 proof_6_211 proof_6_212

/-- Validation certificate proof_6_220. -/
theorem proof_6_220 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7)))
      ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7))) = true := rfl

/-- Validation certificate proof_6_221. -/
theorem proof_6_221 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7))) = true := rfl

/-- Validation certificate proof_6_222. -/
theorem proof_6_222 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6))) = true := rfl

/-- Validation certificate proof_6_22. -/
theorem proof_6_22 :
    checkMasksDown booster6Spec 7 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7)))
      ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7))) = true := by
  exact checkMasksDown_step_true booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7)))
    ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7))) proof_6_220
    proof_6_221 proof_6_222

/-- Validation certificate proof_6_0. -/
theorem proof_6_0 :
    checkMasksDown booster6Spec 8 0 0 = true := by
  exact checkMasksDown_step_true booster6Spec 7 0 0
    proof_6_00 proof_6_01 proof_6_02

/-- Validation certificate proof_6_1. -/
theorem proof_6_1 :
    checkMasksDown booster6Spec 8 (((1 : Nat) <<< 8)) 0 = true := by
  exact checkMasksDown_step_true booster6Spec 7 (((1 : Nat) <<< 8)) 0
    proof_6_10 proof_6_11 proof_6_12

/-- Validation certificate proof_6_2. -/
theorem proof_6_2 :
    checkMasksDown booster6Spec 8 (((1 : Nat) <<< 8)) (((1 : Nat) <<< 8)) = true := by
  exact checkMasksDown_step_true booster6Spec 7 (((1 : Nat) <<< 8)) (((1 : Nat) <<< 8))
    proof_6_20 proof_6_21 proof_6_22

/-- Validation certificate proof_6_9. -/
theorem proof_6_9 :
    booster6Spec.rawCheckValid = true := by
  unfold FrameSpec.rawCheckValid
  change checkMasksDown booster6Spec 9 0 0 = true
  exact
    checkMasksDown_step_true booster6Spec 8 0 0
      proof_6_0 proof_6_1 proof_6_2

/-- Validation certificate booster_6_valid. -/
theorem booster_6_valid :
    (boosters.get ⟨6, by decide⟩).IsValid := by
  simpa [booster6Spec] using
    booster6Spec.rawCheckValid_sound proof_6_9


end BoosterValidation

theorem boosters_valid :
    ∀ spec ∈ boosters, spec.IsValid := by
  intro spec hs
  obtain ⟨i, rfl⟩ := List.get_of_mem hs
  fin_cases i
  · exact BoosterValidation.booster_0_valid
  · exact BoosterValidation.booster_1_valid
  · exact BoosterValidation.booster_2_valid
  · exact BoosterValidation.booster_3_valid
  · exact BoosterValidation.booster_4_valid
  · exact BoosterValidation.booster_5_valid
  · exact BoosterValidation.booster_6_valid

end HypergraphLowerBound
