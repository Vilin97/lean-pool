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

private theorem booster_0_valid :
    (boosters.get ⟨0, by decide⟩).IsValid := by
  exact (boosters.get ⟨0, by decide⟩).checkComplementValid_sound rfl

private theorem booster_1_valid :
    (boosters.get ⟨1, by decide⟩).IsValid := by
  exact (boosters.get ⟨1, by decide⟩).checkComplementValid_sound rfl

private theorem booster_2_valid :
    (boosters.get ⟨2, by decide⟩).IsValid := by
  exact (boosters.get ⟨2, by decide⟩).checkComplementValid_sound rfl

private theorem booster_3_valid :
    (boosters.get ⟨3, by decide⟩).IsValid := by
  exact (boosters.get ⟨3, by decide⟩).checkComplementValid_sound rfl

private def booster4Spec : FrameSpec :=
  boosters.get ⟨4, by decide⟩

private theorem booster_4_check_0 :
    checkComplementMasksDown booster4Spec 7 0 = true := rfl

private theorem booster_4_check_1 :
    checkComplementMasksDown booster4Spec 7 ((1 : Nat) <<< 7) = true := rfl

private theorem booster_4_checkComplementValid :
    booster4Spec.checkComplementValid = true := by
  unfold FrameSpec.checkComplementValid
  change checkComplementMasksDown booster4Spec 8 0 = true
  exact checkComplementMasksDown_step_true booster4Spec 7 0
    booster_4_check_0 booster_4_check_1

private theorem booster_4_valid :
    (boosters.get ⟨4, by decide⟩).IsValid := by
  simpa [booster4Spec] using
    booster4Spec.checkComplementValid_sound booster_4_checkComplementValid

private def booster5Spec : FrameSpec :=
  boosters.get ⟨5, by decide⟩

private theorem booster_5_check_0 :
    checkComplementMasksDown booster5Spec 7 0 = true := rfl

private theorem booster_5_check_1 :
    checkComplementMasksDown booster5Spec 7 ((1 : Nat) <<< 7) = true := rfl

private theorem booster_5_checkComplementValid :
    booster5Spec.checkComplementValid = true := by
  unfold FrameSpec.checkComplementValid
  change checkComplementMasksDown booster5Spec 8 0 = true
  exact checkComplementMasksDown_step_true booster5Spec 7 0
    booster_5_check_0 booster_5_check_1

private theorem booster_5_valid :
    (boosters.get ⟨5, by decide⟩).IsValid := by
  simpa [booster5Spec] using
    booster5Spec.checkComplementValid_sound booster_5_checkComplementValid

private def booster6Spec : FrameSpec :=
  boosters.get ⟨6, by decide⟩

private theorem booster_6_check_00 :
    checkComplementMasksDown booster6Spec 7 0 = true := rfl

private theorem booster_6_check_01 :
    checkComplementMasksDown booster6Spec 7 ((1 : Nat) <<< 7) = true := rfl

private theorem booster_6_check_0 :
    checkComplementMasksDown booster6Spec 8 0 = true := by
  exact checkComplementMasksDown_step_true booster6Spec 7 0
    booster_6_check_00 booster_6_check_01

private theorem booster_6_check_10 :
    checkComplementMasksDown booster6Spec 7 ((1 : Nat) <<< 8) = true := rfl

private theorem booster_6_check_11 :
    checkComplementMasksDown booster6Spec 7
      (((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7)) = true := rfl

private theorem booster_6_check_1 :
    checkComplementMasksDown booster6Spec 8 ((1 : Nat) <<< 8) = true := by
  exact checkComplementMasksDown_step_true booster6Spec 7 ((1 : Nat) <<< 8)
    booster_6_check_10 booster_6_check_11

private theorem booster_6_checkComplementValid :
    booster6Spec.checkComplementValid = true := by
  unfold FrameSpec.checkComplementValid
  change checkComplementMasksDown booster6Spec 9 0 = true
  exact checkComplementMasksDown_step_true booster6Spec 8 0
    booster_6_check_0 booster_6_check_1

private theorem booster_6_valid :
    (boosters.get ⟨6, by decide⟩).IsValid := by
  simpa [booster6Spec] using
    booster6Spec.checkComplementValid_sound booster_6_checkComplementValid

theorem boosters_valid :
    ∀ spec ∈ boosters, spec.IsValid := by
  intro spec hs
  obtain ⟨i, rfl⟩ := List.get_of_mem hs
  fin_cases i
  · exact booster_0_valid
  · exact booster_1_valid
  · exact booster_2_valid
  · exact booster_3_valid
  · exact booster_4_valid
  · exact booster_5_valid
  · exact booster_6_valid

end HypergraphLowerBound
