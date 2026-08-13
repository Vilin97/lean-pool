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
  exact (boosters.get ⟨0, by decide⟩).rawCheckValid_sound rfl

private def booster1Spec : FrameSpec :=
  boosters.get ⟨1, by decide⟩

private theorem booster_1_check_0 :
    checkMasksDown booster1Spec 7 0 0 = true := rfl

private theorem booster_1_check_1 :
    checkMasksDown booster1Spec 7 (((1 : Nat) <<< 7)) 0 = true := rfl

private theorem booster_1_check_2 :
    checkMasksDown booster1Spec 7 (((1 : Nat) <<< 7)) (((1 : Nat) <<< 7)) = true := rfl

private theorem booster_1_rawCheckValid :
    booster1Spec.rawCheckValid = true := by
  unfold FrameSpec.rawCheckValid
  change checkMasksDown booster1Spec 8 0 0 = true
  exact
    checkMasksDown_step_true booster1Spec 7 0 0
      booster_1_check_0 booster_1_check_1 booster_1_check_2

private theorem booster_1_valid :
    (boosters.get ⟨1, by decide⟩).IsValid := by
  simpa [booster1Spec] using booster1Spec.rawCheckValid_sound booster_1_rawCheckValid

private theorem booster_2_valid :
    (boosters.get ⟨2, by decide⟩).IsValid := by
  exact (boosters.get ⟨2, by decide⟩).rawCheckValid_sound rfl

private theorem booster_3_valid :
    (boosters.get ⟨3, by decide⟩).IsValid := by
  exact (boosters.get ⟨3, by decide⟩).rawCheckValid_sound rfl

private def booster4Spec : FrameSpec :=
  boosters.get ⟨4, by decide⟩

private theorem booster_4_check_00 :
    checkMasksDown booster4Spec 6 0 0 = true := rfl

private theorem booster_4_check_01 :
    checkMasksDown booster4Spec 6 (((1 : Nat) <<< 6)) 0 = true := rfl

private theorem booster_4_check_02 :
    checkMasksDown booster4Spec 6 (((1 : Nat) <<< 6)) (((1 : Nat) <<< 6)) = true := rfl

private theorem booster_4_check_0 :
    checkMasksDown booster4Spec 7 0 0 = true := by
  exact checkMasksDown_step_true booster4Spec 6 0 0
    booster_4_check_00 booster_4_check_01 booster_4_check_02

private theorem booster_4_check_10 :
    checkMasksDown booster4Spec 6 (((1 : Nat) <<< 7)) 0 = true := rfl

private theorem booster_4_check_11 :
    checkMasksDown booster4Spec 6 ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6))) 0 = true := rfl

private theorem booster_4_check_12 :
    checkMasksDown booster4Spec 6 ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      (((1 : Nat) <<< 6)) = true := rfl

private theorem booster_4_check_1 :
    checkMasksDown booster4Spec 7 (((1 : Nat) <<< 7)) 0 = true := by
  exact checkMasksDown_step_true booster4Spec 6 (((1 : Nat) <<< 7)) 0
    booster_4_check_10 booster_4_check_11 booster_4_check_12

private theorem booster_4_check_20 :
    checkMasksDown booster4Spec 6 (((1 : Nat) <<< 7)) (((1 : Nat) <<< 7)) = true := rfl

private theorem booster_4_check_21 :
    checkMasksDown booster4Spec 6 ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      (((1 : Nat) <<< 7)) = true := rfl

private theorem booster_4_check_22 :
    checkMasksDown booster4Spec 6 ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6))) = true := rfl

private theorem booster_4_check_2 :
    checkMasksDown booster4Spec 7 (((1 : Nat) <<< 7)) (((1 : Nat) <<< 7)) = true := by
  exact checkMasksDown_step_true booster4Spec 6 (((1 : Nat) <<< 7)) (((1 : Nat) <<< 7))
    booster_4_check_20 booster_4_check_21 booster_4_check_22

private theorem booster_4_rawCheckValid :
    booster4Spec.rawCheckValid = true := by
  unfold FrameSpec.rawCheckValid
  change checkMasksDown booster4Spec 8 0 0 = true
  exact
    checkMasksDown_step_true booster4Spec 7 0 0
      booster_4_check_0 booster_4_check_1 booster_4_check_2

private theorem booster_4_valid :
    (boosters.get ⟨4, by decide⟩).IsValid := by
  simpa [booster4Spec] using booster4Spec.rawCheckValid_sound booster_4_rawCheckValid

private def booster5Spec : FrameSpec :=
  boosters.get ⟨5, by decide⟩

private theorem booster_5_check_00 :
    checkMasksDown booster5Spec 6 0 0 = true := rfl

private theorem booster_5_check_01 :
    checkMasksDown booster5Spec 6 (((1 : Nat) <<< 6)) 0 = true := rfl

private theorem booster_5_check_02 :
    checkMasksDown booster5Spec 6 (((1 : Nat) <<< 6)) (((1 : Nat) <<< 6)) = true := rfl

private theorem booster_5_check_0 :
    checkMasksDown booster5Spec 7 0 0 = true := by
  exact checkMasksDown_step_true booster5Spec 6 0 0
    booster_5_check_00 booster_5_check_01 booster_5_check_02

private theorem booster_5_check_10 :
    checkMasksDown booster5Spec 6 (((1 : Nat) <<< 7)) 0 = true := rfl

private theorem booster_5_check_11 :
    checkMasksDown booster5Spec 6 ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6))) 0 = true := rfl

private theorem booster_5_check_12 :
    checkMasksDown booster5Spec 6 ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      (((1 : Nat) <<< 6)) = true := rfl

private theorem booster_5_check_1 :
    checkMasksDown booster5Spec 7 (((1 : Nat) <<< 7)) 0 = true := by
  exact checkMasksDown_step_true booster5Spec 6 (((1 : Nat) <<< 7)) 0
    booster_5_check_10 booster_5_check_11 booster_5_check_12

private theorem booster_5_check_20 :
    checkMasksDown booster5Spec 6 (((1 : Nat) <<< 7)) (((1 : Nat) <<< 7)) = true := rfl

private theorem booster_5_check_21 :
    checkMasksDown booster5Spec 6 ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      (((1 : Nat) <<< 7)) = true := rfl

private theorem booster_5_check_22 :
    checkMasksDown booster5Spec 6 ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6))) = true := rfl

private theorem booster_5_check_2 :
    checkMasksDown booster5Spec 7 (((1 : Nat) <<< 7)) (((1 : Nat) <<< 7)) = true := by
  exact checkMasksDown_step_true booster5Spec 6 (((1 : Nat) <<< 7)) (((1 : Nat) <<< 7))
    booster_5_check_20 booster_5_check_21 booster_5_check_22

private theorem booster_5_rawCheckValid :
    booster5Spec.rawCheckValid = true := by
  unfold FrameSpec.rawCheckValid
  change checkMasksDown booster5Spec 8 0 0 = true
  exact
    checkMasksDown_step_true booster5Spec 7 0 0
      booster_5_check_0 booster_5_check_1 booster_5_check_2

private theorem booster_5_valid :
    (boosters.get ⟨5, by decide⟩).IsValid := by
  simpa [booster5Spec] using booster5Spec.rawCheckValid_sound booster_5_rawCheckValid

private def booster6Spec : FrameSpec :=
  boosters.get ⟨6, by decide⟩

private theorem booster_6_check_000 :
    checkMasksDown booster6Spec 6 0 0 = true := rfl

private theorem booster_6_check_001 :
    checkMasksDown booster6Spec 6 (((1 : Nat) <<< 6)) 0 = true := rfl

private theorem booster_6_check_002 :
    checkMasksDown booster6Spec 6 (((1 : Nat) <<< 6)) (((1 : Nat) <<< 6)) = true := rfl

private theorem booster_6_check_00 :
    checkMasksDown booster6Spec 7 0 0 = true := by
  exact checkMasksDown_step_true booster6Spec 6 0 0
    booster_6_check_000 booster_6_check_001 booster_6_check_002

private theorem booster_6_check_010 :
    checkMasksDown booster6Spec 6 (((1 : Nat) <<< 7)) 0 = true := rfl

private theorem booster_6_check_011 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6))) 0 = true := rfl

private theorem booster_6_check_012 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      (((1 : Nat) <<< 6)) = true := rfl

private theorem booster_6_check_01 :
    checkMasksDown booster6Spec 7 (((1 : Nat) <<< 7)) 0 = true := by
  exact checkMasksDown_step_true booster6Spec 6 (((1 : Nat) <<< 7)) 0
    booster_6_check_010 booster_6_check_011 booster_6_check_012

private theorem booster_6_check_020 :
    checkMasksDown booster6Spec 6 (((1 : Nat) <<< 7)) (((1 : Nat) <<< 7)) = true := rfl

private theorem booster_6_check_021 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      (((1 : Nat) <<< 7)) = true := rfl

private theorem booster_6_check_022 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6))) = true := rfl

private theorem booster_6_check_02 :
    checkMasksDown booster6Spec 7 (((1 : Nat) <<< 7)) (((1 : Nat) <<< 7)) = true := by
  exact checkMasksDown_step_true booster6Spec 6 (((1 : Nat) <<< 7)) (((1 : Nat) <<< 7))
    booster_6_check_020 booster_6_check_021 booster_6_check_022

private theorem booster_6_check_100 :
    checkMasksDown booster6Spec 6 (((1 : Nat) <<< 8)) 0 = true := rfl

private theorem booster_6_check_101 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 6))) 0 = true := rfl

private theorem booster_6_check_102 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 6)))
      (((1 : Nat) <<< 6)) = true := rfl

private theorem booster_6_check_10 :
    checkMasksDown booster6Spec 7 (((1 : Nat) <<< 8)) 0 = true := by
  exact checkMasksDown_step_true booster6Spec 6 (((1 : Nat) <<< 8)) 0
    booster_6_check_100 booster_6_check_101 booster_6_check_102

private theorem booster_6_check_110 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7))) 0 = true := rfl

private theorem booster_6_check_111 :
    checkMasksDown booster6Spec 6
      ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6))) 0 =
        true := rfl

private theorem booster_6_check_112 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      (((1 : Nat) <<< 6)) = true := rfl

private theorem booster_6_check_11 :
    checkMasksDown booster6Spec 7 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7))) 0 = true := by
  exact checkMasksDown_step_true booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7))) 0
    booster_6_check_110 booster_6_check_111 booster_6_check_112

private theorem booster_6_check_120 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7)))
      (((1 : Nat) <<< 7)) = true := rfl

private theorem booster_6_check_121 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      (((1 : Nat) <<< 7)) = true := rfl

private theorem booster_6_check_122 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      ((((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6))) = true := rfl

private theorem booster_6_check_12 :
    checkMasksDown booster6Spec 7 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7)))
      (((1 : Nat) <<< 7)) = true := by
  exact checkMasksDown_step_true booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7)))
    (((1 : Nat) <<< 7)) booster_6_check_120 booster_6_check_121 booster_6_check_122

private theorem booster_6_check_200 :
    checkMasksDown booster6Spec 6 (((1 : Nat) <<< 8)) (((1 : Nat) <<< 8)) = true := rfl

private theorem booster_6_check_201 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 6)))
      (((1 : Nat) <<< 8)) = true := rfl

private theorem booster_6_check_202 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 6)))
      ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 6))) = true := rfl

private theorem booster_6_check_20 :
    checkMasksDown booster6Spec 7 (((1 : Nat) <<< 8)) (((1 : Nat) <<< 8)) = true := by
  exact checkMasksDown_step_true booster6Spec 6 (((1 : Nat) <<< 8)) (((1 : Nat) <<< 8))
    booster_6_check_200 booster_6_check_201 booster_6_check_202

private theorem booster_6_check_210 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7)))
      (((1 : Nat) <<< 8)) = true := rfl

private theorem booster_6_check_211 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      (((1 : Nat) <<< 8)) = true := rfl

private theorem booster_6_check_212 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 6))) = true := rfl

private theorem booster_6_check_21 :
    checkMasksDown booster6Spec 7 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7)))
      (((1 : Nat) <<< 8)) = true := by
  exact checkMasksDown_step_true booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7)))
    (((1 : Nat) <<< 8)) booster_6_check_210 booster_6_check_211 booster_6_check_212

private theorem booster_6_check_220 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7)))
      ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7))) = true := rfl

private theorem booster_6_check_221 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7))) = true := rfl

private theorem booster_6_check_222 :
    checkMasksDown booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6)))
      ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7) ||| ((1 : Nat) <<< 6))) = true := rfl

private theorem booster_6_check_22 :
    checkMasksDown booster6Spec 7 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7)))
      ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7))) = true := by
  exact checkMasksDown_step_true booster6Spec 6 ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7)))
    ((((1 : Nat) <<< 8) ||| ((1 : Nat) <<< 7))) booster_6_check_220
    booster_6_check_221 booster_6_check_222

private theorem booster_6_check_0 :
    checkMasksDown booster6Spec 8 0 0 = true := by
  exact checkMasksDown_step_true booster6Spec 7 0 0
    booster_6_check_00 booster_6_check_01 booster_6_check_02

private theorem booster_6_check_1 :
    checkMasksDown booster6Spec 8 (((1 : Nat) <<< 8)) 0 = true := by
  exact checkMasksDown_step_true booster6Spec 7 (((1 : Nat) <<< 8)) 0
    booster_6_check_10 booster_6_check_11 booster_6_check_12

private theorem booster_6_check_2 :
    checkMasksDown booster6Spec 8 (((1 : Nat) <<< 8)) (((1 : Nat) <<< 8)) = true := by
  exact checkMasksDown_step_true booster6Spec 7 (((1 : Nat) <<< 8)) (((1 : Nat) <<< 8))
    booster_6_check_20 booster_6_check_21 booster_6_check_22

private theorem booster_6_rawCheckValid :
    booster6Spec.rawCheckValid = true := by
  unfold FrameSpec.rawCheckValid
  change checkMasksDown booster6Spec 9 0 0 = true
  exact
    checkMasksDown_step_true booster6Spec 8 0 0
      booster_6_check_0 booster_6_check_1 booster_6_check_2

private theorem booster_6_valid :
    (boosters.get ⟨6, by decide⟩).IsValid := by
  simpa [booster6Spec] using booster6Spec.rawCheckValid_sound booster_6_rawCheckValid

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
