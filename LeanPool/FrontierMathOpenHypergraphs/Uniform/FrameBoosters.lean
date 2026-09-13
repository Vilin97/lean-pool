/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import LeanPool.FrontierMathOpenHypergraphs.Uniform.FrameDefs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

/-!
# Booster-frame validations

The larger checks are split into blocks of 128 masks to bound kernel memory.
Each block is evaluated directly by the kernel.
-/

@[expose] public section

namespace HypergraphLowerBound

private theorem booster_0_valid :
    (boosters.get ⟨0, by decide⟩).IsValid := by
  exact (boosters.get ⟨0, by decide⟩).checkComplementValid_sound (by decide +kernel)

private theorem booster_1_valid :
    (boosters.get ⟨1, by decide⟩).IsValid := by
  exact (boosters.get ⟨1, by decide⟩).checkComplementValid_sound (by decide +kernel)

private theorem booster_2_valid :
    (boosters.get ⟨2, by decide⟩).IsValid := by
  exact (boosters.get ⟨2, by decide⟩).checkComplementValid_sound (by decide +kernel)

private theorem booster_3_valid :
    (boosters.get ⟨3, by decide⟩).IsValid := by
  exact (boosters.get ⟨3, by decide⟩).checkComplementValid_sound (by decide +kernel)

private theorem booster_4_valid :
    (boosters.get ⟨4, by decide⟩).IsValid := by
  apply (boosters.get ⟨4, by decide⟩).checkComplementValid_sound
  change checkComplementMasksDown _ 8 0 = true
  apply checkComplementMasksDown_step_true <;> decide +kernel

private theorem booster_5_valid :
    (boosters.get ⟨5, by decide⟩).IsValid := by
  apply (boosters.get ⟨5, by decide⟩).checkComplementValid_sound
  change checkComplementMasksDown _ 8 0 = true
  apply checkComplementMasksDown_step_true <;> decide +kernel

private def booster6Spec : FrameSpec :=
  boosters.get ⟨6, by decide⟩

private theorem booster_6_check_0 :
    checkComplementMasksDown booster6Spec 8 0 = true := by
  apply checkComplementMasksDown_step_true <;> decide +kernel

private theorem booster_6_check_1 :
    checkComplementMasksDown booster6Spec 8 ((1 : Nat) <<< 8) = true := by
  apply checkComplementMasksDown_step_true <;> decide +kernel

private theorem booster_6_valid :
    (boosters.get ⟨6, by decide⟩).IsValid := by
  apply booster6Spec.checkComplementValid_sound
  exact checkComplementMasksDown_step_true booster6Spec 8 0
    booster_6_check_0 booster_6_check_1

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
