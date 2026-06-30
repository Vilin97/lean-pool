/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/

import LeanPool.FrontierMathOpenHypergraphs.Uniform.FrameDefs

/-!
# Exact small-frame validations
-/

namespace HypergraphLowerBound

private theorem exactSmallFrame_0_valid :
    (exactSmallFrames.get ⟨0, by decide⟩).IsValid := by
  exact (exactSmallFrames.get ⟨0, by decide⟩).rawCheckValid_sound rfl

private theorem exactSmallFrame_1_valid :
    (exactSmallFrames.get ⟨1, by decide⟩).IsValid := by
  exact (exactSmallFrames.get ⟨1, by decide⟩).rawCheckValid_sound rfl

private theorem exactSmallFrame_2_valid :
    (exactSmallFrames.get ⟨2, by decide⟩).IsValid := by
  exact (exactSmallFrames.get ⟨2, by decide⟩).rawCheckValid_sound rfl

private theorem exactSmallFrame_3_valid :
    (exactSmallFrames.get ⟨3, by decide⟩).IsValid := by
  exact (exactSmallFrames.get ⟨3, by decide⟩).rawCheckValid_sound rfl

private theorem exactSmallFrame_4_valid :
    (exactSmallFrames.get ⟨4, by decide⟩).IsValid := by
  exact (exactSmallFrames.get ⟨4, by decide⟩).rawCheckValid_sound rfl

private theorem exactSmallFrame_5_valid :
    (exactSmallFrames.get ⟨5, by decide⟩).IsValid := by
  exact (exactSmallFrames.get ⟨5, by decide⟩).rawCheckValid_sound rfl

private theorem exactSmallFrame_6_valid :
    (exactSmallFrames.get ⟨6, by decide⟩).IsValid := by
  exact (exactSmallFrames.get ⟨6, by decide⟩).rawCheckValid_sound rfl

private theorem exactSmallFrame_7_valid :
    (exactSmallFrames.get ⟨7, by decide⟩).IsValid := by
  exact (exactSmallFrames.get ⟨7, by decide⟩).rawCheckValid_sound rfl

private theorem exactSmallFrame_8_valid :
    (exactSmallFrames.get ⟨8, by decide⟩).IsValid := by
  exact (exactSmallFrames.get ⟨8, by decide⟩).rawCheckValid_sound rfl

private theorem exactSmallFrame_9_valid :
    (exactSmallFrames.get ⟨9, by decide⟩).IsValid := by
  exact (exactSmallFrames.get ⟨9, by decide⟩).rawCheckValid_sound rfl

private theorem exactSmallFrame_10_valid :
    (exactSmallFrames.get ⟨10, by decide⟩).IsValid := by
  exact (exactSmallFrames.get ⟨10, by decide⟩).rawCheckValid_sound rfl

private theorem exactSmallFrame_11_valid :
    (exactSmallFrames.get ⟨11, by decide⟩).IsValid := by
  exact (exactSmallFrames.get ⟨11, by decide⟩).rawCheckValid_sound rfl

private theorem exactSmallFrame_12_valid :
    (exactSmallFrames.get ⟨12, by decide⟩).IsValid := by
  exact (exactSmallFrames.get ⟨12, by decide⟩).rawCheckValid_sound rfl

private theorem exactSmallFrame_13_valid :
    (exactSmallFrames.get ⟨13, by decide⟩).IsValid := by
  exact (exactSmallFrames.get ⟨13, by decide⟩).rawCheckValid_sound rfl

private theorem exactSmallFrame_14_valid :
    (exactSmallFrames.get ⟨14, by decide⟩).IsValid := by
  exact (exactSmallFrames.get ⟨14, by decide⟩).rawCheckValid_sound rfl

private theorem exactSmallFrame_15_valid :
    (exactSmallFrames.get ⟨15, by decide⟩).IsValid := by
  exact (exactSmallFrames.get ⟨15, by decide⟩).rawCheckValid_sound rfl

private theorem exactSmallFrame_16_valid :
    (exactSmallFrames.get ⟨16, by decide⟩).IsValid := by
  exact (exactSmallFrames.get ⟨16, by decide⟩).rawCheckValid_sound rfl

private theorem exactSmallFrame_17_valid :
    (exactSmallFrames.get ⟨17, by decide⟩).IsValid := by
  exact (exactSmallFrames.get ⟨17, by decide⟩).rawCheckValid_sound rfl

private theorem exactSmallFrame_18_valid :
    (exactSmallFrames.get ⟨18, by decide⟩).IsValid := by
  exact (exactSmallFrames.get ⟨18, by decide⟩).rawCheckValid_sound rfl

private theorem exactSmallFrame_19_valid :
    (exactSmallFrames.get ⟨19, by decide⟩).IsValid := by
  exact (exactSmallFrames.get ⟨19, by decide⟩).rawCheckValid_sound rfl

private theorem exactSmallFrame_20_valid :
    (exactSmallFrames.get ⟨20, by decide⟩).IsValid := by
  exact (exactSmallFrames.get ⟨20, by decide⟩).rawCheckValid_sound rfl

theorem exactSmallFrames_valid :
    ∀ spec ∈ exactSmallFrames, spec.IsValid := by
  intro spec hs
  obtain ⟨i, rfl⟩ := List.get_of_mem hs
  fin_cases i
  · exact exactSmallFrame_0_valid
  · exact exactSmallFrame_1_valid
  · exact exactSmallFrame_2_valid
  · exact exactSmallFrame_3_valid
  · exact exactSmallFrame_4_valid
  · exact exactSmallFrame_5_valid
  · exact exactSmallFrame_6_valid
  · exact exactSmallFrame_7_valid
  · exact exactSmallFrame_8_valid
  · exact exactSmallFrame_9_valid
  · exact exactSmallFrame_10_valid
  · exact exactSmallFrame_11_valid
  · exact exactSmallFrame_12_valid
  · exact exactSmallFrame_13_valid
  · exact exactSmallFrame_14_valid
  · exact exactSmallFrame_15_valid
  · exact exactSmallFrame_16_valid
  · exact exactSmallFrame_17_valid
  · exact exactSmallFrame_18_valid
  · exact exactSmallFrame_19_valid
  · exact exactSmallFrame_20_valid

end HypergraphLowerBound
