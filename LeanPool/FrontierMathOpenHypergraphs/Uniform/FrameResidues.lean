/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/

import LeanPool.FrontierMathOpenHypergraphs.Uniform.FrameDefs

/-!
# Residue-gadget validations
-/

namespace HypergraphLowerBound

private theorem residueGadget_0_valid :
    (residueGadgets.get ⟨0, by decide⟩).IsValid := by
  exact (residueGadgets.get ⟨0, by decide⟩).rawCheckValid_sound rfl

private theorem residueGadget_1_valid :
    (residueGadgets.get ⟨1, by decide⟩).IsValid := by
  exact (residueGadgets.get ⟨1, by decide⟩).rawCheckValid_sound rfl

private theorem residueGadget_2_valid :
    (residueGadgets.get ⟨2, by decide⟩).IsValid := by
  exact (residueGadgets.get ⟨2, by decide⟩).rawCheckValid_sound rfl

private theorem residueGadget_3_valid :
    (residueGadgets.get ⟨3, by decide⟩).IsValid := by
  exact (residueGadgets.get ⟨3, by decide⟩).rawCheckValid_sound rfl

private theorem residueGadget_4_valid :
    (residueGadgets.get ⟨4, by decide⟩).IsValid := by
  exact (residueGadgets.get ⟨4, by decide⟩).rawCheckValid_sound rfl

private theorem residueGadget_5_valid :
    (residueGadgets.get ⟨5, by decide⟩).IsValid := by
  exact (residueGadgets.get ⟨5, by decide⟩).rawCheckValid_sound rfl

private theorem residueGadget_6_valid :
    (residueGadgets.get ⟨6, by decide⟩).IsValid := by
  exact (residueGadgets.get ⟨6, by decide⟩).rawCheckValid_sound rfl

private theorem residueGadget_7_valid :
    (residueGadgets.get ⟨7, by decide⟩).IsValid := by
  exact (residueGadgets.get ⟨7, by decide⟩).rawCheckValid_sound rfl

private theorem residueGadget_8_valid :
    (residueGadgets.get ⟨8, by decide⟩).IsValid := by
  exact (residueGadgets.get ⟨8, by decide⟩).rawCheckValid_sound rfl

private theorem residueGadget_9_valid :
    (residueGadgets.get ⟨9, by decide⟩).IsValid := by
  exact (residueGadgets.get ⟨9, by decide⟩).rawCheckValid_sound rfl

private theorem residueGadget_10_valid :
    (residueGadgets.get ⟨10, by decide⟩).IsValid := by
  exact (residueGadgets.get ⟨10, by decide⟩).rawCheckValid_sound rfl

private theorem residueGadget_11_valid :
    (residueGadgets.get ⟨11, by decide⟩).IsValid := by
  exact (residueGadgets.get ⟨11, by decide⟩).rawCheckValid_sound rfl

theorem residueGadgets_valid :
    ∀ spec ∈ residueGadgets, spec.IsValid := by
  intro spec hs
  obtain ⟨i, rfl⟩ := List.get_of_mem hs
  fin_cases i
  · exact residueGadget_0_valid
  · exact residueGadget_1_valid
  · exact residueGadget_2_valid
  · exact residueGadget_3_valid
  · exact residueGadget_4_valid
  · exact residueGadget_5_valid
  · exact residueGadget_6_valid
  · exact residueGadget_7_valid
  · exact residueGadget_8_valid
  · exact residueGadget_9_valid
  · exact residueGadget_10_valid
  · exact residueGadget_11_valid


end HypergraphLowerBound
