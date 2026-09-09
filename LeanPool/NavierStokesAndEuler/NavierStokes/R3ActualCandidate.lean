/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3CompactCandidate
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCandidateAssembly

@[expose] public section

/-!
# The project's actual sums give a compact whole-space candidate

This is an extraction from `selected_witness`, which retains the original
potential, direct field, and pressure sums. It does not invoke whole-space
uniqueness or claim the comparator's nonexistence conclusion.
-/

noncomputable section

namespace NavierStokes.R3CompactCandidate

open ProblemStatement

theorem selected_compact_candidate :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, Properties u p f := by
  obtain ⟨a, _, ea, eb, ep, forcing, hc, _⟩ := ActualCandidateAssembly.selected_witness
  exact ⟨_, _, _, of_localized_fields hc⟩

end NavierStokes.R3CompactCandidate
