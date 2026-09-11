/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3CompactCandidate
import LeanPool.NavierStokesAndEuler.NavierStokes.R3FiniteEnergyComparison
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCandidateAssembly

/-!
# The constructed compact candidate implies option (C)

Zero initial data and the viscosity-rescaled compact force satisfy the exact
decay conditions in the comparator. Whole-space finite-energy comparison
excludes a global solution for every positive viscosity.
-/

section

/-!
# The project's actual sums give a compact whole-space candidate

This is an extraction from `selected_witness`, which retains the original
potential, direct field, and pressure sums. It does not invoke whole-space
uniqueness or claim the comparator's nonexistence conclusion.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.R3CompactCandidate

open ProblemStatement

theorem selected_compact_candidate :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, Properties u p f := by
  obtain ⟨a, _, ea, eb, ep, forcing, hc, _⟩ := ActualCandidateAssembly.selected_witness
  exact ⟨_, _, _, of_localized_fields hc⟩

end NavierStokes.R3CompactCandidate

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ComparatorBridge

open Set ProblemStatement
open scoped ContDiff

theorem option_C_of_compact_candidate
    {u : VelocityField} {p : PressureField} {f : VelocityField}
    (h : R3CompactCandidate.Properties u p f) (ν : ℝ) (hν : 0 < ν) :
    ∃ (u₀ : Space → Space) (f : Space → ℝ → Space),
      Comparator.InitialVelocityConditionDecay u₀ ∧ Comparator.ForceConditionDecay f ∧
      ¬ (∃ v p, Comparator.NavierStokesExistenceAndSmoothnessRn ν u₀ f v p) := by
  obtain ⟨K, hK, hs⟩ := h.force_support
  have hFd := CompactSpatialForceDecay.forceConditionDecay hK
    (rescale_smooth h.force_smooth (ν ^ 2) hν.le)
    (CompactSpatialForceDecay.rescale_supported hs (ν ^ 2) hν.le)
    (rescale_support h.force_time_support (ν ^ 2) hν)
  refine ⟨fun _ => 0, toComparator (rescaledForce ν f),
    zero_initial_condition_decay, hFd, ?_⟩
  rintro ⟨v, q, hv⟩
  exact compact_candidate_excludes_global_solution h (normalized_solution_Rn hν hv)

/-- Option (C) with exactly the comparator's quantifiers. -/
theorem navier_stokes_breakdown_R3 (ν : ℝ) (hν : ν > 0) :
    ∃ (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (f : EuclideanSpace ℝ (Fin 3) → ℝ → EuclideanSpace ℝ (Fin 3)),
      Comparator.InitialVelocityConditionDecay u₀ ∧ Comparator.ForceConditionDecay f ∧
      ¬ (∃ v p, Comparator.NavierStokesExistenceAndSmoothnessRn ν u₀ f v p) := by
  obtain ⟨u, p, f, h⟩ := R3CompactCandidate.selected_compact_candidate
  exact option_C_of_compact_candidate h ν hν

end NavierStokes.ComparatorBridge
