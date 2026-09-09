/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.WholeSpaceUniqueness
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3CompactCandidate
public import LeanPool.NavierStokesAndEuler.NavierStokes.ComparatorR3Bridge

@[expose] public section

/-!
# Comparison with the compact candidate on all of R³

The whole-space uniqueness proof is ported from the verified R³ development.
The competitor retains exactly the smoothness and finite-energy conditions
of the comparator. The candidate's compact support supplies the reference
solution's bounds on each closed interval before time one.
-/

noncomputable section

namespace NavierStokes.ComparatorBridge

open Set MeasureTheory ProblemStatement
open scoped ContDiff

theorem GlobalSolutionRn.uniformFiniteEnergy {f v : VelocityField} {q : PressureField}
    (h : GlobalSolutionRn f v q) (T : ℝ) :
    NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Icc 0 T) v := by
  obtain ⟨E, hE⟩ := h.globally_bounded_energy
  refine ⟨max 0 (E / 2), le_max_left _ _, ?_⟩
  intro t ht
  constructor
  · simpa only [NavierStokesR3.ProblemStatement.SquareIntegrableAtTime, norm_norm] using!
      (memLp_two_iff_integrable_sq_norm (h.integrable t ht.1).1).mp (h.integrable t ht.1)
  · change (1 / 2 : ℝ) * (∫ x : Space, ‖v (t, x)‖ ^ 2) ≤ max 0 (E / 2)
    have hb := (hE t ht.1).le
    have hm := le_max_right 0 (E / 2)
    linarith

/-- A compact candidate with unbounded speed excludes every global smooth
solution having the comparator's finite-energy bound. -/
theorem compact_candidate_excludes_global_solution
    {u v f : VelocityField} {p q : PressureField}
    (h : R3CompactCandidate.Properties u p f) (hv : GlobalSolutionRn f v q) : False := by
  apply h.not_global_agreement hv.velocity_smooth
  obtain ⟨K, hK, hs⟩ := h.velocity_support
  intro t ht x
  by_cases ht0 : t = 0
  · subst t
    rw [h.zero_initial_velocity, hv.initial_velocity]
  have hpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hpre : NavierStokesR3.Comparison.slab 0 t ⊆ preSingularDomain := by
    intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans_lt ht.2⟩, hz.2⟩
  have hfuture : NavierStokesR3.Comparison.slab 0 t ⊆ futureDomain := by
    intro z hz
    exact ⟨hz.1.1, hz.2⟩
  have hsupport : ∀ r ∈ Icc (0 : ℝ) t, tsupport (fun y => u (r, y)) ⊆ K := by
    intro r hr
    apply closure_minimal _ hK.isClosed
    intro y hy
    by_contra hyK
    exact hy (hs r ⟨hr.1, hr.2.trans_lt ht.2⟩ y hyK)
  have heq := NavierStokesR3.WholeSpaceUniqueness.classical_uniqueness_on_Icc hpos
    (h.velocity_smooth.mono hpre) (hv.velocity_smooth.mono hfuture)
    (h.pressure_smooth.mono hpre) (hv.pressure_smooth.mono hfuture)
    hK hsupport (hv.uniformFiniteEnergy t)
    (fun r hr => h.divergence_free r ⟨hr.1.le, hr.2.trans ht.2⟩)
    (fun r hr => hv.divergence_free r hr.1.le)
    (fun r hr y => by
      simpa only [NavierStokesR3.ProblemStatement.navierStokesResidual,
        navierStokesResidual, one_smul] using
        (h.navier_stokes r ⟨hr.1, hr.2.trans ht.2⟩ y).trans
          (hv.navier_stokes r hr.1 y).symm)
    (fun y => (h.zero_initial_velocity y).trans (hv.initial_velocity y).symm)
  exact heq t ⟨ht.1, le_rfl⟩ x

end NavierStokes.ComparatorBridge
