/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.QuadraticHeatLocal
public import LeanPool.NavierStokesAndEuler.Euler.DivergenceFreeHeat

@[expose] public section

/-! The local quadratic heat construction preserves the actual lifted divergence constraint. -/

noncomputable section

namespace EulerQuadraticSource

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerDivergenceFreeHeat
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

local instance constraintSobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
  inferInstance
local instance constraintSobolevSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) :=
  inferInstance

/-- A local solution driven by the actual divergence-free projected source has zero lifted divergence at every time. -/
theorem exists_local_quadratic_divergenceFree (q : ℕ) (ν : ℝ) (hν : 0 < ν) (S : ℝ) (hS : 0 < S)
    (κ : ℝ) (m : Vector3) (u₀ : SobolevSpace period (q+1))
    (hu₀ : gradientProjection period κ m (value period u₀) = 0)
    (C : Coefficients (Icc (0 : ℝ) S) (SobolevSpace period (q+1)) (SobolevSpace period q))
    (hC : ∀ t u, gradientProjection period κ m (value period (C.apply t u)) = 0) :
    ∃ (T : ℝ) (hT : 0 < T) (hTS : T ≤ S),
      ∃ u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)),
        ‖u‖ ≤ ‖u₀‖+1 ∧ u ⟨0, le_rfl, hT.le⟩ = u₀ ∧
        (∀ t, value period (u t) ∈ divergenceFreeSpace period κ m) ∧
        ∀ t, u t = quadraticDuhamel period ν hν hT.le hTS C u₀ u t := by
  obtain ⟨T, hT, hTS, u, hu, hi, hsol⟩ := exists_local_quadratic_mild period q ν hν S hS u₀ C
  refine ⟨T, hT, hTS, u, hu, hi, ?_, hsol⟩
  let F := (C.comp (timeInclusion hTS)).apply
  have hF : Continuous (fun p : Icc (0 : ℝ) T × SobolevSpace period (q+1) => F p.1 p.2) :=
    (C.comp (timeInclusion hTS)).continuous
  have hz := mild_solution_preserves_gradient_zero period κ m ν hν T hT.le u₀ hu₀ F hF
    (fun t v => hC (timeInclusion hTS t) v) u hsol
  intro t
  exact (gradientEvaluation_zero_iff period κ m (u t)).mp (hz t)

end EulerQuadraticSource
