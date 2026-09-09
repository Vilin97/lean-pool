/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeLpMultiplier
import Mathlib.Tactic.Positivity.Finset

/-! Continuous time-path application and its exact Bochner compatibility. -/

@[expose] public section


noncomputable section

namespace EulerTimeLp

open Set
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual pointwise action of a continuous operator path on a continuous field path. -/
def timePathApply (T : ℝ) (A : C(Icc (0 : ℝ) T, E →L[ℝ] F))
    (u : C(Icc (0 : ℝ) T, E)) : C(Icc (0 : ℝ) T, F) :=
  ⟨fun t => A t (u t), A.continuous.clm_apply u.continuous⟩

/-- The actual continuous-path action has exactly its Bochner multiplier value. -/
theorem pathLp_timePathApply (T : ℝ) (hT : 0 ≤ T) (A : C(Icc (0 : ℝ) T, E →L[ℝ] F))
    (u : C(Icc (0 : ℝ) T, E)) :
    pathLp T hT (timePathApply T A u) = timeMultiplier T hT A (pathLp T hT u) :=
  (timeMultiplier_pathLp T hT A u).symm

/-- Strong L² convergence of actual continuous field paths survives a fixed continuous
time-dependent operator. -/
theorem timePathApply_tendsto (T : ℝ) (hT : 0 ≤ T) (A : C(Icc (0 : ℝ) T, E →L[ℝ] F))
    (u : ℕ → C(Icc (0 : ℝ) T, E)) (U : TimeLp T E)
    (hu : Filter.Tendsto (fun n => pathLp T hT (u n)) Filter.atTop (𝓝 U)) :
    Filter.Tendsto (fun n => pathLp T hT (timePathApply T A (u n))) Filter.atTop
      (𝓝 (timeMultiplier T hT A U)) := by
  have h := (timeMultiplier T hT A).continuous.continuousAt.tendsto.comp hu
  simpa only [pathLp_timePathApply, Function.comp_def] using h

end EulerTimeLp
