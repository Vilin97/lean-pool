/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeLp
import Mathlib.Tactic.Positivity.Finset

/-! The actual continuous-path embedding as a bounded linear time-space map. -/

@[expose] public section


noncomputable section

namespace EulerTimeLp

open MeasureTheory Set EulerVolterraConvolution
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- The actual continuous-path inclusion preserves addition. -/
theorem pathLp_add (T : ℝ) (hT : 0 ≤ T) (f g : C(Icc (0 : ℝ) T, E)) :
    pathLp T hT (f+g) = pathLp T hT f+pathLp T hT g := by
  apply Lp.ext
  filter_upwards [pathLp_ae T hT (f+g), pathLp_ae T hT f, pathLp_ae T hT g,
    Lp.coeFn_add (pathLp T hT f) (pathLp T hT g)] with t h1 h2 h3 h4
  simp only [Pi.add_apply] at h4
  rw [h1, h4, h2, h3]
  rfl

/-- The actual continuous-path inclusion preserves real scalar multiplication. -/
theorem pathLp_smul (T : ℝ) (hT : 0 ≤ T) (r : ℝ) (f : C(Icc (0 : ℝ) T, E)) :
    pathLp T hT (r • f) = r • pathLp T hT f := by
  apply Lp.ext
  filter_upwards [pathLp_ae T hT (r • f), pathLp_ae T hT f,
    Lp.coeFn_smul r (pathLp T hT f)] with t h1 h2 h3
  simp only [Pi.smul_apply] at h3
  rw [h1, h3, h2]
  rfl

/-- The genuine continuous-path to Bochner L² embedding is a bounded linear map. -/
def pathLpOperator (T : ℝ) (hT : 0 ≤ T) : C(Icc (0 : ℝ) T, E) →L[ℝ] TimeLp T E :=
  ({ toFun := pathLp T hT
     map_add' := pathLp_add T hT
     map_smul' := fun r f => by simpa only [RingHom.id_apply] using pathLp_smul T hT r f } :
      C(Icc (0 : ℝ) T, E) →ₗ[ℝ] TimeLp T E).mkContinuous
    ((measureUnivNNReal (timeMeasure T) : ℝ) ^ (1/2 : ℝ)) (pathLp_bound T hT)

/-- The bounded embedding is exactly the actual L² equivalence class of the path. -/
theorem pathLpOperator_apply (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, E)) :
    pathLpOperator T hT f = pathLp T hT f := rfl

end EulerTimeLp
