/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeH1Reconstruction
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpBoundedMap

/-!
# Bounded maps commute with the genuine time-H¹ reconstruction

This identity permits spatial translations to be applied to the two actual
Bochner fields before reconstructing the continuous time representative.
It is an equality of the constructed operators, independent of any smoothness
assumption on their inputs.
-/

@[expose] public section


noncomputable section

namespace EulerTimeH1Reconstruction

open Set ContinuousLinearMap EulerTimeLp EulerTerminalTimePrimitive EulerTimeLpBoundedMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The actual time average commutes with every bounded linear map. -/
theorem mean_timeLift (T : ℝ) (hT : 0 ≤ T) (A : E →L[ℝ] F) (p : TimeLp T E) :
    mean T hT (timeLift T A p) = A (mean T hT p) := by
  change (-T)⁻¹ • initialTrace T hT (timeLift T A p) = A ((-T)⁻¹ • initialTrace T hT p)
  rw [initialTrace_timeLift, map_smul]

/-- The continuous time representative commutes with every bounded linear map. -/
theorem reconstruction_timeLift (T : ℝ) (hT : 0 ≤ T) (A : E →L[ℝ] F)
    (p q : TimeLp T E) (t : Icc (0 : ℝ) T) :
    reconstruction T hT (timeLift T A p, timeLift T A q) t =
      A (reconstruction T hT (p,q) t) := by
  rw [reconstruction_apply, reconstruction_apply, mean_timeLift,
    primitiveTimeLp_timeLift, mean_timeLift]
  change A (mean T hT p) + (realPrimitive T (timeLift T A q) t -
    A (mean T hT (primitiveTimeLp T hT q))) =
      A (mean T hT p + (realPrimitive T q t - mean T hT (primitiveTimeLp T hT q)))
  rw [realPrimitive_timeLift, map_add, map_sub]

end EulerTimeH1Reconstruction
