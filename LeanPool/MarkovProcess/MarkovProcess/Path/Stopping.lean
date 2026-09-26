/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Path.Basic


/-!
# Deterministic stopping of continuous paths

This file defines stopping a continuous path at a fixed deterministic time. It proves only
topological and Borel-measurability properties of this operation; it introduces no stopping
times or stochastic laws.
-/

@[expose] public section

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- Clamp nonnegative time at the fixed deterministic time `T`. -/
def clampTime (T : NNReal) : C(NNReal, NNReal) where
  toFun t := min t T
  continuous_toFun := continuous_id.min continuous_const

@[simp]
theorem clampTime_apply (T t : NNReal) : clampTime T t = min t T := rfl

/-- A continuous path stopped at the fixed deterministic time `T`. -/
def stoppedPath (T : NNReal) (omega : ContinuousPath alpha) : ContinuousPath alpha :=
  omega.comp (clampTime T)

@[simp]
theorem stoppedPath_apply (T : NNReal) (omega : ContinuousPath alpha) (t : NNReal) :
    stoppedPath T omega t = omega (min t T) :=
  rfl

theorem stoppedPath_apply_of_le (T : NNReal) (omega : ContinuousPath alpha) (t : NNReal)
    (ht : t ≤ T) : stoppedPath T omega t = omega t := by
  rw [stoppedPath_apply, min_eq_left ht]

theorem stoppedPath_apply_of_ge (T : NNReal) (omega : ContinuousPath alpha) (t : NNReal)
    (ht : T ≤ t) : stoppedPath T omega t = omega T := by
  rw [stoppedPath_apply, min_eq_right ht]

/-- Every path stopped at a deterministic time is continuous in time. -/
theorem continuous_stoppedPath (T : NNReal) (omega : ContinuousPath alpha) :
    Continuous (stoppedPath T omega) :=
  (stoppedPath T omega).continuous

/-- Stopping at a fixed deterministic time is continuous in the compact-open topology. -/
theorem continuous_stoppedPath_operator (T : NNReal) :
    Continuous (stoppedPath (alpha := alpha) T) :=
  ContinuousMap.continuous_precomp (clampTime T)

/-- Stopping at a fixed deterministic time is Borel measurable. -/
theorem measurable_stoppedPath_operator (T : NNReal) :
    @Measurable (ContinuousPath alpha) (ContinuousPath alpha)
      (borel (ContinuousPath alpha)) (borel (ContinuousPath alpha))
      (stoppedPath (alpha := alpha) T) :=
  (continuous_stoppedPath_operator T).borel_measurable

/-- Successive deterministic stops combine by taking the earlier stopping time. -/
@[simp]
theorem stoppedPath_stoppedPath (S T : NNReal) (omega : ContinuousPath alpha) :
    stoppedPath S (stoppedPath T omega) = stoppedPath (min S T) omega := by
  apply ContinuousMap.ext
  intro t
  simp only [stoppedPath_apply, min_assoc]

end ContinuousPath

end MarkovProcess
