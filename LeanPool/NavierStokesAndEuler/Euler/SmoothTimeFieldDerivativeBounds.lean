/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeField

@[expose] public section

/-! Norms of literal derivative coefficient paths. Currying incurs no
constant, and the bound is uniform in both the time and label variables. -/

noncomputable section

open scoped BoundedContinuousFunction

universe u

namespace SmoothTimeField

variable {K E V : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

private local instance (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] V) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] V) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V)) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] (E →L[ℝ] V))) :=
  inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] (E →L[ℝ] V))) := inferInstance

theorem derivative_jet_norm_le (A : SmoothTimeField K E V) (n : ℕ) :
    ‖A.derivative.jet n‖ ≤ ‖A.jet (n+1)‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro t
  apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).2
  intro x
  change ‖continuousMultilinearCurryRightEquiv' ℝ n E V (A.jet (n+1) t x)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact ((A.jet (n+1) t).norm_coe_le_norm x).trans ((A.jet (n+1)).norm_coe_le_norm t)

theorem derivative_field_norm_le (A : SmoothTimeField K E V) :
    ‖A.derivative.field‖ ≤ ‖A.jet 1‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro t
  apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).2
  intro x
  change ‖continuousMultilinearCurryFin1 ℝ E V (A.jet 1 t x)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact ((A.jet 1 t).norm_coe_le_norm x).trans ((A.jet 1).norm_coe_le_norm t)

end SmoothTimeField
