/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldJoint
public import LeanPool.NavierStokesAndEuler.Euler.SmoothCoefficientTimeRestriction

/-! Restriction of a genuine smooth time field preserves the spatial
jets and the actual one-sided time derivative on a shorter interval. -/

@[expose] public section


noncomputable section

namespace SmoothTimeField

open Set EulerTimeIntervalRestriction
open scoped ContDiff BoundedContinuousFunction

variable {K J E V : Type} [TopologicalSpace K] [CompactSpace K]
  [TopologicalSpace J] [CompactSpace J]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Cache the standard `NormedAddCommGroup (E [×n]→L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeFieldRestriction1 (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] V) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (E [×n]→L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instSmoothTimeFieldRestriction2 (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] V) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeFieldRestriction3 (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V))
    := inferInstance
/-- Cache the standard `NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeFieldRestriction4 (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V)) :=
    inferInstance

/-- Comp time, bundling `field`, `smooth`, `jet`, `jet_eq`. -/
def compTime (A : SmoothTimeField K E V) (f : C(J, K)) : SmoothTimeField J E V where
  field := A.field.comp f
  smooth t := A.smooth (f t)
  jet n := (A.jet n).comp f
  jet_eq n t x := A.jet_eq n (f t) x

@[simp] theorem compTime_apply (A : SmoothTimeField K E V) (f : C(J, K)) (t : J) (x : E) :
    (A.compTime f).field t x=A.field (f t) x := rfl

theorem compTime_jet_norm (A : SmoothTimeField K E V) (f : C(J, K)) (n : ℕ) :
    ‖(A.compTime f).jet n‖ ≤ ‖A.jet n‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro t
  exact (A.jet n).norm_coe_le_norm (f t)

variable {T S : ℝ} {hT : 0 ≤ T} (hS : 0 ≤ S) (hST : S ≤ T)
  {A B : SmoothTimeField (Icc (0 : ℝ) T) E V}

theorem TimeDerivative.restrictInitial (h : TimeDerivative T hT A B) :
    TimeDerivative S hS (A.compTime (initialInclusion T S hST))
      (B.compTime (initialInclusion T S hST)) := by
  intro t x
  have he (s : ℝ) (hs : s ∈ Icc (0 : ℝ) S) :
      (A.compTime (initialInclusion T S hST)).realField S hS s x=A.realField T hT s x := by
    exact congrArg (fun f : E →ᵇ V => f x) (initial_extend T S hT hS hST A.field s hs)
  exact ((h (initialInclusion T S hST t) x).mono (Icc_subset_Icc le_rfl hST)).congr_of_mem he
      t.property

end SmoothTimeField
