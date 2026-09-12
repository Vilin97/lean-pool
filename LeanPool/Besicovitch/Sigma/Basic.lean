/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Statement

/-!
# Basic facts about the one-dimensional rectifiability threshold

The forcing property is monotone in its density threshold.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal MeasureTheory

namespace LeanPool.Besicovitch

variable (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Forcing is monotone in the threshold: a larger density hypothesis is a stronger one. -/
theorem ForcesOneRectifiability.mono {β β' : ℝ≥0∞} (h : β ≤ β')
    (hβ : ForcesOneRectifiability X β) : ForcesOneRectifiability X β' := by
  intro s hs hfinite hdensity
  exact hβ s hs hfinite (hdensity.mono fun _ hx ↦ h.trans hx)

/-- The admissible thresholds are bounded below, by `0`. -/
theorem bddBelow_admissibleThresholds :
    BddBelow {β : ℝ | 0 ≤ β ∧ ForcesOneRectifiability X (ENNReal.ofReal β)} :=
  ⟨0, fun _ h ↦ h.1⟩

/-- An admissible nonnegative threshold bounds `sigmaOne` from above. -/
theorem sigmaOne_le_of_forces {b : ℝ} (hb : 0 ≤ b)
    (hforce : ForcesOneRectifiability X (ENNReal.ofReal b)) : sigmaOne X ≤ b := by
  apply csInf_le
  · exact ⟨0, fun _ h ↦ h.1⟩
  · exact ⟨hb, hforce⟩

/-- Forcing rectifiability at every threshold above `b` proves `sigmaOne ≤ b`. -/
theorem sigmaOne_le_of_forall_gt {b : ℝ} (hb : 0 ≤ b)
    (hforce : ∀ c : ℝ, b < c → ForcesOneRectifiability X (ENNReal.ofReal c)) :
    sigmaOne X ≤ b := by
  apply le_of_forall_pos_le_add
  intro ε hε
  apply sigmaOne_le_of_forces X (add_nonneg hb hε.le)
  exact hforce (b + ε) (lt_add_of_pos_right b hε)

end LeanPool.Besicovitch
