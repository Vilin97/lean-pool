/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousKFunctional

/-!
# Approximate competitors for the continuous K-functional

This file records convention-neutral consequences of the definition of the continuous
`K`-functional as a real infimum. The infimum need not be attained: every positive error admits
a genuine `ContinuousKCompetitor` whose value lies within that error of the infimum.
-/

@[expose] public section

namespace Homogenization

noncomputable section

/-- Every positive error admits a genuine competitor whose value is strictly less than the
continuous `K`-functional plus that error. This does not assert that the infimum is attained. -/
theorem exists_continuousKCompetitor_value_lt_add {d : ℕ}
    (t : ContinuousKScale) (F : UnitCubeEuclideanL2Field d) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : ContinuousKCompetitor d,
      continuousKFunctionalCompetitorValue t F G < continuousKFunctional t F + ε := by
  rw [continuousKFunctional_eq_sInf]
  obtain ⟨a, ⟨G, rfl⟩, ha⟩ :=
    (csInf_lt_iff (continuousKFunctional_range_bddBelow t F)
      (continuousKFunctional_range_nonempty t F)).1 (lt_add_of_pos_right _ hε)
  exact ⟨G, ha⟩

/-- Non-strict version of `exists_continuousKCompetitor_value_lt_add`. -/
theorem exists_continuousKCompetitor_value_le_add {d : ℕ}
    (t : ContinuousKScale) (F : UnitCubeEuclideanL2Field d) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : ContinuousKCompetitor d,
      continuousKFunctionalCompetitorValue t F G ≤ continuousKFunctional t F + ε := by
  obtain ⟨G, hG⟩ := exists_continuousKCompetitor_value_lt_add t F hε
  exact ⟨G, hG.le⟩

/-- A strict upper bound on the continuous `K`-functional contains the value of a genuine
competitor. -/
theorem exists_continuousKCompetitor_value_lt_of_continuousKFunctional_lt {d : ℕ}
    (t : ContinuousKScale) (F : UnitCubeEuclideanL2Field d) {a : ℝ}
    (h : continuousKFunctional t F < a) :
    ∃ G : ContinuousKCompetitor d, continuousKFunctionalCompetitorValue t F G < a := by
  rw [continuousKFunctional_eq_sInf] at h
  obtain ⟨y, ⟨G, rfl⟩, hy⟩ :=
    (csInf_lt_iff (continuousKFunctional_range_bddBelow t F)
      (continuousKFunctional_range_nonempty t F)).1 h
  exact ⟨G, hy⟩

end

end Homogenization
