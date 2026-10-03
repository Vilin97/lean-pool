/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Cube.Basic
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Convex.Continuous

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# First-order differentiability almost everywhere on source cubes

This file supplies the first-differentiability-a.e. input used by the source upper-contact
estimate. The proof is the standard route: convexity on the open cube gives local Lipschitz
regularity; compactness of the closed unit cube upgrades this to a global Lipschitz bound on a
compact neighborhood of `Q_1`; Rademacher then gives differentiability almost everywhere on
`Q_1`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- A convex function on the source cube is locally Lipschitz on `Q_3`. -/
theorem ConvexOn.sourceOpenCube_locallyLipschitzOn {n : ℕ}
    {u : SourceCubeSpace n → ℝ} (hu : ConvexOn ℝ (sourceOpenCube n 3) u) :
    LocallyLipschitzOn (sourceOpenCube n 3) u :=
  hu.locallyLipschitzOn (isOpen_sourceOpenCube 3)

/-- Convexity on `Q_3` gives a global Lipschitz bound on the closed unit cube. -/
theorem ConvexOn.exists_lipschitzOnWith_sourceClosedCube_one {n : ℕ}
    {u : SourceCubeSpace n → ℝ} (hu : ConvexOn ℝ (sourceOpenCube n 3) u) :
    ∃ K, LipschitzOnWith K u (sourceClosedCube n 1) := by
  exact
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      (isCompact_sourceClosedCube (n := n) (r := 1) (by norm_num))
      ((ConvexOn.sourceOpenCube_locallyLipschitzOn hu).mono
        sourceClosedCube_one_subset_sourceOpenCube_three)

/-- Convexity on `Q_3` gives a global Lipschitz bound on `Q_1`. -/
theorem ConvexOn.exists_lipschitzOnWith_sourceOpenCube_one {n : ℕ}
    {u : SourceCubeSpace n → ℝ} (hu : ConvexOn ℝ (sourceOpenCube n 3) u) :
    ∃ K, LipschitzOnWith K u (sourceOpenCube n 1) := by
  rcases ConvexOn.exists_lipschitzOnWith_sourceClosedCube_one hu with ⟨K, hK⟩
  exact ⟨K, hK.mono sourceOpenCube_one_subset_sourceClosedCube_one⟩

/-- Convex functions on the source cube are differentiable almost everywhere on `Q_1`. -/
theorem ConvexOn.ae_differentiableAt_sourceOpenCube_one {n : ℕ}
    {u : SourceCubeSpace n → ℝ} (hu : ConvexOn ℝ (sourceOpenCube n 3) u) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)), DifferentiableAt ℝ u x := by
  rcases ConvexOn.exists_lipschitzOnWith_sourceOpenCube_one hu with ⟨K, hK⟩
  have hwithin :
      ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
        DifferentiableWithinAt ℝ u (sourceOpenCube n 1) x :=
    hK.ae_differentiableWithinAt (isOpen_sourceOpenCube (n := n) 1).measurableSet
  filter_upwards [hwithin,
    ae_restrict_mem (μ := volume) (isOpen_sourceOpenCube (n := n) 1).measurableSet] with x hx hxin
  exact hx.differentiableAt ((isOpen_sourceOpenCube (n := n) 1).mem_nhds hxin)

/-- The non-first-differentiability set in `Q_1` is null for convex functions on `Q_3`. -/
theorem ConvexOn.volume_sourceOpenCube_diff_firstOrderDifferentiabilitySet_eq_zero {n : ℕ}
    {u : SourceCubeSpace n → ℝ} (hu : ConvexOn ℝ (sourceOpenCube n 3) u) :
    volume (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) = 0 := by
  have hae := ConvexOn.ae_differentiableAt_sourceOpenCube_one hu
  rw [ae_iff] at hae
  have hmeas_bad : MeasurableSet {x : SourceCubeSpace n | ¬ DifferentiableAt ℝ u x} :=
    (measurableSet_of_differentiableAt (𝕜 := ℝ) (f := u)).compl
  have hrestrict :
      volume.restrict (sourceOpenCube n 1)
          {x : SourceCubeSpace n | ¬ DifferentiableAt ℝ u x} =
        volume ({x : SourceCubeSpace n | ¬ DifferentiableAt ℝ u x} ∩ sourceOpenCube n 1) := by
    exact Measure.restrict_apply hmeas_bad
  have hset :
      {x : SourceCubeSpace n | ¬ DifferentiableAt ℝ u x} ∩ sourceOpenCube n 1 =
        sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u := by
    ext x
    simp [firstOrderDifferentiabilitySet, and_comm]
  rwa [hrestrict, hset] at hae

end AleksandrovDifferentiability
