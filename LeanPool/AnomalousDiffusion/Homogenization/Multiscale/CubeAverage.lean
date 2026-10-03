/-
Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Tuomo Kuusi
-/
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.

module

public import LeanPool.AnomalousDiffusion.Homogenization.Geometry.TriadicCube
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Cube Average

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

namespace Homogenization

open scoped BigOperators

/-- Scalar integral average over a triadic cube. -/
noncomputable def cubeAverage {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) : ℝ :=
  (cubeVolume Q)⁻¹ * ∫ x in cubeSet Q, f x ∂MeasureTheory.volume

/-- Componentwise vector average over a triadic cube. -/
noncomputable def cubeAverageVec {d : ℕ} (Q : TriadicCube d) (f : Vec d → Vec d) : Vec d :=
  fun i => cubeAverage Q (fun x => f x i)

/-- Entrywise matrix average over a triadic cube. -/
noncomputable def cubeAverageMat {d : ℕ} (Q : TriadicCube d) (f : Vec d → Mat d) : Mat d :=
  fun i j => cubeAverage Q (fun x => f x i j)

/-- Piecewise constant projection onto averages on depth-j triadic descendants. -/
noncomputable def cubeProjection {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (f : Vec d → ℝ) : Vec d → ℝ := by
  classical
  exact fun x =>
    Finset.sum (descendantsAtDepth Q j) fun R =>
      if x ∈ cubeSet R then cubeAverage R f else 0

/-- Difference between successive triadic average projections, starting with the coarse
projection. -/
noncomputable def cubeIncrement {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (f : Vec d → ℝ) : Vec d → ℝ :=
  match j with
  | 0 => cubeProjection Q 0 f
  | n + 1 => fun x => cubeProjection Q (n + 1) f x - cubeProjection Q n f x

end Homogenization
