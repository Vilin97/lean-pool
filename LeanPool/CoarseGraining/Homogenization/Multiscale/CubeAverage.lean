/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicCube
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Cube Average -/

namespace Homogenization

open scoped BigOperators

noncomputable def cubeAverage {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) : ℝ :=
  (cubeVolume Q)⁻¹ * ∫ x in cubeSet Q, f x ∂MeasureTheory.volume

noncomputable def cubeAverageVec {d : ℕ} (Q : TriadicCube d) (f : Vec d → Vec d) : Vec d :=
  fun i => cubeAverage Q (fun x => f x i)

noncomputable def cubeAverageMat {d : ℕ} (Q : TriadicCube d) (f : Vec d → Mat d) : Mat d :=
  fun i j => cubeAverage Q (fun x => f x i j)

noncomputable def cubeProjection {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (f : Vec d → ℝ) : Vec d → ℝ := by
  classical
  exact fun x =>
    Finset.sum (descendantsAtDepth Q j) fun R =>
      if x ∈ cubeSet R then cubeAverage R f else 0

noncomputable def cubeIncrement {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (f : Vec d → ℝ) : Vec d → ℝ :=
  match j with
  | 0 => cubeProjection Q 0 f
  | n + 1 => fun x => cubeProjection Q (n + 1) f x - cubeProjection Q n f x

end Homogenization
