/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.OverlapCenters
import LeanPool.CoarseGraining.Homogenization.Multiscale.NormalizedNorms

/-! # Overlap Lp -/

namespace Homogenization

namespace ScalarOverlap

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

/-- Average of a scalar field on an overlapping cube. -/
noncomputable def cubeAverage {d : ℕ}
    (S : TriadicCube d) (f : Vec d → ℝ) : ℝ :=
  (cubeVolume S)⁻¹ *
    ∫ x in cubeSet S, f x ∂volume

/-- Coordinatewise average of a vector field on an overlapping cube. -/
noncomputable def cubeAverageVec {d : ℕ}
    (S : TriadicCube d) (u : Vec d → Vec d) : Vec d :=
  fun i => cubeAverage S fun x => u x i

/-- Normalized `L^p` norm on an overlapping cube. -/
noncomputable def cubeLpNorm {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (S : TriadicCube d) (p : ℝ≥0∞)
    (u : Vec d → E) : ℝ :=
  (MeasureTheory.eLpNorm u p (normalizedCubeMeasure S)).toReal

theorem cubeAverage_eq_integral_normalizedCubeMeasure {d : ℕ}
    (S : TriadicCube d) (f : Vec d → ℝ) :
    cubeAverage S f = ∫ x, f x ∂ normalizedCubeMeasure S := by
  rw [cubeAverage, normalizedCubeMeasure, cubeMeasure,
    MeasureTheory.integral_smul_measure]
  simp [smul_eq_mul, ENNReal.toReal_ofReal, inv_nonneg, cubeVolume_nonneg]

@[simp] theorem cubeMeasure_middleChildCube {d : ℕ}
    (Q : TriadicCube d) :
    cubeMeasure (middleChildCube Q) = Homogenization.cubeMeasure Q := by
  rw [cubeMeasure, Homogenization.cubeMeasure, cubeSet_middleChildCube_eq_cubeSet]

@[simp] theorem normalizedCubeMeasure_middleChildCube {d : ℕ}
    (Q : TriadicCube d) :
    normalizedCubeMeasure (middleChildCube Q) =
      Homogenization.normalizedCubeMeasure Q := by
  rw [normalizedCubeMeasure, Homogenization.normalizedCubeMeasure]
  simp

@[simp] theorem cubeAverage_middleChildCube {d : ℕ}
    (Q : TriadicCube d) (f : Vec d → ℝ) :
    cubeAverage (middleChildCube Q) f = Homogenization.cubeAverage Q f := by
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    Homogenization.cubeAverage_eq_integral_normalizedCubeMeasure]
  simp

theorem cubeAverage_congr_on_cubeSet {d : ℕ}
    {S : TriadicCube d} {u v : Vec d → ℝ}
    (h : ∀ x ∈ cubeSet S, u x = v x) :
    cubeAverage S u = cubeAverage S v := by
  unfold cubeAverage
  refine congrArg (fun t : ℝ => (cubeVolume S)⁻¹ * t) ?_
  apply MeasureTheory.integral_congr_ae
  exact (MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet S)).2 <|
    Filter.Eventually.of_forall h

theorem cubeLpNorm_congr_on_cubeSet_generic {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (S : TriadicCube d) (p : ℝ≥0∞)
    {u v : Vec d → E} (h : ∀ x ∈ cubeSet S, u x = v x) :
    cubeLpNorm S p u = cubeLpNorm S p v := by
  unfold cubeLpNorm
  rw [MeasureTheory.eLpNorm_congr_ae]
  rw [normalizedCubeMeasure, cubeMeasure, Filter.EventuallyEq]
  exact MeasureTheory.Measure.ae_smul_measure
    ((MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet S)).2 <|
      Filter.Eventually.of_forall h)
    (ENNReal.ofReal ((cubeVolume S)⁻¹))

@[simp] theorem cubeAverage_const {d : ℕ}
    (S : TriadicCube d) (c : ℝ) :
    cubeAverage S (fun _ : Vec d => c) = c := by
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    MeasureTheory.integral_const]
  simp [MeasureTheory.Measure.real, normalizedCubeMeasure_apply_univ]

@[simp] theorem cubeAverageVec_const {d : ℕ}
    (S : TriadicCube d) (c : Vec d) :
    cubeAverageVec S (fun _ : Vec d => c) = c := by
  funext i
  simp [cubeAverageVec]

theorem cubeLpNorm_nonneg {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (S : TriadicCube d) (p : ℝ≥0∞) (f : Vec d → E) :
    0 ≤ cubeLpNorm S p f :=
  ENNReal.toReal_nonneg

@[simp] theorem cubeLpNorm_middleChildCube {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (Q : TriadicCube d) (p : ℝ≥0∞)
    (u : Vec d → E) :
    cubeLpNorm (middleChildCube Q) p u = Homogenization.cubeLpNorm Q p u := by
  unfold cubeLpNorm Homogenization.cubeLpNorm
  simp

theorem cubeLpNorm_const {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (S : TriadicCube d) (p : ℝ≥0∞) (c : E) (hp : p ≠ 0) :
    cubeLpNorm S p (fun _ => c) = ‖c‖ := by
  unfold cubeLpNorm
  rw [MeasureTheory.eLpNorm_const c hp (normalizedCubeMeasure_ne_zero S),
    normalizedCubeMeasure_apply_univ]
  simp

theorem cubeLpNorm_zero {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (S : TriadicCube d) (p : ℝ≥0∞) (hp : p ≠ 0) :
    cubeLpNorm S p (fun _ : Vec d => (0 : E)) = 0 := by
  simpa using cubeLpNorm_const (S := S) (p := p) (c := (0 : E)) hp

end

end ScalarOverlap

end Homogenization
