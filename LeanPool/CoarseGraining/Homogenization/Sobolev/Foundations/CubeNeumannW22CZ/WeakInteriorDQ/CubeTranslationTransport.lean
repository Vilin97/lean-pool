/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicCubeTranslation
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubePoisson.Solver

/-! # Cube Translation Transport -/

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

theorem cubeVolume_originCube_same_scale {d : ℕ} (Q : TriadicCube d) :
    cubeVolume (originCube d Q.scale) = cubeVolume Q := by
  simp [cubeVolume, cubeScaleFactor, originCube]

theorem cubeMeasure_originCube_map_addRight_eq {d : ℕ} (Q : TriadicCube d) :
    Measure.map (fun x : Vec d => x + triadicCubeShift Q)
        (cubeMeasure (originCube d Q.scale)) =
      cubeMeasure Q := by
  have hmp :=
    measurePreserving_addRight_restrict_translateSet
      (d := d) (triadicCubeShift Q) (cubeSet (originCube d Q.scale))
  unfold cubeMeasure
  rw [cubeSet_eq_translateSet_originCube_of_triadicCube Q]
  exact hmp.map_eq

theorem normalizedCubeMeasure_originCube_map_addRight_eq {d : ℕ}
    (Q : TriadicCube d) :
    Measure.map (fun x : Vec d => x + triadicCubeShift Q)
        (normalizedCubeMeasure (originCube d Q.scale)) =
      normalizedCubeMeasure Q := by
  unfold normalizedCubeMeasure
  rw [Measure.map_smul _ (f := fun x : Vec d => x + triadicCubeShift Q)
    (measurable_id.add measurable_const).aemeasurable,
    cubeMeasure_originCube_map_addRight_eq Q,
    cubeVolume_originCube_same_scale Q]

theorem measurePreserving_addRight_normalizedCubeMeasure_originCube {d : ℕ}
    (Q : TriadicCube d) :
    MeasurePreserving (fun x : Vec d => x + triadicCubeShift Q)
      (normalizedCubeMeasure (originCube d Q.scale))
      (normalizedCubeMeasure Q) :=
  ⟨measurable_id.add measurable_const,
    normalizedCubeMeasure_originCube_map_addRight_eq Q⟩

theorem memLp_originCube_comp_addRight_of_memLp {d : ℕ}
    (Q : TriadicCube d) {p : ℝ≥0∞} {F : Vec d → ℝ}
    (hF : MemLp F p (normalizedCubeMeasure Q)) :
    MemLp (fun x => F (x + triadicCubeShift Q)) p
      (normalizedCubeMeasure (originCube d Q.scale)) :=
  hF.comp_measurePreserving
    (measurePreserving_addRight_normalizedCubeMeasure_originCube Q)

theorem cubeLpNorm_originCube_comp_addRight_eq_of_memLp {d : ℕ}
    (Q : TriadicCube d) {F : Vec d → ℝ}
    (hF : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeLpNorm (originCube d Q.scale) (2 : ℝ≥0∞)
        (fun x => F (x + triadicCubeShift Q)) =
      cubeLpNorm Q (2 : ℝ≥0∞) F := by
  rw [cubeLpNorm_eq_eLpNorm_toReal _ _ _
      (memLp_originCube_comp_addRight_of_memLp Q hF).aestronglyMeasurable,
    cubeLpNorm_eq_eLpNorm_toReal _ _ _ hF.aestronglyMeasurable]
  exact congrArg ENNReal.toReal (by
    simpa [Function.comp] using!
      (MeasureTheory.eLpNorm_comp_measurePreserving
        (g := F) (p := (2 : ℝ≥0∞)) hF.aestronglyMeasurable
        (measurePreserving_addRight_normalizedCubeMeasure_originCube Q)))

theorem cubeAverage_originCube_comp_addRight_eq {d : ℕ}
    (Q : TriadicCube d) (F : Vec d → ℝ) :
    cubeAverage (originCube d Q.scale) (fun x => F (x + triadicCubeShift Q)) =
      cubeAverage Q F := by
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  exact
    (measurePreserving_addRight_normalizedCubeMeasure_originCube Q).integral_comp
      (Homeomorph.addRight (triadicCubeShift Q)).measurableEmbedding F

end

end Homogenization
