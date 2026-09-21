/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.LocalWeightedTail
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.ReflectionFiniteP

/-!
# Square-weighted tails under Dirichlet odd reflection

The global good-`λ` argument works with the squared-density measure
`‖f‖² dx`.  This file records that level tails of an odd-reflected
field on a centered parent cube are exactly `3^d` copies of the corresponding
tail on the source cube.
-/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

open MeasureTheory

private theorem lintegral_sqNorm_tail_inter_openCubeSet_eq
    {d : ℕ} {F : Vec d → HilbertVec d} {Q : TriadicCube d} {a : ℝ}
    (hF : AEStronglyMeasurable F (volume.restrict (openCubeSet Q))) :
    ∫⁻ x in {x | a < ‖F x‖} ∩ openCubeSet Q,
        ENNReal.ofReal (‖F x‖ ^ (2 : ℕ)) ∂volume =
      ∫⁻ x in openCubeSet Q,
        (if a < ‖F x‖ then ENNReal.ofReal (‖F x‖ ^ (2 : ℕ)) else 0)
          ∂volume := by
  let T : Set (Vec d) := {x | a < ‖F x‖}
  have hQ : MeasurableSet (openCubeSet Q) := measurableSet_openCubeSet Q
  have hTQ : NullMeasurableSet (T ∩ openCubeSet Q) volume := by
    apply (nullMeasurableSet_restrict hQ.nullMeasurableSet).mp
    simpa [T] using aestronglyMeasurable_const.nullMeasurableSet_lt hF.norm
  calc
    ∫⁻ x in {x | a < ‖F x‖} ∩ openCubeSet Q,
        ENNReal.ofReal (‖F x‖ ^ (2 : ℕ)) ∂volume =
      ∫⁻ x, (T ∩ openCubeSet Q).indicator
        (fun x => ENNReal.ofReal (‖F x‖ ^ (2 : ℕ))) x ∂volume := by
          simpa only [T] using
            (MeasureTheory.lintegral_indicator₀ hTQ
              (fun x => ENNReal.ofReal (‖F x‖ ^ (2 : ℕ)))).symm
    _ = ∫⁻ x, (openCubeSet Q).indicator
        (fun x => if a < ‖F x‖ then ENNReal.ofReal (‖F x‖ ^ (2 : ℕ)) else 0) x
          ∂volume := by
          congr 1
          funext x
          by_cases hxQ : x ∈ openCubeSet Q
          · by_cases hxT : x ∈ T
            · have hxTQ : x ∈ T ∩ openCubeSet Q := ⟨hxT, hxQ⟩
              rw [Set.indicator_of_mem hxTQ,
                Set.indicator_of_mem hxQ,
                if_pos (by simpa [T] using hxT)]
            · rw [Set.indicator_of_notMem (fun h => hxT h.1),
                Set.indicator_of_mem hxQ,
                if_neg (by simpa [T] using hxT)]
          · rw [Set.indicator_of_notMem (fun h => hxQ h.2),
              Set.indicator_of_notMem hxQ]
    _ = ∫⁻ x in openCubeSet Q,
        (if a < ‖F x‖ then ENNReal.ofReal (‖F x‖ ^ (2 : ℕ)) else 0)
          ∂volume := MeasureTheory.lintegral_indicator hQ _

/-- A square-weighted norm tail of the Dirichlet odd reflection on a centered
parent cube is exactly `3^d` copies of the source-cube tail. -/
theorem sqWeightedMeasure_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField_tail
    {d : ℕ} {m : ℤ} (G : Vec d → Vec d) {a : ℝ}
    (hG : AEStronglyMeasurable (fun x => HilbertVec.ofVec (G x))
      (volume.restrict (openCubeSet (originCube d m)))) :
    sqWeightedMeasure
        (fun x => HilbertVec.ofVec
          (cubeDirichletOddReflectionVectorField (originCube d m) G x)) volume
        ({x | a < ‖HilbertVec.ofVec
          (cubeDirichletOddReflectionVectorField (originCube d m) G x)‖} ∩
          openCubeSet (originCube d (m + 1))) =
      ((3 : ℝ≥0∞) ^ d) *
        sqWeightedMeasure (fun x => HilbertVec.ofVec (G x)) volume
          ({x | a < ‖HilbertVec.ofVec (G x)‖} ∩ openCubeSet (originCube d m)) := by
  let F : Vec d → HilbertVec d := fun x => HilbertVec.ofVec
    (cubeDirichletOddReflectionVectorField (originCube d m) G x)
  let S : Vec d → HilbertVec d := fun x => HilbertVec.ofVec (G x)
  let P : TriadicCube d := originCube d (m + 1)
  let Q : TriadicCube d := originCube d m
  let Φ : ℝ → ℝ≥0∞ := fun t =>
    if a < t then ENNReal.ofReal (t ^ (2 : ℕ)) else 0
  have hF : AEStronglyMeasurable F (volume.restrict (openCubeSet P)) := by
    simpa only [F, P, Q] using
      aestronglyMeasurable_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField
        hG
  have htailF : NullMeasurableSet ({x | a < ‖F x‖} ∩ openCubeSet P) volume := by
    apply (nullMeasurableSet_restrict (measurableSet_openCubeSet P).nullMeasurableSet).mp
    simpa using aestronglyMeasurable_const.nullMeasurableSet_lt hF.norm
  have htailS : NullMeasurableSet ({x | a < ‖S x‖} ∩ openCubeSet Q) volume := by
    apply (nullMeasurableSet_restrict (measurableSet_openCubeSet Q).nullMeasurableSet).mp
    simpa only [S, Q] using aestronglyMeasurable_const.nullMeasurableSet_lt hG.norm
  rw [sqWeightedMeasure_apply₀ F htailF, sqWeightedMeasure_apply₀ S htailS]
  calc
    ∫⁻ x in {x | a < ‖F x‖} ∩ openCubeSet P,
        ENNReal.ofReal (‖F x‖ ^ (2 : ℕ)) ∂volume =
      ∫⁻ x in openCubeSet P, Φ ‖F x‖ ∂volume := by
        simpa only [Φ] using lintegral_sqNorm_tail_inter_openCubeSet_eq hF
    _ = ((3 : ℝ≥0∞) ^ d) *
        ∫⁻ x in openCubeSet Q, Φ ‖S x‖ ∂volume := by
        simpa only [F, S, P, Q] using
          lintegral_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField_comp_norm
            G Φ
    _ = ((3 : ℝ≥0∞) ^ d) *
        ∫⁻ x in {x | a < ‖S x‖} ∩ openCubeSet Q,
          ENNReal.ofReal (‖S x‖ ^ (2 : ℕ)) ∂volume := by
        rw [lintegral_sqNorm_tail_inter_openCubeSet_eq hG]

end CubeCalderonZygmund

end

end Homogenization
