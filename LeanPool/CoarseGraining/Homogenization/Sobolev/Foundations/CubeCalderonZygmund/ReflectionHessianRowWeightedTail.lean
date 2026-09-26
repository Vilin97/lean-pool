/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ReflectionWeightedTail
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.ReflectionHessianRowFiniteP
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.Cutoff.Cube

/-!
# Square-weighted tails of reflected Hessian rows

The mixed-parity reflection of a Hessian row has the same pointwise Euclidean
norm as the ordinary odd reflection of the source row.  Consequently its
square-weighted level tail on an origin-cube parent is exactly the existing
odd-vector tail, with no new measure decomposition.
-/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

open MeasureTheory

/-- The square-weighted Hessian-row tail on a centered parent is exactly
`3^d` copies of its source-row tail. -/
theorem reflectedHessianRow_sqWeightedMeasure_parent_tail
    {d : ℕ} {m : ℤ} (i : Fin d) (R : Vec d → Vec d) {a : ℝ}
    (hR : AEStronglyMeasurable (fun x => HilbertVec.ofVec (R x))
      (volume.restrict (openCubeSet (originCube d m)))) :
    sqWeightedMeasure
        (fun x => HilbertVec.ofVec
          (cubeDirichletOddReflectionHessianRowVectorField
            (originCube d m) i R x)) volume
        ({x | a < ‖HilbertVec.ofVec
          (cubeDirichletOddReflectionHessianRowVectorField
            (originCube d m) i R x)‖} ∩
          openCubeSet (originCube d (m + 1))) =
      ((3 : ℝ≥0∞) ^ d) *
        sqWeightedMeasure (fun x => HilbertVec.ofVec (R x)) volume
          ({x | a < ‖HilbertVec.ofVec (R x)‖} ∩
            openCubeSet (originCube d m)) := by
  let Hrow : Vec d → HilbertVec d := fun x => HilbertVec.ofVec
    (cubeDirichletOddReflectionHessianRowVectorField
      (originCube d m) i R x)
  let Hodd : Vec d → HilbertVec d := fun x => HilbertVec.ofVec
    (cubeDirichletOddReflectionVectorField (originCube d m) R x)
  have hnorm : ∀ x, ‖Hrow x‖ = ‖Hodd x‖ := by
    intro x
    exact
      norm_hilbertVec_cubeDirichletOddReflectionHessianRowVectorField_eq_oddReflection
        (originCube d m) i R x
  have hmeasure :
      sqWeightedMeasure Hrow volume = sqWeightedMeasure Hodd volume := by
    apply MeasureTheory.withDensity_congr_ae
    filter_upwards with x
    rw [hnorm x]
  have htail :
      {x | a < ‖Hrow x‖} = {x | a < ‖Hodd x‖} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [hnorm x]
  change sqWeightedMeasure Hrow volume
      ({x | a < ‖Hrow x‖} ∩ openCubeSet (originCube d (m + 1))) = _
  rw [hmeasure, htail]
  exact
    sqWeightedMeasure_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField_tail
      R hR

/-- The Hessian-row tail on the half-scaled parent is bounded by the same
`3^d` source-row tail as the full reflected parent. -/
theorem reflectedHessianRow_sqWeightedMeasure_innerHalf_tail_le
    {d : ℕ} {m : ℤ} (i : Fin d) (R : Vec d → Vec d) {a : ℝ}
    (hR : AEStronglyMeasurable (fun x => HilbertVec.ofVec (R x))
      (volume.restrict (openCubeSet (originCube d m)))) :
    sqWeightedMeasure
        (fun x => HilbertVec.ofVec
          (cubeDirichletOddReflectionHessianRowVectorField
            (originCube d m) i R x)) volume
        ({x | a < ‖HilbertVec.ofVec
          (cubeDirichletOddReflectionHessianRowVectorField
            (originCube d m) i R x)‖} ∩
          scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ)) ≤
      ((3 : ℝ≥0∞) ^ d) *
        sqWeightedMeasure (fun x => HilbertVec.ofVec (R x)) volume
          ({x | a < ‖HilbertVec.ofVec (R x)‖} ∩
            openCubeSet (originCube d m)) := by
  let Qp : TriadicCube d := originCube d (m + 1)
  let Hrow : Vec d → HilbertVec d := fun x => HilbertVec.ofVec
    (cubeDirichletOddReflectionHessianRowVectorField
      (originCube d m) i R x)
  have hhalf : scaledOpenCubeSet Qp (1 / 2 : ℝ) ⊆ openCubeSet Qp := by
    intro x hx
    rw [← ball_cubeCenter_eq_openCubeSet]
    have hxclosed :
        x ∈ Metric.closedBall (cubeCenter Qp)
          ((1 / 2 : ℝ) * cubeRadius Qp) :=
      scaledClosedCubeSet_subset_metricClosedBall Qp
        (by norm_num : 0 ≤ (1 / 2 : ℝ)) (fun k => le_of_lt (hx k))
    exact Metric.closedBall_subset_ball (by
      nlinarith [cubeRadius_pos Qp]) hxclosed
  calc
    sqWeightedMeasure Hrow volume
        ({x | a < ‖Hrow x‖} ∩ scaledOpenCubeSet Qp (1 / 2 : ℝ)) ≤
        sqWeightedMeasure Hrow volume
          ({x | a < ‖Hrow x‖} ∩ openCubeSet Qp) := by
          exact measure_mono (Set.inter_subset_inter_right _ hhalf)
    _ = ((3 : ℝ≥0∞) ^ d) *
        sqWeightedMeasure (fun x => HilbertVec.ofVec (R x)) volume
          ({x | a < ‖HilbertVec.ofVec (R x)‖} ∩
            openCubeSet (originCube d m)) := by
          simpa only [Hrow, Qp] using
            reflectedHessianRow_sqWeightedMeasure_parent_tail
              i R hR

end CubeCalderonZygmund

end

end Homogenization
