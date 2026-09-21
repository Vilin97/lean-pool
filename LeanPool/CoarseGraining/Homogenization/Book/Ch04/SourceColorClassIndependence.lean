/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceIndependence
import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMeasure
import LeanPool.CoarseGraining.Homogenization.Geometry.ScaleColoring

/-!
# Independence of source-local observables on a scale-color class

This is the source-carrier counterpart of the scale-color-class independence
specialization.  Its metric bridge is kept local: the coloring separates cubes
in the ambient sup metric, while source P2 is formulated with the Euclidean
metric.
-/

namespace Homogenization.Book.Ch04

open MeasureTheory ProbabilityTheory

private theorem ambient_norm_le_source_euclideanNorm {d : ℕ} (z : Vec d) :
    ‖z‖ ≤ euclideanNorm z := by
  rw [euclideanNorm_eq_norm_ofVec]
  rw [EuclideanSpace.norm_eq]
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
  intro i
  apply (Real.le_sqrt (norm_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)).2
  exact Finset.single_le_sum (s := Finset.univ) (f := fun i : Fin d => ‖z i‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

private theorem euclideanUnitSeparated_scaleColorClass {d : ℕ}
    {Q R S : TriadicCube d} {k : ℤ} {c : ScaleColor d k}
    (hR : R ∈ descendantsAtScaleScaleColorClass Q k c)
    (hS : S ∈ descendantsAtScaleScaleColorClass Q k c) (hneq : R ≠ S) :
    Source.Coarse.EuclideanUnitSeparated (cubeSet R) (cubeSet S) := by
  intro x y hx hy
  unfold euclideanDist
  have hdist : 1 ≤ dist x y :=
    one_le_dist_of_ne_of_mem_descendantsAtScaleScaleColorClass hR hS hneq hx hy
  have hnorm : 1 ≤ ‖x - y‖ := by
    simpa [dist_eq_norm] using hdist
  exact hnorm.trans (ambient_norm_le_source_euclideanNorm (x - y))

/-- Source-local observables indexed by one scale-color class are independent
under source unit-range dependence. -/
theorem iIndepFun_descendantsAtScaleScaleColorClass_of_sourceUnitRangeDependentLaw
    {d : ℕ} {Q : TriadicCube d} {k : ℤ} {c : ScaleColor d k}
    {P : SourceCoeffLaw d} [IsProbabilityMeasure P]
    {β : {R : TriadicCube d // R ∈ descendantsAtScaleScaleColorClass Q k c} → Type*}
    [∀ R, MeasurableSpace (β R)]
    {X : ∀ R, Source.Coarse.Carrier d → β R}
    (hP : SourceUnitRangeDependentLaw P)
    (hX : ∀ R,
      IsSourceLocalRandomVariable (cubeSet R.1) (measurableSet_cubeSet R.1) (X R)) :
    iIndepFun X P := by
  classical
  let I : Type := {R : TriadicCube d // R ∈ descendantsAtScaleScaleColorClass Q k c}
  let U : I → Set (Vec d) := fun R => cubeSet R.1
  have hU : ∀ R : I, MeasurableSet (U R) := fun R => measurableSet_cubeSet R.1
  have hXU : ∀ R : I, IsSourceLocalRandomVariable (U R) (hU R) (X R) := by
    intro R
    simpa [I, U] using hX R
  have hsep : Pairwise fun R S : I =>
      Source.Coarse.EuclideanUnitSeparated (U R) (U S) := by
    intro R S hRS
    exact euclideanUnitSeparated_scaleColorClass R.2 S.2
      (fun h => hRS (Subtype.ext h))
  simpa [I, U] using
    (iIndepFun_of_sourceLocalRandomVariable_of_sourceUnitRangeDependentLaw
      (d := d) (ι := I) (U := U) hU hP hXU hsep)

end Homogenization.Book.Ch04
