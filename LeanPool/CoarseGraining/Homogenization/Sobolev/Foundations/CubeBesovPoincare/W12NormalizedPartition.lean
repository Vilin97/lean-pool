/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Duality.ProjectionLimit
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.MultiscaleEllipticity
import LeanPool.CoarseGraining.Homogenization.Geometry.BoundedConvexDomain
import LeanPool.CoarseGraining.Homogenization.Multiscale.NormalizedDomainCube
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.BasicLemmas
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.Normalized

/-!
# Normalized `W^{1,2}` data on triadic cubes

This small bridge keeps the source-facing open-cube Sobolev carrier while
identifying its normalized volume with the cube normalization used by the
disjoint Besov hierarchy.
-/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace W1pFunction

/-- Restrict a Sobolev witness on an open triadic cube to one of its open
descendants.  Both its function and stored weak-gradient representatives are
unchanged. -/
def restrictToOpenSubcube {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    {p : ℝ≥0∞} (u : W1pFunction (openCubeSet Q) p)
    (hR : R ∈ descendantsAtDepth Q j) : W1pFunction (openCubeSet R) p :=
  u.restrict (isOpen_openCubeSet R)
    (openCubeSet_subset_of_mem_descendantsAtDepth hR)

@[simp] theorem restrictToOpenSubcube_toFun {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    {p : ℝ≥0∞} (u : W1pFunction (openCubeSet Q) p)
    (hR : R ∈ descendantsAtDepth Q j) :
    (u.restrictToOpenSubcube hR).toFun = u.toFun :=
  rfl

@[simp] theorem restrictToOpenSubcube_grad {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    {p : ℝ≥0∞} (u : W1pFunction (openCubeSet Q) p)
    (hR : R ∈ descendantsAtDepth Q j) :
    (u.restrictToOpenSubcube hR).grad = u.grad :=
  rfl

end W1pFunction

/-- The normalized measure of the source-facing open cube is exactly the
normalized cube measure.  This is a measure equality, not a pointwise carrier
identification. -/
theorem openCubeSet_boundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure
    {d : ℕ} (Q : TriadicCube d) :
    ((isOpenBoundedConvexDomain_openCubeSet Q).toBoundedMeasurableDomain
      (Book.Ch02.openCubeSet_nonempty Q)).normalizedVolume = normalizedCubeMeasure Q := by
  change (MeasureTheory.volume (openCubeSet Q))⁻¹ •
      MeasureTheory.volume.restrict (openCubeSet Q) = normalizedCubeMeasure Q
  rw [volume_openCubeSet_eq_volume_cubeSet,
    ← cubeBoundedMeasurableDomain_restrictedVolume_eq_restrict_openCubeSet]
  exact cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure Q

/-- The exact source-facing normalized `W^{1,2}` seminorm on an open cube is
the normalized cube `L²` norm of the explicit Euclidean gradient magnitude. -/
theorem openCubeSet_normalizedW1pSeminorm_two_eq_cubeLpNorm_euclideanGrad
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (u : W1pFunction (openCubeSet Q) (2 : ℝ≥0∞)) :
    BoundedMeasurableDomain.NormalizedW1pKernel.seminorm
        ((isOpenBoundedConvexDomain_openCubeSet Q).toBoundedMeasurableDomain
          (Book.Ch02.openCubeSet_nonempty Q))
        (2 : ℝ≥0∞) (by norm_num) (by norm_num) u =
      cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x)) := by
  change (MeasureTheory.eLpNorm (fun x => euclideanNorm (u.grad x))
      (2 : ℝ≥0∞)
      ((isOpenBoundedConvexDomain_openCubeSet Q).toBoundedMeasurableDomain
        (Book.Ch02.openCubeSet_nonempty Q)).normalizedVolume).toReal =
    (MeasureTheory.eLpNorm (fun x => euclideanNorm (u.grad x))
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q)).toReal
  exact congrArg ENNReal.toReal
    (openCubeSet_boundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure Q ▸ rfl)

/-- Normalized `L²` energy partitions exactly over descendants.  This is the
measure-theoretic ingredient needed to aggregate the restricted open-cube
Sobolev seminorms. -/
theorem descendantsAverage_cubeLpNorm_euclideanGrad_two_sq_eq
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (u : W1pFunction (openCubeSet Q) (2 : ℝ≥0∞)) (j : ℕ) :
    descendantsAverage Q j
      (fun R => cubeLpNorm R (2 : ℝ≥0∞)
        (fun x => euclideanNorm (u.grad x)) ^ 2) =
      cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x)) ^ 2 := by
  let UQ : BoundedMeasurableDomain d :=
    (isOpenBoundedConvexDomain_openCubeSet Q).toBoundedMeasurableDomain
      (Book.Ch02.openCubeSet_nonempty Q)
  have hmemU : MeasureTheory.MemLp (fun x => euclideanNorm (u.grad x))
      (2 : ℝ≥0∞) UQ.normalizedVolume :=
    u.gradEuclideanMemLp UQ (2 : ℝ≥0∞)
  have hmem : MeasureTheory.MemLp (fun x => euclideanNorm (u.grad x))
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa only [UQ,
      openCubeSet_boundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
      using hmemU
  have hint : MeasureTheory.IntegrableOn
      (fun x => ‖euclideanNorm (u.grad x)‖ ^ (2 : ℝ))
      (cubeSet Q) MeasureTheory.volume := by
    exact integrableOn_of_integrable_normalizedCubeMeasure Q
      (hmem.integrable_norm_rpow (by norm_num) (by norm_num))
  calc
    descendantsAverage Q j
        (fun R => cubeLpNorm R (2 : ℝ≥0∞)
          (fun x => euclideanNorm (u.grad x)) ^ 2)
        = descendantsAverage Q j
            (fun R => cubeAverage R
              (fun x => ‖euclideanNorm (u.grad x)‖ ^ (2 : ℝ))) := by
              unfold descendantsAverage
              refine congrArg (fun t : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
              refine Finset.sum_congr rfl ?_
              intro R hR
              simpa using
                (cubeLpNorm_rpow_eq_cubeAverage_norm_rpow
                  (Q := R) (p := (2 : ℝ≥0∞))
                  (f := fun x => euclideanNorm (u.grad x))
                  (by norm_num) (by norm_num)
                  (memLp_on_descendant_of_memLp hR hmem))
    _ = cubeAverage Q (fun x => ‖euclideanNorm (u.grad x)‖ ^ (2 : ℝ)) := by
      rw [← cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q j _ hint]
    _ = cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x)) ^ 2 := by
      symm
      simpa using
        (cubeLpNorm_rpow_eq_cubeAverage_norm_rpow
          (Q := Q) (p := (2 : ℝ≥0∞))
          (f := fun x => euclideanNorm (u.grad x))
          (by norm_num) (by norm_num) hmem)

/-- The source-facing normalized Sobolev seminorm of a descendant.  The zero
value off the finite descendant family makes this a total function of a cube,
as required by `descendantsAverage`; it is never used on that off-family
branch. -/
noncomputable def descendantOpenCubeSetNormalizedW1pSeminormTwo
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (u : W1pFunction (openCubeSet Q) (2 : ℝ≥0∞)) (j : ℕ)
    (R : TriadicCube d) : ℝ :=
  if hR : R ∈ descendantsAtDepth Q j then
    BoundedMeasurableDomain.NormalizedW1pKernel.seminorm
      ((isOpenBoundedConvexDomain_openCubeSet R).toBoundedMeasurableDomain
        (Book.Ch02.openCubeSet_nonempty R))
      (2 : ℝ≥0∞) (by norm_num) (by norm_num)
      (u.restrictToOpenSubcube hR)
  else 0

/-- On an actual descendant, the totalized seminorm is the literal
source-facing seminorm of the restricted Sobolev witness. -/
theorem descendantOpenCubeSetNormalizedW1pSeminormTwo_eq_of_mem
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (u : W1pFunction (openCubeSet Q) (2 : ℝ≥0∞)) (j : ℕ)
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth Q j) :
    descendantOpenCubeSetNormalizedW1pSeminormTwo Q u j R =
      BoundedMeasurableDomain.NormalizedW1pKernel.seminorm
        ((isOpenBoundedConvexDomain_openCubeSet R).toBoundedMeasurableDomain
          (Book.Ch02.openCubeSet_nonempty R))
        (2 : ℝ≥0∞) (by norm_num) (by norm_num)
        (u.restrictToOpenSubcube hR) := by
  simp only [descendantOpenCubeSetNormalizedW1pSeminormTwo, dif_pos hR]

/-- The exact source-facing normalized Sobolev energy partitions over the
open descendants of a triadic cube. -/
theorem descendantsAverage_openCubeSet_normalizedW1pSeminorm_two_sq_eq
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (u : W1pFunction (openCubeSet Q) (2 : ℝ≥0∞)) (j : ℕ) :
    descendantsAverage Q j
      (fun R => descendantOpenCubeSetNormalizedW1pSeminormTwo Q u j R ^ 2) =
      BoundedMeasurableDomain.NormalizedW1pKernel.seminorm
        ((isOpenBoundedConvexDomain_openCubeSet Q).toBoundedMeasurableDomain
          (Book.Ch02.openCubeSet_nonempty Q))
        (2 : ℝ≥0∞) (by norm_num) (by norm_num) u ^ 2 := by
  calc
    descendantsAverage Q j
        (fun R => descendantOpenCubeSetNormalizedW1pSeminormTwo Q u j R ^ 2)
        = descendantsAverage Q j
            (fun R => cubeLpNorm R (2 : ℝ≥0∞)
              (fun x => euclideanNorm (u.grad x)) ^ 2) := by
          unfold descendantsAverage
          refine congrArg (fun t : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
          refine Finset.sum_congr rfl ?_
          intro R hR
          rw [descendantOpenCubeSetNormalizedW1pSeminormTwo_eq_of_mem Q u j hR]
          rw [openCubeSet_normalizedW1pSeminorm_two_eq_cubeLpNorm_euclideanGrad
            R (u.restrictToOpenSubcube hR)]
          simp
    _ = cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x)) ^ 2 :=
      descendantsAverage_cubeLpNorm_euclideanGrad_two_sq_eq Q u j
    _ = BoundedMeasurableDomain.NormalizedW1pKernel.seminorm
        ((isOpenBoundedConvexDomain_openCubeSet Q).toBoundedMeasurableDomain
          (Book.Ch02.openCubeSet_nonempty Q))
        (2 : ℝ≥0∞) (by norm_num) (by norm_num) u ^ 2 := by
      rw [openCubeSet_normalizedW1pSeminorm_two_eq_cubeLpNorm_euclideanGrad Q u]

end

end Homogenization
