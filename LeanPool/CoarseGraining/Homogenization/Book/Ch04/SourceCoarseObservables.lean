/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceMu
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Internal.CoarseObservableMeasurability.Basic
public import LeanPool.CoarseGraining.Homogenization.Besov.Basic

/-!
# Exact-source coarse observables

The coarse block entries are finite polarizations of the exact source-local
`Mu` observable.  This module packages those deterministic consequences in
the coarse source local sigma algebra.
-/

@[expose] public section

namespace Homogenization.Book.Ch04

open MeasureTheory

noncomputable section

/-- The upper-left entry of the coarse block matrix is exact-source local. -/
theorem isSourceLocalRandomVariable_coarseBlockMatrix_upperLeft_apply_cubeSet
    {d : ℕ} (Q : TriadicCube d) (i j : Fin d) :
    IsSourceLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q)
      (fun a : Source.Coarse.Carrier d =>
        (coarseBlockMatrix (cubeSet Q) a.1).upperLeft i j) := by
  by_cases hij : i = j
  · subst j
    have hmu := (SourceObservable.mu Q (Pi.single i 1, 0)).isLocal
    have hEq :
        (fun a : Source.Coarse.Carrier d =>
          (coarseBlockMatrix (cubeSet Q) a.1).upperLeft i i) =
          fun a => (2 : ℝ) * Mu (cubeSet Q) (Pi.single i 1, 0) a.1 := by
      funext a
      simp [coarseBlockMatrix_upperLeft_apply]
    rw [hEq]
    exact measurable_const.mul hmu
  · have hsum := (SourceObservable.mu Q
      ((Pi.single i 1, 0) + (Pi.single j 1, 0))
      ).isLocal
    have hi := (SourceObservable.mu Q (Pi.single i 1, 0)).isLocal
    have hj := (SourceObservable.mu Q (Pi.single j 1, 0)).isLocal
    have hEq :
        (fun a : Source.Coarse.Carrier d =>
          (coarseBlockMatrix (cubeSet Q) a.1).upperLeft i j) =
          fun a =>
            Mu (cubeSet Q) ((Pi.single i 1, 0) + (Pi.single j 1, 0)) a.1
              - Mu (cubeSet Q) (Pi.single i 1, 0) a.1
              - Mu (cubeSet Q) (Pi.single j 1, 0) a.1 := by
      funext a
      simp [coarseBlockMatrix_upperLeft_apply, hij]
    rw [hEq]
    exact (hsum.sub hi).sub hj

/-- The upper-right entry of the coarse block matrix is exact-source local. -/
theorem isSourceLocalRandomVariable_coarseBlockMatrix_upperRight_apply_cubeSet
    {d : ℕ} (Q : TriadicCube d) (i j : Fin d) :
    IsSourceLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q)
      (fun a : Source.Coarse.Carrier d =>
        (coarseBlockMatrix (cubeSet Q) a.1).upperRight i j) := by
  have hsum := (SourceObservable.mu Q
    ((Pi.single i 1, 0) + (0, Pi.single j 1))).isLocal
  have hi := (SourceObservable.mu Q (Pi.single i 1, 0)).isLocal
  have hj := (SourceObservable.mu Q (0, Pi.single j 1)).isLocal
  have hEq :
      (fun a : Source.Coarse.Carrier d =>
        (coarseBlockMatrix (cubeSet Q) a.1).upperRight i j) =
        fun a =>
          Mu (cubeSet Q) ((Pi.single i 1, 0) + (0, Pi.single j 1)) a.1
            - Mu (cubeSet Q) (Pi.single i 1, 0) a.1
            - Mu (cubeSet Q) (0, Pi.single j 1) a.1 := by
    funext a
    exact coarseBlockMatrix_upperRight_apply (cubeSet Q) a.1 i j
  rw [hEq]
  exact (hsum.sub hi).sub hj

/-- The lower-left entry of the coarse block matrix is exact-source local. -/
theorem isSourceLocalRandomVariable_coarseBlockMatrix_lowerLeft_apply_cubeSet
    {d : ℕ} (Q : TriadicCube d) (i j : Fin d) :
    IsSourceLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q)
      (fun a : Source.Coarse.Carrier d =>
        (coarseBlockMatrix (cubeSet Q) a.1).lowerLeft i j) := by
  have hsum := (SourceObservable.mu Q
    ((0, Pi.single i 1) + (Pi.single j 1, 0))).isLocal
  have hi := (SourceObservable.mu Q (0, Pi.single i 1)).isLocal
  have hj := (SourceObservable.mu Q (Pi.single j 1, 0)).isLocal
  have hEq :
      (fun a : Source.Coarse.Carrier d =>
        (coarseBlockMatrix (cubeSet Q) a.1).lowerLeft i j) =
        fun a =>
          Mu (cubeSet Q) ((0, Pi.single i 1) + (Pi.single j 1, 0)) a.1
            - Mu (cubeSet Q) (0, Pi.single i 1) a.1
            - Mu (cubeSet Q) (Pi.single j 1, 0) a.1 := by
    funext a
    exact coarseBlockMatrix_lowerLeft_apply (cubeSet Q) a.1 i j
  rw [hEq]
  exact (hsum.sub hi).sub hj

/-- The lower-right entry of the coarse block matrix is exact-source local. -/
theorem isSourceLocalRandomVariable_coarseBlockMatrix_lowerRight_apply_cubeSet
    {d : ℕ} (Q : TriadicCube d) (i j : Fin d) :
    IsSourceLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q)
      (fun a : Source.Coarse.Carrier d =>
        (coarseBlockMatrix (cubeSet Q) a.1).lowerRight i j) := by
  by_cases hij : i = j
  · subst j
    have hmu := (SourceObservable.mu Q (0, Pi.single i 1)).isLocal
    have hEq :
        (fun a : Source.Coarse.Carrier d =>
          (coarseBlockMatrix (cubeSet Q) a.1).lowerRight i i) =
          fun a => (2 : ℝ) * Mu (cubeSet Q) (0, Pi.single i 1) a.1 := by
      funext a
      simp [coarseBlockMatrix_lowerRight_apply]
    rw [hEq]
    exact measurable_const.mul hmu
  · have hsum := (SourceObservable.mu Q
      ((0, Pi.single i 1) + (0, Pi.single j 1))).isLocal
    have hi := (SourceObservable.mu Q (0, Pi.single i 1)).isLocal
    have hj := (SourceObservable.mu Q (0, Pi.single j 1)).isLocal
    have hEq :
        (fun a : Source.Coarse.Carrier d =>
          (coarseBlockMatrix (cubeSet Q) a.1).lowerRight i j) =
          fun a =>
            Mu (cubeSet Q) ((0, Pi.single i 1) + (0, Pi.single j 1)) a.1
              - Mu (cubeSet Q) (0, Pi.single i 1) a.1
              - Mu (cubeSet Q) (0, Pi.single j 1) a.1 := by
      funext a
      simp [coarseBlockMatrix_lowerRight_apply, hij]
    rw [hEq]
    exact (hsum.sub hi).sub hj

/-- The unfolded full coarse block matrix is exact-source local. -/
theorem isSourceLocalRandomVariable_toFullBlockMat_coarseBlockMatrix_cubeSet
    {d : ℕ} (Q : TriadicCube d) :
    IsSourceLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q)
      (fun a : Source.Coarse.Carrier d =>
        toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.1)) := by
  let : MeasurableSpace (Source.Coarse.Carrier d) :=
    Source.Coarse.localSigma (cubeSet Q) (measurableSet_cubeSet Q)
  change @Measurable (Source.Coarse.Carrier d) (FullBlockMat d)
    (Source.Coarse.localSigma (cubeSet Q) (measurableSet_cubeSet Q)) _ _
  refine measurable_pi_iff.2 fun x => ?_
  refine measurable_pi_iff.2 fun y => ?_
  cases x with
  | inl i =>
      cases y with
      | inl j =>
          exact isSourceLocalRandomVariable_coarseBlockMatrix_upperLeft_apply_cubeSet Q i j
      | inr j =>
          exact isSourceLocalRandomVariable_coarseBlockMatrix_upperRight_apply_cubeSet Q i j
  | inr i =>
      cases y with
      | inl j =>
          exact isSourceLocalRandomVariable_coarseBlockMatrix_lowerLeft_apply_cubeSet Q i j
      | inr j =>
          exact isSourceLocalRandomVariable_coarseBlockMatrix_lowerRight_apply_cubeSet Q i j

/-- The upper-left coarse block is exact-source local. -/
theorem isSourceLocalRandomVariable_coarseBlockMatrix_upperLeft_cubeSet
    {d : ℕ} (Q : TriadicCube d) :
    IsSourceLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q)
      (fun a : Source.Coarse.Carrier d =>
        (coarseBlockMatrix (cubeSet Q) a.1).upperLeft) :=
  IsSourceLocalRandomVariable.mat_of_entries fun i j =>
    isSourceLocalRandomVariable_coarseBlockMatrix_upperLeft_apply_cubeSet Q i j

/-- The upper-right coarse block is exact-source local. -/
theorem isSourceLocalRandomVariable_coarseBlockMatrix_upperRight_cubeSet
    {d : ℕ} (Q : TriadicCube d) :
    IsSourceLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q)
      (fun a : Source.Coarse.Carrier d =>
        (coarseBlockMatrix (cubeSet Q) a.1).upperRight) :=
  IsSourceLocalRandomVariable.mat_of_entries fun i j =>
    isSourceLocalRandomVariable_coarseBlockMatrix_upperRight_apply_cubeSet Q i j

/-- The lower-left coarse block is exact-source local. -/
theorem isSourceLocalRandomVariable_coarseBlockMatrix_lowerLeft_cubeSet
    {d : ℕ} (Q : TriadicCube d) :
    IsSourceLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q)
      (fun a : Source.Coarse.Carrier d =>
        (coarseBlockMatrix (cubeSet Q) a.1).lowerLeft) :=
  IsSourceLocalRandomVariable.mat_of_entries fun i j =>
    isSourceLocalRandomVariable_coarseBlockMatrix_lowerLeft_apply_cubeSet Q i j

/-- The lower-right coarse block is exact-source local. -/
theorem isSourceLocalRandomVariable_coarseBlockMatrix_lowerRight_cubeSet
    {d : ℕ} (Q : TriadicCube d) :
    IsSourceLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q)
      (fun a : Source.Coarse.Carrier d =>
        (coarseBlockMatrix (cubeSet Q) a.1).lowerRight) :=
  IsSourceLocalRandomVariable.mat_of_entries fun i j =>
    isSourceLocalRandomVariable_coarseBlockMatrix_lowerRight_apply_cubeSet Q i j

/-- The negative lower-left coarse block is exact-source local. -/
theorem isSourceLocalRandomVariable_neg_coarseBlockMatrix_lowerLeft_cubeSet
    {d : ℕ} (Q : TriadicCube d) :
    IsSourceLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q)
      (fun a : Source.Coarse.Carrier d =>
        -((coarseBlockMatrix (cubeSet Q) a.1).lowerLeft)) := by
  let : MeasurableSpace (Source.Coarse.Carrier d) :=
    Source.Coarse.localSigma (cubeSet Q) (measurableSet_cubeSet Q)
  change @Measurable (Source.Coarse.Carrier d) (Mat d)
    (Source.Coarse.localSigma (cubeSet Q) (measurableSet_cubeSet Q)) _ _
  refine measurable_pi_iff.2 fun i => ?_
  refine measurable_pi_iff.2 fun j => ?_
  exact (isSourceLocalRandomVariable_coarseBlockMatrix_lowerLeft_apply_cubeSet Q i j).neg

private theorem isSourceLocalRandomVariable_descendantsAverage
    {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    {F : TriadicCube d → Source.Coarse.Carrier d → ℝ}
    (hF : ∀ R, R ∈ descendantsAtDepth Q j →
      IsSourceLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (F R)) :
    IsSourceLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q)
      (fun a => descendantsAverage Q j (fun R => F R a)) := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  let : MeasurableSpace (Source.Coarse.Carrier d) :=
    Source.Coarse.localSigma (cubeSet Q) (measurableSet_cubeSet Q)
  have hsum : Measurable (fun a : Source.Coarse.Carrier d => D.sum (fun R => F R a)) := by
    refine Finset.measurable_sum D ?_
    intro R hR
    exact (hF R (by simpa [D] using hR)).mono
      (measurableSet_cubeSet R) (measurableSet_cubeSet Q)
      (cubeSet_subset_of_mem_descendantsAtDepth (by simpa [D] using hR))
  simpa [descendantsAverage, D] using! hsum.const_mul ((D.card : ℝ)⁻¹)

/-- The finite descendant average of a coarse energy is exact-source local on
the parent cube. -/
theorem isSourceLocalRandomVariable_descendantsAverage_Mu_cubeSet
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (P0 : BlockVec d) :
    IsSourceLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q)
      (fun a : Source.Coarse.Carrier d =>
        descendantsAverage Q j (fun R => Mu (cubeSet R) P0 a.1)) :=
  isSourceLocalRandomVariable_descendantsAverage Q j fun R _ =>
    (SourceObservable.mu R P0).isLocal

/-- The finite descendant average of an upper-left coarse entry is exact-source
local on the parent cube. -/
theorem isSourceLocalRandomVariable_descendantsAverage_coarseBlockMatrix_upperLeft_apply_cubeSet
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (i k : Fin d) :
    IsSourceLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q)
      (fun a : Source.Coarse.Carrier d => descendantsAverage Q j (fun R =>
        (coarseBlockMatrix (cubeSet R) a.1).upperLeft i k)) :=
  isSourceLocalRandomVariable_descendantsAverage Q j fun R _ =>
    isSourceLocalRandomVariable_coarseBlockMatrix_upperLeft_apply_cubeSet R i k

/-- The finite descendant average of an upper-right coarse entry is exact-source
local on the parent cube. -/
theorem isSourceLocalRandomVariable_descendantsAverage_coarseBlockMatrix_upperRight_apply_cubeSet
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (i k : Fin d) :
    IsSourceLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q)
      (fun a : Source.Coarse.Carrier d => descendantsAverage Q j (fun R =>
        (coarseBlockMatrix (cubeSet R) a.1).upperRight i k)) :=
  isSourceLocalRandomVariable_descendantsAverage Q j fun R _ =>
    isSourceLocalRandomVariable_coarseBlockMatrix_upperRight_apply_cubeSet R i k

/-- The finite descendant average of a lower-left coarse entry is exact-source
local on the parent cube. -/
theorem isSourceLocalRandomVariable_descendantsAverage_coarseBlockMatrix_lowerLeft_apply_cubeSet
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (i k : Fin d) :
    IsSourceLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q)
      (fun a : Source.Coarse.Carrier d => descendantsAverage Q j (fun R =>
        (coarseBlockMatrix (cubeSet R) a.1).lowerLeft i k)) :=
  isSourceLocalRandomVariable_descendantsAverage Q j fun R _ =>
    isSourceLocalRandomVariable_coarseBlockMatrix_lowerLeft_apply_cubeSet R i k

/-- The finite descendant average of a lower-right coarse entry is exact-source
local on the parent cube. -/
theorem isSourceLocalRandomVariable_descendantsAverage_coarseBlockMatrix_lowerRight_apply_cubeSet
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (i k : Fin d) :
    IsSourceLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q)
      (fun a : Source.Coarse.Carrier d => descendantsAverage Q j (fun R =>
        (coarseBlockMatrix (cubeSet R) a.1).lowerRight i k)) :=
  isSourceLocalRandomVariable_descendantsAverage Q j fun R _ =>
    isSourceLocalRandomVariable_coarseBlockMatrix_lowerRight_apply_cubeSet R i k

namespace SourceObservable

/-- The unfolded full coarse block matrix, bundled as an exact-source observable. -/
noncomputable def coarseFullBlockMatrix {d : ℕ} (Q : TriadicCube d) :
    SourceObservable d (cubeSet Q) (FullBlockMat d) where
  measurableSet := measurableSet_cubeSet Q
  toFun := fun a => toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.1)
  isLocal := isSourceLocalRandomVariable_toFullBlockMat_coarseBlockMatrix_cubeSet Q

/-- The upper-left coarse block, bundled as an exact-source observable. -/
noncomputable def coarseBlockUpperLeft {d : ℕ} (Q : TriadicCube d) :
    SourceObservable d (cubeSet Q) (Mat d) where
  measurableSet := measurableSet_cubeSet Q
  toFun := fun a => (coarseBlockMatrix (cubeSet Q) a.1).upperLeft
  isLocal := isSourceLocalRandomVariable_coarseBlockMatrix_upperLeft_cubeSet Q

/-- The upper-right coarse block, bundled as an exact-source observable. -/
noncomputable def coarseBlockUpperRight {d : ℕ} (Q : TriadicCube d) :
    SourceObservable d (cubeSet Q) (Mat d) where
  measurableSet := measurableSet_cubeSet Q
  toFun := fun a => (coarseBlockMatrix (cubeSet Q) a.1).upperRight
  isLocal := isSourceLocalRandomVariable_coarseBlockMatrix_upperRight_cubeSet Q

/-- The lower-left coarse block, bundled as an exact-source observable. -/
noncomputable def coarseBlockLowerLeft {d : ℕ} (Q : TriadicCube d) :
    SourceObservable d (cubeSet Q) (Mat d) where
  measurableSet := measurableSet_cubeSet Q
  toFun := fun a => (coarseBlockMatrix (cubeSet Q) a.1).lowerLeft
  isLocal := isSourceLocalRandomVariable_coarseBlockMatrix_lowerLeft_cubeSet Q

/-- The lower-right coarse block, bundled as an exact-source observable. -/
noncomputable def coarseBlockLowerRight {d : ℕ} (Q : TriadicCube d) :
    SourceObservable d (cubeSet Q) (Mat d) where
  measurableSet := measurableSet_cubeSet Q
  toFun := fun a => (coarseBlockMatrix (cubeSet Q) a.1).lowerRight
  isLocal := isSourceLocalRandomVariable_coarseBlockMatrix_lowerRight_cubeSet Q

/-- The negative lower-left coarse block, bundled as an exact-source observable. -/
noncomputable def negCoarseBlockLowerLeft {d : ℕ} (Q : TriadicCube d) :
    SourceObservable d (cubeSet Q) (Mat d) where
  measurableSet := measurableSet_cubeSet Q
  toFun := fun a => -((coarseBlockMatrix (cubeSet Q) a.1).lowerLeft)
  isLocal := isSourceLocalRandomVariable_neg_coarseBlockMatrix_lowerLeft_cubeSet Q

end SourceObservable

end

end Homogenization.Book.Ch04
