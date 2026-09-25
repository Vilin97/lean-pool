/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.Basic
public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.OverlapFluctuation
public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.StandardProjectionVector

/-! # Standard Projection Increment Energy -/

@[expose] public section

namespace Homogenization

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

/-!
# Energy bounds for standard martingale increments

This file records the local Jensen step needed for the boundary-budget
construction: a child-minus-parent average is controlled by the `L²` energy of
the field measured relative to the parent average on that child.
-/

/-- A child-average jump is controlled coordinatewise by the child `L²`
energy relative to the parent average. -/
theorem vecNormSq_childAverage_sub_parentAverage_le_sum_cubeAverage_sq_sub_parentAverage
    {d : ℕ} {T R : TriadicCube d} (u : Vec d → Vec d)
    (_hRT : R ∈ childCubes T)
    (huR : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    vecNormSq (cubeAverageVec R u - cubeAverageVec T u) ≤
      ∑ i : Fin d, cubeAverage R (fun x => (u x i - cubeAverageVec T u i) ^ 2) := by
  have hfield :
      MeasureTheory.MemLp (fun x => u x - cubeAverageVec T u)
        (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
    huR.sub (MeasureTheory.memLp_const (cubeAverageVec T u))
  have hJ :=
    vecNormSq_cubeAverageVec_le_sum_cubeAverage_sq_of_memLp
      R (fun x => u x - cubeAverageVec T u) hfield
  have havg :
      cubeAverageVec R (fun x => u x - cubeAverageVec T u) =
        cubeAverageVec R u - cubeAverageVec T u :=
    cubeAverageVec_sub_const R u (cubeAverageVec T u) huR
  simpa [havg] using hJ

/-- Pointwise form for a martingale increment on a child cube: the squared
increment value is paid by the child energy relative to the parent average. -/
theorem vecNormSq_cubeIncrementVec_le_sum_cubeAverage_sq_sub_parentAverage
    {d : ℕ} {Q T R : TriadicCube d} {m : ℕ} (u : Vec d → Vec d)
    (hT : T ∈ descendantsAtDepth Q m) (hRT : R ∈ childCubes T) {x : Vec d}
    (hxR : x ∈ cubeSet R)
    (huR : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    vecNormSq (cubeIncrementVec Q (m + 1) u x) ≤
      ∑ i : Fin d, cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2) := by
  rw [cubeIncrementVec_eq_sub_cubeAverageVec_of_mem_childCubes
    (Q := Q) (T := T) (R := R) (m := m) u hT hRT hxR]
  exact
    vecNormSq_childAverage_sub_parentAverage_le_sum_cubeAverage_sq_sub_parentAverage
      (T := T) (R := R) u hRT huR

theorem cubeAverage_sq_sub_parentAverage_nonneg {d : ℕ}
    (T R : TriadicCube d) (u : Vec d → Vec d) (i : Fin d) :
    0 ≤ cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2) := by
  unfold cubeAverage
  exact mul_nonneg (inv_nonneg.mpr (cubeVolume_nonneg R))
    (MeasureTheory.setIntegral_nonneg (measurableSet_cubeSet R)
      fun y _hy => sq_nonneg (u y i - cubeAverageVec T u i))

theorem childEnergy_sum_nonneg {d : ℕ} (T R : TriadicCube d) (u : Vec d → Vec d) :
    0 ≤ ∑ i : Fin d,
      cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2) := by
  exact Finset.sum_nonneg fun i _hi =>
    cubeAverage_sq_sub_parentAverage_nonneg T R u i

theorem parentChildEnergy_sum_nonneg {d : ℕ} (T : TriadicCube d)
    (u : Vec d → Vec d) :
    0 ≤
      ∑ R ∈ childCubes T,
        ∑ i : Fin d,
          cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2) := by
  exact Finset.sum_nonneg fun R _hR => childEnergy_sum_nonneg T R u

/-- The child-energy sum relative to a parent average is controlled by the
ordinary vector `L²` fluctuation on the parent.  The factor `3^d` comes from
summing normalized child averages rather than averaging over the children, and
the factor `d` comes from comparing the Euclidean coordinate sum to the ambient
Pi norm used by `cubeLpNorm`. -/
theorem parentChildEnergy_sum_le_card_mul_cubeLpNorm_cubeFluctuationVec_sq
    {d : ℕ} (T : TriadicCube d) (u : Vec d → Vec d)
    (huT : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure T)) :
    (∑ R ∈ childCubes T,
      ∑ i : Fin d,
        cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2)) ≤
      (3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ) *
        (cubeLpNorm T (2 : ℝ≥0∞) (cubeFluctuationVec T u)) ^ 2 := by
  let v : Vec d → Vec d := cubeFluctuationVec T u
  have hv : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure T) :=
    memLp_cubeFluctuationVec T u huT
  have hcoord_mem :
      ∀ i : Fin d,
        MeasureTheory.MemLp (fun x => v x i) (2 : ℝ≥0∞)
          (normalizedCubeMeasure T) := by
    intro i
    exact memLp_component_of_memLp v i hv
  have hsum_coord :
      ∀ i : Fin d,
        ∑ R ∈ childCubes T,
          cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2) =
        (3 ^ d : ℝ) *
          (cubeLpNorm T (2 : ℝ≥0∞) (fun y => v y i)) ^ 2 := by
    intro i
    let f : Vec d → ℝ := fun y => (u y i - cubeAverageVec T u i) ^ 2
    have hf_int :
        MeasureTheory.IntegrableOn f (cubeSet T) MeasureTheory.volume := by
      have hpow :
          MeasureTheory.IntegrableOn (fun y => ‖v y i‖ ^ (2 : ℝ))
            (cubeSet T) MeasureTheory.volume :=
        integrableOn_of_integrable_normalizedCubeMeasure (Q := T)
          ((hcoord_mem i).integrable_norm_rpow
            (by norm_num : (2 : ℝ≥0∞) ≠ 0)
            (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
      simpa [f, v, cubeFluctuationVec, Real.norm_eq_abs, sq_abs, Real.rpow_two]
        using hpow
    have havg :=
      cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
        T 1 f hf_int
    have hsum :
        ∑ R ∈ childCubes T, cubeAverage R f =
          (3 ^ d : ℝ) * cubeAverage T f := by
      have hpow_ne : (3 ^ d : ℝ) ≠ 0 := by positivity
      simp [descendantsAverage, childCubes_card] at havg
      calc
        ∑ R ∈ childCubes T, cubeAverage R f
            = (3 ^ d : ℝ) *
                ((3 ^ d : ℝ)⁻¹ *
                  ∑ R ∈ childCubes T, cubeAverage R f) := by
              field_simp [hpow_ne]
        _ = (3 ^ d : ℝ) * cubeAverage T f := by
              rw [← havg]
    have hnorm :
        (cubeLpNorm T (2 : ℝ≥0∞) (fun y => v y i)) ^ 2 =
          cubeAverage T f := by
      have hraw :=
        cubeLpNorm_rpow_eq_cubeAverage_norm_rpow
          (Q := T) (p := (2 : ℝ≥0∞)) (f := fun y => v y i)
          (by norm_num) (by norm_num) (hcoord_mem i)
      simpa [f, v, cubeFluctuationVec, Real.norm_eq_abs, sq_abs, Real.rpow_two]
        using hraw
    rw [hsum, ← hnorm]
  calc
    (∑ R ∈ childCubes T,
      ∑ i : Fin d,
        cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2))
        =
          ∑ i : Fin d,
            ∑ R ∈ childCubes T,
              cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2) := by
          rw [Finset.sum_comm]
    _ =
          ∑ i : Fin d,
            (3 ^ d : ℝ) *
              (cubeLpNorm T (2 : ℝ≥0∞) (fun y => v y i)) ^ 2 := by
          exact Finset.sum_congr rfl fun i _hi => hsum_coord i
    _ ≤
          ∑ _i : Fin d,
            (3 ^ d : ℝ) *
              (cubeLpNorm T (2 : ℝ≥0∞) v) ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro i _hi
          have hcomp :=
            cubeLpNorm_two_component_le_cubeLpNorm_two T v i hv
          have hsq :
              (cubeLpNorm T (2 : ℝ≥0∞) (fun y => v y i)) ^ 2 ≤
                (cubeLpNorm T (2 : ℝ≥0∞) v) ^ 2 :=
            (sq_le_sq₀
              (cubeLpNorm_nonneg T (2 : ℝ≥0∞) (fun y => v y i))
              (cubeLpNorm_nonneg T (2 : ℝ≥0∞) v)).mpr hcomp
          exact mul_le_mul_of_nonneg_left hsq (by positivity)
    _ =
          (3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ) *
            (cubeLpNorm T (2 : ℝ≥0∞) v) ^ 2 := by
          simp [Finset.sum_const, nsmul_eq_mul]
          ring

/-- Summed over all depth-`m` parents, the parent child-energy budgets are
controlled by the ordinary standard positive depth average. -/
theorem parentChildEnergy_sum_descendants_le_const_mul_depthAverage
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d) (m : ℕ)
    (huParent :
      ∀ T ∈ descendantsAtDepth Q m,
        MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure T)) :
    (∑ T ∈ descendantsAtDepth Q m,
      ∑ R ∈ childCubes T,
        ∑ i : Fin d,
          cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2)) ≤
      (3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ) *
        ((descendantsAtDepth Q m).card : ℝ) *
          cubeBesovPositiveVectorDepthAverage Q u m := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q m
  let A : TriadicCube d → ℝ := fun T =>
    ∑ R ∈ childCubes T,
      ∑ i : Fin d,
        cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2)
  let N : TriadicCube d → ℝ := fun T =>
    (cubeLpNorm T (2 : ℝ≥0∞) (cubeFluctuationVec T u)) ^ 2
  have hsum :
      ∑ T ∈ D, A T ≤
        ∑ T ∈ D,
          (3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ) * N T := by
    refine Finset.sum_le_sum ?_
    intro T hT
    exact parentChildEnergy_sum_le_card_mul_cubeLpNorm_cubeFluctuationVec_sq
      T u (huParent T (by simpa [D] using hT))
  have hNsum :
      ∑ T ∈ D, N T =
        ((descendantsAtDepth Q m).card : ℝ) *
          cubeBesovPositiveVectorDepthAverage Q u m := by
    have hcard_ne : ((descendantsAtDepth Q m).card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr (descendantsAtDepth_nonempty Q m)
    unfold cubeBesovPositiveVectorDepthAverage descendantsAverage
    change
      ∑ T ∈ D, N T =
        ((descendantsAtDepth Q m).card : ℝ) *
          (((descendantsAtDepth Q m).card : ℝ)⁻¹ *
            ∑ T ∈ descendantsAtDepth Q m,
              (cubeLpNorm T (2 : ℝ≥0∞) (cubeFluctuationVec T u)) ^ 2)
    simp [D, N]
    field_simp [hcard_ne]
  calc
    (∑ T ∈ descendantsAtDepth Q m,
      ∑ R ∈ childCubes T,
        ∑ i : Fin d,
          cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2))
        = ∑ T ∈ D, A T := rfl
    _ ≤
        ∑ T ∈ D,
          (3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ) * N T := hsum
    _ =
        (3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ) *
          ∑ T ∈ D, N T := by
          rw [← Finset.mul_sum]
    _ =
        (3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ) *
          (((descendantsAtDepth Q m).card : ℝ) *
            cubeBesovPositiveVectorDepthAverage Q u m) := by
          rw [hNsum]
    _ =
        (3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ) *
          ((descendantsAtDepth Q m).card : ℝ) *
            cubeBesovPositiveVectorDepthAverage Q u m := by
          ring

/-- If the point lies in a depth-`m` parent, the pointwise martingale
increment at scale `m + 1` is controlled by the finite sum of the child
energies of that parent. -/
theorem vecNormSq_cubeIncrementVec_le_childEnergy_sum_of_mem_parent
    {d : ℕ} {Q T : TriadicCube d} {m : ℕ} (u : Vec d → Vec d)
    (hT : T ∈ descendantsAtDepth Q m) {x : Vec d} (hxT : x ∈ cubeSet T)
    (huChild :
      ∀ R ∈ childCubes T,
        MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    vecNormSq (cubeIncrementVec Q (m + 1) u x) ≤
      ∑ R ∈ childCubes T,
        ∑ i : Fin d,
          cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2) := by
  rcases exists_mem_descendantsAtDepth_of_mem_cubeSet (Q := T) (n := 1) hxT with
    ⟨R, hR, hxR⟩
  have hRT : R ∈ childCubes T := by
    simpa [descendantsAtDepth_one] using hR
  have hlocal :=
    vecNormSq_cubeIncrementVec_le_sum_cubeAverage_sq_sub_parentAverage
      (Q := Q) (T := T) (R := R) (m := m) u hT hRT hxR (huChild R hRT)
  calc
    vecNormSq (cubeIncrementVec Q (m + 1) u x)
        ≤ ∑ i : Fin d,
            cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2) :=
          hlocal
    _ ≤
        ∑ R ∈ childCubes T,
          ∑ i : Fin d,
            cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2) := by
          exact Finset.single_le_sum
            (fun A _hA => childEnergy_sum_nonneg T A u) hRT

/-- Local overlap version of the child-energy budget.  When the overlap cube
does not leave a depth-`m` parent, the fluctuation of the `m + 1` martingale
increment is paid by the finite child-energy sum of that parent. -/
theorem sq_overlapCubeLpNorm_overlapCubeFluctuationVec_cubeIncrementVec_le_four_mul_childEnergy_sum
    {d : ℕ} {Q T S : TriadicCube d} {m : ℕ} (u : Vec d → Vec d)
    (hT : T ∈ descendantsAtDepth Q m)
    (hsub : overlapCubeSet S ⊆ cubeSet T)
    (hinc :
      MeasureTheory.MemLp (cubeIncrementVec Q (m + 1) u)
        (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (huChild :
      ∀ R ∈ childCubes T,
        MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    (overlapCubeLpNorm S (2 : ℝ≥0∞)
      (overlapCubeFluctuationVec S (cubeIncrementVec Q (m + 1) u))) ^ 2 ≤
      4 *
        ∑ R ∈ childCubes T,
          ∑ i : Fin d,
            cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2) := by
  have hB :
      0 ≤
        ∑ R ∈ childCubes T,
          ∑ i : Fin d,
            cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2) := by
    exact Finset.sum_nonneg fun R hR => childEnergy_sum_nonneg T R u
  exact
    sq_overlapCubeLpNorm_two_overlapCubeFluctuationVec_le_four_mul_of_forall_overlapCubeSet_vecNormSq_le
      (S := S) (u := cubeIncrementVec Q (m + 1) u) hinc hB
      (fun x hxS =>
        vecNormSq_cubeIncrementVec_le_childEnergy_sum_of_mem_parent
          (Q := Q) (T := T) (m := m) u hT (hsub hxS) huChild)

/-- Depth-`m` parents whose standard cubes meet a fixed overlap cube.  This
is the local-neighbor family needed for the true finite-overlap summation. -/
noncomputable def overlapIntersectingParentsAtDepth {d : ℕ}
    (Q S : TriadicCube d) (m : ℕ) : Finset (TriadicCube d) := by
  classical
  exact (descendantsAtDepth Q m).filter fun T =>
    (overlapCubeSet S ∩ cubeSet T).Nonempty

theorem mem_overlapIntersectingParentsAtDepth_iff {d : ℕ}
    {Q S T : TriadicCube d} {m : ℕ} :
    T ∈ overlapIntersectingParentsAtDepth Q S m ↔
      T ∈ descendantsAtDepth Q m ∧ (overlapCubeSet S ∩ cubeSet T).Nonempty := by
  classical
  simp [overlapIntersectingParentsAtDepth]

/-- Pointwise local-neighbor version: on an overlap cube contained in `Q`, a
martingale increment is paid by child energies of only those depth-`m` parents
which meet that overlap cube. -/
theorem vecNormSq_cubeIncrementVec_le_overlapIntersectingParentEnergy_sum
    {d : ℕ} {Q S : TriadicCube d} {m : ℕ} (u : Vec d → Vec d)
    (hSsub : overlapCubeSet S ⊆ cubeSet Q) {x : Vec d} (hxS : x ∈ overlapCubeSet S)
    (huChild :
      ∀ T ∈ descendantsAtDepth Q m, ∀ R ∈ childCubes T,
        MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    vecNormSq (cubeIncrementVec Q (m + 1) u x) ≤
      ∑ T ∈ overlapIntersectingParentsAtDepth Q S m,
        ∑ R ∈ childCubes T,
          ∑ i : Fin d,
            cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2) := by
  rcases exists_mem_descendantsAtDepth_of_mem_cubeSet (Q := Q) (n := m)
      (hSsub hxS) with
    ⟨T, hT, hxT⟩
  have hTneighbor : T ∈ overlapIntersectingParentsAtDepth Q S m := by
    rw [mem_overlapIntersectingParentsAtDepth_iff]
    exact ⟨hT, ⟨x, hxS, hxT⟩⟩
  have hlocal :
      vecNormSq (cubeIncrementVec Q (m + 1) u x) ≤
        ∑ R ∈ childCubes T,
          ∑ i : Fin d,
            cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2) :=
    vecNormSq_cubeIncrementVec_le_childEnergy_sum_of_mem_parent
      (Q := Q) (T := T) (m := m) u hT hxT (huChild T hT)
  calc
    vecNormSq (cubeIncrementVec Q (m + 1) u x)
        ≤
          ∑ R ∈ childCubes T,
            ∑ i : Fin d,
              cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2) :=
          hlocal
    _ ≤
        ∑ T ∈ overlapIntersectingParentsAtDepth Q S m,
          ∑ R ∈ childCubes T,
            ∑ i : Fin d,
              cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2) := by
          exact Finset.single_le_sum
            (fun A _hA => parentChildEnergy_sum_nonneg A u) hTneighbor

/-- Overlap-fluctuation local-neighbor budget for one martingale increment. -/
theorem sq_overlapCubeLpNorm_overlapCubeFluctuationVec_cubeIncrementVec_le_four_mul_overlapIntersectingParentEnergy_sum
    {d : ℕ} {Q S : TriadicCube d} {m : ℕ} (u : Vec d → Vec d)
    (hSsub : overlapCubeSet S ⊆ cubeSet Q)
    (hinc :
      MeasureTheory.MemLp (cubeIncrementVec Q (m + 1) u)
        (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (huChild :
      ∀ T ∈ descendantsAtDepth Q m, ∀ R ∈ childCubes T,
        MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    (overlapCubeLpNorm S (2 : ℝ≥0∞)
      (overlapCubeFluctuationVec S (cubeIncrementVec Q (m + 1) u))) ^ 2 ≤
      4 *
        ∑ T ∈ overlapIntersectingParentsAtDepth Q S m,
          ∑ R ∈ childCubes T,
            ∑ i : Fin d,
              cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2) := by
  have hB :
      0 ≤
        ∑ T ∈ overlapIntersectingParentsAtDepth Q S m,
          ∑ R ∈ childCubes T,
            ∑ i : Fin d,
              cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2) := by
    exact Finset.sum_nonneg fun T _hT => parentChildEnergy_sum_nonneg T u
  exact
    sq_overlapCubeLpNorm_two_overlapCubeFluctuationVec_le_four_mul_of_forall_overlapCubeSet_vecNormSq_le
      (S := S) (u := cubeIncrementVec Q (m + 1) u) hinc hB
      (fun x hxS =>
        vecNormSq_cubeIncrementVec_le_overlapIntersectingParentEnergy_sum
          (Q := Q) (S := S) (m := m) u hSsub hxS huChild)

end

end Homogenization
