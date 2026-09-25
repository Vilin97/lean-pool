/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.AveragingScale

/-! # Averaging Residual -/

@[expose] public section

namespace Homogenization

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Pointwise

namespace SmoothOverlapPartition

/-- The partition-parametrized averaging field preserves constants on the
parent cube. -/
theorem averagingField_const_of_mem_openCubeSet {d : ℕ}
    {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (c : Vec d)
    {x : Vec d} (hx : x ∈ openCubeSet Q) :
    P.averagingField (fun _ : Vec d => c) x = c := by
  funext i
  have hsum := P.sum_eq_one hx
  calc
    P.averagingField (fun _ : Vec d => c) x i
        =
          (overlapCentersAtDepth Q j).sum
            (fun S => P.weight S x * c i) := by
          simp [averagingField]
    _ =
          ((overlapCentersAtDepth Q j).sum
            (fun S => P.weight S x)) * c i := by
          rw [Finset.sum_mul]
    _ = c i := by
          rw [hsum]
          ring

/-- Coordinate form of the residual identity
`h - A_j h = sum_S phi_S (h - h_S)`. -/
theorem sub_averagingField_apply_eq_sum_weighted_overlap_fluctuation {d : ℕ}
    {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    {x : Vec d} (hx : x ∈ openCubeSet Q) (i : Fin d) :
    (h x - P.averagingField h x) i =
      (overlapCentersAtDepth Q j).sum
        (fun S => P.weight S x *
          (h x i - overlapCubeAverageVec S h i)) := by
  have hsum := P.sum_eq_one hx
  calc
    (h x - P.averagingField h x) i
        =
          h x i -
            (overlapCentersAtDepth Q j).sum
              (fun S => P.weight S x * overlapCubeAverageVec S h i) := by
          simp [averagingField]
    _ =
          ((overlapCentersAtDepth Q j).sum
            (fun S => P.weight S x)) * h x i -
            (overlapCentersAtDepth Q j).sum
              (fun S => P.weight S x * overlapCubeAverageVec S h i) := by
          rw [hsum]
          ring
    _ =
          (overlapCentersAtDepth Q j).sum
            (fun S => P.weight S x * h x i) -
            (overlapCentersAtDepth Q j).sum
              (fun S => P.weight S x * overlapCubeAverageVec S h i) := by
          rw [Finset.sum_mul]
    _ =
          (overlapCentersAtDepth Q j).sum
            (fun S => P.weight S x *
              (h x i - overlapCubeAverageVec S h i)) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro S _hS
          ring

/-- A partition weight belonging to an active overlap center is at most one on
the parent cube. -/
theorem weight_le_one_of_mem_openCubeSet {d : ℕ}
    {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j)
    {S : TriadicCube d} {x : Vec d}
    (hS : S ∈ overlapCentersAtDepth Q j) (hx : x ∈ openCubeSet Q) :
    P.weight S x ≤ 1 := by
  have hsum := P.sum_eq_one hx
  have hnonneg :
      ∀ T ∈ overlapCentersAtDepth Q j, 0 ≤ P.weight T x := by
    intro T hT
    exact P.nonneg hT hx
  have hsingle :
      P.weight S x ≤
        (overlapCentersAtDepth Q j).sum (fun T => P.weight T x) :=
    Finset.single_le_sum hnonneg hS
  simpa [hsum] using hsingle

/-- Pointwise coordinate residual bound obtained from the partition identity
and bounded active overlap.  This is the local algebraic heart of the
`L²` residual estimate; the subsequent integral step uses support containment
and the finite-overlap comparison. -/
theorem sub_averagingField_apply_sq_le_activeCard_mul_sum_overlap_fluctuation_sq
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    {x : Vec d} (hx : x ∈ openCubeSet Q) (i : Fin d) :
    ((h x - P.averagingField h x) i) ^ 2 ≤
      (((overlapCentersAtDepth Q j).filter
          (fun S => P.weight S x ≠ 0)).card : ℝ) *
        (overlapCentersAtDepth Q j).sum
          (fun S => (h x i - overlapCubeAverageVec S h i) ^ 2) := by
  classical
  let D : Finset (TriadicCube d) := overlapCentersAtDepth Q j
  let A : Finset (TriadicCube d) := D.filter (fun S => P.weight S x ≠ 0)
  let b : TriadicCube d → ℝ :=
    fun S => P.weight S x * (h x i - overlapCubeAverageVec S h i)
  let a : TriadicCube d → ℝ :=
    fun S => h x i - overlapCubeAverageVec S h i
  have hres :
      (h x - P.averagingField h x) i = D.sum b := by
    simpa [D, b, a] using
      P.sub_averagingField_apply_eq_sum_weighted_overlap_fluctuation h hx i
  have hsum_active : A.sum b = D.sum b := by
    dsimp [A]
    refine Finset.sum_filter_of_ne ?_
    intro S _hS hb
    dsimp [b] at hb ⊢
    intro hzero
    exact hb (by simp [hzero])
  have hcauchy :
      (A.sum b) ^ 2 ≤ (A.card : ℝ) * A.sum (fun S => (b S) ^ 2) :=
    sq_sum_le_card_mul_sum_sq
  have hweighted_le_unweighted :
      A.sum (fun S => (b S) ^ 2) ≤ D.sum (fun S => (a S) ^ 2) := by
    calc
      A.sum (fun S => (b S) ^ 2)
          ≤ A.sum (fun S => (a S) ^ 2) := by
            refine Finset.sum_le_sum ?_
            intro S hS_active
            have hS : S ∈ D := by
              simpa [A] using (Finset.mem_of_mem_filter S hS_active)
            have hw_nonneg : 0 ≤ P.weight S x :=
              P.nonneg (by simpa [D] using hS) hx
            have hw_le : P.weight S x ≤ 1 :=
              P.weight_le_one_of_mem_openCubeSet (by simpa [D] using hS) hx
            have ha_sq_nonneg : 0 ≤ (a S) ^ 2 := sq_nonneg (a S)
            have hw_sq_le_one : (P.weight S x) ^ 2 ≤ 1 := by
              nlinarith [mul_nonneg hw_nonneg (sub_nonneg.mpr hw_le)]
            have hmul_le :
                (P.weight S x) ^ 2 * (a S) ^ 2 ≤ 1 * (a S) ^ 2 :=
              mul_le_mul_of_nonneg_right hw_sq_le_one ha_sq_nonneg
            calc
              (b S) ^ 2 = (P.weight S x) ^ 2 * (a S) ^ 2 := by
                simp [b, a]
                ring
              _ ≤ (a S) ^ 2 := by
                simpa using hmul_le
      _ ≤ D.sum (fun S => (a S) ^ 2) := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset _ _)
              (by
                intro S _hSD _hSnot
                exact sq_nonneg (a S))
  calc
    ((h x - P.averagingField h x) i) ^ 2
        = (D.sum b) ^ 2 := by rw [hres]
    _ = (A.sum b) ^ 2 := by rw [hsum_active]
    _ ≤ (A.card : ℝ) * A.sum (fun S => (b S) ^ 2) := hcauchy
    _ ≤ (A.card : ℝ) * D.sum (fun S => (a S) ^ 2) := by
          exact mul_le_mul_of_nonneg_left hweighted_le_unweighted (by positivity)
    _ =
        (((overlapCentersAtDepth Q j).filter
          (fun S => P.weight S x ≠ 0)).card : ℝ) *
          (overlapCentersAtDepth Q j).sum
            (fun S => (h x i - overlapCubeAverageVec S h i) ^ 2) := by
          rfl

/-- Sharper pointwise coordinate residual bound retaining the active-center
sum.  This is the form used for the support-localized integral estimate. -/
theorem sub_averagingField_apply_sq_le_activeCard_mul_activeSum_overlap_fluctuation_sq
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    {x : Vec d} (hx : x ∈ openCubeSet Q) (i : Fin d) :
    ((h x - P.averagingField h x) i) ^ 2 ≤
      (((overlapCentersAtDepth Q j).filter
          (fun S => P.weight S x ≠ 0)).card : ℝ) *
        ((overlapCentersAtDepth Q j).filter
          (fun S => P.weight S x ≠ 0)).sum
          (fun S => (h x i - overlapCubeAverageVec S h i) ^ 2) := by
  classical
  let D : Finset (TriadicCube d) := overlapCentersAtDepth Q j
  let A : Finset (TriadicCube d) := D.filter (fun S => P.weight S x ≠ 0)
  let b : TriadicCube d → ℝ :=
    fun S => P.weight S x * (h x i - overlapCubeAverageVec S h i)
  let a : TriadicCube d → ℝ :=
    fun S => h x i - overlapCubeAverageVec S h i
  have hres :
      (h x - P.averagingField h x) i = D.sum b := by
    simpa [D, b, a] using
      P.sub_averagingField_apply_eq_sum_weighted_overlap_fluctuation h hx i
  have hsum_active : A.sum b = D.sum b := by
    dsimp [A]
    refine Finset.sum_filter_of_ne ?_
    intro S _hS hb
    dsimp [b] at hb ⊢
    intro hzero
    exact hb (by simp [hzero])
  have hcauchy :
      (A.sum b) ^ 2 ≤ (A.card : ℝ) * A.sum (fun S => (b S) ^ 2) :=
    sq_sum_le_card_mul_sum_sq
  have hweighted_le_unweighted :
      A.sum (fun S => (b S) ^ 2) ≤ A.sum (fun S => (a S) ^ 2) := by
    refine Finset.sum_le_sum ?_
    intro S hS_active
    have hS : S ∈ D := by
      simpa [A] using (Finset.mem_of_mem_filter S hS_active)
    have hw_nonneg : 0 ≤ P.weight S x :=
      P.nonneg (by simpa [D] using hS) hx
    have hw_le : P.weight S x ≤ 1 :=
      P.weight_le_one_of_mem_openCubeSet (by simpa [D] using hS) hx
    have ha_sq_nonneg : 0 ≤ (a S) ^ 2 := sq_nonneg (a S)
    have hw_sq_le_one : (P.weight S x) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hw_nonneg (sub_nonneg.mpr hw_le)]
    have hmul_le :
        (P.weight S x) ^ 2 * (a S) ^ 2 ≤ 1 * (a S) ^ 2 :=
      mul_le_mul_of_nonneg_right hw_sq_le_one ha_sq_nonneg
    calc
      (b S) ^ 2 = (P.weight S x) ^ 2 * (a S) ^ 2 := by
        simp [b, a]
        ring
      _ ≤ (a S) ^ 2 := by
        simpa using hmul_le
  calc
    ((h x - P.averagingField h x) i) ^ 2
        = (D.sum b) ^ 2 := by rw [hres]
    _ = (A.sum b) ^ 2 := by rw [hsum_active]
    _ ≤ (A.card : ℝ) * A.sum (fun S => (b S) ^ 2) := hcauchy
    _ ≤ (A.card : ℝ) * A.sum (fun S => (a S) ^ 2) := by
          exact mul_le_mul_of_nonneg_left hweighted_le_unweighted (by positivity)
    _ =
      (((overlapCentersAtDepth Q j).filter
          (fun S => P.weight S x ≠ 0)).card : ℝ) *
        ((overlapCentersAtDepth Q j).filter
          (fun S => P.weight S x ≠ 0)).sum
          (fun S => (h x i - overlapCubeAverageVec S h i) ^ 2) := by
          rfl

/-- Active terms in the residual estimate are supported in their corresponding
open overlap cubes, so the active fluctuation sum is dominated by the
indicator sum over all retained overlap centers. -/
theorem activeSum_overlap_fluctuation_sq_le_sum_openOverlap_indicator
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    {x : Vec d} (hx : x ∈ openCubeSet Q) (i : Fin d) :
    ((overlapCentersAtDepth Q j).filter
        (fun S => P.weight S x ≠ 0)).sum
        (fun S => (h x i - overlapCubeAverageVec S h i) ^ 2) ≤
      (overlapCentersAtDepth Q j).sum
        (fun S =>
          (openOverlapCubeSet S).indicator
            (fun y : Vec d => (h y i - overlapCubeAverageVec S h i) ^ 2) x) := by
  classical
  let D : Finset (TriadicCube d) := overlapCentersAtDepth Q j
  let A : Finset (TriadicCube d) := D.filter (fun S => P.weight S x ≠ 0)
  let F : TriadicCube d → Vec d → ℝ :=
    fun S y => (h y i - overlapCubeAverageVec S h i) ^ 2
  have hactive_eq :
      A.sum (fun S => F S x) =
        A.sum
          (fun S => (openOverlapCubeSet S).indicator (F S) x) := by
    refine Finset.sum_congr rfl ?_
    intro S hS_active
    have hS_mem : S ∈ D := by
      simpa [A] using (Finset.mem_of_mem_filter S hS_active)
    have hS_weight : P.weight S x ≠ 0 := by
      simpa [A] using (Finset.mem_filter.mp hS_active).2
    have hxS : x ∈ openOverlapCubeSet S :=
      P.support_subset (by simpa [D] using hS_mem) hx hS_weight
    simp [Set.indicator, hxS, F]
  calc
    A.sum (fun S => F S x)
        =
          A.sum
            (fun S => (openOverlapCubeSet S).indicator (F S) x) :=
          hactive_eq
    _ ≤
          D.sum
            (fun S => (openOverlapCubeSet S).indicator (F S) x) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _)
            (by
              intro S _hSD _hSnot
              by_cases hxS : x ∈ openOverlapCubeSet S
              · simp [Set.indicator, hxS, F, sq_nonneg]
              · simp [Set.indicator, hxS])
    _ =
        (overlapCentersAtDepth Q j).sum
          (fun S =>
            (openOverlapCubeSet S).indicator
              (fun y : Vec d => (h y i - overlapCubeAverageVec S h i) ^ 2) x) := by
          rfl

/-- Vector-valued pointwise residual bound, obtained by summing the coordinate
active-center estimates. -/
theorem vecNormSq_sub_averagingField_le_activeCard_mul_activeSum_vecNormSq
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    {x : Vec d} (hx : x ∈ openCubeSet Q) :
    vecNormSq (h x - P.averagingField h x) ≤
      (((overlapCentersAtDepth Q j).filter
          (fun S => P.weight S x ≠ 0)).card : ℝ) *
        ((overlapCentersAtDepth Q j).filter
          (fun S => P.weight S x ≠ 0)).sum
          (fun S => vecNormSq (h x - overlapCubeAverageVec S h)) := by
  classical
  let A : Finset (TriadicCube d) :=
    (overlapCentersAtDepth Q j).filter (fun S => P.weight S x ≠ 0)
  let m : ℝ := (A.card : ℝ)
  calc
    vecNormSq (h x - P.averagingField h x)
        =
          ∑ i : Fin d, ((h x - P.averagingField h x) i) ^ 2 := by
          simp [vecNormSq, vecDot, pow_two]
    _ ≤
          ∑ i : Fin d,
            m * A.sum
              (fun S => (h x i - overlapCubeAverageVec S h i) ^ 2) := by
          refine Finset.sum_le_sum ?_
          intro i _hi
          simpa [A, m] using
            P.sub_averagingField_apply_sq_le_activeCard_mul_activeSum_overlap_fluctuation_sq
              h hx i
    _ =
          m * ∑ i : Fin d,
            A.sum (fun S => (h x i - overlapCubeAverageVec S h i) ^ 2) := by
          rw [Finset.mul_sum]
    _ =
          m * A.sum
            (fun S =>
              ∑ i : Fin d, (h x i - overlapCubeAverageVec S h i) ^ 2) := by
          rw [Finset.sum_comm]
    _ =
          m * A.sum
            (fun S => vecNormSq (h x - overlapCubeAverageVec S h)) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro S _hS
          simp [vecNormSq, vecDot, pow_two]
    _ =
      (((overlapCentersAtDepth Q j).filter
          (fun S => P.weight S x ≠ 0)).card : ℝ) *
        ((overlapCentersAtDepth Q j).filter
          (fun S => P.weight S x ≠ 0)).sum
          (fun S => vecNormSq (h x - overlapCubeAverageVec S h)) := by
          rfl

/-- Vector-valued active sums are dominated by overlap-cube indicator sums,
retaining the support information from the partition. -/
theorem activeSum_vecNormSq_le_sum_openOverlap_indicator
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    {x : Vec d} (hx : x ∈ openCubeSet Q) :
    ((overlapCentersAtDepth Q j).filter
        (fun S => P.weight S x ≠ 0)).sum
        (fun S => vecNormSq (h x - overlapCubeAverageVec S h)) ≤
      (overlapCentersAtDepth Q j).sum
        (fun S =>
          (openOverlapCubeSet S).indicator
            (fun y : Vec d => vecNormSq (h y - overlapCubeAverageVec S h)) x) := by
  classical
  let D : Finset (TriadicCube d) := overlapCentersAtDepth Q j
  let A : Finset (TriadicCube d) := D.filter (fun S => P.weight S x ≠ 0)
  let F : TriadicCube d → Vec d → ℝ :=
    fun S y => vecNormSq (h y - overlapCubeAverageVec S h)
  have hactive_eq :
      A.sum (fun S => F S x) =
        A.sum
          (fun S => (openOverlapCubeSet S).indicator (F S) x) := by
    refine Finset.sum_congr rfl ?_
    intro S hS_active
    have hS_mem : S ∈ D := by
      simpa [A] using (Finset.mem_of_mem_filter S hS_active)
    have hS_weight : P.weight S x ≠ 0 := by
      simpa [A] using (Finset.mem_filter.mp hS_active).2
    have hxS : x ∈ openOverlapCubeSet S :=
      P.support_subset (by simpa [D] using hS_mem) hx hS_weight
    simp [Set.indicator, hxS, F]
  calc
    A.sum (fun S => F S x)
        =
          A.sum
            (fun S => (openOverlapCubeSet S).indicator (F S) x) :=
          hactive_eq
    _ ≤
          D.sum
            (fun S => (openOverlapCubeSet S).indicator (F S) x) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _)
            (by
              intro S _hSD _hSnot
              by_cases hxS : x ∈ openOverlapCubeSet S
              · simp [Set.indicator, hxS, F, vecNormSq_nonneg]
              · simp [Set.indicator, hxS])
    _ =
        (overlapCentersAtDepth Q j).sum
          (fun S =>
            (openOverlapCubeSet S).indicator
              (fun y : Vec d => vecNormSq (h y - overlapCubeAverageVec S h)) x) := by
          rfl

/-- Pointwise residual energy estimate with the abstract active-cardinality
constant from the partition. -/
theorem exists_vecNormSq_sub_averagingField_le_activeBound_mul_sum_openOverlap_indicator
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d) :
    ∃ M : ℕ,
      ∀ {x : Vec d}, x ∈ openCubeSet Q →
        vecNormSq (h x - P.averagingField h x) ≤
          (M : ℝ) *
            (overlapCentersAtDepth Q j).sum
              (fun S =>
                (openOverlapCubeSet S).indicator
                  (fun y : Vec d => vecNormSq (h y - overlapCubeAverageVec S h)) x) := by
  refine ⟨P.activeCardBound, ?_⟩
  intro x hx
  let A : Finset (TriadicCube d) :=
    (overlapCentersAtDepth Q j).filter (fun S => P.weight S x ≠ 0)
  let localEnergy : ℝ :=
    A.sum (fun S => vecNormSq (h x - overlapCubeAverageVec S h))
  let indicators : ℝ :=
    (overlapCentersAtDepth Q j).sum
      (fun S =>
        (openOverlapCubeSet S).indicator
          (fun y : Vec d => vecNormSq (h y - overlapCubeAverageVec S h)) x)
  have hres :
      vecNormSq (h x - P.averagingField h x) ≤
        (A.card : ℝ) * localEnergy := by
    simpa [A, localEnergy] using
      P.vecNormSq_sub_averagingField_le_activeCard_mul_activeSum_vecNormSq h hx
  have hcard : (A.card : ℝ) ≤ (P.activeCardBound : ℝ) := by
    exact_mod_cast P.active_card_bound hx
  have hlocal_nonneg : 0 ≤ localEnergy := by
    dsimp [localEnergy]
    exact Finset.sum_nonneg fun S _hS => vecNormSq_nonneg _
  have hlocal_le_indicators : localEnergy ≤ indicators := by
    simpa [A, localEnergy, indicators] using
      P.activeSum_vecNormSq_le_sum_openOverlap_indicator h hx
  have hindicators_nonneg : 0 ≤ indicators :=
    hlocal_nonneg.trans hlocal_le_indicators
  calc
    vecNormSq (h x - P.averagingField h x)
        ≤ (A.card : ℝ) * localEnergy := hres
    _ ≤ (P.activeCardBound : ℝ) * localEnergy :=
          mul_le_mul_of_nonneg_right hcard hlocal_nonneg
    _ ≤ (P.activeCardBound : ℝ) * indicators := by
          exact mul_le_mul_of_nonneg_left hlocal_le_indicators (by positivity)
    _ =
        (P.activeCardBound : ℝ) *
          (overlapCentersAtDepth Q j).sum
            (fun S =>
              (openOverlapCubeSet S).indicator
                (fun y : Vec d => vecNormSq (h y - overlapCubeAverageVec S h)) x) := by
          rfl

/-- `ENNReal` pointwise residual energy estimate using closed overlap-cube
indicators.  This is the form designed to integrate against
`normalizedCubeMeasure Q`. -/
theorem exists_ofReal_vecNormSq_sub_averagingField_le_activeBound_mul_sum_overlap_indicator
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d) :
    ∃ M : ℕ,
      ∀ {x : Vec d}, x ∈ openCubeSet Q →
        ENNReal.ofReal (vecNormSq (h x - P.averagingField h x)) ≤
          (M : ℝ≥0∞) *
            (overlapCentersAtDepth Q j).sum
              (fun S =>
                (overlapCubeSet S).indicator
                  (fun y : Vec d =>
                    ENNReal.ofReal
                      (vecNormSq (h y - overlapCubeAverageVec S h))) x) := by
  classical
  rcases P.exists_vecNormSq_sub_averagingField_le_activeBound_mul_sum_openOverlap_indicator
      h with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro x hx
  let openRealSum : ℝ :=
    (overlapCentersAtDepth Q j).sum
      (fun S =>
        (openOverlapCubeSet S).indicator
          (fun y : Vec d => vecNormSq (h y - overlapCubeAverageVec S h)) x)
  let overlapRealSum : ℝ :=
    (overlapCentersAtDepth Q j).sum
      (fun S =>
        (overlapCubeSet S).indicator
          (fun y : Vec d => vecNormSq (h y - overlapCubeAverageVec S h)) x)
  let overlapEnnSum : ℝ≥0∞ :=
    (overlapCentersAtDepth Q j).sum
      (fun S =>
        (overlapCubeSet S).indicator
          (fun y : Vec d =>
            ENNReal.ofReal
              (vecNormSq (h y - overlapCubeAverageVec S h))) x)
  have hopen_le_overlap : openRealSum ≤ overlapRealSum := by
    dsimp [openRealSum, overlapRealSum]
    refine Finset.sum_le_sum ?_
    intro S _hS
    by_cases hxOpen : x ∈ openOverlapCubeSet S
    · have hxClosed : x ∈ overlapCubeSet S :=
        openOverlapCubeSet_subset_overlapCubeSet S hxOpen
      simp [Set.indicator, hxOpen, hxClosed]
    · by_cases hxClosed : x ∈ overlapCubeSet S
      · simp [Set.indicator, hxOpen, hxClosed, vecNormSq_nonneg]
      · simp [Set.indicator, hxOpen, hxClosed]
  have hoverlap_nonneg : 0 ≤ overlapRealSum := by
    dsimp [overlapRealSum]
    refine Finset.sum_nonneg ?_
    intro S _hS
    by_cases hxS : x ∈ overlapCubeSet S
    · simp [Set.indicator, hxS, vecNormSq_nonneg]
    · simp [Set.indicator, hxS]
  have hreal :
      vecNormSq (h x - P.averagingField h x) ≤
        (M : ℝ) * overlapRealSum := by
    calc
      vecNormSq (h x - P.averagingField h x)
          ≤ (M : ℝ) * openRealSum := by
            simpa [openRealSum] using hM hx
      _ ≤ (M : ℝ) * overlapRealSum := by
            exact mul_le_mul_of_nonneg_left hopen_le_overlap
              (Nat.cast_nonneg M)
  have hsum_ofReal : ENNReal.ofReal overlapRealSum = overlapEnnSum := by
    dsimp [overlapRealSum, overlapEnnSum]
    rw [ENNReal.ofReal_sum_of_nonneg]
    · refine Finset.sum_congr rfl ?_
      intro S _hS
      by_cases hxS : x ∈ overlapCubeSet S
      · simp [Set.indicator, hxS]
      · simp [Set.indicator, hxS]
    · intro S _hS
      by_cases hxS : x ∈ overlapCubeSet S
      · simp [Set.indicator, hxS, vecNormSq_nonneg]
      · simp [Set.indicator, hxS]
  calc
    ENNReal.ofReal (vecNormSq (h x - P.averagingField h x))
        ≤ ENNReal.ofReal ((M : ℝ) * overlapRealSum) :=
          ENNReal.ofReal_le_ofReal hreal
    _ = (M : ℝ≥0∞) * overlapEnnSum := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg M)]
          rw [ENNReal.ofReal_natCast, hsum_ofReal]

/-- Integrated `lintegral` residual-energy estimate for the overlap averaging
competitor.  The only measurability input is the family of closed-overlap
fluctuation indicators needed by the finite-sum integral comparison. -/
theorem exists_lintegral_ofReal_vecNormSq_sub_averagingField_le
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    (hfQ :
      ∀ S ∈ overlapCentersAtDepth Q j,
        AEMeasurable
          ((overlapCubeSet S).indicator
            (fun y : Vec d =>
              ENNReal.ofReal
                (vecNormSq (h y - overlapCubeAverageVec S h))))
          (MeasureTheory.volume.restrict (cubeSet Q))) :
    ∃ M : ℕ,
      ∫⁻ x,
          ENNReal.ofReal (vecNormSq (h x - P.averagingField h x))
          ∂ normalizedCubeMeasure Q
        ≤
          (M : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
            (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
              (overlapCentersAtDepth Q j).sum
                (fun S =>
                  ∫⁻ x,
                    ENNReal.ofReal
                      (vecNormSq (h x - overlapCubeAverageVec S h))
                    ∂ normalizedOverlapCubeMeasure S)) := by
  classical
  rcases P.exists_ofReal_vecNormSq_sub_averagingField_le_activeBound_mul_sum_overlap_indicator
      h with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  let Fsum : Vec d → ℝ≥0∞ :=
    fun x =>
      (overlapCentersAtDepth Q j).sum
        (fun S =>
          (overlapCubeSet S).indicator
            (fun y : Vec d =>
              ENNReal.ofReal
                (vecNormSq (h y - overlapCubeAverageVec S h))) x)
  have hpoint :
      (fun x =>
          ENNReal.ofReal (vecNormSq (h x - P.averagingField h x))) ≤ᵐ[
        normalizedCubeMeasure Q] fun x => (M : ℝ≥0∞) * Fsum x := by
    filter_upwards [ae_openCubeSet_normalizedCubeMeasure Q] with x hx
    simpa [Fsum] using hM hx
  have hlin :
      ∫⁻ x,
          ENNReal.ofReal (vecNormSq (h x - P.averagingField h x))
          ∂ normalizedCubeMeasure Q
        ≤
          ∫⁻ x, (M : ℝ≥0∞) * Fsum x ∂ normalizedCubeMeasure Q :=
    MeasureTheory.lintegral_mono_ae hpoint
  have hconst :
      ∫⁻ x, (M : ℝ≥0∞) * Fsum x ∂ normalizedCubeMeasure Q =
        (M : ℝ≥0∞) *
          ∫⁻ x, Fsum x ∂ normalizedCubeMeasure Q := by
    rw [MeasureTheory.lintegral_const_mul'
      (r := (M : ℝ≥0∞)) (f := Fsum)]
    norm_num
  have hoverlap :
      ∫⁻ x, Fsum x ∂ normalizedCubeMeasure Q
        ≤
          (3 ^ d : ℝ≥0∞) *
            (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
              (overlapCentersAtDepth Q j).sum
                (fun S =>
                  ∫⁻ x,
                    ENNReal.ofReal
                      (vecNormSq (h x - overlapCubeAverageVec S h))
                    ∂ normalizedOverlapCubeMeasure S)) := by
    simpa [Fsum] using
      overlapCentersAtDepth_lintegral_sum_indicator_normalizedCubeMeasure_le
        (Q := Q) (j := j)
        (f := fun S x =>
          ENNReal.ofReal (vecNormSq (h x - overlapCubeAverageVec S h)))
        hfQ
  calc
    ∫⁻ x,
        ENNReal.ofReal (vecNormSq (h x - P.averagingField h x))
        ∂ normalizedCubeMeasure Q
        ≤
          ∫⁻ x, (M : ℝ≥0∞) * Fsum x ∂ normalizedCubeMeasure Q := hlin
    _ =
          (M : ℝ≥0∞) *
            ∫⁻ x, Fsum x ∂ normalizedCubeMeasure Q := hconst
    _ ≤
          (M : ℝ≥0∞) *
            ((3 ^ d : ℝ≥0∞) *
              (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
                (overlapCentersAtDepth Q j).sum
                (fun S =>
                  ∫⁻ x,
                    ENNReal.ofReal
                      (vecNormSq (h x - overlapCubeAverageVec S h))
                    ∂ normalizedOverlapCubeMeasure S))) := by
          exact mul_le_mul_of_nonneg_left hoverlap
            (zero_le : (0 : ℝ≥0∞) ≤ (M : ℝ≥0∞))
    _ =
          (M : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
            (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
              (overlapCentersAtDepth Q j).sum
                (fun S =>
                  ∫⁻ x,
                    ENNReal.ofReal
                      (vecNormSq (h x - overlapCubeAverageVec S h))
                    ∂ normalizedOverlapCubeMeasure S)) := by
          rw [mul_assoc]

/-- Real squared `L²` residual estimate for the overlap averaging competitor,
packaged from the `lintegral` estimate.  The finiteness hypothesis is
intentional: without it, `ENNReal.toReal` would turn an infinite upper bound
into zero. -/
theorem exists_cubeLpNorm_sq_sub_averagingField_le
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    (hfQ :
      ∀ S ∈ overlapCentersAtDepth Q j,
        AEMeasurable
          ((overlapCubeSet S).indicator
            (fun y : Vec d =>
              ENNReal.ofReal
                (vecNormSq (h y - overlapCubeAverageVec S h))))
          (MeasureTheory.volume.restrict (cubeSet Q))) :
    ∃ M : ℕ,
      ∀ _hfinite :
        ((M : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
          (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
            (overlapCentersAtDepth Q j).sum
              (fun S =>
                ∫⁻ x,
                  ENNReal.ofReal
                    (vecNormSq (h x - overlapCubeAverageVec S h))
                  ∂ normalizedOverlapCubeMeasure S))) ≠ ∞,
        (cubeLpNorm Q (2 : ℝ≥0∞)
          (fun x => h x - P.averagingField h x)) ^ 2 ≤
          (((M : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
            (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
              (overlapCentersAtDepth Q j).sum
                (fun S =>
                  ∫⁻ x,
                    ENNReal.ofReal
                      (vecNormSq (h x - overlapCubeAverageVec S h))
                    ∂ normalizedOverlapCubeMeasure S)))).toReal := by
  rcases P.exists_lintegral_ofReal_vecNormSq_sub_averagingField_le h hfQ
    with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro hfinite
  exact
    cubeLpNorm_two_sq_le_lintegral_ofReal_vecNormSq_toReal_of_le
      (Q := Q)
      (F := fun x => h x - P.averagingField h x)
      hfinite hM

/-- Squared residual estimate against the existing overlapping positive depth
average.  This is the residual half of the averaging-competitor estimate,
before taking square roots. -/
theorem exists_cubeLpNorm_sq_sub_averagingField_le_mul_depthAverage
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    (hfQ :
      ∀ S ∈ overlapCentersAtDepth Q j,
        AEMeasurable
          ((overlapCubeSet S).indicator
            (fun y : Vec d =>
              ENNReal.ofReal
                (vecNormSq (h y - overlapCubeAverageVec S h))))
          (MeasureTheory.volume.restrict (cubeSet Q)))
    (hloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp h (2 : ℝ≥0∞)
          (normalizedOverlapCubeMeasure S)) :
    ∃ C : ℝ, 0 ≤ C ∧
      (cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x => h x - P.averagingField h x)) ^ 2 ≤
        C * cubeBesovOverlappingPositiveVectorDepthAverage Q h j := by
  classical
  rcases P.exists_cubeLpNorm_sq_sub_averagingField_le h hfQ with ⟨M, hM⟩
  let A : ℝ≥0∞ :=
    (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
      (overlapCentersAtDepth Q j).sum
        (fun S =>
          ∫⁻ x,
            ENNReal.ofReal
              (vecNormSq (h x - overlapCubeAverageVec S h))
            ∂ normalizedOverlapCubeMeasure S))
  let B : ℝ≥0∞ :=
    (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
      (overlapCentersAtDepth Q j).sum
        (fun S =>
          ∫⁻ x,
            ‖overlapCubeFluctuationVec S h x‖ₑ ^ (2 : ℝ)
            ∂ normalizedOverlapCubeMeasure S))
  let C : ℝ := (M : ℝ) * (3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ)
  refine ⟨C, by positivity, ?_⟩
  have hres_sq :
      (cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x => h x - P.averagingField h x)) ^ 2 ≤
        (((M : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) * A).toReal) := by
    have hfinite :
        ((M : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) * A) ≠ ∞ := by
      simpa [A] using
        residualEuclideanOverlapBound_ne_top_of_memLp_overlap Q h j M hloc
    simpa [A] using hM hfinite
  have hA_le : A ≤ (Fintype.card (Fin d) : ℝ≥0∞) * B := by
    simpa [A, B] using
      overlapCentersAtDepth_average_lintegral_ofReal_vecNormSq_fluctuation_le
        Q j h
  have hB_ne : B ≠ ∞ := by
    simpa [B] using
      overlapCentersAtDepth_average_lintegral_fluctuation_ne_top Q h j hloc
  have hright_ne :
      (M : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
          ((Fintype.card (Fin d) : ℝ≥0∞) * B) ≠ ∞ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by simp : (M : ℝ≥0∞) ≠ ∞)
        (by simp : (3 ^ d : ℝ≥0∞) ≠ ∞))
      (ENNReal.mul_ne_top
        (by simp : (Fintype.card (Fin d) : ℝ≥0∞) ≠ ∞) hB_ne)
  have hA_toReal :
      (((M : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) * A).toReal) ≤
        (((M : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
          ((Fintype.card (Fin d) : ℝ≥0∞) * B)).toReal) := by
    refine ENNReal.toReal_mono hright_ne ?_
    exact mul_le_mul_of_nonneg_left hA_le (zero_le)
  have hB_toReal :
      B.toReal = cubeBesovOverlappingPositiveVectorDepthAverage Q h j := by
    have hfin :
        ∀ S ∈ overlapCentersAtDepth Q j,
          (∫⁻ x,
            ‖overlapCubeFluctuationVec S h x‖ₑ ^ (2 : ℝ)
            ∂ normalizedOverlapCubeMeasure S) ≠ ∞ := by
      intro S hS
      exact lintegral_overlapCubeFluctuationVec_rpow_enorm_two_ne_top S h
        (hloc S hS)
    simpa [B] using
      toReal_overlapCentersAtDepth_average_lintegral_fluctuation_eq_depthAverage
        Q h j hfin
  have hconst_toReal :
      (((M : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
          ((Fintype.card (Fin d) : ℝ≥0∞) * B)).toReal) =
        C * cubeBesovOverlappingPositiveVectorDepthAverage Q h j := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul]
    simp [C, hB_toReal]
    ring
  calc
    (cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x => h x - P.averagingField h x)) ^ 2
        ≤ (((M : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) * A).toReal) := hres_sq
    _ ≤
        (((M : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
          ((Fintype.card (Fin d) : ℝ≥0∞) * B)).toReal) := hA_toReal
    _ = C * cubeBesovOverlappingPositiveVectorDepthAverage Q h j := hconst_toReal

theorem exists_cubeLpNorm_sub_averagingField_le_mul_sqrt_depthAverage
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    (hfQ :
      ∀ S ∈ overlapCentersAtDepth Q j,
        AEMeasurable
          ((overlapCubeSet S).indicator
            (fun y : Vec d =>
              ENNReal.ofReal
                (vecNormSq (h y - overlapCubeAverageVec S h))))
          (MeasureTheory.volume.restrict (cubeSet Q)))
    (hloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp h (2 : ℝ≥0∞)
          (normalizedOverlapCubeMeasure S)) :
    ∃ C : ℝ, 0 ≤ C ∧
      cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x => h x - P.averagingField h x) ≤
        C * Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q h j) := by
  rcases P.exists_cubeLpNorm_sq_sub_averagingField_le_mul_depthAverage h hfQ hloc
    with ⟨C2, hC2_nonneg, hsq⟩
  refine ⟨Real.sqrt C2, Real.sqrt_nonneg _, ?_⟩
  let A : ℝ :=
    cubeLpNorm Q (2 : ℝ≥0∞)
      (fun x => h x - P.averagingField h x)
  let D : ℝ := cubeBesovOverlappingPositiveVectorDepthAverage Q h j
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact cubeLpNorm_nonneg Q (2 : ℝ≥0∞)
      (fun x => h x - P.averagingField h x)
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    exact cubeBesovOverlappingPositiveVectorDepthAverage_nonneg Q h j
  have hright_nonneg : 0 ≤ Real.sqrt C2 * Real.sqrt D :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq' : A ^ 2 ≤ (Real.sqrt C2 * Real.sqrt D) ^ 2 := by
    calc
      A ^ 2 ≤ C2 * D := by
        simpa [A, D] using hsq
      _ = (Real.sqrt C2 * Real.sqrt D) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hC2_nonneg, Real.sq_sqrt hD_nonneg]
  have hle : A ≤ Real.sqrt C2 * Real.sqrt D :=
    (sq_le_sq₀ hA_nonneg hright_nonneg).mp hsq'
  simpa [A, D] using hle

theorem exists_cubeLpNorm_sq_sub_averagingField_le_mul_depthAverage_of_memLp_overlap
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    (hloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp h (2 : ℝ≥0∞)
          (normalizedOverlapCubeMeasure S)) :
    ∃ C : ℝ, 0 ≤ C ∧
      (cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x => h x - P.averagingField h x)) ^ 2 ≤
        C * cubeBesovOverlappingPositiveVectorDepthAverage Q h j := by
  refine
    P.exists_cubeLpNorm_sq_sub_averagingField_le_mul_depthAverage h ?_ hloc
  intro S hS
  exact aemeasurable_overlapCubeResidualIndicator_of_memLp hS (hloc S hS)

theorem exists_cubeLpNorm_sub_averagingField_le_mul_sqrt_depthAverage_of_memLp_overlap
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    (hloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp h (2 : ℝ≥0∞)
          (normalizedOverlapCubeMeasure S)) :
    ∃ C : ℝ, 0 ≤ C ∧
      cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x => h x - P.averagingField h x) ≤
        C * Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q h j) := by
  refine P.exists_cubeLpNorm_sub_averagingField_le_mul_sqrt_depthAverage h ?_ hloc
  intro S hS
  exact aemeasurable_overlapCubeResidualIndicator_of_memLp hS (hloc S hS)

end SmoothOverlapPartition


end

end Homogenization
