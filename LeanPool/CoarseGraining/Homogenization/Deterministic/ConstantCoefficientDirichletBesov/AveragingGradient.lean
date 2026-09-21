/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.CubeVectorH1

/-! # Averaging Gradient -/

namespace Homogenization

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Pointwise

namespace SmoothOverlapPartition

/-- The vector field obtained by averaging `h` on overlap cubes and blending
the averages with a smooth overlap partition. -/
noncomputable def averagingField {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d) :
    Vec d → Vec d :=
  fun x i =>
    (overlapCentersAtDepth Q j).sum
      (fun S => P.weight S x * overlapCubeAverageVec S h i)

@[simp] theorem averagingField_apply {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    (x : Vec d) (i : Fin d) :
    P.averagingField h x i =
      (overlapCentersAtDepth Q j).sum
        (fun S => P.weight S x * overlapCubeAverageVec S h i) :=
  rfl

/-- Each coordinate of the overlap averaging field is globally `C¹`, since it
is a finite linear combination of the smooth partition weights. -/
theorem contDiff_averagingField_coord {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d) (i : Fin d) :
    ContDiff ℝ 1 (fun x : Vec d => P.averagingField h x i) := by
  dsimp [averagingField]
  exact ContDiff.sum fun S _hS =>
    (P.contDiff_weight S).mul contDiff_const

/-- The overlap averaging field packaged as a coordinatewise `H¹` competitor
on the parent cube. -/
noncomputable def averagingCompetitor {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d) :
    CubeVectorH1Function Q where
  coord := fun i =>
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_openCubeSet Q)
      (P.contDiff_averagingField_coord h i)

@[simp] theorem averagingCompetitor_toField_apply {d : ℕ}
    {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    (x : Vec d) (i : Fin d) :
    (P.averagingCompetitor h).toField x i = P.averagingField h x i :=
  rfl

@[simp] theorem averagingCompetitor_coord_grad_apply {d : ℕ}
    {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    (x : Vec d) (i k : Fin d) :
    ((P.averagingCompetitor h).coord i).grad x k =
      euclideanCoordDeriv k (fun y : Vec d => P.averagingField h y i) x :=
  rfl

/-- Coordinate derivative of one component of the overlap averaging field. -/
theorem euclideanCoordDeriv_averagingField_coord_eq_sum {d : ℕ}
    {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    (x : Vec d) (i k : Fin d) :
    euclideanCoordDeriv k (fun y : Vec d => P.averagingField h y i) x =
      (overlapCentersAtDepth Q j).sum
        (fun S =>
          euclideanCoordDeriv k (P.weight S) x *
            overlapCubeAverageVec S h i) := by
  classical
  let D : Finset (TriadicCube d) := overlapCentersAtDepth Q j
  let F : TriadicCube d → Vec d → ℝ :=
    fun S y => P.weight S y * overlapCubeAverageVec S h i
  have hsum :
      fderiv ℝ (fun y : Vec d => ∑ S ∈ D, F S y) x =
        ∑ S ∈ D, fderiv ℝ (F S) x := by
    rw [fderiv_fun_sum]
    intro S _hS
    dsimp [F]
    exact ((P.contDiff_weight S).mul contDiff_const).differentiable
      (by simp) x
  calc
    euclideanCoordDeriv k (fun y : Vec d => P.averagingField h y i) x
        = (fderiv ℝ (fun y : Vec d => ∑ S ∈ D, F S y) x) (basisVec k) := by
          rfl
    _ = (∑ S ∈ D, fderiv ℝ (F S) x) (basisVec k) := by
          rw [hsum]
    _ = ∑ S ∈ D, (fderiv ℝ (F S) x) (basisVec k) := by
          simp
    _ =
        ∑ S ∈ D,
          euclideanCoordDeriv k (P.weight S) x *
            overlapCubeAverageVec S h i := by
          refine Finset.sum_congr rfl ?_
          intro S _hS
          have hdiff : DifferentiableAt ℝ (P.weight S) x :=
            (P.contDiff_weight S).differentiable (by simp) x
          dsimp [F, euclideanCoordDeriv]
          rw [fderiv_mul_const]
          · simp [mul_comm]
          · exact hdiff
    _ =
      (overlapCentersAtDepth Q j).sum
        (fun S =>
          euclideanCoordDeriv k (P.weight S) x *
            overlapCubeAverageVec S h i) := by
          rfl

/-- Coordinate derivative of the overlap averaging field after subtracting the
point value using the partition-of-unity cancellation. -/
theorem euclideanCoordDeriv_averagingField_coord_eq_sum_fluctuation {d : ℕ}
    {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    {x : Vec d} (hx : x ∈ openCubeSet Q) (i k : Fin d) :
    euclideanCoordDeriv k (fun y : Vec d => P.averagingField h y i) x =
      (overlapCentersAtDepth Q j).sum
        (fun S =>
          euclideanCoordDeriv k (P.weight S) x *
            (overlapCubeAverageVec S h i - h x i)) := by
  classical
  let D : Finset (TriadicCube d) := overlapCentersAtDepth Q j
  let a : TriadicCube d → ℝ := fun S => euclideanCoordDeriv k (P.weight S) x
  let b : TriadicCube d → ℝ := fun S => overlapCubeAverageVec S h i
  let c : ℝ := h x i
  have hzero : D.sum a = 0 := by
    simpa [D, a] using P.coordDeriv_sum_eq_zero hx k
  calc
    euclideanCoordDeriv k (fun y : Vec d => P.averagingField h y i) x
        = D.sum (fun S => a S * b S) := by
          simpa [D, a, b] using
            P.euclideanCoordDeriv_averagingField_coord_eq_sum h x i k
    _ =
        D.sum (fun S => a S * (b S - c) + a S * c) := by
          refine Finset.sum_congr rfl ?_
          intro S _hS
          ring
    _ =
        D.sum (fun S => a S * (b S - c)) + D.sum (fun S => a S * c) := by
          rw [Finset.sum_add_distrib]
    _ =
        D.sum (fun S => a S * (b S - c)) + D.sum a * c := by
          rw [Finset.sum_mul]
    _ =
        D.sum (fun S => a S * (b S - c)) := by
          rw [hzero]
          ring
    _ =
      (overlapCentersAtDepth Q j).sum
        (fun S =>
          euclideanCoordDeriv k (P.weight S) x *
            (overlapCubeAverageVec S h i - h x i)) := by
          rfl

/-- Pointwise scalar derivative bound for the overlap averaging field, in the
same localized fluctuation budget used by the residual estimate. -/
theorem exists_euclideanCoordDeriv_averagingField_coord_sq_le
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {x : Vec d}, x ∈ openCubeSet Q → ∀ i k : Fin d,
        (euclideanCoordDeriv k
            (fun y : Vec d => P.averagingField h y i) x) ^ 2 ≤
          (3 ^ d : ℝ) * (C / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2 *
            (overlapCentersAtDepth Q j).sum
              (fun S =>
                (overlapCubeSet S).indicator
                  (fun y : Vec d =>
                    (h y i - overlapCubeAverageVec S h i) ^ 2) x) := by
  classical
  let C : ℝ := P.coordDerivConstant
  have hC_nonneg : 0 ≤ C := by
    simpa [C] using P.coordDerivConstant_nonneg
  refine ⟨C, hC_nonneg, ?_⟩
  intro x hx i k
  let D : Finset (TriadicCube d) := overlapCentersAtDepth Q j
  let A : Finset (TriadicCube d) := overlapCentersAtDepthContaining Q j x
  let scale : ℝ := cubeScaleFactor Q / (3 : ℝ) ^ j
  let B : ℝ := C / scale
  let a : TriadicCube d → ℝ :=
    fun S => euclideanCoordDeriv k (P.weight S) x
  let f : TriadicCube d → ℝ :=
    fun S => overlapCubeAverageVec S h i - h x i
  let F : TriadicCube d → Vec d → ℝ :=
    fun S y => (h y i - overlapCubeAverageVec S h i) ^ 2
  let b : TriadicCube d → ℝ := fun S => a S * f S
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact div_pos
      (by
        simpa [cubeScaleFactor] using
          (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale))
      (by positivity)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact div_nonneg hC_nonneg (le_of_lt hscale_pos)
  have hderiv :
      euclideanCoordDeriv k
          (fun y : Vec d => P.averagingField h y i) x =
        D.sum b := by
    simpa [D, a, f, b] using
      P.euclideanCoordDeriv_averagingField_coord_eq_sum_fluctuation h hx i k
  have hsum_active : A.sum b = D.sum b := by
    dsimp [A, overlapCentersAtDepthContaining]
    refine Finset.sum_filter_of_ne ?_
    intro S hS hb
    by_contra hxS
    have hzero : euclideanCoordDeriv k (P.weight S) x = 0 :=
      P.coordDeriv_zero_of_not_mem_overlap (S := S) (x := x) k
        (by simpa [D] using hS) hx hxS
    have ha0 : a S = 0 := by
      simpa [a] using hzero
    exact hb (by simp [ha0])
  have hcard : (A.card : ℝ) ≤ (3 ^ d : ℝ) := by
    exact_mod_cast overlapCentersAtDepthContaining_card_le_pow Q j x
  have hA_F_nonneg : 0 ≤ A.sum (fun S => F S x) := by
    exact Finset.sum_nonneg fun S _hS => sq_nonneg _
  have hsum_sq :
      A.sum (fun S => (b S) ^ 2) ≤ B ^ 2 * A.sum (fun S => F S x) := by
    calc
      A.sum (fun S => (b S) ^ 2)
          ≤ A.sum (fun S => B ^ 2 * F S x) := by
            refine Finset.sum_le_sum ?_
            intro S hS
            have hS_mem : S ∈ D := by
              exact (mem_overlapCentersAtDepthContaining_iff.mp
                (by simpa [A] using hS)).1
            have habs : |a S| ≤ B := by
              simpa [a, B, scale, C] using
                P.coordDeriv_bound k (by simpa [D] using hS_mem) hx
            have hasq : (a S) ^ 2 ≤ B ^ 2 := by
              have hs := (sq_le_sq₀ (abs_nonneg (a S)) hB_nonneg).mpr habs
              simpa [sq_abs] using hs
            have hf_eq : (f S) ^ 2 = F S x := by
              dsimp [f, F]
              ring
            have hf_nonneg : 0 ≤ F S x := by
              dsimp [F]
              exact sq_nonneg _
            calc
              (b S) ^ 2 = (a S) ^ 2 * (f S) ^ 2 := by
                dsimp [b]
                ring
              _ = (a S) ^ 2 * F S x := by rw [hf_eq]
              _ ≤ B ^ 2 * F S x :=
                mul_le_mul_of_nonneg_right hasq hf_nonneg
      _ = B ^ 2 * A.sum (fun S => F S x) := by
            rw [Finset.mul_sum]
  have hA_to_D :
      A.sum (fun S => F S x) ≤
        D.sum
          (fun S =>
            (overlapCubeSet S).indicator (F S) x) := by
    have hactive_eq :
        A.sum (fun S => F S x) =
          A.sum
            (fun S => (overlapCubeSet S).indicator (F S) x) := by
      refine Finset.sum_congr rfl ?_
      intro S hS
      have hxS : x ∈ overlapCubeSet S :=
        (mem_overlapCentersAtDepthContaining_iff.mp
          (by simpa [A] using hS)).2
      simp [Set.indicator, hxS, F]
    calc
      A.sum (fun S => F S x)
          = A.sum
              (fun S => (overlapCubeSet S).indicator (F S) x) :=
            hactive_eq
      _ ≤ D.sum
              (fun S => (overlapCubeSet S).indicator (F S) x) := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by
                intro S hS
                exact (mem_overlapCentersAtDepthContaining_iff.mp
                  (by simpa [A] using hS)).1)
              (by
                intro S _hSD _hSnot
                by_cases hxS : x ∈ overlapCubeSet S
                · simp [Set.indicator, hxS, F, sq_nonneg]
                · simp [Set.indicator, hxS])
  have hD_nonneg :
      0 ≤ D.sum
        (fun S => (overlapCubeSet S).indicator (F S) x) := by
    exact Finset.sum_nonneg fun S _hS => by
      by_cases hxS : x ∈ overlapCubeSet S
      · simp [Set.indicator, hxS, F, sq_nonneg]
      · simp [Set.indicator, hxS]
  have hcauchy :
      (A.sum b) ^ 2 ≤ (A.card : ℝ) * A.sum (fun S => (b S) ^ 2) :=
    sq_sum_le_card_mul_sum_sq
  calc
    (euclideanCoordDeriv k
        (fun y : Vec d => P.averagingField h y i) x) ^ 2
        = (D.sum b) ^ 2 := by rw [hderiv]
    _ = (A.sum b) ^ 2 := by rw [hsum_active]
    _ ≤ (A.card : ℝ) * A.sum (fun S => (b S) ^ 2) := hcauchy
    _ ≤ (3 ^ d : ℝ) * (B ^ 2 * A.sum (fun S => F S x)) := by
          exact mul_le_mul hcard hsum_sq
            (Finset.sum_nonneg fun S _hS => sq_nonneg _)
            (by positivity)
    _ ≤ (3 ^ d : ℝ) *
          (B ^ 2 *
            D.sum
              (fun S =>
                (overlapCubeSet S).indicator (F S) x)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hA_to_D (sq_nonneg B))
            (by positivity)
    _ =
        (3 ^ d : ℝ) * (C / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2 *
          (overlapCentersAtDepth Q j).sum
            (fun S =>
              (overlapCubeSet S).indicator
                (fun y : Vec d =>
                  (h y i - overlapCubeAverageVec S h i) ^ 2) x) := by
          simp [D, B, scale, F]
          ring

/-- `ENNReal` pointwise scalar derivative estimate for the overlap averaging
field.  This is the form that can be integrated directly. -/
theorem exists_ofReal_euclideanCoordDeriv_averagingField_coord_sq_le
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {x : Vec d}, x ∈ openCubeSet Q → ∀ i k : Fin d,
        ENNReal.ofReal
          ((euclideanCoordDeriv k
              (fun y : Vec d => P.averagingField h y i) x) ^ 2) ≤
          ENNReal.ofReal
              ((3 ^ d : ℝ) *
                (C / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2) *
            (overlapCentersAtDepth Q j).sum
              (fun S =>
                (overlapCubeSet S).indicator
                  (fun y : Vec d =>
                    ENNReal.ofReal
                      ((h y i - overlapCubeAverageVec S h i) ^ 2)) x) := by
  classical
  rcases P.exists_euclideanCoordDeriv_averagingField_coord_sq_le h with
    ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro x hx i k
  let K : ℝ := (3 ^ d : ℝ) *
    (C / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2
  let realSum : ℝ :=
    (overlapCentersAtDepth Q j).sum
      (fun S =>
        (overlapCubeSet S).indicator
          (fun y : Vec d =>
            (h y i - overlapCubeAverageVec S h i) ^ 2) x)
  let ennSum : ℝ≥0∞ :=
    (overlapCentersAtDepth Q j).sum
      (fun S =>
        (overlapCubeSet S).indicator
          (fun y : Vec d =>
            ENNReal.ofReal
              ((h y i - overlapCubeAverageVec S h i) ^ 2)) x)
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hrealSum_nonneg : 0 ≤ realSum := by
    dsimp [realSum]
    refine Finset.sum_nonneg ?_
    intro S _hS
    by_cases hxS : x ∈ overlapCubeSet S
    · simp [Set.indicator, hxS, sq_nonneg]
    · simp [Set.indicator, hxS]
  have hreal :
      (euclideanCoordDeriv k
          (fun y : Vec d => P.averagingField h y i) x) ^ 2 ≤
        K * realSum := by
    simpa [K, realSum] using hC hx i k
  have hsum_ofReal : ENNReal.ofReal realSum = ennSum := by
    dsimp [realSum, ennSum]
    rw [ENNReal.ofReal_sum_of_nonneg]
    · refine Finset.sum_congr rfl ?_
      intro S _hS
      by_cases hxS : x ∈ overlapCubeSet S
      · simp [Set.indicator, hxS]
      · simp [Set.indicator, hxS]
    · intro S _hS
      by_cases hxS : x ∈ overlapCubeSet S
      · simp [Set.indicator, hxS, sq_nonneg]
      · simp [Set.indicator, hxS]
  calc
    ENNReal.ofReal
        ((euclideanCoordDeriv k
            (fun y : Vec d => P.averagingField h y i) x) ^ 2)
        ≤ ENNReal.ofReal (K * realSum) :=
          ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal K * ennSum := by
          rw [ENNReal.ofReal_mul hK_nonneg, hsum_ofReal]
    _ =
        ENNReal.ofReal
            ((3 ^ d : ℝ) *
              (C / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2) *
          (overlapCentersAtDepth Q j).sum
            (fun S =>
              (overlapCubeSet S).indicator
                (fun y : Vec d =>
                  ENNReal.ofReal
                    ((h y i - overlapCubeAverageVec S h i) ^ 2)) x) := by
          rfl

/-- Integrated scalar derivative estimate up to the localized overlap
fluctuation indicator budget. -/
theorem exists_lintegral_ofReal_euclideanCoordDeriv_averagingField_coord_sq_le
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i k : Fin d,
        ∫⁻ x,
          ENNReal.ofReal
            ((euclideanCoordDeriv k
                (fun y : Vec d => P.averagingField h y i) x) ^ 2)
          ∂ normalizedCubeMeasure Q
        ≤
          ENNReal.ofReal
              ((3 ^ d : ℝ) *
                (C / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2) *
            ∫⁻ x,
              (overlapCentersAtDepth Q j).sum
                (fun S =>
                  (overlapCubeSet S).indicator
                    (fun y : Vec d =>
                      ENNReal.ofReal
                        ((h y i - overlapCubeAverageVec S h i) ^ 2)) x)
              ∂ normalizedCubeMeasure Q := by
  classical
  rcases P.exists_ofReal_euclideanCoordDeriv_averagingField_coord_sq_le h with
    ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro i k
  let K : ℝ≥0∞ :=
    ENNReal.ofReal
      ((3 ^ d : ℝ) *
        (C / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2)
  let fluct : Vec d → ℝ≥0∞ :=
    fun x =>
      (overlapCentersAtDepth Q j).sum
        (fun S =>
          (overlapCubeSet S).indicator
            (fun y : Vec d =>
              ENNReal.ofReal
                ((h y i - overlapCubeAverageVec S h i) ^ 2)) x)
  have hK_ne_top : K ≠ ∞ := by
    dsimp [K]
    exact ENNReal.ofReal_ne_top
  have hpoint :
      (fun x =>
        ENNReal.ofReal
          ((euclideanCoordDeriv k
              (fun y : Vec d => P.averagingField h y i) x) ^ 2))
        ≤ᵐ[normalizedCubeMeasure Q]
      fun x => K * fluct x := by
    filter_upwards [ae_openCubeSet_normalizedCubeMeasure Q] with x hx
    simpa [K, fluct] using hC hx i k
  calc
    ∫⁻ x,
        ENNReal.ofReal
          ((euclideanCoordDeriv k
              (fun y : Vec d => P.averagingField h y i) x) ^ 2)
        ∂ normalizedCubeMeasure Q
        ≤ ∫⁻ x, K * fluct x ∂ normalizedCubeMeasure Q :=
          MeasureTheory.lintegral_mono_ae hpoint
    _ = K * ∫⁻ x, fluct x ∂ normalizedCubeMeasure Q := by
          rw [MeasureTheory.lintegral_const_mul' K fluct hK_ne_top]
    _ =
        ENNReal.ofReal
            ((3 ^ d : ℝ) *
              (C / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2) *
          ∫⁻ x,
            (overlapCentersAtDepth Q j).sum
              (fun S =>
                (overlapCubeSet S).indicator
                  (fun y : Vec d =>
                    ENNReal.ofReal
                      ((h y i - overlapCubeAverageVec S h i) ^ 2)) x)
            ∂ normalizedCubeMeasure Q := by
          rfl

/-- Integrated scalar derivative estimate after converting the localized
indicator budget to the vector overlap fluctuation average. -/
theorem exists_lintegral_ofReal_euclideanCoordDeriv_averagingField_coord_sq_le_vector_average
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    (hloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp h (2 : ℝ≥0∞)
          (normalizedOverlapCubeMeasure S)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i k : Fin d,
        ∫⁻ x,
          ENNReal.ofReal
            ((euclideanCoordDeriv k
                (fun y : Vec d => P.averagingField h y i) x) ^ 2)
          ∂ normalizedCubeMeasure Q
        ≤
          ENNReal.ofReal
              ((3 ^ d : ℝ) *
                (C / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2) *
            ((3 ^ d : ℝ≥0∞) *
              (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
                (overlapCentersAtDepth Q j).sum
                  (fun S =>
                    ∫⁻ x,
                      ENNReal.ofReal
                        (vecNormSq (h x - overlapCubeAverageVec S h))
                      ∂ normalizedOverlapCubeMeasure S))) := by
  classical
  rcases P.exists_lintegral_ofReal_euclideanCoordDeriv_averagingField_coord_sq_le h
    with ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro i k
  let K : ℝ≥0∞ :=
    ENNReal.ofReal
      ((3 ^ d : ℝ) *
        (C / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2)
  let I : ℝ≥0∞ :=
    ∫⁻ x,
      (overlapCentersAtDepth Q j).sum
        (fun S =>
          (overlapCubeSet S).indicator
            (fun y : Vec d =>
              ENNReal.ofReal
                ((h y i - overlapCubeAverageVec S h i) ^ 2)) x)
      ∂ normalizedCubeMeasure Q
  let A : ℝ≥0∞ :=
    (3 ^ d : ℝ≥0∞) *
      (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
        (overlapCentersAtDepth Q j).sum
          (fun S =>
            ∫⁻ x,
              ENNReal.ofReal
                (vecNormSq (h x - overlapCubeAverageVec S h))
              ∂ normalizedOverlapCubeMeasure S))
  have hI_le_A : I ≤ A := by
    simpa [I, A] using
      lintegral_sum_coord_fluctuation_indicator_le_vector_average
        Q h j i hloc
  calc
    ∫⁻ x,
        ENNReal.ofReal
          ((euclideanCoordDeriv k
              (fun y : Vec d => P.averagingField h y i) x) ^ 2)
        ∂ normalizedCubeMeasure Q
        ≤ K * I := by
          simpa [K, I] using hC i k
    _ ≤ K * A := by
          exact mul_le_mul_right hI_le_A K
    _ =
        ENNReal.ofReal
            ((3 ^ d : ℝ) *
              (C / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2) *
          ((3 ^ d : ℝ≥0∞) *
            (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
              (overlapCentersAtDepth Q j).sum
                (fun S =>
                  ∫⁻ x,
                    ENNReal.ofReal
                      (vecNormSq (h x - overlapCubeAverageVec S h))
                    ∂ normalizedOverlapCubeMeasure S))) := by
          rfl

/-- Normalized scalar `L²` version of the integrated derivative estimate,
still with the vector-overlap average as an `ENNReal.toReal` budget. -/
theorem exists_cubeLpNorm_euclideanCoordDeriv_averagingField_coord_sq_le_vector_average_toReal
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    (hloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp h (2 : ℝ≥0∞)
          (normalizedOverlapCubeMeasure S)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i k : Fin d,
        (cubeLpNorm Q (2 : ℝ≥0∞)
          (fun x =>
            euclideanCoordDeriv k
              (fun y : Vec d => P.averagingField h y i) x)) ^ 2
        ≤
          (ENNReal.ofReal
              ((3 ^ d : ℝ) *
                (C / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2) *
            ((3 ^ d : ℝ≥0∞) *
              (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
                (overlapCentersAtDepth Q j).sum
                  (fun S =>
                    ∫⁻ x,
                      ENNReal.ofReal
                        (vecNormSq (h x - overlapCubeAverageVec S h))
                      ∂ normalizedOverlapCubeMeasure S)))).toReal := by
  classical
  rcases
    P.exists_lintegral_ofReal_euclideanCoordDeriv_averagingField_coord_sq_le_vector_average
      h hloc with
    ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro i k
  let R : ℝ≥0∞ :=
    ENNReal.ofReal
      ((3 ^ d : ℝ) *
        (C / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2) *
      ((3 ^ d : ℝ≥0∞) *
        (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
          (overlapCentersAtDepth Q j).sum
            (fun S =>
              ∫⁻ x,
                ENNReal.ofReal
                  (vecNormSq (h x - overlapCubeAverageVec S h))
                ∂ normalizedOverlapCubeMeasure S)))
  have hA_ne_top :
      (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
        (overlapCentersAtDepth Q j).sum
          (fun S =>
            ∫⁻ x,
              ENNReal.ofReal
                (vecNormSq (h x - overlapCubeAverageVec S h))
              ∂ normalizedOverlapCubeMeasure S)) ≠ ∞ :=
    overlapCentersAtDepth_average_lintegral_ofReal_vecNormSq_fluctuation_ne_top
      Q h j hloc
  have hR_ne_top : R ≠ ∞ := by
    dsimp [R]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (by simp : (3 ^ d : ℝ≥0∞) ≠ ∞) hA_ne_top)
  have htoReal :
      (∫⁻ x,
          ENNReal.ofReal
            ((euclideanCoordDeriv k
                (fun y : Vec d => P.averagingField h y i) x) ^ 2)
          ∂ normalizedCubeMeasure Q).toReal ≤ R.toReal :=
    ENNReal.toReal_mono hR_ne_top (by simpa [R] using hC i k)
  calc
    (cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x =>
          euclideanCoordDeriv k
            (fun y : Vec d => P.averagingField h y i) x)) ^ 2
        =
          (∫⁻ x,
            ENNReal.ofReal
              ((euclideanCoordDeriv k
                  (fun y : Vec d => P.averagingField h y i) x) ^ 2)
            ∂ normalizedCubeMeasure Q).toReal := by
          rw [cubeLpNorm_two_sq_eq_lintegral_ofReal_sq_toReal]
    _ ≤ R.toReal := htoReal
    _ =
        (ENNReal.ofReal
            ((3 ^ d : ℝ) *
              (C / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2) *
          ((3 ^ d : ℝ≥0∞) *
            (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
              (overlapCentersAtDepth Q j).sum
                (fun S =>
                  ∫⁻ x,
                    ENNReal.ofReal
                      (vecNormSq (h x - overlapCubeAverageVec S h))
                    ∂ normalizedOverlapCubeMeasure S)))).toReal := by
          rfl

/-- Real-valued squared normalized scalar derivative bound in terms of the
overlapping positive depth average. -/
theorem exists_cubeLpNorm_euclideanCoordDeriv_averagingField_coord_sq_le_depthAverage
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    (hloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp h (2 : ℝ≥0∞)
          (normalizedOverlapCubeMeasure S)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i k : Fin d,
        (cubeLpNorm Q (2 : ℝ≥0∞)
          (fun x =>
            euclideanCoordDeriv k
              (fun y : Vec d => P.averagingField h y i) x)) ^ 2
        ≤
          ((3 ^ d : ℝ) *
              (C / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2) *
            ((3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ) *
              cubeBesovOverlappingPositiveVectorDepthAverage Q h j) := by
  classical
  rcases
    P.exists_cubeLpNorm_euclideanCoordDeriv_averagingField_coord_sq_le_vector_average_toReal
      h hloc with
    ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro i k
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
  let K : ℝ := (3 ^ d : ℝ) *
    (C / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hsq :
      (cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x =>
          euclideanCoordDeriv k
            (fun y : Vec d => P.averagingField h y i) x)) ^ 2
      ≤
        (ENNReal.ofReal K * ((3 ^ d : ℝ≥0∞) * A)).toReal := by
    simpa [K, A] using hC i k
  have hA_le : A ≤ (Fintype.card (Fin d) : ℝ≥0∞) * B := by
    simpa [A, B] using
      overlapCentersAtDepth_average_lintegral_ofReal_vecNormSq_fluctuation_le
        Q j h
  have hB_ne : B ≠ ∞ := by
    simpa [B] using
      overlapCentersAtDepth_average_lintegral_fluctuation_ne_top Q h j hloc
  have hright_ne :
      ENNReal.ofReal K *
          ((3 ^ d : ℝ≥0∞) *
            ((Fintype.card (Fin d) : ℝ≥0∞) * B)) ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top
        (by simp : (3 ^ d : ℝ≥0∞) ≠ ∞)
        (ENNReal.mul_ne_top
          (by simp : (Fintype.card (Fin d) : ℝ≥0∞) ≠ ∞) hB_ne))
  have htoReal_mono :
      (ENNReal.ofReal K * ((3 ^ d : ℝ≥0∞) * A)).toReal ≤
        (ENNReal.ofReal K *
          ((3 ^ d : ℝ≥0∞) *
            ((Fintype.card (Fin d) : ℝ≥0∞) * B))).toReal := by
    refine ENNReal.toReal_mono hright_ne ?_
    refine mul_le_mul_right ?_ _
    exact mul_le_mul_right hA_le (3 ^ d : ℝ≥0∞)
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
      (ENNReal.ofReal K *
          ((3 ^ d : ℝ≥0∞) *
            ((Fintype.card (Fin d) : ℝ≥0∞) * B))).toReal =
        K * ((3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ) *
          cubeBesovOverlappingPositiveVectorDepthAverage Q h j) := by
    rw [ENNReal.toReal_ofReal_mul K _ hK_nonneg]
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
    rw [hB_toReal]
    simp
    ring_nf
    simp
  calc
    (cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x =>
          euclideanCoordDeriv k
            (fun y : Vec d => P.averagingField h y i) x)) ^ 2
        ≤ (ENNReal.ofReal K * ((3 ^ d : ℝ≥0∞) * A)).toReal := hsq
    _ ≤
        (ENNReal.ofReal K *
          ((3 ^ d : ℝ≥0∞) *
            ((Fintype.card (Fin d) : ℝ≥0∞) * B))).toReal := htoReal_mono
    _ =
        K * ((3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ) *
          cubeBesovOverlappingPositiveVectorDepthAverage Q h j) :=
        hconst_toReal
    _ =
        ((3 ^ d : ℝ) *
            (C / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2) *
          ((3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ) *
            cubeBesovOverlappingPositiveVectorDepthAverage Q h j) := by
        rfl

/-- Square-rooted normalized scalar derivative bound for the overlap averaging
field.  The scale appears as the inverse overlap side length
`(cubeScaleFactor Q / 3^j)^{-1}`. -/
theorem exists_cubeLpNorm_euclideanCoordDeriv_averagingField_coord_le_invScale_sqrt_depthAverage
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    (hloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp h (2 : ℝ≥0∞)
          (normalizedOverlapCubeMeasure S)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i k : Fin d,
        cubeLpNorm Q (2 : ℝ≥0∞)
          (fun x =>
            euclideanCoordDeriv k
              (fun y : Vec d => P.averagingField h y i) x)
        ≤
          (C / (cubeScaleFactor Q / (3 : ℝ) ^ j)) *
            Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q h j) := by
  classical
  rcases
    P.exists_cubeLpNorm_euclideanCoordDeriv_averagingField_coord_sq_le_depthAverage
      h hloc with
    ⟨C, hC_nonneg, hC⟩
  let M : ℝ :=
    (3 ^ d : ℝ) * ((3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ))
  refine ⟨Real.sqrt M * C, mul_nonneg (Real.sqrt_nonneg _) hC_nonneg, ?_⟩
  intro i k
  let A : ℝ :=
    cubeLpNorm Q (2 : ℝ≥0∞)
      (fun x =>
        euclideanCoordDeriv k
          (fun y : Vec d => P.averagingField h y i) x)
  let scale : ℝ := cubeScaleFactor Q / (3 : ℝ) ^ j
  let D : ℝ := cubeBesovOverlappingPositiveVectorDepthAverage Q h j
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact cubeLpNorm_nonneg Q (2 : ℝ≥0∞)
      (fun x =>
        euclideanCoordDeriv k
          (fun y : Vec d => P.averagingField h y i) x)
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    exact cubeBesovOverlappingPositiveVectorDepthAverage_nonneg Q h j
  have hscale_nonneg : 0 ≤ scale := by
    dsimp [scale]
    exact div_nonneg
      (le_of_lt <| by
        simpa [cubeScaleFactor] using
          (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale))
      (by positivity)
  have hCg_sq : (Real.sqrt M * C) ^ 2 = M * C ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hM_nonneg]
  have hdivCg_sq :
      (Real.sqrt M * C / scale) ^ 2 =
        (Real.sqrt M * C) ^ 2 / scale ^ 2 := by
    ring
  have hright_nonneg :
      0 ≤ ((Real.sqrt M * C) / scale) * Real.sqrt D := by
    exact mul_nonneg
      (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hC_nonneg) hscale_nonneg)
      (Real.sqrt_nonneg _)
  have hsq :
      A ^ 2 ≤ (((Real.sqrt M * C) / scale) * Real.sqrt D) ^ 2 := by
    calc
      A ^ 2
          ≤
            ((3 ^ d : ℝ) * (C / scale) ^ 2) *
              ((3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ) * D) := by
            simpa [A, scale, D] using hC i k
      _ = (((Real.sqrt M * C) / scale) * Real.sqrt D) ^ 2 := by
            rw [mul_pow]
            rw [Real.sq_sqrt hD_nonneg]
            rw [hdivCg_sq, hCg_sq]
            dsimp [M]
            ring
  have hle : A ≤ ((Real.sqrt M * C) / scale) * Real.sqrt D :=
    (sq_le_sq₀ hA_nonneg hright_nonneg).mp hsq
  simpa [A, scale, D, M] using hle

end SmoothOverlapPartition


end

end Homogenization
