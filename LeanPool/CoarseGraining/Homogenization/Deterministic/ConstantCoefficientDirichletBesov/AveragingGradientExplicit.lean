/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.AveragingResidualExplicit

/-! # Averaging Gradient Explicit -/

@[expose] public section

namespace Homogenization

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Pointwise

namespace SmoothOverlapPartition

/-- Scalar derivative constant for the explicit overlap averaging gradient
estimate. -/
noncomputable def scalarGradientConstant {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) : ℝ :=
  Real.sqrt ((3 ^ d : ℝ) * ((3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ))) *
    P.coordDerivConstant

theorem scalarGradientConstant_nonneg {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) :
    0 ≤ P.scalarGradientConstant := by
  unfold scalarGradientConstant
  exact mul_nonneg (Real.sqrt_nonneg _) P.coordDerivConstant_nonneg

noncomputable def gradientConstant {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) : ℝ :=
  (Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ) *
    P.scalarGradientConstant

theorem gradientConstant_nonneg {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) :
    0 ≤ P.gradientConstant := by
  unfold gradientConstant
  exact mul_nonneg
    (mul_nonneg (by positivity) (by positivity))
    P.scalarGradientConstant_nonneg

/-- Pointwise scalar derivative bound for the overlap averaging field with the
explicit derivative constant stored in the partition. -/
theorem euclideanCoordDeriv_averagingField_coord_sq_le
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    {x : Vec d} (hx : x ∈ openCubeSet Q) (i k : Fin d) :
    (euclideanCoordDeriv k
        (fun y : Vec d => P.averagingField h y i) x) ^ 2 ≤
      (3 ^ d : ℝ) *
        (P.coordDerivConstant / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2 *
          (overlapCentersAtDepth Q j).sum
            (fun S =>
              (overlapCubeSet S).indicator
                (fun y : Vec d =>
                  (h y i - overlapCubeAverageVec S h i) ^ 2) x) := by
  classical
  let D : Finset (TriadicCube d) := overlapCentersAtDepth Q j
  let A : Finset (TriadicCube d) := overlapCentersAtDepthContaining Q j x
  let scale : ℝ := cubeScaleFactor Q / (3 : ℝ) ^ j
  let B : ℝ := P.coordDerivConstant / scale
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
    exact div_nonneg P.coordDerivConstant_nonneg (le_of_lt hscale_pos)
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
              simpa [a, B, scale] using
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
        (3 ^ d : ℝ) *
          (P.coordDerivConstant / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2 *
          (overlapCentersAtDepth Q j).sum
            (fun S =>
              (overlapCubeSet S).indicator
                (fun y : Vec d =>
                  (h y i - overlapCubeAverageVec S h i) ^ 2) x) := by
          simp [D, B, scale, F]
          ring

theorem ofReal_euclideanCoordDeriv_averagingField_coord_sq_le
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    {x : Vec d} (hx : x ∈ openCubeSet Q) (i k : Fin d) :
    ENNReal.ofReal
      ((euclideanCoordDeriv k
          (fun y : Vec d => P.averagingField h y i) x) ^ 2) ≤
      ENNReal.ofReal
          ((3 ^ d : ℝ) *
            (P.coordDerivConstant / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2) *
        (overlapCentersAtDepth Q j).sum
          (fun S =>
            (overlapCubeSet S).indicator
              (fun y : Vec d =>
                ENNReal.ofReal
                  ((h y i - overlapCubeAverageVec S h i) ^ 2)) x) := by
  classical
  let K : ℝ := (3 ^ d : ℝ) *
    (P.coordDerivConstant / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2
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
  have hreal :
      (euclideanCoordDeriv k
          (fun y : Vec d => P.averagingField h y i) x) ^ 2 ≤
        K * realSum := by
    simpa [K, realSum] using
      P.euclideanCoordDeriv_averagingField_coord_sq_le h hx i k
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
              (P.coordDerivConstant / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2) *
          (overlapCentersAtDepth Q j).sum
            (fun S =>
              (overlapCubeSet S).indicator
                (fun y : Vec d =>
                  ENNReal.ofReal
                    ((h y i - overlapCubeAverageVec S h i) ^ 2)) x) := by
          rfl

theorem lintegral_ofReal_euclideanCoordDeriv_averagingField_coord_sq_le
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d) (i k : Fin d) :
    ∫⁻ x,
      ENNReal.ofReal
        ((euclideanCoordDeriv k
            (fun y : Vec d => P.averagingField h y i) x) ^ 2)
      ∂ normalizedCubeMeasure Q
    ≤
      ENNReal.ofReal
          ((3 ^ d : ℝ) *
            (P.coordDerivConstant / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2) *
        ∫⁻ x,
          (overlapCentersAtDepth Q j).sum
            (fun S =>
              (overlapCubeSet S).indicator
                (fun y : Vec d =>
                  ENNReal.ofReal
                    ((h y i - overlapCubeAverageVec S h i) ^ 2)) x)
          ∂ normalizedCubeMeasure Q := by
  classical
  let K : ℝ≥0∞ :=
    ENNReal.ofReal
      ((3 ^ d : ℝ) *
        (P.coordDerivConstant / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2)
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
    simpa [K, fluct] using
      P.ofReal_euclideanCoordDeriv_averagingField_coord_sq_le h hx i k
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
              (P.coordDerivConstant / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2) *
          ∫⁻ x,
            (overlapCentersAtDepth Q j).sum
              (fun S =>
                (overlapCubeSet S).indicator
                  (fun y : Vec d =>
                    ENNReal.ofReal
                      ((h y i - overlapCubeAverageVec S h i) ^ 2)) x)
            ∂ normalizedCubeMeasure Q := by
          rfl

theorem cubeLpNorm_euclideanCoordDeriv_averagingField_coord_sq_le_depthAverage
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    (hloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp h (2 : ℝ≥0∞)
          (normalizedOverlapCubeMeasure S))
    (i k : Fin d) :
    (cubeLpNorm Q (2 : ℝ≥0∞)
      (fun x =>
        euclideanCoordDeriv k
          (fun y : Vec d => P.averagingField h y i) x)) ^ 2
    ≤
      ((3 ^ d : ℝ) *
          (P.coordDerivConstant / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2) *
        ((3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ) *
          cubeBesovOverlappingPositiveVectorDepthAverage Q h j) := by
  classical
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
    (P.coordDerivConstant / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hI_le_A :
      ∫⁻ x,
        (overlapCentersAtDepth Q j).sum
          (fun S =>
            (overlapCubeSet S).indicator
              (fun y : Vec d =>
                ENNReal.ofReal
                  ((h y i - overlapCubeAverageVec S h i) ^ 2)) x)
        ∂ normalizedCubeMeasure Q ≤
      (3 ^ d : ℝ≥0∞) * A := by
    simpa [A] using
      lintegral_sum_coord_fluctuation_indicator_le_vector_average
        Q h j i hloc
  have hlin :
      ∫⁻ x,
        ENNReal.ofReal
          ((euclideanCoordDeriv k
              (fun y : Vec d => P.averagingField h y i) x) ^ 2)
        ∂ normalizedCubeMeasure Q
      ≤ ENNReal.ofReal K * ((3 ^ d : ℝ≥0∞) * A) := by
    calc
      ∫⁻ x,
        ENNReal.ofReal
          ((euclideanCoordDeriv k
              (fun y : Vec d => P.averagingField h y i) x) ^ 2)
        ∂ normalizedCubeMeasure Q
          ≤ ENNReal.ofReal K *
              ∫⁻ x,
                (overlapCentersAtDepth Q j).sum
                  (fun S =>
                    (overlapCubeSet S).indicator
                      (fun y : Vec d =>
                        ENNReal.ofReal
                          ((h y i - overlapCubeAverageVec S h i) ^ 2)) x)
                ∂ normalizedCubeMeasure Q := by
            simpa [K] using
              P.lintegral_ofReal_euclideanCoordDeriv_averagingField_coord_sq_le h i k
      _ ≤ ENNReal.ofReal K * ((3 ^ d : ℝ≥0∞) * A) := by
            exact mul_le_mul_right hI_le_A (ENNReal.ofReal K)
  let R : ℝ≥0∞ := ENNReal.ofReal K * ((3 ^ d : ℝ≥0∞) * A)
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
      R.toReal ≤
        (ENNReal.ofReal K *
          ((3 ^ d : ℝ≥0∞) *
            ((Fintype.card (Fin d) : ℝ≥0∞) * B))).toReal := by
    refine ENNReal.toReal_mono hright_ne ?_
    dsimp [R]
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
  have htoReal :
      (∫⁻ x,
        ENNReal.ofReal
          ((euclideanCoordDeriv k
              (fun y : Vec d => P.averagingField h y i) x) ^ 2)
        ∂ normalizedCubeMeasure Q).toReal ≤ R.toReal := by
    refine ENNReal.toReal_mono ?_ hlin
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (by simp : (3 ^ d : ℝ≥0∞) ≠ ∞)
        (ne_top_of_le_ne_top
          (ENNReal.mul_ne_top
            (by simp : (Fintype.card (Fin d) : ℝ≥0∞) ≠ ∞) hB_ne)
          hA_le))
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
            (P.coordDerivConstant / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2) *
          ((3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ) *
            cubeBesovOverlappingPositiveVectorDepthAverage Q h j) := by
        rfl

theorem cubeLpNorm_euclideanCoordDeriv_averagingField_coord_le_invScale_sqrt_depthAverage
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    (hloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp h (2 : ℝ≥0∞)
          (normalizedOverlapCubeMeasure S))
    (i k : Fin d) :
    cubeLpNorm Q (2 : ℝ≥0∞)
      (fun x =>
        euclideanCoordDeriv k
          (fun y : Vec d => P.averagingField h y i) x)
    ≤
      (P.scalarGradientConstant / (cubeScaleFactor Q / (3 : ℝ) ^ j)) *
        Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q h j) := by
  let M : ℝ :=
    (3 ^ d : ℝ) * ((3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ))
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
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact div_pos
      (by
        simpa [cubeScaleFactor] using
          (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale))
      (by positivity)
  have hconst_sq :
      P.scalarGradientConstant ^ 2 = M * P.coordDerivConstant ^ 2 := by
    dsimp [scalarGradientConstant, M]
    rw [mul_pow, Real.sq_sqrt hM_nonneg]
  have hright_nonneg :
      0 ≤ (P.scalarGradientConstant / scale) * Real.sqrt D := by
    exact mul_nonneg
      (div_nonneg P.scalarGradientConstant_nonneg hscale_nonneg)
      (Real.sqrt_nonneg _)
  have hsq :
      A ^ 2 ≤ ((P.scalarGradientConstant / scale) * Real.sqrt D) ^ 2 := by
    calc
      A ^ 2
          ≤
            ((3 ^ d : ℝ) *
                (P.coordDerivConstant / scale) ^ 2) *
              ((3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ) * D) := by
            simpa [A, scale, D] using
              P.cubeLpNorm_euclideanCoordDeriv_averagingField_coord_sq_le_depthAverage
                h hloc i k
      _ = ((P.scalarGradientConstant / scale) * Real.sqrt D) ^ 2 := by
            rw [mul_pow]
            rw [Real.sq_sqrt hD_nonneg]
            field_simp [ne_of_gt hscale_pos]
            rw [hconst_sq]
            dsimp [M]
            ring
  exact (sq_le_sq₀ hA_nonneg hright_nonneg).mp hsq

theorem gradientCoordL2NormSum_averagingCompetitor_le_volume_invScale_sqrt_depthAverage
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    (hloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp h (2 : ℝ≥0∞)
          (normalizedOverlapCubeMeasure S)) :
    (P.averagingCompetitor h).gradientCoordL2NormSum ≤
      (cubeVolume Q) ^ (1 / 2 : ℝ) *
        (P.gradientConstant / (cubeScaleFactor Q / (3 : ℝ) ^ j)) *
          Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q h j) := by
  classical
  let n : ℝ := Fintype.card (Fin d)
  let scale : ℝ := cubeScaleFactor Q / (3 : ℝ) ^ j
  let D : ℝ := cubeBesovOverlappingPositiveVectorDepthAverage Q h j
  let base : ℝ :=
    (cubeVolume Q) ^ (1 / 2 : ℝ) *
      (P.scalarGradientConstant / scale) * Real.sqrt D
  have hvol_half_nonneg : 0 ≤ (cubeVolume Q) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (cubeVolume_nonneg Q) _
  have hcoord_raw :
      ∀ i k : Fin d,
        ‖((P.averagingCompetitor h).coord i).gradCoordToScalarL2 k‖ ≤
          base := by
    intro i k
    let f : Vec d → ℝ :=
      fun x => ((P.averagingCompetitor h).coord i).grad x k
    let hgi : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
      H1Function.grad_memL2_normalizedCubeMeasure
        ((P.averagingCompetitor h).coord i) k
    have hnorm_eq :
        ‖Homogenization.toScalarL2
            (memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hgi)‖ =
          ‖((P.averagingCompetitor h).coord i).gradCoordToScalarL2 k‖ := by
      congr 1
    have hnorm :
        ‖((P.averagingCompetitor h).coord i).gradCoordToScalarL2 k‖ =
          (cubeVolume Q) ^ (1 / 2 : ℝ) *
            cubeLpNorm Q (2 : ℝ≥0∞) f := by
      rw [← hnorm_eq]
      exact norm_toScalarL2_openCubeSet_eq_volume_rpow_half_mul_cubeLpNorm_two
        Q hgi
    have hcube :
        cubeLpNorm Q (2 : ℝ≥0∞) f ≤
          (P.scalarGradientConstant / scale) * Real.sqrt D := by
      simpa [f, scale, D] using
        P.cubeLpNorm_euclideanCoordDeriv_averagingField_coord_le_invScale_sqrt_depthAverage
          h hloc i k
    calc
      ‖((P.averagingCompetitor h).coord i).gradCoordToScalarL2 k‖
          = (cubeVolume Q) ^ (1 / 2 : ℝ) *
              cubeLpNorm Q (2 : ℝ≥0∞) f := hnorm
      _ ≤
          (cubeVolume Q) ^ (1 / 2 : ℝ) *
            ((P.scalarGradientConstant / scale) * Real.sqrt D) := by
          exact mul_le_mul_of_nonneg_left hcube hvol_half_nonneg
      _ = base := by
          ring
  have hsum :
      (P.averagingCompetitor h).gradientCoordL2NormSum ≤
        ∑ i : Fin d, ∑ k : Fin d, base := by
    unfold CubeVectorH1Function.gradientCoordL2NormSum
    exact Finset.sum_le_sum fun i _hi => by
      unfold H1Function.gradientCoordL2NormSum
      exact Finset.sum_le_sum fun k _hk => hcoord_raw i k
  have hsum_const :
      (∑ i : Fin d, ∑ k : Fin d, base) = n * n * base := by
    simp [n, Finset.sum_const, nsmul_eq_mul]
    ring
  calc
    (P.averagingCompetitor h).gradientCoordL2NormSum
        ≤ ∑ i : Fin d, ∑ k : Fin d, base := hsum
    _ = n * n * base := hsum_const
    _ =
        (cubeVolume Q) ^ (1 / 2 : ℝ) *
          (P.gradientConstant / (cubeScaleFactor Q / (3 : ℝ) ^ j)) *
            Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q h j) := by
        simp [base, n, scale, D, gradientConstant]
        ring

theorem rpow_neg_mul_relativeGradientCoordL2NormSum_averagingCompetitor_le_sqrt_depthAverage
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    (hloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp h (2 : ℝ≥0∞)
          (normalizedOverlapCubeMeasure S)) :
    Real.rpow (3 : ℝ) (-(j : ℝ)) *
        (P.averagingCompetitor h).relativeGradientCoordL2NormSum ≤
      P.gradientConstant *
        Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q h j) := by
  let G : CubeVectorH1Function Q := P.averagingCompetitor h
  let t : ℝ := Real.rpow (3 : ℝ) (-(j : ℝ))
  let scale : ℝ := cubeScaleFactor Q / (3 : ℝ) ^ j
  let D : ℝ := cubeBesovOverlappingPositiveVectorDepthAverage Q h j
  let α : ℝ := cubeScaleFactor Q / Real.sqrt (cubeVolume Q)
  have hraw := P.gradientCoordL2NormSum_averagingCompetitor_le_volume_invScale_sqrt_depthAverage
    h hloc
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    exact div_nonneg
      (le_of_lt <| by
        simpa [cubeScaleFactor] using
          (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale))
      (Real.sqrt_nonneg _)
  have hrel_le :
      G.relativeGradientCoordL2NormSum ≤
        α * ((cubeVolume Q) ^ (1 / 2 : ℝ) *
          (P.gradientConstant / scale) * Real.sqrt D) := by
    calc
      G.relativeGradientCoordL2NormSum
          = α * G.gradientCoordL2NormSum := by
            rfl
      _ ≤
          α * ((cubeVolume Q) ^ (1 / 2 : ℝ) *
            (P.gradientConstant / scale) * Real.sqrt D) := by
          exact mul_le_mul_of_nonneg_left (by simpa [G, scale, D] using hraw)
            hα_nonneg
  have hscaleFactor_ne : cubeScaleFactor Q ≠ 0 := by
    exact ne_of_gt <| by
      simpa [cubeScaleFactor] using
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hsqrtVol_ne : Real.sqrt (cubeVolume Q) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (cubeVolume_pos Q)
  have hpow_ne : (3 : ℝ) ^ j ≠ 0 := by
    exact pow_ne_zero j (by norm_num : (3 : ℝ) ≠ 0)
  have hscale_cancel :
      t * (α * ((cubeVolume Q) ^ (1 / 2 : ℝ) *
          (P.gradientConstant / scale) * Real.sqrt D)) =
        P.gradientConstant * Real.sqrt D := by
    dsimp [t, α, scale]
    rw [Real.rpow_neg (by norm_num : 0 ≤ (3 : ℝ))]
    rw [Real.rpow_natCast]
    rw [← Real.sqrt_eq_rpow]
    field_simp [hscaleFactor_ne, hsqrtVol_ne, hpow_ne]
  calc
    Real.rpow (3 : ℝ) (-(j : ℝ)) *
        (P.averagingCompetitor h).relativeGradientCoordL2NormSum
        = t * G.relativeGradientCoordL2NormSum := by
          rfl
    _ ≤
        t * (α * ((cubeVolume Q) ^ (1 / 2 : ℝ) *
          (P.gradientConstant / scale) * Real.sqrt D)) := by
          exact mul_le_mul_of_nonneg_left hrel_le ht_nonneg
    _ = P.gradientConstant * Real.sqrt D := hscale_cancel

end SmoothOverlapPartition

end

end Homogenization
