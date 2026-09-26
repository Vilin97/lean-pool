/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.DualityPositiveBridge.Contracts
public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.StandardProjectionSharpKernel
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfacesComponentwise

/-! # Coordinate Standard -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped BigOperators ENNReal

/-!
# Coordinate full-dual tests and the standard positive norm

This file separates the purely algebraic coordinate insertion step from the
remaining finite-overlap localization estimate.  A scalar full-dual unit test
inserted into one coordinate has controlled ordinary positive vector Besov
norm; the still-analytic bridge is the passage from that ordinary norm to the
corrected overlapping norm used by the Dirichlet theorem.
-/

private theorem cubeBesovConjExponent_two_eq_coordinateStandard :
    cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
  simpa [cubeBesovConjExponent] using
    (ENNReal.HolderConjugate.conjExponent_eq
      (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))

@[simp] theorem cubeAverageVec_coordinateVectorField_same {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (g : Vec d → ℝ) :
    cubeAverageVec Q (coordinateVectorField i g) i = cubeAverage Q g := by
  simp [cubeAverageVec]

@[simp] theorem cubeAverageVec_coordinateVectorField_of_ne {d : ℕ}
    (Q : TriadicCube d) {i j : Fin d} (hji : j ≠ i) (g : Vec d → ℝ) :
    cubeAverageVec Q (coordinateVectorField i g) j = 0 := by
  have hzero : cubeAverage Q (fun _ : Vec d => (0 : ℝ)) = 0 := by
    simpa using cubeAverage_const Q (0 : ℝ)
  simp [cubeAverageVec, coordinateVectorField, hji, hzero]

theorem cubeFluctuationVec_coordinateVectorField {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (g : Vec d → ℝ) :
    cubeFluctuationVec Q (coordinateVectorField i g) =
      coordinateVectorField i (cubeFluctuation Q g) := by
  funext x j
  by_cases hji : j = i
  · subst j
    simp [cubeFluctuationVec, cubeFluctuation, cubeAverageVec]
  · have hzero : cubeAverage Q (fun _ : Vec d => (0 : ℝ)) = 0 := by
      simpa using cubeAverage_const Q (0 : ℝ)
    simp [cubeFluctuationVec, cubeAverageVec, coordinateVectorField, hji, hzero]

theorem norm_coordinateVectorField_apply {d : ℕ}
    (i : Fin d) (g : Vec d → ℝ) (x : Vec d) :
    ‖coordinateVectorField i g x‖ = ‖g x‖ := by
  classical
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg (g x))).2 ?_
    intro j
    by_cases hji : j = i
    · subst j
      simp [coordinateVectorField]
    · simp [coordinateVectorField, hji]
  · simpa [coordinateVectorField] using
      norm_le_pi_norm (coordinateVectorField i g x) i

theorem sq_cubeLpNorm_two_coordinateVectorField {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (g : Vec d → ℝ) :
    (cubeLpNorm Q (2 : ℝ≥0∞) (coordinateVectorField i g)) ^ 2 =
      (cubeLpNorm Q (2 : ℝ≥0∞) g) ^ 2 := by
  rw [cubeLpNorm_two_sq_eq_lintegral_rpow_enorm_toReal (E := Vec d),
    cubeLpNorm_two_sq_eq_lintegral_rpow_enorm_toReal (E := ℝ)]
  congr 1
  apply MeasureTheory.lintegral_congr
  intro x
  rw [← ofReal_norm, ← ofReal_norm,
    norm_coordinateVectorField_apply]

theorem cubeBesovPositiveVectorDepthAverage_coordinateVectorField {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (g : Vec d → ℝ) (j : ℕ) :
    cubeBesovPositiveVectorDepthAverage Q (coordinateVectorField i g) j =
      cubeBesovDepthAverage Q (2 : ℝ≥0∞) g j := by
  classical
  unfold cubeBesovPositiveVectorDepthAverage cubeBesovDepthAverage
  congr 1
  funext R
  rw [cubeFluctuationVec_coordinateVectorField]
  simpa [cubeBesovOscillation, Real.rpow_natCast] using
    sq_cubeLpNorm_two_coordinateVectorField R i (cubeFluctuation R g)

theorem cubeBesovPositiveVectorDepthSeminorm_coordinateVectorField {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (i : Fin d) (g : Vec d → ℝ) (j : ℕ) :
    cubeBesovPositiveVectorDepthSeminorm Q s (coordinateVectorField i g) j =
      cubeBesovScaleWeight (-s) Q *
        cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) g j := by
  have hmul :
      cubeBesovScaleWeight (-s) Q * cubeBesovScaleWeight s Q = 1 :=
    cubeBesovScaleWeight_neg_mul_cubeBesovScaleWeight Q s
  unfold cubeBesovPositiveVectorDepthSeminorm cubeBesovDepthSeminorm
  rw [cubeBesovPositiveVectorDepthAverage_coordinateVectorField Q i g j]
  rw [cubeBesovDepthWeight_eq_scaleWeight_mul_rpow]
  have hsqrt :
      cubeBesovDepthAverage Q (2 : ℝ≥0∞) g j ^
          (1 / ENNReal.toReal (2 : ℝ≥0∞)) =
        Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) g j) := by
    rw [Real.sqrt_eq_rpow]
    norm_num
  rw [hsqrt]
  calc
    Real.rpow (3 : ℝ) (s * (j : ℝ)) *
        Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) g j)
        =
      (cubeBesovScaleWeight (-s) Q * cubeBesovScaleWeight s Q) *
        (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) g j)) := by
        rw [hmul]
        ring
    _ =
      cubeBesovScaleWeight (-s) Q *
        (cubeBesovScaleWeight s Q * Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) g j)) := by
        ring

theorem cubeBesovPositiveVectorPartialSeminormTwo_coordinateVectorField {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (i : Fin d) (g : Vec d → ℝ) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N (coordinateVectorField i g) =
      cubeBesovScaleWeight (-s) Q *
        cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g := by
  unfold cubeBesovPositiveVectorPartialSeminormTwo
  calc
    Real.sqrt
        (Finset.sum (Finset.range (N + 1)) fun j =>
          (cubeBesovPositiveVectorDepthSeminorm Q s
            (coordinateVectorField i g) j) ^ 2)
        =
      Real.sqrt
        (Finset.sum (Finset.range (N + 1)) fun j =>
          (cubeBesovScaleWeight (-s) Q *
            cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) g j) ^ 2) := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro j _hj
        rw [cubeBesovPositiveVectorDepthSeminorm_coordinateVectorField]
    _ =
      cubeBesovScaleWeight (-s) Q *
        Real.sqrt
          (Finset.sum (Finset.range (N + 1)) fun j =>
            (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) g j) ^ 2) := by
        exact sqrt_sum_sq_const_mul_eq_componentwise
          (Finset.range (N + 1)) (cubeBesovScaleWeight (-s) Q)
          (fun j => cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) g j)
          (cubeBesovScaleWeight_nonneg (-s) Q)
    _ =
      cubeBesovScaleWeight (-s) Q *
        cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g := by
        unfold cubeBesovPartialSeminorm
        rw [Real.sqrt_eq_rpow]
        norm_num

theorem cubeBesovPartialSeminorm_two_two_le_dualTestNorm_two_two {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (g : Vec d → ℝ) :
    cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g ≤
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g := by
  have hq : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
    rw [cubeBesovConjExponent_two_eq_coordinateStandard]
    norm_num
  rw [cubeBesovDualTestNorm_of_conjExponent_ne_top Q s (2 : ℝ≥0∞)
    (2 : ℝ≥0∞) N g hq]
  rw [cubeBesovConjExponent_two_eq_coordinateStandard]
  unfold cubeBesovPartialNorm
  exact le_add_of_nonneg_right
    (mul_nonneg (cubeBesovScaleWeight_nonneg s Q) (norm_nonneg _))

theorem cubeBesovPositiveVectorPartialSeminormTwo_coordinateVectorField_le_scaleWeight_neg
    {d : ℕ} (Q : TriadicCube d) {s : ℝ} (N : ℕ) (i : Fin d) (g : Vec d → ℝ)
    (hg : CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) g) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N (coordinateVectorField i g) ≤
      cubeBesovScaleWeight (-s) Q := by
  rw [cubeBesovPositiveVectorPartialSeminormTwo_coordinateVectorField]
  calc
    cubeBesovScaleWeight (-s) Q *
        cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g
        ≤
      cubeBesovScaleWeight (-s) Q *
        cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g := by
        exact mul_le_mul_of_nonneg_left
          (cubeBesovPartialSeminorm_two_two_le_dualTestNorm_two_two Q s N g)
          (cubeBesovScaleWeight_nonneg (-s) Q)
    _ ≤ cubeBesovScaleWeight (-s) Q * 1 := by
        exact mul_le_mul_of_nonneg_left (hg.1 N)
          (cubeBesovScaleWeight_nonneg (-s) Q)
    _ = cubeBesovScaleWeight (-s) Q := by ring

theorem sqrt_vecNormSq_cubeAverageVec_coordinateVectorField {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (g : Vec d → ℝ) :
    Real.sqrt (vecNormSq (cubeAverageVec Q (coordinateVectorField i g))) =
      ‖cubeAverage Q g‖ := by
  have hsq :
      vecNormSq (cubeAverageVec Q (coordinateVectorField i g)) =
        (cubeAverage Q g) ^ 2 := by
    classical
    rw [vecNormSq, vecDot, Finset.sum_eq_single i]
    · simp [pow_two]
    · intro j _hj hji
      have hzero : cubeAverage Q (fun _ : Vec d => (0 : ℝ)) = 0 := by
        simpa using cubeAverage_const Q (0 : ℝ)
      simp [cubeAverageVec, coordinateVectorField, hji, hzero]
    · simp
  rw [hsq, Real.sqrt_sq_eq_abs, Real.norm_eq_abs]

theorem norm_cubeAverage_le_scaleWeight_neg_of_cubeBesovDualFullTest_two_two
    {d : ℕ} (Q : TriadicCube d) {s : ℝ} (g : Vec d → ℝ)
    (hg : CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) g) :
    ‖cubeAverage Q g‖ ≤ cubeBesovScaleWeight (-s) Q := by
  have hmean :
      cubeBesovScaleWeight s Q * ‖cubeAverage Q g‖ ≤ 1 := by
    exact
      (cubeBesovScaleWeight_mul_norm_cubeAverage_le_cubeBesovDualTestNorm
        Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) 0 g).trans (hg.1 0)
  have hmul :
      cubeBesovScaleWeight (-s) Q * cubeBesovScaleWeight s Q = 1 :=
    cubeBesovScaleWeight_neg_mul_cubeBesovScaleWeight Q s
  calc
    ‖cubeAverage Q g‖
        = (cubeBesovScaleWeight (-s) Q * cubeBesovScaleWeight s Q) *
            ‖cubeAverage Q g‖ := by
          rw [hmul]
          ring
    _ =
        cubeBesovScaleWeight (-s) Q *
          (cubeBesovScaleWeight s Q * ‖cubeAverage Q g‖) := by
          ring
    _ ≤ cubeBesovScaleWeight (-s) Q * 1 := by
          exact mul_le_mul_of_nonneg_left hmean
            (cubeBesovScaleWeight_nonneg (-s) Q)
    _ = cubeBesovScaleWeight (-s) Q := by ring

/-- Standard, non-overlapping version of the coordinate full-dual bridge. -/
def UnitFullDualCoordinateStandardBridge
    (d : ℕ) [NeZero d] (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ (Q : TriadicCube d) {s : ℝ} (i : Fin d) (g : Vec d → ℝ),
      0 < s →
      s < 1 →
      CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) g →
        CubeVectorBesovHRegularity Q s (coordinateVectorField i g) ∧
          cubeBesovPositiveVectorNormTwo Q s (coordinateVectorField i g) ≤
            C * cubeBesovScaleWeight (-s) Q

theorem unitFullDualCoordinateStandardBridge
    (d : ℕ) [NeZero d] :
    UnitFullDualCoordinateStandardBridge d 2 := by
  refine ⟨by norm_num, ?_⟩
  intro Q s i g _hs _hs_lt_one hg
  have hpartial :
      ∀ N : ℕ,
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
            (coordinateVectorField i g) ≤
          cubeBesovScaleWeight (-s) Q := by
    intro N
    exact
      cubeBesovPositiveVectorPartialSeminormTwo_coordinateVectorField_le_scaleWeight_neg
        Q N i g hg
  have hreg : CubeVectorBesovHRegularity Q s (coordinateVectorField i g) := by
    refine ⟨?_, ?_⟩
    · exact coordinateVectorField_memLp_of_cubeBesovDualFullTest_two_two hg
    · exact ⟨cubeBesovScaleWeight (-s) Q, by
        rintro x ⟨N, rfl⟩
        exact hpartial N⟩
  have hsem :
      cubeBesovPositiveVectorSeminormTwo Q s (coordinateVectorField i g) ≤
        cubeBesovScaleWeight (-s) Q :=
    cubeBesovPositiveVectorSeminormTwo_le_of_partialBound Q s
      (coordinateVectorField i g) hpartial
  have hmean :
      Real.sqrt (vecNormSq (cubeAverageVec Q (coordinateVectorField i g))) ≤
        cubeBesovScaleWeight (-s) Q := by
    rw [sqrt_vecNormSq_cubeAverageVec_coordinateVectorField]
    exact norm_cubeAverage_le_scaleWeight_neg_of_cubeBesovDualFullTest_two_two
      Q g hg
  refine ⟨hreg, ?_⟩
  unfold cubeBesovPositiveVectorNormTwo
  calc
    Real.sqrt (vecNormSq (cubeAverageVec Q (coordinateVectorField i g))) +
        cubeBesovPositiveVectorSeminormTwo Q s (coordinateVectorField i g)
        ≤ cubeBesovScaleWeight (-s) Q + cubeBesovScaleWeight (-s) Q :=
          add_le_add hmean hsem
    _ = 2 * cubeBesovScaleWeight (-s) Q := by ring

/--
Low-exponent coordinate bridge with the sharp-boundary loss displayed in the
RHS.  It is only required for `s < 1/2`, exactly the summability range of the
sharp boundary kernel.
-/
def UnitFullDualCoordinateOverlappingBridgeSharpLoss
    (d : ℕ) [NeZero d] (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ (Q : TriadicCube d) {s : ℝ} (i : Fin d) (g : Vec d → ℝ),
      0 < s →
      s < 1 / 2 →
      CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) g →
        CubeVectorOverlappingBesovHRegularity Q s (coordinateVectorField i g) ∧
          cubeBesovOverlappingPositiveVectorNormTwo Q s (coordinateVectorField i g) ≤
            C * (1 + Real.sqrt (sharpBoundaryKernelLoss d s)) *
              cubeBesovScaleWeight (-s) Q

/--
Low-exponent coordinate bridge supplied by the sharp-boundary comparison.

This is the honest replacement for the old uniform all-exponents overlap
bridge: it works for `s < 1/2`, carries the explicit sharp-boundary loss, and
keeps the overlap-cube `MemLp` closure package as an input.
-/
theorem unitFullDualCoordinateOverlappingBridge_sharpBoundaryKernel
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {s : ℝ}
    (i : Fin d) (g : Vec d → ℝ)
    (hs : 0 < s) (hs_lt_half : s < 1 / 2)
    (hg : CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) g)
    (hmem : SharpBoundaryProjectionMemLp Q (coordinateVectorField i g)) :
    CubeVectorOverlappingBesovHRegularity Q s (coordinateVectorField i g) ∧
      cubeBesovOverlappingPositiveVectorNormTwo Q s (coordinateVectorField i g) ≤
        (2 * (1 + Real.sqrt (sharpBoundaryKernelLoss d s))) *
          cubeBesovScaleWeight (-s) Q := by
  have hs_lt_one : s < 1 := by nlinarith
  rcases
      (unitFullDualCoordinateStandardBridge d).2 Q i g hs hs_lt_one hg with
    ⟨hstdReg, hstdNorm⟩
  have hoverReg :
      CubeVectorOverlappingBesovHRegularity Q s (coordinateVectorField i g) :=
    CubeVectorOverlappingBesovHRegularity.of_sharpBoundaryKernel
      hs_lt_half hstdReg hmem
  have hoverNorm :
      cubeBesovOverlappingPositiveVectorNormTwo Q s (coordinateVectorField i g) ≤
        (1 + Real.sqrt (sharpBoundaryKernelLoss d s)) *
          cubeBesovPositiveVectorNormTwo Q s (coordinateVectorField i g) :=
    cubeBesovOverlappingPositiveVectorNormTwo_le_one_add_sqrt_sharpBoundaryKernel
      Q s (coordinateVectorField i g) hs_lt_half hstdReg hmem
  refine ⟨hoverReg, ?_⟩
  have hfactor_nonneg :
      0 ≤ 1 + Real.sqrt (sharpBoundaryKernelLoss d s) := by
    positivity
  calc
    cubeBesovOverlappingPositiveVectorNormTwo Q s (coordinateVectorField i g)
        ≤
          (1 + Real.sqrt (sharpBoundaryKernelLoss d s)) *
            cubeBesovPositiveVectorNormTwo Q s (coordinateVectorField i g) :=
          hoverNorm
    _ ≤
          (1 + Real.sqrt (sharpBoundaryKernelLoss d s)) *
            (2 * cubeBesovScaleWeight (-s) Q) := by
          exact mul_le_mul_of_nonneg_left hstdNorm hfactor_nonneg
    _ =
        (2 * (1 + Real.sqrt (sharpBoundaryKernelLoss d s))) *
            cubeBesovScaleWeight (-s) Q := by ring

/-- Coordinate full-dual tests satisfy the `MemLp` closure package needed by
the sharp-boundary standard-to-overlap comparison. -/
theorem sharpBoundaryProjectionMemLp_coordinateVectorField_of_cubeBesovDualFullTest_two_two
    {d : ℕ} {Q : TriadicCube d} {s : ℝ}
    (i : Fin d) (g : Vec d → ℝ)
    (hg : CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) g) :
    SharpBoundaryProjectionMemLp Q (coordinateVectorField i g) :=
  SharpBoundaryProjectionMemLp.of_memLp
    (coordinateVectorField_memLp_of_cubeBesovDualFullTest_two_two hg)

/-- The sharp-boundary coordinate bridge follows once the overlap-cube `MemLp`
closure package is available for coordinate full-dual tests. -/
theorem UnitFullDualCoordinateOverlappingBridgeSharpLoss.of_sharpBoundaryMemLp
    {d : ℕ} [NeZero d]
    (hmem :
      ∀ (Q : TriadicCube d) {s : ℝ} (i : Fin d) (g : Vec d → ℝ),
        0 < s →
        s < 1 / 2 →
        CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) g →
          SharpBoundaryProjectionMemLp Q (coordinateVectorField i g)) :
    UnitFullDualCoordinateOverlappingBridgeSharpLoss d 2 := by
  refine ⟨by norm_num, ?_⟩
  intro Q s i g hs hs_lt_half hg
  have h :=
    unitFullDualCoordinateOverlappingBridge_sharpBoundaryKernel
      Q i g hs hs_lt_half hg (hmem Q i g hs hs_lt_half hg)
  simpa [mul_assoc] using h

/-- Closed sharp-boundary coordinate full-dual bridge. -/
theorem unitFullDualCoordinateOverlappingBridgeSharpLoss
    (d : ℕ) [NeZero d] :
    UnitFullDualCoordinateOverlappingBridgeSharpLoss d 2 :=
  UnitFullDualCoordinateOverlappingBridgeSharpLoss.of_sharpBoundaryMemLp
    (fun _Q _s i g _hs _hs_lt_half hg =>
      sharpBoundaryProjectionMemLp_coordinateVectorField_of_cubeBesovDualFullTest_two_two
        i g hg)

end

end Homogenization
