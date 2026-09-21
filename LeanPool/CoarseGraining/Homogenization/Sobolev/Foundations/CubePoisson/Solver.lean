/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveH1
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCoerciveH1
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareMeanZero
import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.BasicLemmas
import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2

/-! # Solver -/

namespace Homogenization

open scoped BigOperators ENNReal Topology

/-!
# Cube-local Poisson solver and normalized-norm bridges

This file records the Poisson-solver structure used by the cube-local Poincare
arguments, together with the bridges between `MemL2On (openCubeSet Q)` and the
normalized-cube `MemLp` measure that make the variational layer applicable.
-/

theorem nonneg_le_of_sq_le_mul_self {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ 2 ≤ y * x) :
    x ≤ y := by
  by_cases hx0 : x = 0
  · rw [hx0]
    exact hy
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have h' : x * x ≤ y * x := by
      simpa [pow_two] using h
    exact (mul_le_mul_iff_of_pos_right hxpos).mp h'

/-- A mean-zero Neumann solution of `-Δw = F` on a cube, in weak form. The test
space is mean-zero `H¹`, which fixes the additive constant. -/
structure MeanZeroNeumannPoissonSolution {d : ℕ} (Q : TriadicCube d)
    (F : Vec d → ℝ) where
  w : H1MeanZeroFunction (openCubeSet Q)
  equation :
    ∀ φ : H1MeanZeroFunction (openCubeSet Q),
      ∫ x in openCubeSet Q, vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x)
        ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q, F x * φ.toH1Function x ∂MeasureTheory.volume

namespace MeanZeroNeumannPoissonSolution

variable {d : ℕ} {Q : TriadicCube d} {F : Vec d → ℝ}

@[simp] theorem equation_self (W : MeanZeroNeumannPoissonSolution Q F) :
    ∫ x in openCubeSet Q, vecDot (W.w.toH1Function.grad x) (W.w.toH1Function.grad x)
        ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q, F x * W.w.toH1Function x ∂MeasureTheory.volume :=
  W.equation W.w

end MeanZeroNeumannPoissonSolution

/-- Existence of the mean-zero Neumann Poisson solver on a cube for normalized
`L²` right-hand sides with zero normalized average. -/
def HasMeanZeroNeumannPoissonSolverOnCube {d : ℕ} (Q : TriadicCube d) : Prop :=
  ∀ F : Vec d → ℝ,
    MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q) →
    cubeAverage Q F = 0 →
    ∃ _W : MeanZeroNeumannPoissonSolution Q F, True

theorem memL2On_openCubeSet_of_memLp_normalizedCubeMeasure {d : ℕ}
    (Q : TriadicCube d) {F : Vec d → ℝ}
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    MemL2On (openCubeSet Q) F := by
  have hle :
      cubeMeasure Q ≤ ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q := by
    have hvol_nonneg : 0 ≤ cubeVolume Q := cubeVolume_nonneg Q
    have hmul :
        ENNReal.ofReal (cubeVolume Q) * ENNReal.ofReal ((cubeVolume Q)⁻¹) = 1 := by
      rw [← ENNReal.ofReal_mul hvol_nonneg]
      have hreal : cubeVolume Q * (cubeVolume Q)⁻¹ = 1 := by
        field_simp [(cubeVolume_pos Q).ne']
      rw [hreal]
      norm_num
    have heq : ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q = cubeMeasure Q := by
      rw [normalizedCubeMeasure]
      ext s
      rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.smul_apply]
      change
        ENNReal.ofReal (cubeVolume Q) *
            (ENNReal.ofReal ((cubeVolume Q)⁻¹) * (cubeMeasure Q) s) =
          (cubeMeasure Q) s
      rw [← mul_assoc, hmul, one_mul]
    exact le_of_eq heq.symm
  have hFCube :
      MeasureTheory.MemLp F (2 : ℝ≥0∞) (cubeMeasure Q) :=
    hF.of_measure_le_smul (c := ENNReal.ofReal (cubeVolume Q))
      ENNReal.ofReal_ne_top hle
  simpa [MemL2On, cubeMeasure, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
    using hFCube

private theorem real_rpow_half_le_self_add_one {a : ℝ} (ha : 0 ≤ a) :
    a ^ (1 / 2 : ℝ) ≤ a + 1 := by
  by_cases ha_le_one : a ≤ 1
  · calc
      a ^ (1 / 2 : ℝ) ≤ 1 := by
        exact Real.rpow_le_one ha ha_le_one (by norm_num)
      _ ≤ a + 1 := by linarith
  · have hone_le_a : 1 ≤ a := le_of_lt (lt_of_not_ge ha_le_one)
    calc
      a ^ (1 / 2 : ℝ) ≤ a := by
        exact Real.rpow_le_self_of_one_le hone_le_a (by norm_num)
      _ ≤ a + 1 := by linarith

theorem cubeLpNorm_two_le_volume_inv_add_one_mul_norm_toScalarL2_openCubeSet {d : ℕ}
    (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) f ≤
      ((cubeVolume Q)⁻¹ + 1) *
        ‖Homogenization.toScalarL2
          (memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hf)‖ := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume Q)⁻¹)
  let μ : MeasureTheory.Measure (Vec d) := volumeMeasureOn (openCubeSet Q)
  let hopen : MemScalarL2 (openCubeSet Q) f :=
    memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hf
  have hhalf : ((1 / (2 : ℝ≥0∞)).toReal : ℝ) = (1 / 2 : ℝ) := by
    norm_num
  have hc_le : c ^ ((1 / (2 : ℝ≥0∞)).toReal) ≤
      ENNReal.ofReal (((cubeVolume Q)⁻¹) + 1) := by
    rw [hhalf]
    dsimp [c]
    rw [ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q))
      (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    exact ENNReal.ofReal_le_ofReal
      (real_rpow_half_le_self_add_one (inv_nonneg.mpr (cubeVolume_nonneg Q)))
  have hμ_eq : cubeMeasure Q = μ := by
    dsimp [μ, volumeMeasureOn]
    exact volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q
  have hopen_norm :
      ‖Homogenization.toScalarL2 hopen‖ =
        (MeasureTheory.eLpNorm f (2 : ℝ≥0∞) μ).toReal := by
    dsimp [hopen, μ]
    rw [Homogenization.toScalarL2, MeasureTheory.Lp.norm_toLp]
  have htop :
      ENNReal.ofReal (((cubeVolume Q)⁻¹) + 1) *
          MeasureTheory.eLpNorm f (2 : ℝ≥0∞) μ ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hopen.2.ne
  have hmain :
      MeasureTheory.eLpNorm f (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ≤
        ENNReal.ofReal (((cubeVolume Q)⁻¹) + 1) *
          MeasureTheory.eLpNorm f (2 : ℝ≥0∞) μ := by
    calc
      MeasureTheory.eLpNorm f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)
          = c ^ ((1 / (2 : ℝ≥0∞)).toReal) *
              MeasureTheory.eLpNorm f (2 : ℝ≥0∞) μ := by
              rw [normalizedCubeMeasure]
              dsimp [c]
              rw [MeasureTheory.eLpNorm_smul_measure_of_ne_top
                (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
              simp [hμ_eq, μ]
      _ ≤ ENNReal.ofReal (((cubeVolume Q)⁻¹) + 1) *
          MeasureTheory.eLpNorm f (2 : ℝ≥0∞) μ := by
            exact mul_le_mul_left hc_le _
  have htoReal :
      cubeLpNorm Q (2 : ℝ≥0∞) f ≤
        (ENNReal.ofReal (((cubeVolume Q)⁻¹) + 1) *
          MeasureTheory.eLpNorm f (2 : ℝ≥0∞) μ).toReal := by
    exact ENNReal.toReal_mono htop hmain
  calc
    cubeLpNorm Q (2 : ℝ≥0∞) f
        ≤ (ENNReal.ofReal (((cubeVolume Q)⁻¹) + 1) *
          MeasureTheory.eLpNorm f (2 : ℝ≥0∞) μ).toReal := htoReal
    _ = ((cubeVolume Q)⁻¹ + 1) *
        ‖Homogenization.toScalarL2 hopen‖ := by
          rw [ENNReal.toReal_mul]
          rw [ENNReal.toReal_ofReal
            (by
              have hInv : 0 ≤ (cubeVolume Q)⁻¹ :=
                inv_nonneg.mpr (cubeVolume_nonneg Q)
              linarith)]
          rw [hopen_norm]

/-- Exact normalized-to-unnormalized `L²` conversion on an open cube.

The older inequality above uses the harmless but scale-wasteful factor
`(cubeVolume Q)⁻¹ + 1`.  For the q=2 Calderon-Zygmund path we need the exact
probability-measure normalization factor. -/
theorem cubeLpNorm_two_eq_volume_inv_rpow_half_mul_norm_toScalarL2_openCubeSet {d : ℕ}
    (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) f =
      ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
        ‖Homogenization.toScalarL2
          (memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hf)‖ := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume Q)⁻¹)
  let μ : MeasureTheory.Measure (Vec d) := volumeMeasureOn (openCubeSet Q)
  let hopen : MemScalarL2 (openCubeSet Q) f :=
    memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hf
  have hhalf : ((1 / (2 : ℝ≥0∞)).toReal : ℝ) = (1 / 2 : ℝ) := by
    norm_num
  have hμ_eq : cubeMeasure Q = μ := by
    dsimp [μ, volumeMeasureOn]
    exact volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q
  have hnorm_eq :
      cubeLpNorm Q (2 : ℝ≥0∞) f =
        (c ^ ((1 / (2 : ℝ≥0∞)).toReal) *
          MeasureTheory.eLpNorm f (2 : ℝ≥0∞) μ).toReal := by
    unfold cubeLpNorm normalizedCubeMeasure
    rw [MeasureTheory.eLpNorm_smul_measure_of_ne_top
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    simp [c, hμ_eq, μ]
  have hopen_norm :
      ‖Homogenization.toScalarL2 hopen‖ =
        (MeasureTheory.eLpNorm f (2 : ℝ≥0∞) μ).toReal := by
    dsimp [hopen, μ]
    rw [Homogenization.toScalarL2, MeasureTheory.Lp.norm_toLp]
  have hfactor :
      (c ^ ((1 / (2 : ℝ≥0∞)).toReal)).toReal =
        ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) := by
    rw [hhalf]
    dsimp [c]
    rw [ENNReal.ofReal_rpow_of_nonneg
      (inv_nonneg.mpr (cubeVolume_nonneg Q))
      (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    rw [ENNReal.toReal_ofReal
      (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q)) _)]
  rw [hnorm_eq, ENNReal.toReal_mul, hopen_norm, hfactor]

theorem norm_toScalarL2_openCubeSet_le_volume_add_one_mul_cubeLpNorm_two {d : ℕ}
    (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ‖Homogenization.toScalarL2
        (memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hf)‖ ≤
      (cubeVolume Q + 1) * cubeLpNorm Q (2 : ℝ≥0∞) f := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume Q)⁻¹)
  let μ : MeasureTheory.Measure (Vec d) := volumeMeasureOn (openCubeSet Q)
  let hopen : MemScalarL2 (openCubeSet Q) f :=
    memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hf
  have hhalf : ((1 / (2 : ℝ≥0∞)).toReal : ℝ) = (1 / 2 : ℝ) := by
    norm_num
  have hμ_eq : cubeMeasure Q = μ := by
    dsimp [μ, volumeMeasureOn]
    exact volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q
  have hc_pos : c ≠ 0 := by
    dsimp [c]
    exact ENNReal.ofReal_ne_zero_iff.2 (inv_pos.mpr (cubeVolume_pos Q))
  have hnorm_eq :
      cubeLpNorm Q (2 : ℝ≥0∞) f =
        (c ^ ((1 / (2 : ℝ≥0∞)).toReal) *
          MeasureTheory.eLpNorm f (2 : ℝ≥0∞) μ).toReal := by
    unfold cubeLpNorm normalizedCubeMeasure
    rw [MeasureTheory.eLpNorm_smul_measure_of_ne_top
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    simp [c, hμ_eq, μ]
  have hopen_norm :
      ‖Homogenization.toScalarL2 hopen‖ =
        (MeasureTheory.eLpNorm f (2 : ℝ≥0∞) μ).toReal := by
    dsimp [hopen, μ]
    rw [Homogenization.toScalarL2, MeasureTheory.Lp.norm_toLp]
  have hc_factor_pos :
      0 < (c ^ ((1 / (2 : ℝ≥0∞)).toReal)).toReal := by
    have hc_rpow_ne_zero : c ^ ((1 / (2 : ℝ≥0∞)).toReal) ≠ 0 := by
      rw [hhalf]
      exact ne_of_gt
        (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.mpr hc_pos)
          (by norm_num : 0 ≤ (1 / 2 : ℝ)))
    have hc_rpow_ne_top : c ^ ((1 / (2 : ℝ≥0∞)).toReal) ≠ ∞ := by
      rw [hhalf]
      exact ENNReal.rpow_ne_top_of_ne_zero hc_pos ENNReal.ofReal_ne_top
    exact ENNReal.toReal_pos hc_rpow_ne_zero hc_rpow_ne_top
  have hcube_eq :
      cubeLpNorm Q (2 : ℝ≥0∞) f =
        (c ^ ((1 / (2 : ℝ≥0∞)).toReal)).toReal *
          ‖Homogenization.toScalarL2 hopen‖ := by
    rw [hnorm_eq, ENNReal.toReal_mul]
    rw [hopen_norm]
  have hfactor_inv_le : ((c ^ ((1 / (2 : ℝ≥0∞)).toReal)).toReal)⁻¹ ≤
      cubeVolume Q + 1 := by
    rw [hhalf]
    dsimp [c]
    rw [ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q))
      (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    rw [ENNReal.toReal_ofReal
      (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q)) _)]
    have hvol_pos : 0 < cubeVolume Q := cubeVolume_pos Q
    have hsqrt_inv :
        (((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ))⁻¹ =
          (cubeVolume Q) ^ (1 / 2 : ℝ) := by
      rw [Real.inv_rpow (le_of_lt hvol_pos) (1 / 2 : ℝ)]
      rw [inv_inv]
    rw [hsqrt_inv]
    exact real_rpow_half_le_self_add_one (cubeVolume_nonneg Q)
  calc
    ‖Homogenization.toScalarL2 hopen‖
        = ((c ^ ((1 / (2 : ℝ≥0∞)).toReal)).toReal)⁻¹ *
          cubeLpNorm Q (2 : ℝ≥0∞) f := by
            rw [hcube_eq]
            field_simp [hc_factor_pos.ne']
    _ ≤ (cubeVolume Q + 1) * cubeLpNorm Q (2 : ℝ≥0∞) f := by
          exact mul_le_mul_of_nonneg_right hfactor_inv_le
            (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) f)

theorem norm_toScalarL2_openCubeSet_eq_volume_rpow_half_mul_cubeLpNorm_two {d : ℕ}
    (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ‖Homogenization.toScalarL2
        (memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hf)‖ =
      (cubeVolume Q) ^ (1 / 2 : ℝ) * cubeLpNorm Q (2 : ℝ≥0∞) f := by
  let A : ℝ := ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ)
  let N : ℝ :=
    ‖Homogenization.toScalarL2
        (memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hf)‖
  let L : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) f
  have hA_pos : 0 < A := by
    dsimp [A]
    exact Real.rpow_pos_of_pos (inv_pos.mpr (cubeVolume_pos Q)) _
  have hL_eq : L = A * N := by
    simpa [A, N, L] using
      cubeLpNorm_two_eq_volume_inv_rpow_half_mul_norm_toScalarL2_openCubeSet Q hf
  have hA_inv :
      A⁻¹ = (cubeVolume Q) ^ (1 / 2 : ℝ) := by
    dsimp [A]
    rw [Real.inv_rpow (le_of_lt (cubeVolume_pos Q)) (1 / 2 : ℝ)]
    rw [inv_inv]
  calc
    N = A⁻¹ * L := by
      rw [hL_eq]
      field_simp [hA_pos.ne']
    _ = (cubeVolume Q) ^ (1 / 2 : ℝ) * L := by
      rw [hA_inv]
    _ = (cubeVolume Q) ^ (1 / 2 : ℝ) *
        cubeLpNorm Q (2 : ℝ≥0∞) f := rfl

noncomputable def meanZeroNeumannPoissonSolutionOfCoerciveEstimate {d : ℕ}
    (Q : TriadicCube d) (F : Vec d → ℝ)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    MeanZeroNeumannPoissonSolution Q F := by
  letI : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hF_open : MemScalarL2 (openCubeSet Q) F := by
    simpa [MemScalarL2, volumeMeasureOn] using
      memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  let hC : H1CoerciveEstimate (openCubeSet Q) :=
    scaledTranslatedCubeMeanZeroH1CoerciveEstimate Q
  refine
    { w := H1MeanZeroFunction.scalarRhsProblemSolution (U := openCubeSet Q) hF_open hC
      equation := ?_ }
  intro φ
  simpa using
    H1MeanZeroFunction.scalarRhsProblemSolution_firstVariation_eq_integral
      (U := openCubeSet Q) hF_open hC φ

/-- Mean-zero Neumann Poisson existence on cubes, constructed from the
coercive Hilbert variational layer and the bounded-open-convex Poincare
estimate for cubes. -/
theorem cubeMeanZeroNeumannPoissonSolverOnCube {d : ℕ} (Q : TriadicCube d) :
    HasMeanZeroNeumannPoissonSolverOnCube Q := by
  intro F hF _hmean
  exact ⟨meanZeroNeumannPoissonSolutionOfCoerciveEstimate Q F hF, True.intro⟩

noncomputable def cubeMeanZeroH1CoerciveConstant {d : ℕ} (Q : TriadicCube d) : ℝ := by
  exact (scaledTranslatedCubeMeanZeroH1CoerciveEstimate Q).fixedValue

theorem cubeMeanZeroH1CoerciveConstant_nonneg {d : ℕ} (Q : TriadicCube d) :
    0 ≤ cubeMeanZeroH1CoerciveConstant Q := by
  unfold cubeMeanZeroH1CoerciveConstant
  exact (scaledTranslatedCubeMeanZeroH1CoerciveEstimate Q).constant_nonneg

theorem cubeMeanZeroH1CoerciveConstant_eq_scale_mul_unit {d : ℕ}
    (Q : TriadicCube d) :
    cubeMeanZeroH1CoerciveConstant Q =
      cubeScaleFactor Q *
        (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue := by
  unfold cubeMeanZeroH1CoerciveConstant
  rw [scaledTranslatedCubeMeanZeroH1CoerciveEstimate_constant]

theorem meanZeroNeumannPoissonSolution_norm_gradToHilbertVectorL2_le {d : ℕ}
    (Q : TriadicCube d) {F : Vec d → ℝ}
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (W : MeanZeroNeumannPoissonSolution Q F) :
    ‖W.w.gradToHilbertVectorL2‖ ≤
      cubeMeanZeroH1CoerciveConstant Q *
        ‖Homogenization.toScalarL2
          (memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hF)‖ := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let hF_open : MemScalarL2 (openCubeSet Q) F :=
    memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  let hC : H1CoerciveEstimate (openCubeSet Q) :=
    scaledTranslatedCubeMeanZeroH1CoerciveEstimate Q
  change ‖W.w.gradToHilbertVectorL2‖ ≤
    hC.fixedValue * ‖Homogenization.toScalarL2 hF_open‖
  let G : HilbertVectorL2 (openCubeSet Q) := W.w.gradToHilbertVectorL2
  have henergy_left :
      ∫ x in openCubeSet Q,
          vecDot (W.w.toH1Function.grad x) (W.w.toH1Function.grad x)
            ∂MeasureTheory.volume =
        inner ℝ G G := by
    dsimp [G]
    simpa [H1MeanZeroFunction.gradToHilbertVectorL2, H1Function.gradToHilbertVectorL2] using
      (inner_toHilbertVectorL2OfVecField_eq_integral
        (U := openCubeSet Q)
        W.w.toH1Function.grad_memVectorL2
        W.w.toH1Function.grad_memVectorL2).symm
  have hrhs_inner :
      ∫ x in openCubeSet Q, F x * W.w.toH1Function x ∂MeasureTheory.volume =
        inner ℝ (Homogenization.toScalarL2 hF_open) W.w.toScalarL2 := by
    rw [scalarInner_eq_integral]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards
        [Homogenization.coeFn_toScalarL2 hF_open,
          H1Function.coeFn_toScalarL2 W.w.toH1Function]
      with x hFx hWx
    rw [hFx]
    change F x * W.w.toH1Function.toFun x =
      F x * W.w.toH1Function.toScalarL2 x
    rw [hWx]
  have hinner_eq :
      inner ℝ G G = inner ℝ (Homogenization.toScalarL2 hF_open) W.w.toScalarL2 := by
    calc
      inner ℝ G G =
          ∫ x in openCubeSet Q,
            vecDot (W.w.toH1Function.grad x) (W.w.toH1Function.grad x)
              ∂MeasureTheory.volume := henergy_left.symm
      _ = ∫ x in openCubeSet Q, F x * W.w.toH1Function x ∂MeasureTheory.volume :=
          W.equation_self
      _ = inner ℝ (Homogenization.toScalarL2 hF_open) W.w.toScalarL2 := hrhs_inner
  have hsq_le :
      ‖G‖ ^ 2 ≤
        (hC.fixedValue * ‖Homogenization.toScalarL2 hF_open‖) * ‖G‖ := by
    calc
      ‖G‖ ^ 2 = inner ℝ G G := by
        symm
        exact real_inner_self_eq_norm_sq G
      _ = inner ℝ (Homogenization.toScalarL2 hF_open) W.w.toScalarL2 := hinner_eq
      _ ≤ |inner ℝ (Homogenization.toScalarL2 hF_open) W.w.toScalarL2| :=
        le_abs_self _
      _ ≤ ‖Homogenization.toScalarL2 hF_open‖ * ‖W.w.toScalarL2‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ ‖Homogenization.toScalarL2 hF_open‖ *
          (hC.fixedValue * W.w.gradientL2Norm) := by
            exact mul_le_mul_of_nonneg_left
              (by
                simpa [H1MeanZeroFunction.valueL2Norm] using hC.bound W.w)
              (norm_nonneg _)
      _ ≤ ‖Homogenization.toScalarL2 hF_open‖ * (hC.fixedValue * ‖G‖) := by
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            exact mul_le_mul_of_nonneg_left
              (H1MeanZeroFunction.gradientL2Norm_le_norm_gradToHilbertVectorL2
                (d := d) W.w)
              hC.constant_nonneg
      _ = (hC.fixedValue * ‖Homogenization.toScalarL2 hF_open‖) * ‖G‖ := by ring
  exact
    nonneg_le_of_sq_le_mul_self (norm_nonneg G)
      (mul_nonneg hC.constant_nonneg (norm_nonneg _)) hsq_le

theorem meanZeroNeumannPoissonSolution_sum_cubeLpNorm_grad_le {d : ℕ}
    (Q : TriadicCube d) {F : Vec d → ℝ}
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (W : MeanZeroNeumannPoissonSolution Q F) :
    ∑ i : Fin d, cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x => W.w.toH1Function.grad x i) ≤
      (((cubeVolume Q)⁻¹ + 1) * (d : ℝ) *
          cubeMeanZeroH1CoerciveConstant Q *
        (cubeVolume Q + 1)) *
        cubeLpNorm Q (2 : ℝ≥0∞) F := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let hC : H1CoerciveEstimate (openCubeSet Q) :=
    scaledTranslatedCubeMeanZeroH1CoerciveEstimate Q
  change ∑ i : Fin d, cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x => W.w.toH1Function.grad x i) ≤
      (((cubeVolume Q)⁻¹ + 1) * (d : ℝ) * hC.fixedValue *
        (cubeVolume Q + 1)) * cubeLpNorm Q (2 : ℝ≥0∞) F
  let A : ℝ := ((cubeVolume Q)⁻¹ + 1)
  let B : ℝ := cubeVolume Q + 1
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    have hInv : 0 ≤ (cubeVolume Q)⁻¹ := inv_nonneg.mpr (cubeVolume_nonneg Q)
    linarith
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    linarith [cubeVolume_nonneg Q]
  have hcoord :
      ∀ i : Fin d,
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => W.w.toH1Function.grad x i) ≤
          A * ‖W.w.toH1Function.gradCoordToScalarL2 i‖ := by
    intro i
    let hgi : MeasureTheory.MemLp (fun x => W.w.toH1Function.grad x i)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
      W.w.toH1Function.grad_memL2_normalizedCubeMeasure i
    have hnorm_eq :
        ‖Homogenization.toScalarL2
            (memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hgi)‖ =
          ‖W.w.toH1Function.gradCoordToScalarL2 i‖ := by
      congr 1
    simpa [A, hnorm_eq] using
      cubeLpNorm_two_le_volume_inv_add_one_mul_norm_toScalarL2_openCubeSet
        Q hgi
  calc
    ∑ i : Fin d, cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x => W.w.toH1Function.grad x i)
        ≤ ∑ i : Fin d, A * ‖W.w.toH1Function.gradCoordToScalarL2 i‖ := by
          exact Finset.sum_le_sum fun i _hi => hcoord i
    _ = A * W.w.toH1Function.gradientCoordL2NormSum := by
          exact (Finset.mul_sum (s := Finset.univ)
            (f := fun i : Fin d => ‖W.w.toH1Function.gradCoordToScalarL2 i‖) A).symm
    _ ≤ A * ((d : ℝ) * ‖W.w.toH1Function.gradToVectorL2‖) := by
          exact mul_le_mul_of_nonneg_left W.w.toH1Function.gradientCoordL2NormSum_le
            hA_nonneg
    _ ≤ A * ((d : ℝ) * ‖W.w.toH1Function.gradToHilbertVectorL2‖) := by
          refine mul_le_mul_of_nonneg_left ?_ hA_nonneg
          exact mul_le_mul_of_nonneg_left
            (H1Function.norm_gradToVectorL2_le_norm_gradToHilbertVectorL2
              W.w.toH1Function)
            (Nat.cast_nonneg d)
    _ ≤ A * ((d : ℝ) *
          (hC.fixedValue *
            ‖Homogenization.toScalarL2
              (memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hF)‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ hA_nonneg
          exact mul_le_mul_of_nonneg_left
            (by
              simpa [hC, H1MeanZeroFunction.gradToHilbertVectorL2] using!
                meanZeroNeumannPoissonSolution_norm_gradToHilbertVectorL2_le Q hF W)
            (Nat.cast_nonneg d)
    _ ≤ A * ((d : ℝ) * (hC.fixedValue * (B * cubeLpNorm Q (2 : ℝ≥0∞) F))) := by
          refine mul_le_mul_of_nonneg_left ?_ hA_nonneg
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d)
          exact mul_le_mul_of_nonneg_left
            (by
              simpa [B] using
                norm_toScalarL2_openCubeSet_le_volume_add_one_mul_cubeLpNorm_two Q hF)
            hC.constant_nonneg
    _ = (((cubeVolume Q)⁻¹ + 1) * (d : ℝ) * hC.fixedValue *
          (cubeVolume Q + 1)) *
        cubeLpNorm Q (2 : ℝ≥0∞) F := by
          dsimp [A, B]
          ring

theorem meanZeroNeumannPoissonSolution_sum_cubeLpNorm_grad_le_exact {d : ℕ}
    (Q : TriadicCube d) {F : Vec d → ℝ}
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (W : MeanZeroNeumannPoissonSolution Q F) :
    ∑ i : Fin d, cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x => W.w.toH1Function.grad x i) ≤
      (((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * (d : ℝ) *
          cubeMeanZeroH1CoerciveConstant Q *
        (cubeVolume Q) ^ (1 / 2 : ℝ)) *
        cubeLpNorm Q (2 : ℝ≥0∞) F := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let hC : H1CoerciveEstimate (openCubeSet Q) :=
    scaledTranslatedCubeMeanZeroH1CoerciveEstimate Q
  change ∑ i : Fin d, cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x => W.w.toH1Function.grad x i) ≤
      (((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * (d : ℝ) * hC.fixedValue *
        (cubeVolume Q) ^ (1 / 2 : ℝ)) *
        cubeLpNorm Q (2 : ℝ≥0∞) F
  let A : ℝ := ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ)
  let B : ℝ := (cubeVolume Q) ^ (1 / 2 : ℝ)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q)) _
  have hcoord :
      ∀ i : Fin d,
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => W.w.toH1Function.grad x i) =
          A * ‖W.w.toH1Function.gradCoordToScalarL2 i‖ := by
    intro i
    let hgi : MeasureTheory.MemLp (fun x => W.w.toH1Function.grad x i)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
      W.w.toH1Function.grad_memL2_normalizedCubeMeasure i
    have hnorm_eq :
        ‖Homogenization.toScalarL2
            (memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hgi)‖ =
          ‖W.w.toH1Function.gradCoordToScalarL2 i‖ := by
      congr 1
    simpa [A, hnorm_eq] using
      cubeLpNorm_two_eq_volume_inv_rpow_half_mul_norm_toScalarL2_openCubeSet
        Q hgi
  calc
    ∑ i : Fin d, cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x => W.w.toH1Function.grad x i)
        = ∑ i : Fin d, A * ‖W.w.toH1Function.gradCoordToScalarL2 i‖ := by
          exact Finset.sum_congr rfl fun i _hi => hcoord i
    _ = A * W.w.toH1Function.gradientCoordL2NormSum := by
          exact (Finset.mul_sum (s := Finset.univ)
            (f := fun i : Fin d => ‖W.w.toH1Function.gradCoordToScalarL2 i‖) A).symm
    _ ≤ A * ((d : ℝ) * ‖W.w.toH1Function.gradToVectorL2‖) := by
          exact mul_le_mul_of_nonneg_left W.w.toH1Function.gradientCoordL2NormSum_le
            hA_nonneg
    _ ≤ A * ((d : ℝ) * ‖W.w.toH1Function.gradToHilbertVectorL2‖) := by
          refine mul_le_mul_of_nonneg_left ?_ hA_nonneg
          exact mul_le_mul_of_nonneg_left
            (H1Function.norm_gradToVectorL2_le_norm_gradToHilbertVectorL2
              W.w.toH1Function)
            (Nat.cast_nonneg d)
    _ ≤ A * ((d : ℝ) *
          (hC.fixedValue *
            ‖Homogenization.toScalarL2
              (memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hF)‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ hA_nonneg
          exact mul_le_mul_of_nonneg_left
            (by
              simpa [hC, H1MeanZeroFunction.gradToHilbertVectorL2] using!
                meanZeroNeumannPoissonSolution_norm_gradToHilbertVectorL2_le Q hF W)
            (Nat.cast_nonneg d)
    _ = A * ((d : ℝ) *
          (hC.fixedValue * (B * cubeLpNorm Q (2 : ℝ≥0∞) F))) := by
          rw [norm_toScalarL2_openCubeSet_eq_volume_rpow_half_mul_cubeLpNorm_two Q hF]
    _ = (((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * (d : ℝ) * hC.fixedValue *
          (cubeVolume Q) ^ (1 / 2 : ℝ)) *
        cubeLpNorm Q (2 : ℝ≥0∞) F := by
          dsimp [A, B]
          ring

end Homogenization
