/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInterior
import LeanPool.CoarseGraining.Homogenization.Ambient.HilbertFinite
import LeanPool.CoarseGraining.Homogenization.Multiscale.NormalizedDomainCube
import LeanPool.CoarseGraining.Homogenization.Sobolev.NormalizedLp
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.DifferenceQuotient

/-! # Weak Hessian Euclidean -/

namespace Homogenization

open scoped BigOperators ENNReal

noncomputable section

/-!
# Euclidean norms for weak Hessians

This module gives the coordinate weak-Hessian carrier its canonical Euclidean
(Frobenius) pointwise magnitude and its volume-normalized `L²` norm on cubes.
The pre-existing coordinate-`ℓ¹` norm remains available for estimates proved
before this Euclidean interface was introduced.
-/

/-- Frobenius magnitude of a real matrix. -/
noncomputable def matrixFrobeniusMagnitude {d : ℕ} (A : Mat d) : ℝ :=
  Real.sqrt (∑ i : Fin d, ∑ j : Fin d, (A i j) ^ 2)

theorem matrixFrobeniusMagnitude_nonneg {d : ℕ} (A : Mat d) :
    0 ≤ matrixFrobeniusMagnitude A :=
  Real.sqrt_nonneg _

theorem sq_matrixFrobeniusMagnitude {d : ℕ} (A : Mat d) :
    matrixFrobeniusMagnitude A ^ 2 =
      ∑ i : Fin d, ∑ j : Fin d, (A i j) ^ 2 := by
  unfold matrixFrobeniusMagnitude
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _)

@[simp] theorem matrixFrobeniusMagnitude_zero {d : ℕ} :
    matrixFrobeniusMagnitude (0 : Mat d) = 0 := by
  simp [matrixFrobeniusMagnitude]

/-- The explicit matrix Frobenius magnitude agrees with the norm of the
project's Euclidean Hilbert matrix realization. -/
theorem matrixFrobeniusMagnitude_eq_norm_hilbertMat_ofMat {d : ℕ} (A : Mat d) :
    matrixFrobeniusMagnitude A = ‖HilbertMat.ofMat A‖ := by
  have hleft_nonneg : 0 ≤ matrixFrobeniusMagnitude A :=
    matrixFrobeniusMagnitude_nonneg A
  have hright_nonneg : 0 ≤ ‖HilbertMat.ofMat A‖ := norm_nonneg _
  have hsq : ‖HilbertMat.ofMat A‖ ^ 2 =
      ∑ i : Fin d, ∑ j : Fin d, A i j ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp_rw [HilbertVec.norm_sq_eq_sum_sq]
  apply (sq_eq_sq₀ hleft_nonneg hright_nonneg).mp
  calc
    matrixFrobeniusMagnitude A ^ 2 =
        ∑ i : Fin d, ∑ j : Fin d, A i j ^ 2 :=
      sq_matrixFrobeniusMagnitude A
    _ = ‖HilbertMat.ofMat A‖ ^ 2 := hsq.symm

theorem matrixFrobeniusMagnitude_le_sum_abs {d : ℕ} (A : Mat d) :
    matrixFrobeniusMagnitude A ≤ ∑ i : Fin d, ∑ j : Fin d, |A i j| := by
  have hsq :
      ∑ i : Fin d, ∑ j : Fin d, A i j ^ 2 ≤
        (∑ i : Fin d, ∑ j : Fin d, |A i j|) ^ 2 := by
    have hrow : ∀ i : Fin d,
        ∑ j : Fin d, A i j ^ 2 ≤ (∑ j : Fin d, |A i j|) ^ 2 := by
      intro i
      simpa [sq_abs, pow_two] using
        Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
          (f := fun j => |A i j|) (by intro _ _; exact abs_nonneg _)
    have hrow_nonneg : ∀ i : Fin d, 0 ≤ ∑ j : Fin d, |A i j| := by
      intro i
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    calc
      ∑ i : Fin d, ∑ j : Fin d, A i j ^ 2
          ≤ ∑ i : Fin d, (∑ j : Fin d, |A i j|) ^ 2 :=
            Finset.sum_le_sum fun i _ => hrow i
      _ ≤ (∑ i : Fin d, ∑ j : Fin d, |A i j|) ^ 2 := by
        simpa [pow_two] using
          Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
            (f := fun i => ∑ j : Fin d, |A i j|)
            (by intro i _; exact hrow_nonneg i)
  calc
    matrixFrobeniusMagnitude A
        = Real.sqrt (∑ i : Fin d, ∑ j : Fin d, A i j ^ 2) := rfl
    _ ≤ Real.sqrt ((∑ i : Fin d, ∑ j : Fin d, |A i j|) ^ 2) :=
      Real.sqrt_le_sqrt hsq
    _ = ∑ i : Fin d, ∑ j : Fin d, |A i j| := by
      rw [Real.sqrt_sq_eq_abs]
      exact abs_of_nonneg (Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => abs_nonneg _)

namespace HasWeakHessianOn

variable {d : ℕ} {U : Set (Vec d)} {u : H1Function U}

/-- Pointwise matrix Frobenius magnitude of the weak Hessian carrier. -/
noncomputable def frobeniusMagnitude (H : HasWeakHessianOn U u) : Vec d → ℝ :=
  fun x => matrixFrobeniusMagnitude (fun i j => H.hess i j x)

/-- The pointwise square of `frobeniusMagnitude` is the sum of the squares of
all weak Hessian coordinates. -/
theorem sq_frobeniusMagnitude (H : HasWeakHessianOn U u) (x : Vec d) :
    H.frobeniusMagnitude x ^ 2 =
      ∑ i : Fin d, ∑ j : Fin d, (H.hess i j x) ^ 2 := by
  exact sq_matrixFrobeniusMagnitude (fun i j => H.hess i j x)

/-- Each weak Hessian coordinate is square-integrable for normalized cube
volume whenever its carrier domain is that open cube. -/
theorem hess_memLp_normalizedCubeMeasure (Q : TriadicCube d)
    {v : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) v) (i j : Fin d) :
    MeasureTheory.MemLp (H.hess i j) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact (H.hess_memL2 i j).smul_measure ENNReal.ofReal_ne_top

/-- The pointwise Frobenius magnitude of a weak Hessian is in normalized
`L²` on every cube on which the carrier is defined. -/
theorem frobeniusMagnitude_memLp_normalizedCubeMeasure (Q : TriadicCube d)
    {v : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) v) :
    MeasureTheory.MemLp H.frobeniusMagnitude (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
  let G : Fin d → Fin d → Vec d → ℝ := fun i j x => |H.hess i j x|
  have hG : ∀ i j, MeasureTheory.MemLp (G i j) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
    intro i j
    simpa [G, Real.norm_eq_abs] using
      (H.hess_memLp_normalizedCubeMeasure Q i j).norm
  have hrow : ∀ i : Fin d, MeasureTheory.MemLp (fun x => ∑ j : Fin d, G i j x)
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    intro i
    exact MeasureTheory.memLp_finsetSum Finset.univ
      (fun j _ => hG i j)
  have hsum : MeasureTheory.MemLp (fun x => ∑ i : Fin d, ∑ j : Fin d, G i j x)
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    exact MeasureTheory.memLp_finsetSum Finset.univ (fun i _ => hrow i)
  have hsquare_meas : MeasureTheory.AEStronglyMeasurable
      (fun x => ∑ i : Fin d, ∑ j : Fin d, (H.hess i j x) ^ 2)
      (normalizedCubeMeasure Q) := by
    apply Finset.aestronglyMeasurable_fun_sum Finset.univ
    intro i _
    apply Finset.aestronglyMeasurable_fun_sum Finset.univ
    intro j _
    exact (H.hess_memLp_normalizedCubeMeasure Q i j).1.pow 2
  have hmag_meas : MeasureTheory.AEStronglyMeasurable H.frobeniusMagnitude
      (normalizedCubeMeasure Q) := by
    have hsqrt := Real.continuous_sqrt.comp_aestronglyMeasurable hsquare_meas
    simpa [frobeniusMagnitude, matrixFrobeniusMagnitude] using! hsqrt
  refine hsum.mono hmag_meas ?_
  filter_upwards with x
  have hsum_nonneg : 0 ≤ ∑ i : Fin d, ∑ j : Fin d, G i j x := by
    exact Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsum_norm : ‖∑ i : Fin d, ∑ j : Fin d, G i j x‖ =
      ∑ i : Fin d, ∑ j : Fin d, G i j x := by
    rw [Real.norm_eq_abs, abs_of_nonneg hsum_nonneg]
  rw [hsum_norm]
  change |matrixFrobeniusMagnitude (fun i j => H.hess i j x)| ≤
    ∑ i : Fin d, ∑ j : Fin d, |H.hess i j x|
  calc |matrixFrobeniusMagnitude (fun i j => H.hess i j x)|
      = matrixFrobeniusMagnitude (fun i j => H.hess i j x) :=
        abs_of_nonneg (matrixFrobeniusMagnitude_nonneg _)
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, |H.hess i j x| :=
        matrixFrobeniusMagnitude_le_sum_abs (fun i j => H.hess i j x)

theorem integral_frobeniusMagnitude_sq_eq_sum_integral (Q : TriadicCube d)
    {v : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) v) :
    ∫ x, H.frobeniusMagnitude x ^ 2 ∂normalizedCubeMeasure Q =
      ∑ i : Fin d, ∑ j : Fin d,
        ∫ x, (H.hess i j x) ^ 2 ∂normalizedCubeMeasure Q := by
  have hint : ∀ i j : Fin d, MeasureTheory.Integrable
      (fun x => (H.hess i j x) ^ 2) (normalizedCubeMeasure Q) := by
    intro i j
    simpa [Real.norm_eq_abs, sq_abs] using
      (H.hess_memLp_normalizedCubeMeasure Q i j).integrable_norm_rpow
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp : (2 : ℝ≥0∞) ≠ ∞)
  calc
    ∫ x, H.frobeniusMagnitude x ^ 2 ∂normalizedCubeMeasure Q =
        ∫ x, ∑ i : Fin d, ∑ j : Fin d, (H.hess i j x) ^ 2
          ∂normalizedCubeMeasure Q := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          exact H.sq_frobeniusMagnitude x
    _ = ∑ i : Fin d, ∫ x, ∑ j : Fin d, (H.hess i j x) ^ 2
          ∂normalizedCubeMeasure Q := by
          exact MeasureTheory.integral_finsetSum Finset.univ
            (fun i _ => MeasureTheory.integrable_finsetSum Finset.univ
              (fun j _ => hint i j))
    _ = ∑ i : Fin d, ∑ j : Fin d, ∫ x, (H.hess i j x) ^ 2
          ∂normalizedCubeMeasure Q := by
          apply Finset.sum_congr rfl
          intro i _
          exact MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hint i j)

theorem integral_hess_sq_normalizedCubeMeasure (Q : TriadicCube d)
    {v : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) v) (i j : Fin d) :
    ∫ x, (H.hess i j x) ^ 2 ∂normalizedCubeMeasure Q =
      (cubeVolume Q)⁻¹ * ‖H.hessCoordToScalarL2 i j‖ ^ 2 := by
  have hcoord :
      ‖H.hessCoordToScalarL2 i j‖ ^ 2 =
        ∫ x in openCubeSet Q, (H.hess i j x) ^ 2 ∂MeasureTheory.volume := by
    rw [hessCoordToScalarL2, Homogenization.toScalarL2, MeasureTheory.Lp.norm_toLp]
    exact toReal_eLpNorm_two_sq_eq_integral_sq (H.hess_memL2 i j)
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
    MeasureTheory.integral_smul_measure]
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (cubeVolume_nonneg Q)), hcoord]
  simp only [smul_eq_mul]

/-- The proof-carrying normalized `L²` value of the pointwise Frobenius
magnitude, on the safe half-open carrier of a cube. -/
noncomputable def frobeniusMagnitudeNormalizedLpNorm (Q : TriadicCube d)
    {v : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) v) : ℝ :=
  (cubeBoundedMeasurableDomain Q).normalizedLpNorm (2 : ℝ≥0∞)
    H.frobeniusMagnitude (by
      simpa [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
        using H.frobeniusMagnitude_memLp_normalizedCubeMeasure Q)

/-- Literal manuscript formula for the proof-carrying normalized Frobenius
`L²` value. -/
theorem frobeniusMagnitudeNormalizedLpNorm_eq_integral (Q : TriadicCube d)
    {v : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) v) :
    H.frobeniusMagnitudeNormalizedLpNorm Q =
      (∫ x, H.frobeniusMagnitude x ^ (2 : ℝ) ∂normalizedCubeMeasure Q) ^
        (1 / (2 : ℝ)) := by
  unfold frobeniusMagnitudeNormalizedLpNorm
  rw [BoundedMeasurableDomain.normalizedLpNorm_eq_normalizedLpMoment_rpow
    (cubeBoundedMeasurableDomain Q) (2 : ℝ≥0∞) (by norm_num) (by simp)]
  simp only [BoundedMeasurableDomain.normalizedLpMoment,
    cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
    ENNReal.toReal_ofNat]
  norm_num

theorem frobeniusMagnitudeNormalizedLpNorm_sq (Q : TriadicCube d)
    {v : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) v) :
    H.frobeniusMagnitudeNormalizedLpNorm Q ^ 2 =
      (cubeVolume Q)⁻¹ *
        ∑ i : Fin d, ∑ j : Fin d, ‖H.hessCoordToScalarL2 i j‖ ^ 2 := by
  have hmem : MeasureTheory.MemLp H.frobeniusMagnitude (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) :=
    H.frobeniusMagnitude_memLp_normalizedCubeMeasure Q
  have hnorm_sq : H.frobeniusMagnitudeNormalizedLpNorm Q ^ 2 =
      ∫ x, H.frobeniusMagnitude x ^ 2 ∂normalizedCubeMeasure Q := by
    let hmemU : MeasureTheory.MemLp H.frobeniusMagnitude (2 : ℝ≥0∞)
        (cubeBoundedMeasurableDomain Q).normalizedVolume := by
      simpa [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
        using hmem
    unfold frobeniusMagnitudeNormalizedLpNorm
      BoundedMeasurableDomain.normalizedLpNorm
      BoundedMeasurableDomain.normalizedLpFiniteENorm
      BoundedMeasurableDomain.normalizedLpENorm
    simpa [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using
      (toReal_eLpNorm_two_sq_eq_integral_sq hmemU)
  calc
    H.frobeniusMagnitudeNormalizedLpNorm Q ^ 2 =
        ∫ x, H.frobeniusMagnitude x ^ 2 ∂normalizedCubeMeasure Q := hnorm_sq
    _ = ∑ i : Fin d, ∑ j : Fin d,
        ∫ x, (H.hess i j x) ^ 2 ∂normalizedCubeMeasure Q :=
      H.integral_frobeniusMagnitude_sq_eq_sum_integral Q
    _ = ∑ i : Fin d, ∑ j : Fin d,
        (cubeVolume Q)⁻¹ * ‖H.hessCoordToScalarL2 i j‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact H.integral_hess_sq_normalizedCubeMeasure Q i j
    _ = (cubeVolume Q)⁻¹ *
        ∑ i : Fin d, ∑ j : Fin d, ‖H.hessCoordToScalarL2 i j‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact (Finset.mul_sum _ _ _).symm

/-- The volume-normalized `L²` Frobenius norm of a weak Hessian on an open
cube.  The inverse square-root volume factor is explicit. -/
noncomputable def frobeniusNormalizedL2 (Q : TriadicCube d)
    {v : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) v) : ℝ :=
  ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
    Real.sqrt (∑ i : Fin d, ∑ j : Fin d,
      ‖H.hessCoordToScalarL2 i j‖ ^ 2)

/-- Squared characterization of the normalized Frobenius `L²` norm. -/
theorem frobeniusNormalizedL2_sq
    (Q : TriadicCube d) {v : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) v) :
    H.frobeniusNormalizedL2 Q ^ 2 =
      (cubeVolume Q)⁻¹ *
        ∑ i : Fin d, ∑ j : Fin d, ‖H.hessCoordToScalarL2 i j‖ ^ 2 := by
  unfold frobeniusNormalizedL2
  have hvol_nonneg : 0 ≤ (cubeVolume Q)⁻¹ := by
    exact inv_nonneg.mpr (cubeVolume_nonneg Q)
  have hsum_nonneg : 0 ≤ ∑ i : Fin d, ∑ j : Fin d,
      ‖H.hessCoordToScalarL2 i j‖ ^ 2 := by
    exact Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [mul_pow]
  have hfactor_sq : ((cubeVolume Q)⁻¹ ^ (1 / 2 : ℝ)) ^ 2 =
      (cubeVolume Q)⁻¹ := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hvol_nonneg]
    norm_num
  rw [hfactor_sq]
  rw [Real.sq_sqrt hsum_nonneg]

/-- The Hilbert sum of coordinate `L²` norms is bounded by their `ℓ¹` sum. -/
theorem sqrt_sum_sq_hessCoordToScalarL2_le_hessianCoordL2NormSum
    (H : HasWeakHessianOn U u) :
    Real.sqrt (∑ i : Fin d, ∑ j : Fin d,
      ‖H.hessCoordToScalarL2 i j‖ ^ 2) ≤ H.hessianCoordL2NormSum := by
  have hsq :
      ∑ i : Fin d, ∑ j : Fin d, ‖H.hessCoordToScalarL2 i j‖ ^ 2 ≤
        (∑ i : Fin d, ∑ j : Fin d, ‖H.hessCoordToScalarL2 i j‖) ^ 2 := by
    have hrow : ∀ i : Fin d,
        ∑ j : Fin d, ‖H.hessCoordToScalarL2 i j‖ ^ 2 ≤
          (∑ j : Fin d, ‖H.hessCoordToScalarL2 i j‖) ^ 2 := by
      intro i
      simpa [pow_two] using
        Finset.sum_sq_le_sq_sum_of_nonneg
          (s := Finset.univ) (f := fun j => ‖H.hessCoordToScalarL2 i j‖)
          (by intro _ _; exact norm_nonneg _)
    have hrows_nonneg : ∀ i : Fin d,
        0 ≤ ∑ j : Fin d, ‖H.hessCoordToScalarL2 i j‖ := by
      intro i
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    calc
      ∑ i : Fin d, ∑ j : Fin d, ‖H.hessCoordToScalarL2 i j‖ ^ 2
          ≤ ∑ i : Fin d, (∑ j : Fin d, ‖H.hessCoordToScalarL2 i j‖) ^ 2 :=
            Finset.sum_le_sum fun i _ => hrow i
      _ ≤ (∑ i : Fin d, ∑ j : Fin d, ‖H.hessCoordToScalarL2 i j‖) ^ 2 := by
        simpa [pow_two] using
          Finset.sum_sq_le_sq_sum_of_nonneg
            (s := Finset.univ)
            (f := fun i => ∑ j : Fin d, ‖H.hessCoordToScalarL2 i j‖)
            (by intro i _; exact hrows_nonneg i)
  have hsum_nonneg : 0 ≤ H.hessianCoordL2NormSum :=
    H.hessianCoordL2NormSum_nonneg
  calc
    Real.sqrt (∑ i : Fin d, ∑ j : Fin d,
        ‖H.hessCoordToScalarL2 i j‖ ^ 2)
        ≤ Real.sqrt (H.hessianCoordL2NormSum ^ 2) := Real.sqrt_le_sqrt hsq
    _ = H.hessianCoordL2NormSum := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hsum_nonneg]

/-- Bridge from the Frobenius norm to the older volume-normalized coordinate
`ℓ¹` Hessian norm. -/
theorem frobeniusNormalizedL2_le_volumeNormalized_hessianCoordL2NormSum
    (Q : TriadicCube d) {v : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) v) :
    H.frobeniusNormalizedL2 Q ≤
      ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * H.hessianCoordL2NormSum := by
  unfold frobeniusNormalizedL2
  exact mul_le_mul_of_nonneg_left
    H.sqrt_sum_sq_hessCoordToScalarL2_le_hessianCoordL2NormSum
    (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q)) _)

/-- The coordinate Hilbert-sum realization is exactly the proof-carrying
normalized `L²` norm of the pointwise Frobenius magnitude. -/
theorem frobeniusNormalizedL2_eq_frobeniusMagnitudeNormalizedLpNorm
    (Q : TriadicCube d) {v : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) v) :
    H.frobeniusNormalizedL2 Q = H.frobeniusMagnitudeNormalizedLpNorm Q := by
  have hleft_nonneg : 0 ≤ H.frobeniusNormalizedL2 Q := by
    unfold frobeniusNormalizedL2
    exact mul_nonneg
      (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q)) _)
      (Real.sqrt_nonneg _)
  have hright_nonneg : 0 ≤ H.frobeniusMagnitudeNormalizedLpNorm Q := by
    unfold frobeniusMagnitudeNormalizedLpNorm
      BoundedMeasurableDomain.normalizedLpNorm
      BoundedMeasurableDomain.normalizedLpFiniteENorm
      BoundedMeasurableDomain.normalizedLpENorm
    exact ENNReal.toReal_nonneg
  apply (sq_eq_sq₀ hleft_nonneg hright_nonneg).mp
  rw [H.frobeniusNormalizedL2_sq Q,
    H.frobeniusMagnitudeNormalizedLpNorm_sq Q]

/-- The normalized Frobenius `L²` value does not depend on the particular
weak-Hessian representative of an `H¹` function on an open cube. -/
theorem frobeniusNormalizedL2_eq_of_hasWeakHessianOn
    (Q : TriadicCube d) {v : H1Function (openCubeSet Q)}
    (H K : HasWeakHessianOn (openCubeSet Q) v) :
    H.frobeniusNormalizedL2 Q = K.frobeniusNormalizedL2 Q := by
  have hcoord : ∀ i j : Fin d,
      H.hessCoordToScalarL2 i j = K.hessCoordToScalarL2 i j := by
    intro i j
    apply (Homogenization.toScalarL2_eq_toScalarL2_iff
      (H.hess_memL2 i j) (K.hess_memL2 i j)).mpr
    exact HasWeakPartialDerivOn.ae_eq (isOpen_openCubeSet Q)
      (MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
        ((H.hess_memL2 i j).locallyIntegrable (by norm_num)))
      (MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
        ((K.hess_memL2 i j).locallyIntegrable (by norm_num)))
      (H.weak_second i j) (K.weak_second i j)
  unfold frobeniusNormalizedL2
  congr 3
  funext i
  apply Finset.sum_congr rfl
  intro j _
  rw [hcoord i j]

end HasWeakHessianOn

end

end Homogenization
