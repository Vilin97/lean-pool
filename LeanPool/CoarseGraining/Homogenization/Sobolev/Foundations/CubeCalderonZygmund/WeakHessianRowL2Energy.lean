/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.GlobalLocalization
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.WeakHessianEuclidean
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! # Weak Hessian Row L2Energy -/

namespace Homogenization

open scoped BigOperators ENNReal

noncomputable section

namespace CubeCalderonZygmund

open MeasureTheory

/-- Total square-weighted mass is exactly the square of the `L²` `eLpNorm`.
This identity itself needs no integrability assumption. -/
theorem sqWeightedMeasure_apply_univ_eq_eLpNorm_two_sq
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (f : α → E) (μ : Measure α) :
    sqWeightedMeasure f μ Set.univ = (eLpNorm f 2 μ) ^ (2 : ℕ) := by
  rw [sqWeightedMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  change (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ (2 : ℕ)) ∂μ) = _
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [← ENNReal.rpow_natCast,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    ← ENNReal.rpow_mul]
  norm_num

end CubeCalderonZygmund

namespace HasWeakHessianOn

open MeasureTheory

variable {d : ℕ} {U : Set (Vec d)} {u : H1Function U}

/-!
# Quantitative `L²` energy of one weak-Hessian row

The coordinate `L²` data in `HasWeakHessianOn` control each Euclidean
Hilbert realization of a Hessian row.  The estimates below retain the older
coordinate-`ℓ1` energy `hessianCoordL2NormSum`, which is the quantity supplied
by the quantitative weak-`H²` theory.
-/

/-- A Hilbertified Hessian row belongs to raw `L²` on the carrier domain. -/
theorem hessianHilbertRow_memLp_two (H : HasWeakHessianOn U u) (i : Fin d) :
    MemLp (hilbertifyVecField (fun x j ↦ H.hess i j x)) 2
      (volumeMeasureOn U) := by
  rw [memLp_piLp_iff]
  intro j
  simpa only [hilbertifyVecField, Function.comp_apply, HilbertVec.ofVec,
    PiLp.toLp_apply] using H.hess_memL2 i j

/-- A Hessian coordinate's raw `eLpNorm` is the extended-real realization of
the norm stored in `hessCoordToScalarL2`. -/
theorem eLpNorm_hess_eq_ofReal_norm_hessCoordToScalarL2
    (H : HasWeakHessianOn U u) (i j : Fin d) :
    eLpNorm (fun x ↦ H.hess i j x) 2 (volumeMeasureOn U) =
      ENNReal.ofReal ‖H.hessCoordToScalarL2 i j‖ := by
  calc
    eLpNorm (fun x ↦ H.hess i j x) 2 (volumeMeasureOn U) =
        ‖H.hessCoordToScalarL2 i j‖ₑ := by
      exact (Lp.enorm_toLp (H.hess_memL2 i j)).symm
    _ = ENNReal.ofReal ‖H.hessCoordToScalarL2 i j‖ :=
      (ofReal_norm _).symm

/-- The raw Euclidean `L²` norm of one Hessian row is bounded by the total
coordinate `L²` energy recorded by the weak-Hessian witness. -/
theorem eLpNorm_hessianHilbertRow_two_le
    (H : HasWeakHessianOn U u) (i : Fin d) :
    eLpNorm (hilbertifyVecField (fun x j ↦ H.hess i j x)) 2
        (volumeMeasureOn U) ≤
      ENNReal.ofReal H.hessianCoordL2NormSum := by
  let row : Vec d → HilbertVec d :=
    hilbertifyVecField (fun x j ↦ H.hess i j x)
  let singleCoord : Fin d → Vec d → HilbertVec d :=
    fun j x ↦ HilbertVec.ofVec (Pi.single j (H.hess i j x))
  have hsingle : ∀ j : Fin d, MemLp (singleCoord j) 2 (volumeMeasureOn U) := by
    intro j
    rw [memLp_piLp_iff]
    intro k
    by_cases hjk : j = k
    · subst k
      simpa only [singleCoord, Function.comp_apply, HilbertVec.ofVec,
        PiLp.toLp_apply, Pi.single_eq_same] using H.hess_memL2 i j
    · simpa only [singleCoord, Function.comp_apply, HilbertVec.ofVec,
        PiLp.toLp_apply, Pi.single_eq_of_ne (Ne.symm hjk)] using
        (MemLp.zero' : MemLp (fun _ : Vec d ↦ (0 : ℝ)) 2
          (volumeMeasureOn U))
  have hrow : row = ∑ j : Fin d, singleCoord j := by
    funext x
    ext k
    simp [row, singleCoord, hilbertifyVecField]
  have hrow_le : eLpNorm row 2 (volumeMeasureOn U) ≤
      ∑ j : Fin d, eLpNorm (fun x ↦ H.hess i j x) 2
        (volumeMeasureOn U) := by
    rw [hrow]
    refine (eLpNorm_sum_le (fun j _ ↦ (hsingle j).aestronglyMeasurable)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans_eq ?_
    apply Finset.sum_congr rfl
    intro j _
    apply eLpNorm_congr_norm_ae
    exact ae_of_all _ fun x ↦ by simp [singleCoord]
  calc
    eLpNorm (hilbertifyVecField (fun x j ↦ H.hess i j x)) 2
        (volumeMeasureOn U) = eLpNorm row 2 (volumeMeasureOn U) := rfl
    _ ≤ ∑ j : Fin d, eLpNorm (fun x ↦ H.hess i j x) 2
          (volumeMeasureOn U) := hrow_le
    _ = ∑ j : Fin d, ENNReal.ofReal ‖H.hessCoordToScalarL2 i j‖ := by
      apply Finset.sum_congr rfl
      intro j _
      exact H.eLpNorm_hess_eq_ofReal_norm_hessCoordToScalarL2 i j
    _ = ENNReal.ofReal (∑ j : Fin d, ‖H.hessCoordToScalarL2 i j‖) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      exact fun j _ ↦ norm_nonneg _
    _ ≤ ENNReal.ofReal H.hessianCoordL2NormSum := by
      apply ENNReal.ofReal_le_ofReal
      unfold hessianCoordL2NormSum
      exact Finset.single_le_sum
        (fun k _ ↦ Finset.sum_nonneg fun j _ ↦ norm_nonneg
          (H.hessCoordToScalarL2 k j))
        (Finset.mem_univ i)

/-- Real-valued form of the raw one-row `L²` estimate. -/
theorem toReal_eLpNorm_hessianHilbertRow_two_le
    (H : HasWeakHessianOn U u) (i : Fin d) :
    (eLpNorm (hilbertifyVecField (fun x j ↦ H.hess i j x)) 2
      (volumeMeasureOn U)).toReal ≤ H.hessianCoordL2NormSum := by
  have htop := (H.hessianHilbertRow_memLp_two i).eLpNorm_ne_top
  rw [← ENNReal.le_ofReal_iff_toReal_le htop H.hessianCoordL2NormSum_nonneg]
  exact H.eLpNorm_hessianHilbertRow_two_le i

/-- The total raw square-weighted mass of one Hilbertified Hessian row is
bounded by the square of `hessianCoordL2NormSum`. -/
theorem sqWeightedMeasure_hessianHilbertRow_apply_univ_le
    (H : HasWeakHessianOn U u) (i : Fin d) :
    CubeCalderonZygmund.sqWeightedMeasure
        (hilbertifyVecField (fun x j ↦ H.hess i j x))
        (volumeMeasureOn U) Set.univ ≤
      ENNReal.ofReal (H.hessianCoordL2NormSum ^ (2 : ℕ)) := by
  rw [CubeCalderonZygmund.sqWeightedMeasure_apply_univ_eq_eLpNorm_two_sq]
  rw [ENNReal.ofReal_pow H.hessianCoordL2NormSum_nonneg]
  exact pow_le_pow_left₀ bot_le (H.eLpNorm_hessianHilbertRow_two_le i) 2

/-- On a cube, a Hilbertified Hessian row belongs to normalized `L²`. -/
theorem hessianHilbertRow_memLp_two_normalizedCubeMeasure
    (Q : TriadicCube d) {v : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) v) (i : Fin d) :
    MemLp (hilbertifyVecField (fun x j ↦ H.hess i j x)) 2
      (normalizedCubeMeasure Q) := by
  rw [memLp_piLp_iff]
  intro j
  simpa only [hilbertifyVecField, Function.comp_apply, HilbertVec.ofVec,
    PiLp.toLp_apply] using H.hess_memLp_normalizedCubeMeasure Q i j

/-- The normalized Euclidean `L²` norm of one Hessian row has the expected
inverse-square-root volume factor. -/
theorem eLpNorm_hessianHilbertRow_two_normalizedCubeMeasure_le
    (Q : TriadicCube d) {v : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) v) (i : Fin d) :
    eLpNorm (hilbertifyVecField (fun x j ↦ H.hess i j x)) 2
        (normalizedCubeMeasure Q) ≤
      ENNReal.ofReal
        (((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * H.hessianCoordL2NormSum) := by
  have hfactor : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2 (inv_pos.mpr (cubeVolume_pos Q))
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
    eLpNorm_smul_measure_of_ne_zero hfactor]
  rw [show (1 / (2 : ℝ≥0∞)).toReal = (2 : ℝ)⁻¹ by norm_num]
  simp only [smul_eq_mul]
  calc
    ENNReal.ofReal ((cubeVolume Q)⁻¹) ^ (2 : ℝ)⁻¹ *
          eLpNorm (hilbertifyVecField (fun x j ↦ H.hess i j x)) 2
            (volumeMeasureOn (openCubeSet Q)) ≤
        ENNReal.ofReal ((cubeVolume Q)⁻¹) ^ (2 : ℝ)⁻¹ *
          ENNReal.ofReal H.hessianCoordL2NormSum := by
      exact mul_le_mul_of_nonneg_left
        (H.eLpNorm_hessianHilbertRow_two_le i) bot_le
    _ = ENNReal.ofReal
        (((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * H.hessianCoordL2NormSum) := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
      rw [ENNReal.ofReal_mul
        (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q)) _)]
      congr 1
      rw [← ENNReal.ofReal_rpow_of_nonneg
        (inv_nonneg.mpr (cubeVolume_nonneg Q)) (by norm_num)]

/-- Real-valued form of the normalized one-row `L²` estimate. -/
theorem toReal_eLpNorm_hessianHilbertRow_two_normalizedCubeMeasure_le
    (Q : TriadicCube d) {v : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) v) (i : Fin d) :
    (eLpNorm (hilbertifyVecField (fun x j ↦ H.hess i j x)) 2
      (normalizedCubeMeasure Q)).toReal ≤
      ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * H.hessianCoordL2NormSum := by
  have htop :=
    (H.hessianHilbertRow_memLp_two_normalizedCubeMeasure Q i).eLpNorm_ne_top
  rw [← ENNReal.le_ofReal_iff_toReal_le htop (mul_nonneg
    (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q)) _)
    H.hessianCoordL2NormSum_nonneg)]
  exact H.eLpNorm_hessianHilbertRow_two_normalizedCubeMeasure_le Q i

/-- The normalized total square-weighted mass of one Hessian row is controlled
by the square of the volume-normalized weak-`H²` energy. -/
theorem sqWeightedMeasure_hessianHilbertRow_normalizedCubeMeasure_apply_univ_le
    (Q : TriadicCube d) {v : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) v) (i : Fin d) :
    CubeCalderonZygmund.sqWeightedMeasure
        (hilbertifyVecField (fun x j ↦ H.hess i j x))
        (normalizedCubeMeasure Q) Set.univ ≤
      ENNReal.ofReal
        ((((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
          H.hessianCoordL2NormSum) ^ (2 : ℕ)) := by
  rw [CubeCalderonZygmund.sqWeightedMeasure_apply_univ_eq_eLpNorm_two_sq]
  rw [ENNReal.ofReal_pow (mul_nonneg
    (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q)) _)
    H.hessianCoordL2NormSum_nonneg)]
  exact pow_le_pow_left₀ bot_le
    (H.eLpNorm_hessianHilbertRow_two_normalizedCubeMeasure_le Q i) 2

/-- A measurable-domain zero extension of one Hessian row belongs to global
`L²`. -/
theorem indicator_hessianHilbertRow_memLp_two
    (H : HasWeakHessianOn U u) (i : Fin d) (hU : MeasurableSet U) :
    MemLp (U.indicator (hilbertifyVecField (fun x j ↦ H.hess i j x))) 2
      volume := by
  exact (CubeCalderonZygmund.memLp_indicator_iff_restrict hU).2
    (H.hessianHilbertRow_memLp_two i)

/-- The global square-weighted mass of a Hessian row extended by zero is
controlled by its local weak-`H²` energy. -/
theorem sqWeightedMeasure_indicator_hessianHilbertRow_apply_univ_le
    (H : HasWeakHessianOn U u) (i : Fin d) (hU : MeasurableSet U) :
    CubeCalderonZygmund.sqWeightedMeasure
        (U.indicator (hilbertifyVecField (fun x j ↦ H.hess i j x)))
        volume Set.univ ≤
      ENNReal.ofReal (H.hessianCoordL2NormSum ^ (2 : ℕ)) := by
  rw [CubeCalderonZygmund.sqWeightedMeasure_indicator_eq_restrict hU]
  exact H.sqWeightedMeasure_hessianHilbertRow_apply_univ_le i

end HasWeakHessianOn

end

end Homogenization
