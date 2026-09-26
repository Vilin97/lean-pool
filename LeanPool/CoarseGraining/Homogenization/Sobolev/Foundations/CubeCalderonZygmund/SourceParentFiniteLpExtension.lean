/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.InteriorLocalInputs
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.FiniteLp
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionGeometry
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ScaledCubeGeometry

/-!
# Source-supported finite-`L^p` data on a centered parent cube

This module packages extension by zero from an origin cube into its centered
parent, retaining both the finite-exponent and energy memberships.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

private theorem normalizedCubeMeasure_originCube_eq_smul_restrict_openCubeSet
    {d : ℕ} (m : ℤ) :
    normalizedCubeMeasure (originCube d m) =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        (volume.restrict (openCubeSet (originCube d m))) := by
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_originCube_eq_volume_restrict_openCubeSet_originCube]

private theorem cubeVolume_originCube_succ {d : ℕ} (m : ℤ) :
    cubeVolume (originCube d (m + 1)) =
      (3 : ℝ) ^ d * cubeVolume (originCube d m) := by
  simp [cubeVolume, cubeScaleFactor, originCube, zpow_add₀]
  rw [mul_pow]
  ring

private theorem normalizedCubeMeasure_parent_restrict_source
    {d : ℕ} (m : ℤ) :
    (normalizedCubeMeasure (originCube d (m + 1))).restrict
        (openCubeSet (originCube d m)) =
      ((3 : ℝ≥0∞) ^ d)⁻¹ • normalizedCubeMeasure (originCube d m) := by
  rw [normalizedCubeMeasure_originCube_eq_smul_restrict_openCubeSet,
    Measure.restrict_smul,
    normalizedCubeMeasure_originCube_eq_smul_restrict_openCubeSet]
  have hsource_parent : openCubeSet (originCube d m) ⊆
      openCubeSet (originCube d (m + 1)) := by
    calc
      openCubeSet (originCube d m) =
          scaledOpenCubeSet (originCube d (m + 1)) (1 / 3 : ℝ) :=
        (scaledOpenCubeSet_originCube_succ_one_div_three d m).symm
      _ ⊆ scaledClosedCubeSet (originCube d (m + 1)) (1 / 3 : ℝ) :=
        scaledOpenCubeSet_subset_scaledClosedCubeSet _ _
      _ ⊆ openCubeSet (originCube d (m + 1)) :=
        scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one _
          (by norm_num) (by norm_num)
  rw [Measure.restrict_restrict (isOpen_openCubeSet _).measurableSet,
    Set.inter_eq_left.mpr hsource_parent]
  have hscalar : ENNReal.ofReal ((cubeVolume (originCube d (m + 1)))⁻¹) =
      ((3 : ℝ≥0∞) ^ d)⁻¹ *
        ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) := by
    rw [cubeVolume_originCube_succ]
    let N : ℝ := (3 : ℝ) ^ d
    let V : ℝ := cubeVolume (originCube d m)
    change ENNReal.ofReal ((N * V)⁻¹) = _
    have hN : 0 < N := by positivity
    have hreal : ((N * V)⁻¹ : ℝ) = N⁻¹ * V⁻¹ := by
      rw [mul_inv_rev]
      ring
    rw [hreal, ENNReal.ofReal_mul (inv_nonneg.mpr hN.le)]
    congr 1
    norm_num [N]
  rw [hscalar, smul_smul]

/-- The source datum, extended by zero, as finite-`L^p` data on the centered
parent cube. -/
noncomputable def sourceParentFiniteLpExtension
    {d : ℕ} (m : ℤ) (q : FiniteLpExponent)
    (h : CubeEuclideanL2LpField (originCube d m) q) :
    CubeEuclideanL2LpField (originCube d (m + 1)) q := by
  let U : Set (Vec d) := openCubeSet (originCube d m)
  have hU : MeasurableSet U := (isOpen_openCubeSet _).measurableSet
  have hc : ((3 : ℝ≥0∞) ^ d)⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (ENNReal.pow_ne_zero (by norm_num) d)
  have hq : MemLp (hilbertifyVecField (openParentDatumExtension U h.toField))
      q.exponent (normalizedCubeMeasure (originCube d (m + 1))) := by
    rw [hilbertifyVecField_openParentDatumExtension, memLp_indicator_iff_restrict hU,
      normalizedCubeMeasure_parent_restrict_source]
    exact h.euclideanMemLp.smul_measure hc
  have htwo : MemLp (hilbertifyVecField (openParentDatumExtension U h.toField)) 2
      (normalizedCubeMeasure (originCube d (m + 1))) := by
    rw [hilbertifyVecField_openParentDatumExtension, memLp_indicator_iff_restrict hU,
      normalizedCubeMeasure_parent_restrict_source]
    exact h.euclideanMemL2.smul_measure hc
  change MemLp (fun x => HilbertVec.ofVec
    (openParentDatumExtension U h.toField x)) q.exponent
      (normalizedCubeMeasure (originCube d (m + 1))) at hq
  change MemLp (fun x => HilbertVec.ofVec
    (openParentDatumExtension U h.toField x)) 2
      (normalizedCubeMeasure (originCube d (m + 1))) at htwo
  exact ⟨⟨openParentDatumExtension U h.toField, hq⟩, htwo⟩

@[simp] theorem sourceParentFiniteLpExtension_toField
    {d : ℕ} (m : ℤ) (q : FiniteLpExponent)
    (h : CubeEuclideanL2LpField (originCube d m) q) :
    (sourceParentFiniteLpExtension m q h).toField =
      openParentDatumExtension (openCubeSet (originCube d m)) h.toField := by
  rfl

/-- The normalized finite-exponent norm of a datum extended by zero to its
centered parent has the exact probability-mass factor. -/
theorem eLpNorm_sourceParentFiniteLpExtension
    {d : ℕ} (m : ℤ) (q : FiniteLpExponent)
    (h : CubeEuclideanL2LpField (originCube d m) q) :
    eLpNorm (hilbertifyVecField (sourceParentFiniteLpExtension m q h).toField)
        q.exponent (normalizedCubeMeasure (originCube d (m + 1))) =
      (((3 : ℝ≥0∞) ^ d)⁻¹) ^ (q.exponent.toReal)⁻¹ *
        eLpNorm (hilbertifyVecField h.toField) q.exponent
          (normalizedCubeMeasure (originCube d m)) := by
  rw [sourceParentFiniteLpExtension_toField,
    hilbertifyVecField_openParentDatumExtension,
    eLpNorm_indicator_eq_eLpNorm_restrict
      (isOpen_openCubeSet _).measurableSet,
    normalizedCubeMeasure_parent_restrict_source,
    eLpNorm_smul_measure_of_ne_top q.lt_top.ne]
  rw [smul_eq_mul, one_div, ENNReal.toReal_inv]

/-- The source-supported parent extension cannot increase the normalized
finite-exponent Euclidean norm. -/
theorem eLpNorm_sourceParentFiniteLpExtension_le
    {d : ℕ} (m : ℤ) (q : FiniteLpExponent)
    (h : CubeEuclideanL2LpField (originCube d m) q) :
    eLpNorm (hilbertifyVecField (sourceParentFiniteLpExtension m q h).toField)
        q.exponent (normalizedCubeMeasure (originCube d (m + 1))) ≤
      eLpNorm (hilbertifyVecField h.toField) q.exponent
        (normalizedCubeMeasure (originCube d m)) := by
  rw [eLpNorm_sourceParentFiniteLpExtension]
  apply mul_le_of_le_one_left bot_le
  exact ENNReal.rpow_le_one
      (ENNReal.inv_le_one.mpr (one_le_pow₀ (by norm_num : (1 : ℝ≥0∞) ≤ 3)))
      (inv_nonneg.mpr ENNReal.toReal_nonneg)

/-- The normalized `L²` norm of a source-supported parent extension has the
same exact probability-mass factor. -/
theorem eLpNorm_two_sourceParentFiniteLpExtension
    {d : ℕ} (m : ℤ) (q : FiniteLpExponent)
    (h : CubeEuclideanL2LpField (originCube d m) q) :
    eLpNorm (hilbertifyVecField (sourceParentFiniteLpExtension m q h).toField)
        2 (normalizedCubeMeasure (originCube d (m + 1))) =
      (((3 : ℝ≥0∞) ^ d)⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal *
        eLpNorm (hilbertifyVecField h.toField) 2
          (normalizedCubeMeasure (originCube d m)) := by
  rw [sourceParentFiniteLpExtension_toField,
    hilbertifyVecField_openParentDatumExtension,
    eLpNorm_indicator_eq_eLpNorm_restrict
      (isOpen_openCubeSet _).measurableSet,
    normalizedCubeMeasure_parent_restrict_source,
    eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
  rfl

/-- The source-supported parent extension cannot increase its normalized
Euclidean `L²` norm. -/
theorem eLpNorm_two_sourceParentFiniteLpExtension_le
    {d : ℕ} (m : ℤ) (q : FiniteLpExponent)
    (h : CubeEuclideanL2LpField (originCube d m) q) :
    eLpNorm (hilbertifyVecField (sourceParentFiniteLpExtension m q h).toField)
        2 (normalizedCubeMeasure (originCube d (m + 1))) ≤
      eLpNorm (hilbertifyVecField h.toField) 2
        (normalizedCubeMeasure (originCube d m)) := by
  rw [eLpNorm_two_sourceParentFiniteLpExtension]
  apply mul_le_of_le_one_left bot_le
  exact ENNReal.rpow_le_one
      (ENNReal.inv_le_one.mpr (one_le_pow₀ (by norm_num : (1 : ℝ≥0∞) ≤ 3)))
      (by norm_num)

/-- The parent extension is a raw vector `L²` datum on the open parent cube,
as needed by the canonical adjoint solver. -/
theorem memVectorL2_sourceParentFiniteLpExtension
    {d : ℕ} (m : ℤ) (q : FiniteLpExponent)
    (h : CubeEuclideanL2LpField (originCube d m) q) :
    MemVectorL2 (openCubeSet (originCube d (m + 1)))
      (sourceParentFiniteLpExtension m q h).toField := by
  apply MeasureTheory.MemLp.of_eval
  intro i
  have hcoord : MemLp (fun x => HilbertVec.ofVec
      ((sourceParentFiniteLpExtension m q h).toField x)) 2
      (normalizedCubeMeasure (originCube d (m + 1))) :=
    (sourceParentFiniteLpExtension m q h).euclideanMemL2
  rw [MeasureTheory.memLp_piLp_iff] at hcoord
  simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using
    memL2On_openCubeSet_of_memLp_normalizedCubeMeasure
      (originCube d (m + 1)) (hcoord i)

end CubeCalderonZygmund

end
end Homogenization
