/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ExactOverlapEuclideanLpComparison

/-!
# Full exact-overlap control for Euclidean fractional-Sobolev fields

This module adds the inhomogeneous scalar-coordinate estimate needed to use
smooth Euclidean fractional-Sobolev fields as positive exact-overlap tests.
The constant is chosen before the cube, fractional order, exponent, field,
and coordinate.
-/

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- A dimension-only full positive-test constant. -/
noncomputable def cubeEuclideanWspExactOverlapFullControlConstant
    (d : ℕ) : ℝ≥0∞ :=
  1 + d * cubeEuclideanWspOverlapDimensionConstant d

theorem cubeEuclideanWspExactOverlapFullControlConstant_lt_top (d : ℕ) :
    cubeEuclideanWspExactOverlapFullControlConstant d < ∞ := by
  unfold cubeEuclideanWspExactOverlapFullControlConstant
  have hlower : Gagliardo.gagliardoBesovLowerConstant d ≠ ∞ := by
    unfold Gagliardo.gagliardoBesovLowerConstant
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num))
      (ENNReal.pow_ne_top (by norm_num))
  have hdimension : 0 ≤ (d : ℝ) + 4 := by positivity
  have hpower : (d : ℝ≥0∞) ^ ((d : ℝ) + 4) < ∞ :=
    ENNReal.rpow_lt_top_of_nonneg hdimension (ENNReal.natCast_ne_top d)
  exact ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top,
    ENNReal.mul_lt_top (ENNReal.natCast_lt_top d)
      (by
        unfold cubeEuclideanWspOverlapDimensionConstant
        exact ENNReal.mul_lt_top
          (ENNReal.mul_lt_top (by finiteness) (lt_top_iff_ne_top.mpr hlower))
          hpower)⟩

private theorem exactOverlapIntegrableOfEuclideanWspField {d : ℕ}
    {s : FractionalOrder} (Q : TriadicCube d) (p : FiniteLpExponent)
    (F : CubeEuclideanWspField Q s p) (i : Fin d) :
    ExactOverlapIntegrable Q (fun x => F.toField x i) where
  root := (cubeEuclideanLp_coordinate_memLp F.toCubeEuclideanLpField i).integrable
    p.one_lt.le
  overlap := fun _ _ hS =>
    (Gagliardo.memLp_overlap_of_memLp
      (cubeEuclideanLp_coordinate_memLp F.toCubeEuclideanLpField i) hS).integrable
      p.one_lt.le

private theorem exactOverlapRootMean_enorm_le_normalizedEuclideanLp
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : CubeEuclideanWspField Q s p) (i : Fin d)
    (hF : ExactOverlapIntegrable Q (fun x => F.toField x i)) :
    ENNReal.ofReal |exactOverlapRootMean Q (fun x => F.toField x i) hF.root| ≤
      (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm p.exponent
        F.toField := by
  let μ := normalizedCubeMeasure Q
  let : IsProbabilityMeasure μ := ⟨by simp [μ]⟩
  have hcoord : MemLp (fun x => F.toField x i) p.exponent μ := by
    simpa only [μ] using cubeEuclideanLp_coordinate_memLp F.toCubeEuclideanLpField i
  have hcoord_meas : AEStronglyMeasurable (fun x => F.toField x i) μ :=
    hcoord.aestronglyMeasurable
  calc
    ENNReal.ofReal |exactOverlapRootMean Q (fun x => F.toField x i) hF.root| =
        ‖∫ x, F.toField x i ∂μ‖ₑ := by
      unfold exactOverlapRootMean
      change ENNReal.ofReal |∫ x, F.toField x i ∂μ| =
        ‖∫ x, F.toField x i ∂μ‖ₑ
      exact (Real.enorm_eq_ofReal_abs _).symm
    _ ≤ ∫⁻ x, ‖F.toField x i‖ₑ ∂μ :=
      enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (fun x => F.toField x i) 1 μ := by
      rw [eLpNorm_one_eq_lintegral_enorm hcoord_meas]
    _ ≤ eLpNorm (fun x => F.toField x i) p.exponent μ :=
      eLpNorm_le_eLpNorm_of_exponent_le p.one_lt.le
    _ ≤ eLpNorm (fun x => HilbertVec.ofVec (F.toField x)) p.exponent μ :=
      coordinate_eLpNorm_le_euclidean μ p F.toField i
    _ = (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm p.exponent
        F.toField := by
      unfold BoundedMeasurableDomain.normalizedEuclideanLpENorm
      have hmeas : AEStronglyMeasurable (fun x => euclideanNorm (F.toField x))
          (cubeBoundedMeasurableDomain Q).normalizedVolume := by
        rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
        simpa only [euclideanNorm_eq_norm_ofVec] using F.euclideanMemLp.aestronglyMeasurable.norm
      rw [BoundedMeasurableDomain.normalizedLpENorm_eq_eLpNorm _ _ _ hmeas,
        cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
      simpa only [euclideanNorm_eq_norm_ofVec] using
        (eLpNorm_norm (fun x => HilbertVec.ofVec (F.toField x))
          F.euclideanMemLp.aestronglyMeasurable).symm

private theorem exactOverlapRootWeight_rpow_eq_wspScalePowerWeight
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent) :
    (exactOverlapRootWeight Q s.1) ^ p.exponent.toReal =
      cubeEuclideanWspScalePowerWeight Q s p := by
  unfold exactOverlapRootWeight cubeEuclideanWspScalePowerWeight cubeScaleFactor
  rw [← ENNReal.rpow_mul]
  have hthree : (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) := by norm_num
  have hbase : ENNReal.ofReal ((3 : ℝ) ^ Q.scale) =
      (ENNReal.ofReal (3 : ℝ)) ^ (Q.scale : ℝ) := by
    rw [← Real.rpow_intCast]
    rw [ENNReal.ofReal_rpow_of_pos (by norm_num : 0 < (3 : ℝ))]
  rw [hthree, hbase]
  calc
    (ENNReal.ofReal (3 : ℝ)) ^
        ((-((Q.scale : ℤ) : ℝ) * s.1) * p.exponent.toReal) =
      (ENNReal.ofReal (3 : ℝ)) ^
        ((Q.scale : ℝ) * (-s.1 * p.exponent.toReal)) := by
        congr 1
        ring
    _ = ((ENNReal.ofReal (3 : ℝ)) ^ (Q.scale : ℝ)) ^
        (-s.1 * p.exponent.toReal) := ENNReal.rpow_mul _ _ _

private theorem exactOverlapRootWeight_mul_normalizedEuclideanLpENorm_le_wspFull
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : CubeEuclideanWspField Q s p) :
    exactOverlapRootWeight Q s.1 *
        (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm p.exponent
          F.toField ≤
      cubeEuclideanWspFullENorm Q s p F.toField := by
  let W := cubeEuclideanWspScalePowerWeight Q s p
  let L := (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
    p.exponent F.toField
  let S := cubeEuclideanWspESeminorm Q s p F.toField
  let t := p.exponent.toReal
  have ht : 0 < t :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne
  have hpower : W * L ^ t ≤ W * L ^ t + S ^ t := le_add_of_nonneg_right bot_le
  have hroot := ENNReal.rpow_le_rpow hpower (inv_nonneg.mpr ht.le)
  have hweight : (exactOverlapRootWeight Q s.1) ^ t = W := by
    simpa only [W, t] using
      exactOverlapRootWeight_rpow_eq_wspScalePowerWeight Q s p
  rw [cubeEuclideanWspFullENorm]
  change exactOverlapRootWeight Q s.1 * L ≤ (W * L ^ t + S ^ t) ^ t⁻¹
  calc
    exactOverlapRootWeight Q s.1 * L =
        (exactOverlapRootWeight Q s.1 * L) ^ (t * t⁻¹) := by
          rw [mul_inv_cancel₀ ht.ne', ENNReal.rpow_one]
    _ = ((exactOverlapRootWeight Q s.1 * L) ^ t) ^ t⁻¹ := by
      rw [ENNReal.rpow_mul]
    _ = (W * L ^ t) ^ t⁻¹ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ ht.le, hweight]
    _ ≤ (W * L ^ t + S ^ t) ^ t⁻¹ := hroot

private theorem cubeEuclideanWspESeminorm_le_fullENorm
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : CubeEuclideanWspField Q s p) :
    cubeEuclideanWspESeminorm Q s p F.toField ≤
      cubeEuclideanWspFullENorm Q s p F.toField := by
  let W := cubeEuclideanWspScalePowerWeight Q s p
  let L := (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
    p.exponent F.toField
  let S := cubeEuclideanWspESeminorm Q s p F.toField
  let t := p.exponent.toReal
  have ht : 0 < t :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne
  have hpower : S ^ t ≤ W * L ^ t + S ^ t := le_add_of_nonneg_left bot_le
  have hroot := ENNReal.rpow_le_rpow hpower (inv_nonneg.mpr ht.le)
  rw [cubeEuclideanWspFullENorm]
  change S ≤ (W * L ^ t + S ^ t) ^ t⁻¹
  calc
    S = S ^ (t * t⁻¹) := by rw [mul_inv_cancel₀ ht.ne', ENNReal.rpow_one]
    _ = (S ^ t) ^ t⁻¹ := by rw [ENNReal.rpow_mul]
    _ ≤ (W * L ^ t + S ^ t) ^ t⁻¹ := hroot

/-- Each scalar coordinate exact-overlap full norm is bounded by one explicit
dimension-only multiple of the Euclidean fractional-Sobolev full norm.  The
coordinate's root and overlap integrability certificates are derived from the
Euclidean `L^p` carrier. -/
theorem exactOverlapScalarPFullNorm_le_dimensionConstant_mul_cubeEuclideanWspFull
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : CubeEuclideanWspField Q s p) (i : Fin d) :
    exactOverlapFiniteNorm (exactOverlapScalarPParameters s p) Q
        (fun x => F.toField x i)
        (exactOverlapIntegrableOfEuclideanWspField Q p F i) ≤
      cubeEuclideanWspExactOverlapFullControlConstant d *
        cubeEuclideanWspFullENorm Q s p F.toField := by
  let hscalar := exactOverlapIntegrableOfEuclideanWspField Q p F i
  let C := cubeEuclideanWspOverlapDimensionConstant d
  let L := (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
    p.exponent F.toField
  let N := cubeEuclideanWspFullENorm Q s p F.toField
  have hseminorm :
      exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q
          (fun x => F.toField x i) hscalar ≤
        (d : ℝ≥0∞) * C * N := by
    calc
      exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q
          (fun x => F.toField x i) hscalar ≤
        (d : ℝ≥0∞) * cubeEuclideanPositiveBesovOverlapESeminorm Q s p
          F.toCubeEuclideanLpField :=
        exactOverlapScalarPSeminorm_le_dimension_mul_cubeEuclideanOverlap
          Q s p F.toCubeEuclideanLpField i hscalar
      _ ≤ (d : ℝ≥0∞) * (C * cubeEuclideanWspESeminorm Q s p F.toField) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul_left
            (cubeEuclideanOverlap_le_dimensionConstant_mul_wsp
              Q s p F.toCubeEuclideanLpField) (d : ℝ≥0∞)
      _ ≤ (d : ℝ≥0∞) * (C * N) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul_left
            (mul_le_mul_left (cubeEuclideanWspESeminorm_le_fullENorm Q s p F) C)
            (d : ℝ≥0∞)
      _ = (d : ℝ≥0∞) * C * N := by ring
  have hmean : exactOverlapRootWeight Q s.1 *
      ENNReal.ofReal |exactOverlapRootMean Q (fun x => F.toField x i) hscalar.root| ≤ N := by
    calc
      exactOverlapRootWeight Q s.1 *
          ENNReal.ofReal |exactOverlapRootMean Q (fun x => F.toField x i) hscalar.root| ≤
        exactOverlapRootWeight Q s.1 * L := by
          simpa [mul_comm] using mul_le_mul_left
            (exactOverlapRootMean_enorm_le_normalizedEuclideanLp Q s p F i hscalar)
            (exactOverlapRootWeight Q s.1)
      _ ≤ N := exactOverlapRootWeight_mul_normalizedEuclideanLpENorm_le_wspFull
        Q s p F
  rw [exactOverlapFiniteNorm_eq]
  calc
    exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q
        (fun x => F.toField x i) hscalar +
          exactOverlapRootWeight Q s.1 *
            ENNReal.ofReal |exactOverlapRootMean Q (fun x => F.toField x i) hscalar.root| ≤
      (d : ℝ≥0∞) * C * N + N := add_le_add hseminorm hmean
    _ = (1 + (d : ℝ≥0∞) * C) * N := by ring
    _ = cubeEuclideanWspExactOverlapFullControlConstant d * N := by
      simp only [cubeEuclideanWspExactOverlapFullControlConstant, C]

end

end Homogenization
