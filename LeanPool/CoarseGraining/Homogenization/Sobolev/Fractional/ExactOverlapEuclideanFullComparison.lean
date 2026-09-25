/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.CenteredCubeHsRegularity
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ExactOverlapEuclideanComparison
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ExactOverlapEuclideanPoincare

/-!
# Exact Euclidean overlap full-norm comparison on centered cubes

This module compares the source-facing exact overlap `B^s_{2,2}` full norm
with the approved physical Euclidean `H^s` full norm on every centered
triadic cube.  Both objects use their canonical `L²` certificates, so the
public API has no integrability, measurability, or certificate binder.

## Main definitions

- `centeredCubeExactOverlapEuclideanSeminormTwo`: the canonical physical
  exact-overlap seminorm.
- `centeredCubeExactOverlapEuclideanNormTwo`: the canonical physical
  exact-overlap full norm.

## Main results

- `centeredCubeExactOverlapEuclideanRootMeanENorm_le_normalizedEuclideanLpENorm`:
  the Euclidean root mean is bounded by the normalized Euclidean `L²` norm.
- `exists_centeredCubeEuclideanHs_exactOverlapEuclideanNormTwo_comparison`:
  one finite constant, fixed before scale and field, controls both full-norm
  comparison directions.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The canonical exact Euclidean overlap seminorm on a centered cube. -/
noncomputable def centeredCubeExactOverlapEuclideanSeminormTwo {d : ℕ} {m : ℤ}
    (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m) : ℝ≥0∞ :=
  exactOverlapEuclideanSeminormTwo s (originCube d m) F
    F.exactOverlapEuclideanIntegrable

/-- The canonical exact Euclidean overlap full norm on a centered cube. -/
noncomputable def centeredCubeExactOverlapEuclideanNormTwo {d : ℕ} {m : ℤ}
    (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m) : ℝ≥0∞ :=
  exactOverlapEuclideanNormTwo s (originCube d m) F
    F.exactOverlapEuclideanIntegrable

/-- Evaluation of the canonical exact Euclidean overlap seminorm. -/
theorem centeredCubeExactOverlapEuclideanSeminormTwo_eq {d : ℕ} {m : ℤ}
    (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m) :
    centeredCubeExactOverlapEuclideanSeminormTwo s F =
      exactOverlapEuclideanSeminormTwo s (originCube d m) F
        F.exactOverlapEuclideanIntegrable :=
  rfl

/-- Evaluation of the canonical exact Euclidean overlap full norm. -/
theorem centeredCubeExactOverlapEuclideanNormTwo_eq {d : ℕ} {m : ℤ}
    (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m) :
    centeredCubeExactOverlapEuclideanNormTwo s F =
      exactOverlapEuclideanNormTwo s (originCube d m) F
        F.exactOverlapEuclideanIntegrable :=
  rfl

/-- The Euclidean magnitude of the normalized root mean is bounded by the
normalized Euclidean `L²` norm carried by the centered-cube field. -/
theorem centeredCubeExactOverlapEuclideanRootMeanENorm_le_normalizedEuclideanLpENorm
    {d : ℕ} {m : ℤ} (F : CenteredCubeEuclideanL2Field d m) :
    exactOverlapEuclideanRootMeanENorm (originCube d m) F
        F.exactOverlapEuclideanIntegrable ≤
      (centeredCubeDomain d m).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F := by
  let μ := normalizedCubeMeasure (originCube d m)
  have hmem : MemLp (fun x => HilbertVec.ofVec (F x)) (2 : ℝ≥0∞) μ := by
    simpa only [μ, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using
        F.euclideanMemL2
  let : IsProbabilityMeasure μ := ⟨by simp [μ]⟩
  have hintegrable : Integrable (fun x => HilbertVec.ofVec (F x)) μ :=
    (hmem.mono_exponent (show (1 : ℝ≥0∞) ≤ 2 by norm_num)).integrable (by norm_num)
  have hmean :
      (fun i => exactOverlapRootMean (originCube d m) (fun x => F x i)
        (F.exactOverlapEuclideanIntegrable.coordinate i).root) =
        (∫ x, HilbertVec.ofVec (F x) ∂μ).toVec := by
    funext i
    unfold exactOverlapRootMean
    simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using
      (eval_integral_piLp (fun j => hintegrable.eval_piLp j) i).symm
  calc
    exactOverlapEuclideanRootMeanENorm (originCube d m) F
        F.exactOverlapEuclideanIntegrable =
        ‖∫ x, HilbertVec.ofVec (F x) ∂μ‖ₑ := by
      rw [exactOverlapEuclideanRootMeanENorm_eq_ofReal_euclideanNorm, hmean,
        euclideanNorm_eq_norm_ofVec, HilbertVec.ofVec_toVec, ofReal_norm]
    _ ≤ ∫⁻ x, ‖HilbertVec.ofVec (F x)‖ₑ ∂μ :=
      enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (fun x => HilbertVec.ofVec (F x)) 1 μ := by
      rw [eLpNorm_one_eq_lintegral_enorm]
    _ ≤ eLpNorm (fun x => HilbertVec.ofVec (F x)) 2 μ :=
      eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hmem.aestronglyMeasurable
    _ = (centeredCubeDomain d m).normalizedEuclideanLpENorm 2 F := by
      simp only [μ, centeredCubeDomain,
        cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
        BoundedMeasurableDomain.normalizedEuclideanLpENorm,
        BoundedMeasurableDomain.normalizedLpENorm, euclideanNorm_eq_norm_ofVec,
        eLpNorm_norm]

/-- The root-weighted normalized Euclidean `L²` norm is controlled by the
canonical exact-overlap full norm on every centered cube. -/
theorem centeredCubeRootWeight_mul_normalizedEuclideanLpENorm_le_exactOverlapNormTwo
    {d : ℕ} {m : ℤ} (s : FractionalOrder)
    (F : CenteredCubeEuclideanL2Field d m) :
    exactOverlapRootWeight (originCube d m) s.1 *
        (centeredCubeDomain d m).normalizedEuclideanLpENorm 2 F ≤
      centeredCubeExactOverlapEuclideanNormTwo s F := by
  have hmem : MemLp (fun x => HilbertVec.ofVec (F x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m)) := by
    simpa only [centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using
        F.euclideanMemL2
  have h := exactOverlapRootWeight_mul_eLpNorm_le_exactOverlapEuclideanNormTwo
    s (originCube d m) F hmem
  simpa only [centeredCubeExactOverlapEuclideanNormTwo,
    centeredCubeDomain,
    cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
    BoundedMeasurableDomain.normalizedEuclideanLpENorm,
    BoundedMeasurableDomain.normalizedLpENorm, euclideanNorm_eq_norm_ofVec,
    eLpNorm_norm] using h

/-- One scale-independent constant for both directions of the exact-overlap
and physical Euclidean fractional full-norm comparison. -/
noncomputable def centeredCubeExactOverlapEuclideanFullComparisonConstant
    (d : ℕ) (s : FractionalOrder) : ℝ≥0∞ :=
  1 + centeredCubeExactOverlapEuclideanComparisonConstant d s

/-- The common exact-overlap/physical full-norm comparison constant is finite. -/
theorem centeredCubeExactOverlapEuclideanFullComparisonConstant_lt_top
    (d : ℕ) (s : FractionalOrder) :
    centeredCubeExactOverlapEuclideanFullComparisonConstant d s < ∞ := by
  unfold centeredCubeExactOverlapEuclideanFullComparisonConstant
  exact ENNReal.add_lt_top.2
    ⟨ENNReal.one_lt_top,
      centeredCubeExactOverlapEuclideanComparisonConstant_lt_top d s⟩

/-- The exact-overlap Euclidean full norm is bounded by the approved physical
Euclidean fractional full norm, uniformly in the centered-cube scale. -/
theorem centeredCubeExactOverlapEuclideanNormTwo_le_mul_centeredCubeEuclideanHsFullENorm
    {d : ℕ} {m : ℤ} [NeZero d] (s : FractionalOrder)
    (F : CenteredCubeEuclideanL2Field d m) :
    centeredCubeExactOverlapEuclideanNormTwo s F ≤
      centeredCubeExactOverlapEuclideanFullComparisonConstant d s *
        centeredCubeEuclideanHsFullENorm s F := by
  let K := centeredCubeExactOverlapEuclideanComparisonConstant d s
  let C := centeredCubeExactOverlapEuclideanFullComparisonConstant d s
  have hseminorm : centeredCubeExactOverlapEuclideanSeminormTwo s F ≤
      K * centeredCubeEuclideanHsESeminorm s F := by
    calc
      centeredCubeExactOverlapEuclideanSeminormTwo s F ≤
          (((2 * 3 ^ d : ℝ≥0∞) *
            ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) + 2 * s.1))) ^ ((2 : ℝ)⁻¹)) *
            centeredCubeEuclideanHsESeminorm s F :=
        exactOverlapEuclideanSeminormTwo_le_mul_centeredCubeEuclideanHsESeminorm s F
      _ ≤ K * centeredCubeEuclideanHsESeminorm s F := by
        exact mul_le_mul_left
          (le_max_right (Gagliardo.gagliardoBesovLowerConstant d)
            (((2 * 3 ^ d : ℝ≥0∞) *
              ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) + 2 * s.1))) ^ ((2 : ℝ)⁻¹))) _
  have hmean :=
    centeredCubeExactOverlapEuclideanRootMeanENorm_le_normalizedEuclideanLpENorm F
  have hKleC : K ≤ C := by
    exact le_add_of_nonneg_left (zero_le : (0 : ℝ≥0∞) ≤ 1)
  have honeleC : 1 ≤ C := by
    exact le_add_of_nonneg_right (zero_le : (0 : ℝ≥0∞) ≤ K)
  rw [centeredCubeExactOverlapEuclideanNormTwo_eq, exactOverlapEuclideanNormTwo_eq,
    centeredCubeEuclideanHsFullENorm_eq]
  change centeredCubeExactOverlapEuclideanSeminormTwo s F +
      exactOverlapRootWeight (originCube d m) s.1 *
        exactOverlapEuclideanRootMeanENorm (originCube d m) F
          F.exactOverlapEuclideanIntegrable ≤
    C * (exactOverlapRootWeight (originCube d m) s.1 *
      (centeredCubeDomain d m).normalizedEuclideanLpENorm 2 F +
        centeredCubeEuclideanHsESeminorm s F)
  calc
    centeredCubeExactOverlapEuclideanSeminormTwo s F +
        exactOverlapRootWeight (originCube d m) s.1 *
          exactOverlapEuclideanRootMeanENorm (originCube d m) F
            F.exactOverlapEuclideanIntegrable ≤
      K * centeredCubeEuclideanHsESeminorm s F +
        exactOverlapRootWeight (originCube d m) s.1 *
          (centeredCubeDomain d m).normalizedEuclideanLpENorm 2 F := by
      exact add_le_add hseminorm (mul_le_mul_right hmean _)
    _ ≤ C * centeredCubeEuclideanHsESeminorm s F +
        C * (exactOverlapRootWeight (originCube d m) s.1 *
          (centeredCubeDomain d m).normalizedEuclideanLpENorm 2 F) := by
      exact add_le_add (mul_le_mul_left hKleC _)
        (by
          simpa only [one_mul] using
            (mul_le_mul_left honeleC
              (exactOverlapRootWeight (originCube d m) s.1 *
                (centeredCubeDomain d m).normalizedEuclideanLpENorm 2 F)))
    _ = C * (exactOverlapRootWeight (originCube d m) s.1 *
        (centeredCubeDomain d m).normalizedEuclideanLpENorm 2 F +
          centeredCubeEuclideanHsESeminorm s F) := by
      simp only [C, centeredCubeExactOverlapEuclideanFullComparisonConstant]
      ring

/-- The approved physical Euclidean fractional full norm is bounded by the
exact-overlap Euclidean full norm, uniformly in the centered-cube scale. -/
theorem centeredCubeEuclideanHsFullENorm_le_mul_centeredCubeExactOverlapEuclideanNormTwo
    {d : ℕ} {m : ℤ} [NeZero d] (s : FractionalOrder)
    (F : CenteredCubeEuclideanL2Field d m) :
    centeredCubeEuclideanHsFullENorm s F ≤
      centeredCubeExactOverlapEuclideanFullComparisonConstant d s *
        centeredCubeExactOverlapEuclideanNormTwo s F := by
  let K := centeredCubeExactOverlapEuclideanComparisonConstant d s
  let C := centeredCubeExactOverlapEuclideanFullComparisonConstant d s
  have hseminorm : centeredCubeEuclideanHsESeminorm s F ≤
      K * centeredCubeExactOverlapEuclideanSeminormTwo s F := by
    calc
      centeredCubeEuclideanHsESeminorm s F ≤
          Gagliardo.gagliardoBesovLowerConstant d *
            centeredCubeExactOverlapEuclideanSeminormTwo s F :=
        centeredCubeEuclideanHsESeminorm_le_mul_exactOverlapEuclideanSeminormTwo s F
      _ ≤ K * centeredCubeExactOverlapEuclideanSeminormTwo s F := by
        exact mul_le_mul_left
          (le_max_left (Gagliardo.gagliardoBesovLowerConstant d)
            (((2 * 3 ^ d : ℝ≥0∞) *
              ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) + 2 * s.1))) ^ ((2 : ℝ)⁻¹))) _
  have hroot :=
    centeredCubeRootWeight_mul_normalizedEuclideanLpENorm_le_exactOverlapNormTwo
      s F
  have hseminorm_le_full : centeredCubeExactOverlapEuclideanSeminormTwo s F ≤
      centeredCubeExactOverlapEuclideanNormTwo s F := by
    rw [centeredCubeExactOverlapEuclideanNormTwo_eq, exactOverlapEuclideanNormTwo_eq]
    exact le_add_right le_rfl
  rw [centeredCubeEuclideanHsFullENorm_eq]
  change exactOverlapRootWeight (originCube d m) s.1 *
      (centeredCubeDomain d m).normalizedEuclideanLpENorm 2 F +
        centeredCubeEuclideanHsESeminorm s F ≤
    C * centeredCubeExactOverlapEuclideanNormTwo s F
  calc
    exactOverlapRootWeight (originCube d m) s.1 *
        (centeredCubeDomain d m).normalizedEuclideanLpENorm 2 F +
          centeredCubeEuclideanHsESeminorm s F ≤
      centeredCubeExactOverlapEuclideanNormTwo s F +
        K * centeredCubeExactOverlapEuclideanNormTwo s F := by
      exact add_le_add hroot
        (hseminorm.trans (mul_le_mul_right hseminorm_le_full K))
    _ = C * centeredCubeExactOverlapEuclideanNormTwo s F := by
      simp only [C, centeredCubeExactOverlapEuclideanFullComparisonConstant]
      ring

/-- Uniform source-facing equivalence between the exact-overlap Euclidean
`B^s_{2,2}` full norm and the approved physical Euclidean `H^s` full norm on
every centered triadic cube.  The finite constant is chosen before scale and
field, and all integrability and comparison obligations are internal. -/
theorem exists_centeredCubeEuclideanHs_exactOverlapEuclideanNormTwo_comparison
    (d : ℕ) [NeZero d] (s : FractionalOrder) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m : ℤ) (F : CenteredCubeEuclideanL2Field d m),
        centeredCubeExactOverlapEuclideanNormTwo s F ≤
            C * centeredCubeEuclideanHsFullENorm s F ∧
          centeredCubeEuclideanHsFullENorm s F ≤
            C * centeredCubeExactOverlapEuclideanNormTwo s F := by
  refine ⟨centeredCubeExactOverlapEuclideanFullComparisonConstant d s,
    centeredCubeExactOverlapEuclideanFullComparisonConstant_lt_top d s, ?_⟩
  intro m F
  exact ⟨centeredCubeExactOverlapEuclideanNormTwo_le_mul_centeredCubeEuclideanHsFullENorm
      s F,
    centeredCubeEuclideanHsFullENorm_le_mul_centeredCubeExactOverlapEuclideanNormTwo
      s F⟩

end

end Homogenization
