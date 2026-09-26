/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.ContinuousKRegularity
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.FullNormEquivalence

/-!
# Full continuous K-regularity for the unit-cube Dirichlet problem

This module integrates the pointwise continuous `K`-functional estimate and
combines it with the exact normalized Euclidean `L²` energy estimate.  The
resulting full-norm constant is chosen before the fractional order, datum, and
solution.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem UnitCubeEuclideanL2Field.ambientMemL2 {d : ℕ}
    (F : UnitCubeEuclideanL2Field d) :
    MemLp F (2 : ℝ≥0∞) (unitCenteredCubeDomain d).normalizedVolume := by
  apply MemLp.of_eval
  intro i
  have hF := F.euclideanMemL2
  rw [memLp_piLp_iff] at hF
  simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using hF i

private theorem continuousKSeminorm_le_of_pointwise
    {d : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hpoint : ∀ (h : UnitCubeEuclideanL2Field d)
      (w : H10Function (openCubeSet (originCube d 0)))
      (t : ContinuousKScale),
      CubeDirichletDivergenceProblem (originCube d 0) w h →
        continuousKFunctional t (unitCubeGradientEuclideanL2Field w) ≤
          C * continuousKFunctional t h) :
    ∀ (s : FractionalOrder) (h : UnitCubeEuclideanL2Field d)
      (w : H10Function (openCubeSet (originCube d 0))),
      CubeDirichletDivergenceProblem (originCube d 0) w h →
        continuousKSeminorm s (unitCubeGradientEuclideanL2Field w) ≤
          (ENNReal.ofReal C ^ 2) ^ (1 / 2 : ℝ) * continuousKSeminorm s h := by
  intro s h w hweak
  let out : UnitCubeEuclideanL2Field d := unitCubeGradientEuclideanL2Field w
  let c : ℝ≥0∞ := ENNReal.ofReal C
  have hintegrand : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      continuousKSeminormIntegrand s.1 out t ≤
        c ^ 2 * continuousKSeminormIntegrand s.1 h t := by
    intro t ht
    let kt : ContinuousKScale := ⟨t, ⟨ht.1, ht.2.le⟩⟩
    have hK : continuousKFunctional kt out ≤ C * continuousKFunctional kt h := by
      simpa only [out] using hpoint h w kt hweak
    have hCkh_nonneg : 0 ≤ C * continuousKFunctional kt h :=
      mul_nonneg hC (continuousKFunctional_nonneg kt h)
    have hKsq : continuousKFunctional kt out ^ 2 ≤
        (C * continuousKFunctional kt h) ^ 2 :=
      (sq_le_sq₀ (continuousKFunctional_nonneg kt out) hCkh_nonneg).2 hK
    have hKsq_ofReal :
        ENNReal.ofReal (continuousKFunctional kt out ^ 2) ≤
          c ^ 2 * ENNReal.ofReal (continuousKFunctional kt h ^ 2) := by
      calc
        ENNReal.ofReal (continuousKFunctional kt out ^ 2) ≤
            ENNReal.ofReal ((C * continuousKFunctional kt h) ^ 2) :=
          ENNReal.ofReal_le_ofReal hKsq
        _ = c ^ 2 * ENNReal.ofReal (continuousKFunctional kt h ^ 2) := by
          rw [ENNReal.ofReal_pow hCkh_nonneg, ENNReal.ofReal_mul hC,
            ENNReal.ofReal_pow (continuousKFunctional_nonneg kt h)]
          ring
    rw [continuousKSeminormIntegrand_eq_of_mem s.1 out ht,
      continuousKSeminormIntegrand_eq_of_mem s.1 h ht]
    change
      ENNReal.ofReal (Real.rpow t (-2 * s.1)) *
          ENNReal.ofReal (continuousKFunctional kt out ^ 2) * ENNReal.ofReal t⁻¹ ≤
        c ^ 2 *
          (ENNReal.ofReal (Real.rpow t (-2 * s.1)) *
            ENNReal.ofReal (continuousKFunctional kt h ^ 2) * ENNReal.ofReal t⁻¹)
    calc
      ENNReal.ofReal (Real.rpow t (-2 * s.1)) *
          ENNReal.ofReal (continuousKFunctional kt out ^ 2) * ENNReal.ofReal t⁻¹ ≤
        ENNReal.ofReal (Real.rpow t (-2 * s.1)) *
          (c ^ 2 * ENNReal.ofReal (continuousKFunctional kt h ^ 2)) *
            ENNReal.ofReal t⁻¹ := by
              gcongr
      _ = c ^ 2 *
          (ENNReal.ofReal (Real.rpow t (-2 * s.1)) *
            ENNReal.ofReal (continuousKFunctional kt h ^ 2) * ENNReal.ofReal t⁻¹) := by
              ring
  have hintegral :
      (∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 out t) ≤
        c ^ 2 *
          ∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 h t := by
    calc
      (∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 out t) ≤
          ∫⁻ t in Set.Ioo (0 : ℝ) 1,
            c ^ 2 * continuousKSeminormIntegrand s.1 h t :=
        setLIntegral_mono' measurableSet_Ioo hintegrand
      _ = c ^ 2 *
          ∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 h t := by
        rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  rw [continuousKSeminorm_eq_lintegral, continuousKSeminorm_eq_lintegral]
  calc
    (∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 out t) ^
          (1 / 2 : ℝ) ≤
        (c ^ 2 *
          ∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 h t) ^
            (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow hintegral (by norm_num)
    _ = (c ^ 2) ^ (1 / 2 : ℝ) *
        (∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 h t) ^
          (1 / 2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    _ = (ENNReal.ofReal C ^ 2) ^ (1 / 2 : ℝ) *
        (∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 h t) ^
          (1 / 2 : ℝ) := rfl

/-- Integrating the pointwise continuous `K`-functional estimate gives a
uniform continuum interpolation-seminorm estimate. -/
theorem exists_unitCubeDirichletContinuousKSeminormRegularity
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (s : FractionalOrder) (h : UnitCubeEuclideanL2Field d)
        (w : H10Function (openCubeSet (originCube d 0))),
        CubeDirichletDivergenceProblem (originCube d 0) w h →
          continuousKSeminorm s (unitCubeGradientEuclideanL2Field w) ≤
            C * continuousKSeminorm s h := by
  rcases exists_unitCubeDirichletContinuousKFunctionalRegularity d with
    ⟨C, hC, hpoint⟩
  let Csem : ℝ≥0∞ := (ENNReal.ofReal C ^ 2) ^ (1 / 2 : ℝ)
  refine ⟨Csem, ?_, ?_⟩
  · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  · simpa only [Csem] using continuousKSeminorm_le_of_pointwise hC hpoint

/-- The weak Dirichlet equation controls the exact normalized Euclidean `L²`
norm of the solution gradient by that of the datum.  The concrete ambient-norm
energy theorem is converted here using both directions of the explicit
finite-dimensional Euclidean/ambient norm comparison. -/
theorem exists_unitCubeGradientNormalizedEuclideanL2EnergyRegularity
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (h : UnitCubeEuclideanL2Field d)
        (w : H10Function (openCubeSet (originCube d 0))),
        CubeDirichletDivergenceProblem (originCube d 0) w h →
          (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
              (unitCubeGradientEuclideanL2Field w) ≤
            C * (unitCenteredCubeDomain d).normalizedEuclideanLpENorm
              (2 : ℝ≥0∞) h := by
  rcases cubeDirichletDivergenceEnergyEstimate d with ⟨C₀, hC₀, henergy⟩
  let Cenergy : ℝ≥0∞ := ENNReal.ofReal (d : ℝ) * ENNReal.ofReal C₀
  refine ⟨Cenergy, ?_, ?_⟩
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  · intro h w hweak
    let out : UnitCubeEuclideanL2Field d := unitCubeGradientEuclideanL2Field w
    let μ : Measure (Vec d) := (unitCenteredCubeDomain d).normalizedVolume
    have hout_mem : MemLp out (2 : ℝ≥0∞) μ := out.ambientMemL2
    have hh_mem : MemLp h (2 : ℝ≥0∞) μ := h.ambientMemL2
    have hh_cube_mem :
        MemLp h (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d 0)) := by
      rw [normalizedCubeMeasure_originCube_zero_eq_unitCenteredCubeDomain_normalizedVolume]
      exact hh_mem
    have henergy_real :
        (eLpNorm out (2 : ℝ≥0∞) μ).toReal ≤
          C₀ * (eLpNorm h (2 : ℝ≥0∞) μ).toReal := by
      simpa only [cubeLpNorm, μ, out, unitCubeGradientEuclideanL2Field,
        normalizedCubeMeasure_originCube_zero_eq_unitCenteredCubeDomain_normalizedVolume]
        using henergy (originCube d 0) h w hh_cube_mem hweak
    have henergy_ennreal :
        eLpNorm out (2 : ℝ≥0∞) μ ≤
          ENNReal.ofReal C₀ * eLpNorm h (2 : ℝ≥0∞) μ := by
      apply (ENNReal.toReal_le_toReal hout_mem.eLpNorm_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hh_mem.eLpNorm_ne_top)).mp
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC₀]
      exact henergy_real
    have hout_euclidean_le :
        eLpNorm (fun x => euclideanNorm (out x)) (2 : ℝ≥0∞) μ ≤
          ENNReal.ofReal (d : ℝ) * eLpNorm out (2 : ℝ≥0∞) μ := by
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      filter_upwards [] with x
      simpa only [Real.norm_eq_abs, abs_of_nonneg (euclideanNorm_nonneg (out x))] using
        euclideanNorm_le_dimension_mul_norm (out x)
    have hh_ambient_le_euclidean :
        eLpNorm h (2 : ℝ≥0∞) μ ≤
          eLpNorm (fun x => euclideanNorm (h x)) (2 : ℝ≥0∞) μ := by
      apply eLpNorm_mono
      intro x
      simpa only [Real.norm_eq_abs, abs_of_nonneg (euclideanNorm_nonneg (h x))] using
        norm_le_euclideanNorm (h x)
    change
      eLpNorm (fun x => euclideanNorm (out x)) (2 : ℝ≥0∞) μ ≤
        Cenergy * eLpNorm (fun x => euclideanNorm (h x)) (2 : ℝ≥0∞) μ
    calc
      eLpNorm (fun x => euclideanNorm (out x)) (2 : ℝ≥0∞) μ ≤
          ENNReal.ofReal (d : ℝ) * eLpNorm out (2 : ℝ≥0∞) μ :=
        hout_euclidean_le
      _ ≤ ENNReal.ofReal (d : ℝ) *
          (ENNReal.ofReal C₀ * eLpNorm h (2 : ℝ≥0∞) μ) := by
        gcongr
      _ ≤ ENNReal.ofReal (d : ℝ) *
          (ENNReal.ofReal C₀ *
            eLpNorm (fun x => euclideanNorm (h x)) (2 : ℝ≥0∞) μ) := by
        gcongr
      _ = Cenergy *
          eLpNorm (fun x => euclideanNorm (h x)) (2 : ℝ≥0∞) μ := by
        simp only [Cenergy]
        ring

/-- The exact additive continuous-interpolation full norm of the unit-cube
Dirichlet solution gradient is controlled by that of the datum.  A single
finite dimension-dependent constant is chosen before the fractional order,
datum, and solution; all endpoint and comparison estimates are discharged in
the proof. -/
theorem exists_unitCubeDirichletContinuousKFullENormRegularity
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (s : FractionalOrder) (h : UnitCubeEuclideanL2Field d)
        (w : H10Function (openCubeSet (originCube d 0))),
        CubeDirichletDivergenceProblem (originCube d 0) w h →
          continuousKFullENorm s (unitCubeGradientEuclideanL2Field w) ≤
            C * continuousKFullENorm s h := by
  rcases exists_unitCubeGradientNormalizedEuclideanL2EnergyRegularity d with
    ⟨Cenergy, hCenergy, henergy⟩
  rcases exists_unitCubeDirichletContinuousKSeminormRegularity d with
    ⟨Csem, hCsem, hsem⟩
  let C : ℝ≥0∞ := max Cenergy Csem
  refine ⟨C, (max_lt_iff.2 ⟨hCenergy, hCsem⟩), ?_⟩
  intro s h w hweak
  rw [continuousKFullENorm_eq, continuousKFullENorm_eq]
  calc
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
          (unitCubeGradientEuclideanL2Field w) +
        continuousKSeminorm s (unitCubeGradientEuclideanL2Field w) ≤
      Cenergy *
          (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) h +
        Csem * continuousKSeminorm s h :=
      add_le_add (henergy h w hweak) (hsem s h w hweak)
    _ ≤ C * (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) h +
        C * continuousKSeminorm s h := by
      apply add_le_add
      · exact mul_le_mul_left (le_max_left Cenergy Csem) _
      · exact mul_le_mul_left (le_max_right Cenergy Csem) _
    _ = C *
        ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) h +
          continuousKSeminorm s h) := by
      rw [mul_add]

end

end Homogenization
