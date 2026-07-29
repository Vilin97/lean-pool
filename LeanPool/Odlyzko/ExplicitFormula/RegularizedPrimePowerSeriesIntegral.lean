/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPrimePowerIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Regularized Prime Power Series Integral

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Ideal IsDedekindDomain MeasureTheory Real

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

theorem hasSum_integral_poitouTransform_regularized_mul_primePowerLogTerm
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    HasSum
      (fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦
        ∫ t : ℝ,
          poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
            primePowerLogTerm K pe.1 pe.2 (σ + t * I))
      (∫ t : ℝ,
        ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
          poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
            primePowerLogTerm K pe.1 pe.2 (σ + t * I)) := by
  let Φ : ℝ → ℂ := fun t ↦
    poitouTransform (regularizedScaledTartar y δ) (σ + t * I)
  let b : HeightOneSpectrum (𝓞 K) × ℕ → ℝ := fun pe ↦
    ‖primePowerLogTerm K pe.1 pe.2 (σ : ℂ)‖
  have hΦ : Integrable Φ :=
    poitouTransform_regularizedScaledTartar_vertical_integrable hδ y σ
  have hb : Summable b :=
    summable_norm_primePowerLogTerm K
      (s := (σ : ℂ)) (by simpa using hσ)
  apply hasSum_integral_of_dominated_convergence
    (fun pe t ↦ ‖Φ t‖ * b pe)
  · intro pe
    apply hΦ.aestronglyMeasurable.mul
    have heq :
        (fun t : ℝ ↦ primePowerLogTerm K pe.1 pe.2 (σ + t * I)) =
          fun t : ℝ ↦
            (Real.log (primeIdealNorm K pe.1) : ℂ) *
              Complex.exp
                (-(((pe.2 + 1 : ℕ) : ℝ) *
                  Real.log (primeIdealNorm K pe.1)) * (σ + t * I)) := by
      funext t
      exact primePowerLogTerm_eq_log_mul_cexp_neg K pe.1 pe.2 _
    rw [heq]
    fun_prop
  · intro pe
    filter_upwards [] with t
    rw [norm_mul]
    dsimp only [Φ]
    dsimp only [b]
    rw [norm_primePowerLogTerm, norm_primePowerLogTerm]
    simp
  · filter_upwards [] with t
    exact hb.mul_left ‖Φ t‖
  · have hnorm : Integrable (fun t ↦ ‖Φ t‖) := hΦ.norm
    convert hnorm.const_mul (∑' pe, b pe) using 1
    funext t
    rw [tsum_mul_left]
    ring
  · filter_upwards [] with t
    have hst : 1 < (σ + t * I : ℂ).re := by simpa using hσ
    exact
      (((summable_norm_primePowerLogTerm K hst).of_norm.mul_left (Φ t)).hasSum)

theorem integral_poitouTransform_regularized_mul_neg_logDeriv_dedekindZeta_eq_tsum
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    (∫ t : ℝ,
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        (-logDeriv (dedekindZeta K) (σ + t * I))) =
      ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
        ((2 * Real.pi *
          regularizedPrimePowerPoitouWeight K y δ pe.1 pe.2 : ℝ) : ℂ) := by
  calc
    _ = ∫ t : ℝ,
        ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
          poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
            primePowerLogTerm K pe.1 pe.2 (σ + t * I) := by
      apply integral_congr_ae
      filter_upwards [] with t
      have hst : 1 < (σ + t * I : ℂ).re := by simpa using hσ
      rw [neg_logDeriv_dedekindZeta_eq_tsum_primePower K hst,
        tsum_mul_left]
    _ = ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
        ∫ t : ℝ,
          poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
            primePowerLogTerm K pe.1 pe.2 (σ + t * I) :=
      (hasSum_integral_poitouTransform_regularized_mul_primePowerLogTerm
        K hδ y hσ).tsum_eq.symm
    _ = _ := by
      congr 1
      funext pe
      exact integral_poitouTransform_regularized_mul_primePowerLogTerm
        K hδ y σ pe.1 pe.2

theorem summable_regularizedPrimePowerPoitouWeight
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦
      regularizedPrimePowerPoitouWeight K y δ pe.1 pe.2) := by
  have hs :
      Summable (fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦
        ((2 * Real.pi *
          regularizedPrimePowerPoitouWeight K y δ pe.1 pe.2 : ℝ) : ℂ)) := by
    apply
      (hasSum_integral_poitouTransform_regularized_mul_primePowerLogTerm
        K hδ y hσ).summable.congr
    intro pe
    exact integral_poitouTransform_regularized_mul_primePowerLogTerm
      K hδ y σ pe.1 pe.2
  have hsReal :
      Summable (fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦
        2 * Real.pi *
          regularizedPrimePowerPoitouWeight K y δ pe.1 pe.2) :=
    Complex.summable_ofReal.mp hs
  exact (summable_mul_left_iff (mul_ne_zero (by norm_num) Real.pi_ne_zero)).mp hsReal

theorem tsum_regularizedPrimePowerPoitouWeight_nonneg
    (y δ : ℝ) :
    0 ≤ ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
      regularizedPrimePowerPoitouWeight K y δ pe.1 pe.2 :=
  tsum_nonneg fun pe ↦
    regularizedPrimePowerPoitouWeight_nonneg K y δ pe.1 pe.2

end NumberField.Odlyzko
