/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyStandardSourceLinf

/-!
# Source-faithful interpolation for the scalar-standard contribution

At one physical scale the source proof combines a local-average `L∞` bound
with the already established squared `L²` estimate. The interpolation here
is applied to that fixed output function itself. This is important because
the stopping collection depends on the input, so it would be incorrect to
silently treat the construction as a fixed operator and invoke an operator
interpolation theorem.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyStoppingExtraction

attribute [local instance] Classical.propDecidable

/-- Direct interpolation of one output function between a pointwise bound
and its squared `L²` mass. -/
theorem lintegral_enorm_rpow_le_linf_mul_sq
    {E : Type*} [NormedAddCommGroup E]
    (F : ℝ → E) {M q : ℝ} (hM : 0 ≤ M) (hq : 2 ≤ q)
    (hbound : ∀ x, ‖F x‖ ≤ M) :
    (∫⁻ x, ‖F x‖ₑ ^ q) ≤
      ENNReal.ofReal (M ^ (q - 2)) * ∫⁻ x, ‖F x‖ₑ ^ (2 : ℕ) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro x
  change ‖F x‖ₑ ^ q ≤ ENNReal.ofReal (M ^ (q - 2)) * ‖F x‖ₑ ^ (2 : ℕ)
  calc
    ‖F x‖ₑ ^ q = ‖F x‖ₑ ^ (q - 2) * ‖F x‖ₑ ^ (2 : ℕ) := by
      nth_rewrite 1 [show q = (q - 2) + 2 by ring]
      rw [ENNReal.rpow_add_of_nonneg (q - 2) 2 (by linarith) (by norm_num)]
      rw [ENNReal.rpow_two]
    _ ≤ ENNReal.ofReal (M ^ (q - 2)) * ‖F x‖ₑ ^ (2 : ℕ) := by
      gcongr
      rw [← ENNReal.ofReal_rpow_of_nonneg hM (by linarith)]
      apply ENNReal.rpow_le_rpow
      · rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hbound x)
      · linarith

private theorem eLpNorm_two_sq_lintegral_source {E : Type*} [ENorm E] [TopologicalSpace E]
    (F : ℝ → E) (hF : AEStronglyMeasurable F volume) :
    eLpNorm F 2 volume ^ 2 = ∫⁻ x, ‖F x‖ₑ ^ (2 : ℕ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hF]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [← ENNReal.rpow_mul_natCast]
  norm_num

private theorem aestronglyMeasurable_sourceAction
    (S : Finset RealInterval) (f : ℝ → ℂ) (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (scale : RealInterval → ℤ)
    (R : Finset ℤ) (N : ℤ → Finset RealInterval) :
    AEStronglyMeasurable (energyStandardFixedPhysicalSourceAction S f I₀ k₀ scale R N) volume :=
  (Lp.aestronglyMeasurable (energyStandardFixedPhysicalSourceLp S f hf I₀ k₀ scale R N)).congr
    (energyStandardFixedPhysicalSourceLp_ae_eq S f hf I₀ k₀ scale R N)

/-- The `Lp`-valued squared estimate transferred to the actual pointwise
fixed-physical-scale source action. -/
theorem energyStandardFixedPhysicalSourceAction_sq_lintegral_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ j : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (R : Finset ℤ) (N : ℤ → Finset RealInterval)
    (hN : ∀ s ∈ R, N s ⊆ energyStandardIntervals S f I₀ k₀ s scale)
    (hfixed : ∀ s ∈ R, ∀ I ∈ N s, scale I + 2 = j) :
    (∫⁻ x, ‖energyStandardFixedPhysicalSourceAction
        S f I₀ k₀ scale R N x‖ₑ ^ (2 : ℕ)) ≤
      ENNReal.ofReal ((R.card : ℝ) *
        ((2560 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ /
          (2 : ℝ) ^ j) * ∫ x, ‖f x‖)) := by
  rw [← eLpNorm_two_sq_lintegral_source _
    (aestronglyMeasurable_sourceAction S f hf I₀ k₀ scale _ N)]
  rw [eLpNorm_congr_ae
    (energyStandardFixedPhysicalSourceLp_ae_eq S f hf I₀ k₀ scale R N).symm]
  rw [← MeasureTheory.Lp.enorm_def]
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _) 2]
  exact ENNReal.ofReal_le_ofReal
    (norm_energyStandardFixedPhysicalSourceLp_sq_le
      hf I₀ k₀ j scale hlam hsub R N hN hfixed)

/-- Fixed-scale `L²`--`L∞` interpolation for the actual scalar-standard
source action, before specializing the source-gap range. -/
theorem energyStandardFixedPhysicalSourceAction_rpow_lintegral_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ j : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (R : Finset ℤ) (N : ℤ → Finset RealInterval)
    (hN : ∀ s ∈ R, N s ⊆ energyStandardIntervals S f I₀ k₀ s scale)
    (hfixed : ∀ s ∈ R, ∀ I ∈ N s, scale I + 2 = j)
    {q : ℝ} (hq : 2 ≤ q) :
    (∫⁻ x, ‖energyStandardFixedPhysicalSourceAction
        S f I₀ k₀ scale R N x‖ₑ ^ q) ≤
      ENNReal.ofReal
          ((80 * positiveDyadicAmplitudeBound * intervalL1Average f I₀) ^ (q - 2)) *
        ENNReal.ofReal ((R.card : ℝ) *
          ((2560 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ /
            (2 : ℝ) ^ j) * ∫ x, ‖f x‖)) := by
  apply (lintegral_enorm_rpow_le_linf_mul_sq
    (energyStandardFixedPhysicalSourceAction S f I₀ k₀ scale R N)
    (mul_nonneg (mul_nonneg (by norm_num) positiveDyadicAmplitudeBound_nonneg)
      (intervalL1Average_nonneg f I₀)) hq
    (norm_energyStandardFixedPhysicalSourceAction_le_localAverage
      hf I₀ k₀ j scale hlam hsub R N hN hfixed)).trans
  exact mul_le_mul_of_nonneg_left
    (energyStandardFixedPhysicalSourceAction_sq_lintegral_le
      hf I₀ k₀ j scale hlam hsub R N hN hfixed) (by positivity)

/-- Norm form of the fixed-scale interpolation estimate. -/
theorem eLpNorm_energyStandardFixedPhysicalSourceAction_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ j : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (R : Finset ℤ) (N : ℤ → Finset RealInterval)
    (hN : ∀ s ∈ R, N s ⊆ energyStandardIntervals S f I₀ k₀ s scale)
    (hfixed : ∀ s ∈ R, ∀ I ∈ N s, scale I + 2 = j)
    {q : ℝ} (hq : 2 ≤ q) :
    eLpNorm (energyStandardFixedPhysicalSourceAction
        S f I₀ k₀ scale R N) (ENNReal.ofReal q) volume ≤
      (ENNReal.ofReal
          ((80 * positiveDyadicAmplitudeBound * intervalL1Average f I₀) ^ (q - 2)) *
        ENNReal.ofReal ((R.card : ℝ) *
          ((2560 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ /
            (2 : ℝ) ^ j) * ∫ x, ‖f x‖))) ^ (1 / q) := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hqne : ENNReal.ofReal q ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr hq0
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hqne ENNReal.ofReal_ne_top
      (aestronglyMeasurable_sourceAction S f hf I₀ k₀ scale _ N),
    ENNReal.toReal_ofReal hq0.le]
  exact ENNReal.rpow_le_rpow
    (energyStandardFixedPhysicalSourceAction_rpow_lintegral_le
      hf I₀ k₀ j scale hlam hsub R N hN hfixed hq)
    (one_div_nonneg.mpr hq0.le)

/-- The same squared pointwise-output estimate with the paper's exact source
gap range `0 ≤ s ≤ j-k₀`, hence exactly one factor `j`. -/
theorem energyStandardFixedPhysicalSourceAction_sq_lintegral_le_j_mul
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ j : ℤ) (hk₀ : 1 ≤ k₀) (hk₀j : k₀ ≤ j)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : ℤ → Finset RealInterval)
    (hN : ∀ s ∈ standardSourceGaps k₀ j,
      N s ⊆ energyStandardIntervals S f I₀ k₀ s scale)
    (hfixed : ∀ s ∈ standardSourceGaps k₀ j, ∀ I ∈ N s,
      scale I + 2 = j) :
    (∫⁻ x, ‖energyStandardFixedPhysicalSourceAction S f I₀ k₀ scale
        (standardSourceGaps k₀ j) N x‖ₑ ^ (2 : ℕ)) ≤
      ENNReal.ofReal ((j : ℝ) *
        ((2560 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ /
          (2 : ℝ) ^ j) * ∫ x, ‖f x‖)) := by
  rw [← eLpNorm_two_sq_lintegral_source _
    (aestronglyMeasurable_sourceAction S f hf I₀ k₀ scale _ N)]
  rw [eLpNorm_congr_ae (energyStandardFixedPhysicalSourceLp_ae_eq S f hf I₀ k₀ scale
    (standardSourceGaps k₀ j) N).symm]
  rw [← MeasureTheory.Lp.enorm_def]
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _) 2]
  exact ENNReal.ofReal_le_ofReal
    (norm_energyStandardFixedPhysicalSourceLp_sq_le_j_mul
      hf I₀ k₀ j hk₀ hk₀j scale hlam hsub N hN hfixed)

/-- The precise source fixed-scale interpolation estimate: the local-average
`L∞` endpoint and the `j 2⁻j` squared `L²` endpoint are both visible. -/
theorem energyStandardFixedPhysicalSourceAction_rpow_lintegral_le_j_mul
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ j : ℤ) (hk₀ : 1 ≤ k₀) (hk₀j : k₀ ≤ j)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : ℤ → Finset RealInterval)
    (hN : ∀ s ∈ standardSourceGaps k₀ j,
      N s ⊆ energyStandardIntervals S f I₀ k₀ s scale)
    (hfixed : ∀ s ∈ standardSourceGaps k₀ j, ∀ I ∈ N s,
      scale I + 2 = j) {q : ℝ} (hq : 2 ≤ q) :
    (∫⁻ x, ‖energyStandardFixedPhysicalSourceAction S f I₀ k₀ scale
        (standardSourceGaps k₀ j) N x‖ₑ ^ q) ≤
      ENNReal.ofReal
          ((80 * positiveDyadicAmplitudeBound * intervalL1Average f I₀) ^ (q - 2)) *
        ENNReal.ofReal ((j : ℝ) *
          ((2560 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ /
            (2 : ℝ) ^ j) * ∫ x, ‖f x‖)) := by
  apply (lintegral_enorm_rpow_le_linf_mul_sq
    (energyStandardFixedPhysicalSourceAction S f I₀ k₀ scale
      (standardSourceGaps k₀ j) N)
    (mul_nonneg (mul_nonneg (by norm_num) positiveDyadicAmplitudeBound_nonneg)
      (intervalL1Average_nonneg f I₀)) hq
    (norm_energyStandardFixedPhysicalSourceAction_le_localAverage hf I₀ k₀ j scale
      hlam hsub (standardSourceGaps k₀ j) N hN hfixed)).trans
  exact mul_le_mul_of_nonneg_left
    (energyStandardFixedPhysicalSourceAction_sq_lintegral_le_j_mul
      hf I₀ k₀ j hk₀ hk₀j scale hlam hsub N hN hfixed) (by positivity)

/-- `L^q` norm form of the exact source-gap estimate. -/
theorem eLpNorm_energyStandardFixedPhysicalSourceAction_le_j_mul
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ j : ℤ) (hk₀ : 1 ≤ k₀) (hk₀j : k₀ ≤ j)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : ℤ → Finset RealInterval)
    (hN : ∀ s ∈ standardSourceGaps k₀ j,
      N s ⊆ energyStandardIntervals S f I₀ k₀ s scale)
    (hfixed : ∀ s ∈ standardSourceGaps k₀ j, ∀ I ∈ N s,
      scale I + 2 = j) {q : ℝ} (hq : 2 ≤ q) :
    eLpNorm (energyStandardFixedPhysicalSourceAction S f I₀ k₀ scale
        (standardSourceGaps k₀ j) N) (ENNReal.ofReal q) volume ≤
      (ENNReal.ofReal
          ((80 * positiveDyadicAmplitudeBound * intervalL1Average f I₀) ^ (q - 2)) *
        ENNReal.ofReal ((j : ℝ) *
          ((2560 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ /
            (2 : ℝ) ^ j) * ∫ x, ‖f x‖))) ^ (1 / q) := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hqne : ENNReal.ofReal q ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr hq0
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hqne ENNReal.ofReal_ne_top
      (aestronglyMeasurable_sourceAction S f hf I₀ k₀ scale _ N),
    ENNReal.toReal_ofReal hq0.le]
  exact ENNReal.rpow_le_rpow
    (energyStandardFixedPhysicalSourceAction_rpow_lintegral_le_j_mul
      hf I₀ k₀ j hk₀ hk₀j scale hlam hsub N hN hfixed hq)
    (one_div_nonneg.mpr hq0.le)


end KrauseLaceyBadScale
end QuadraticCarleson
