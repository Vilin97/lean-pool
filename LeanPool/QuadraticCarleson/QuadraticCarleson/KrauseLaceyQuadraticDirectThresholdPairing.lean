/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNonstandardLocalInterpolation
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectSummation

/-!
# Threshold pairing algebra for the direct quadratic proof

This module isolates the low/high split in the direct proof supplied by the
author. The low portion uses only Holder and the `L²` estimate; the high
portion is the already-proved local-average pairing estimate. The final
lemmas insert `A = δ^{-2}` and `Λ = δ^{-(p-1)}` exactly.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyBadScale


/-- Holder together with the pointwise low truncation estimate. This is the
`L²` half of the direct threshold argument, independent of the particular
maximal operator. -/
theorem lintegral_pairing_interpolationLow_le
    {U g : ℝ → ℂ} (hU : AEMeasurable U volume)
    (hg : Measurable g) (hgi : Integrable g) {a p : ℝ}
    (ha : 0 < a) (hp : 0 < p) (hp2 : p ≤ 2) :
    (∫⁻ x, ‖U x‖ₑ * ‖interpolationLow g a x‖ₑ) ≤
      eLpNorm U 2 volume *
        (ENNReal.ofReal (a ^ (2 - p)) *
          ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p)) ^ (1 / 2 : ℝ) := by
  have hlow := integrable_interpolationLow_local hg hgi a
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq volume
    Real.HolderConjugate.two_two hU.enorm hlow.aestronglyMeasurable.enorm
  calc
    _ ≤ eLpNorm U 2 volume * eLpNorm (interpolationLow g a) 2 volume := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
          hU.aestronglyMeasurable,
        eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
          hlow.aestronglyMeasurable]
      simpa only [Pi.mul_apply, ENNReal.toReal_ofNat] using hholder
    _ ≤ _ := mul_le_mul' le_rfl
      (eLpNorm_interpolationLow_le_rpow g ha hp hp2 hg)

/-- The same low-truncation Holder estimate for a nonnegative
extended-real-valued maximal function. This is the form needed by
`offsetTailMaximalOn`, whose values are already norms. -/
theorem lintegral_pairing_interpolationLow_ennreal_le
    {U : ℝ → ℝ≥0∞} {g : ℝ → ℂ} (hU : AEMeasurable U volume)
    (hg : Measurable g) (hgi : Integrable g) {a p : ℝ}
    (ha : 0 < a) (hp : 0 < p) (hp2 : p ≤ 2) :
    (∫⁻ x, U x * ‖interpolationLow g a x‖ₑ) ≤
      eLpNorm U 2 volume *
        (ENNReal.ofReal (a ^ (2 - p)) *
          ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p)) ^ (1 / 2 : ℝ) := by
  have hlow := integrable_interpolationLow_local hg hgi a
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq volume
    Real.HolderConjugate.two_two hU hlow.aestronglyMeasurable.enorm
  calc
    _ ≤ eLpNorm U 2 volume * eLpNorm (interpolationLow g a) 2 volume := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
          hU.aestronglyMeasurable,
        eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
          hlow.aestronglyMeasurable]
      simpa only [Pi.mul_apply, ENNReal.toReal_ofNat, enorm_eq_self] using hholder
    _ ≤ _ := mul_le_mul' le_rfl
      (eLpNorm_interpolationLow_le_rpow g ha hp hp2 hg)

/-- The elementary real identity which turns the low Holder factor into the
source expression `δ A^{1-p/2} V`. -/
theorem sqrt_mul_rpow_mul_sqrt
    {A V p : ℝ} (hA : 0 < A) (hV : 0 ≤ V) :
    Real.sqrt V * (A ^ (2 - p) * V) ^ (1 / 2 : ℝ) =
      A ^ (1 - p / 2) * V := by
  have hApow : 0 ≤ A ^ (2 - p) := Real.rpow_nonneg hA.le _
  rw [Real.mul_rpow hApow hV]
  rw [← Real.rpow_mul hA.le]
  rw [show (2 - p) * (1 / 2 : ℝ) = 1 - p / 2 by ring]
  rw [← Real.sqrt_eq_rpow]
  calc
    Real.sqrt V * (A ^ (1 - p / 2) * Real.sqrt V) =
        A ^ (1 - p / 2) * (Real.sqrt V * Real.sqrt V) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hV]

/-- The low part of the direct proof in its normalized form. If `U` has
`L²` size at most `δ √V` and `g` has `p`-mass at most `V`, then truncating
at `A` costs exactly `δ A^{1-p/2} V`. -/
theorem lintegral_pairing_interpolationLow_le_normalized
    {U g : ℝ → ℂ} (hUmeas : AEMeasurable U volume)
    (hg : Measurable g) (hgi : Integrable g) {a p delta V : ℝ}
    (ha : 0 < a) (hp : 0 < p) (hp2 : p ≤ 2)
    (hdelta : 0 ≤ delta) (hV : 0 ≤ V)
    (hU : eLpNorm U 2 volume ≤ ENNReal.ofReal (delta * Real.sqrt V))
    (hgp : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p)) ≤ ENNReal.ofReal V) :
    (∫⁻ x, ‖U x‖ₑ * ‖interpolationLow g a x‖ₑ) ≤
      ENNReal.ofReal (delta * a ^ (1 - p / 2) * V) := by
  calc
    _ ≤ eLpNorm U 2 volume *
        (ENNReal.ofReal (a ^ (2 - p)) *
          ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p)) ^ (1 / 2 : ℝ) :=
      lintegral_pairing_interpolationLow_le hUmeas hg hgi ha hp hp2
    _ ≤ ENNReal.ofReal (delta * Real.sqrt V) *
        (ENNReal.ofReal (a ^ (2 - p)) * ENNReal.ofReal V) ^ (1 / 2 : ℝ) := by
      apply mul_le_mul' hU
      apply ENNReal.rpow_le_rpow
      · exact mul_le_mul' le_rfl hgp
      norm_num
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le (2 - p))]
      rw [ENNReal.ofReal_rpow_of_nonneg
        (mul_nonneg (Real.rpow_nonneg ha.le _) hV) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      rw [← ENNReal.ofReal_mul (mul_nonneg hdelta (Real.sqrt_nonneg V))]
      rw [show delta * Real.sqrt V * (a ^ (2 - p) * V) ^ (1 / 2 : ℝ) =
        delta * (Real.sqrt V * (a ^ (2 - p) * V) ^ (1 / 2 : ℝ)) by ring]
      rw [sqrt_mul_rpow_mul_sqrt ha hV]
      congr 1
      ring

/-- The high part of the direct proof: the local-average pairing estimate
turns the high truncation into the factor `A^{1-p}`. -/
theorem lintegral_nonstandard_pairing_interpolationHigh_le
    {S : Finset RealInterval} {f g : ℝ → ℂ} (hf : Integrable f)
    (hg : Measurable g) (hgi : Integrable g) {a p G : ℝ}
    (ha : 0 < a) (hp : 1 < p) (hG : 0 ≤ G)
    (hgp : Integrable (fun x ↦ ‖g x‖ ^ p))
    (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale)
    (hgavg : ∀ I ∈ N, (∫ x in I.carrier, ‖g x‖ ^ p) ≤ G * I.length) :
    (∫⁻ x, ‖badLengthTailMaximal S f I₀ k₀ s scale N x‖ₑ *
      ‖interpolationHigh g a x‖ₑ) ≤
      ENNReal.ofReal
        (8 * positiveDyadicAmplitudeBound * (a ^ (1 - p) * G) * ∫ x, ‖f x‖) := by
  apply lintegral_nonstandard_pairing_le_of_averages_le hf
    (integrable_interpolationHigh_local hg hgi a) I₀ k₀ s scale hlam N hN
  · exact mul_nonneg (Real.rpow_nonneg ha.le _) hG
  · intro I hI
    exact intervalL1Average_interpolationHigh_le hg hgi ha hp hgp I (hgavg I hI)

/-- At `A = δ^{-2}`, the high threshold factor is exactly
`δ^{p-1}` after multiplication by the exceptional-average cutoff. -/
theorem directQuadratic_high_pairing_factor
    {p : ℝ} (s : ℕ) :
    directQuadraticLowThreshold s ^ (1 - p) *
      directQuadraticExceptionalThreshold p s =
      directQuadraticDelta s ^ (p - 1) :=
  directQuadratic_high_threshold_identity p s

/-- At `A = δ^{-2}`, the normalized low term is exactly the same offset
decay as the high term. -/
theorem directQuadratic_low_pairing_factor
    {p : ℝ} (s : ℕ) :
    directQuadraticDelta s *
      directQuadraticLowThreshold s ^ (1 - p / 2) =
      directQuadraticDelta s ^ (p - 1) :=
  directQuadratic_low_threshold_identity p s

/-- The normalized low pairing at the author's choice
`A = (2^{-s/2})^{-2}`. -/
theorem lintegral_pairing_interpolationLow_le_directQuadratic
    {U g : ℝ → ℂ} (hUmeas : AEMeasurable U volume)
    (hg : Measurable g) (hgi : Integrable g) {p V : ℝ} (s : ℕ)
    (hp : 0 < p) (hp2 : p ≤ 2) (hV : 0 ≤ V)
    (hU : eLpNorm U 2 volume ≤
      ENNReal.ofReal (directQuadraticDelta s * Real.sqrt V))
    (hgp : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p)) ≤ ENNReal.ofReal V) :
    (∫⁻ x, ‖U x‖ₑ *
      ‖interpolationLow g (directQuadraticLowThreshold s) x‖ₑ) ≤
      ENNReal.ofReal (directQuadraticDelta s ^ (p - 1) * V) := by
  have hdelta : 0 ≤ directQuadraticDelta s := (directQuadraticDelta_pos s).le
  have ha : 0 < directQuadraticLowThreshold s :=
    Real.rpow_pos_of_pos (directQuadraticDelta_pos s) _
  calc
    _ ≤ ENNReal.ofReal (directQuadraticDelta s *
        directQuadraticLowThreshold s ^ (1 - p / 2) * V) :=
      lintegral_pairing_interpolationLow_le_normalized hUmeas hg hgi ha hp hp2
        hdelta hV hU hgp
    _ = _ := by
      rw [show directQuadraticDelta s *
          directQuadraticLowThreshold s ^ (1 - p / 2) * V =
          (directQuadraticDelta s *
            directQuadraticLowThreshold s ^ (1 - p / 2)) * V by ring]
      rw [directQuadratic_low_threshold_identity]

/-- The high local-average pairing at the author's simultaneous choice
`A = δ^{-2}`, `Λ = δ^{-(p-1)}`. -/
theorem lintegral_nonstandard_pairing_interpolationHigh_le_directQuadratic
    {S : Finset RealInterval} {f g : ℝ → ℂ} (hf : Integrable f)
    (hg : Measurable g) (hgi : Integrable g) {p : ℝ}
    (hp : 1 < p) (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale)
    (hgp : Integrable (fun x ↦ ‖g x‖ ^ p))
    (hgavg : ∀ I ∈ N, (∫ x in I.carrier, ‖g x‖ ^ p) ≤
      directQuadraticExceptionalThreshold p s * I.length) :
    (∫⁻ x, ‖badLengthTailMaximal S f I₀ k₀ s scale N x‖ₑ *
      ‖interpolationHigh g (directQuadraticLowThreshold s) x‖ₑ) ≤
      ENNReal.ofReal (8 * positiveDyadicAmplitudeBound *
        directQuadraticDelta s ^ (p - 1) * ∫ x, ‖f x‖) := by
  have ha : 0 < directQuadraticLowThreshold s :=
    Real.rpow_pos_of_pos (directQuadraticDelta_pos s) _
  have hG : 0 ≤ directQuadraticExceptionalThreshold p s :=
    Real.rpow_nonneg (directQuadraticDelta_pos s).le _
  calc
    _ ≤ ENNReal.ofReal (8 * positiveDyadicAmplitudeBound *
        (directQuadraticLowThreshold s ^ (1 - p) *
          directQuadraticExceptionalThreshold p s) * ∫ x, ‖f x‖) :=
      lintegral_nonstandard_pairing_interpolationHigh_le hf hg hgi ha hp hG hgp
        I₀ k₀ s scale hlam N hN hgavg
    _ = _ := by
      rw [directQuadratic_high_threshold_identity]


end KrauseLaceyBadScale
end QuadraticCarleson
