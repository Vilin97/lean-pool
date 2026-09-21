/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNonstandardPairing
import LeanPool.QuadraticCarleson.QuadraticCarleson.LpInterpolationTwoInfinity

/-!
# Local interpolation of the actual nonstandard contribution

Split the test function at a positive threshold. The low part is handled
by the proved maximal `L²` estimate; the high part uses the exact local
interval-average pairing bound. This is the source-faithful interpolation
mechanism for `1 < p ≤ 2`, with every threshold and constant explicit.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyBadScale


theorem norm_interpolationHigh_le_rpow (g : ℝ → ℂ) {a p : ℝ}
    (ha : 0 < a) (hp : 1 < p) (x : ℝ) :
    ‖interpolationHigh g a x‖ ≤ a ^ (1 - p) * ‖g x‖ ^ p := by
  by_cases hx : a < ‖g x‖
  · rw [interpolationHigh, ite_eq_left hx]
    have he : ‖g x‖ = ‖g x‖ ^ (1 - p) * ‖g x‖ ^ p := by
      rw [← Real.rpow_add (ha.trans hx), sub_add_cancel, Real.rpow_one]
    calc
      ‖g x‖ = _ := he
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos ha hx.le (by linarith)) (Real.rpow_nonneg (norm_nonneg _) _)
  · rw [interpolationHigh, ite_eq_right hx, norm_zero]
    exact mul_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg (norm_nonneg _) _)

theorem norm_interpolationLow_sq_le_rpow (g : ℝ → ℂ) {a p : ℝ}
    (ha : 0 < a) (hp : 0 < p) (hp2 : p ≤ 2) (x : ℝ) :
    ‖interpolationLow g a x‖ ^ 2 ≤ a ^ (2 - p) * ‖g x‖ ^ p := by
  by_cases hx : ‖g x‖ ≤ a
  · rw [interpolationLow, ite_eq_left hx]
    by_cases hz : ‖g x‖ = 0
    · simp [hz, Real.zero_rpow hp.ne']
    have hu : 0 < ‖g x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have he : ‖g x‖ ^ 2 = ‖g x‖ ^ (2 - p) * ‖g x‖ ^ p := by
      rw [← Real.rpow_add hu, sub_add_cancel, Real.rpow_two]
    calc
      ‖g x‖ ^ 2 = _ := he
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (norm_nonneg _) hx (by linarith)) (Real.rpow_nonneg (norm_nonneg _) _)
  · rw [interpolationLow, ite_eq_right hx, norm_zero, zero_pow (by omega : 2 ≠ 0)]
    exact mul_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg (norm_nonneg _) _)

theorem integrable_interpolationHigh_local
    {g : ℝ → ℂ} (hg : Measurable g) (hgi : Integrable g) (a : ℝ) :
    Integrable (interpolationHigh g a) := by
  apply hgi.mono (stronglyMeasurable_interpolationHigh hg.stronglyMeasurable a).aestronglyMeasurable
  filter_upwards with x
  unfold interpolationHigh
  split_ifs <;> simp [norm_nonneg]

theorem integrable_interpolationLow_local
    {g : ℝ → ℂ} (hg : Measurable g) (hgi : Integrable g) (a : ℝ) :
    Integrable (interpolationLow g a) := by
  have hm : Measurable (interpolationLow g a) :=
    Measurable.ite (measurableSet_le hg.norm measurable_const) hg measurable_const
  apply hgi.mono hm.aestronglyMeasurable
  filter_upwards with x
  unfold interpolationLow
  split_ifs <;> simp [norm_nonneg]

theorem intervalL1Average_interpolationHigh_le
    {g : ℝ → ℂ} (hg : Measurable g) (hgi : Integrable g) {a p G : ℝ}
    (ha : 0 < a) (hp : 1 < p) (hgp : Integrable (fun x ↦ ‖g x‖ ^ p))
    (I : RealInterval) (hI : (∫ x in I.carrier, ‖g x‖ ^ p) ≤ G * I.length) :
    intervalL1Average (interpolationHigh g a) I ≤ a ^ (1 - p) * G := by
  unfold intervalL1Average
  have hpow := Real.rpow_nonneg ha.le (1 - p)
  calc
    _ ≤ I.length⁻¹ * ∫ x in I.carrier, a ^ (1 - p) * ‖g x‖ ^ p := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr I.length_pos.le)
      exact integral_mono (integrable_interpolationHigh_local hg hgi a).norm.integrableOn
        (hgp.const_mul _).integrableOn (norm_interpolationHigh_le_rpow g ha hp)
    _ = I.length⁻¹ * (a ^ (1 - p) * ∫ x in I.carrier, ‖g x‖ ^ p) := by
      rw [integral_const_mul]
    _ ≤ I.length⁻¹ * (a ^ (1 - p) * (G * I.length)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hI hpow)
        (inv_nonneg.mpr I.length_pos.le)
    _ = _ := by field_simp [I.length_pos.ne']

theorem eLpNorm_interpolationLow_le_rpow
    (g : ℝ → ℂ) {a p : ℝ} (ha : 0 < a) (hp : 0 < p) (hp2 : p ≤ 2)
    (hg : Measurable g) :
    eLpNorm (interpolationLow g a) 2 volume ≤
      (ENNReal.ofReal (a ^ (2 - p)) * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p)) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (a ^ (2 - p)) * ENNReal.ofReal (‖g x‖ ^ p) := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _) 2,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _)]
      exact ENNReal.ofReal_le_ofReal (norm_interpolationLow_sq_le_rpow g ha hp hp2 x)
    _ = _ := lintegral_const_mul _ ((hg.norm.pow_const p).ennreal_ofReal)

/-- Quantitative local interpolation for every positive splitting
threshold. The only test-function condition is the actual local `p`-mass
bound on the intervals, precisely the condition in the source argument. -/
theorem lintegral_nonstandard_pairing_le_threshold
    {S : Finset RealInterval} {f g : ℝ → ℂ} (hf : Integrable f)
    (hg : Measurable g) (hgi : Integrable g) {p a G : ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) (ha : 0 < a) (hG : 0 ≤ G)
    (hgp : Integrable (fun x ↦ ‖g x‖ ^ p))
    (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ) (hk₀ : 3 ≤ k₀)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale)
    (hgavg : ∀ I ∈ N, (∫ x in I.carrier, ‖g x‖ ^ p) ≤ G * I.length) :
    (∫⁻ x, ‖badLengthTailMaximal S f I₀ k₀ s scale N x‖ₑ * ‖g x‖ₑ) ≤
      ENNReal.ofReal ((4 * (s : ℝ) + 12) * Real.sqrt (nonstandardSignedEnergyBudget f I₀ s) +
        Real.sqrt (badRemovedEnergyBudget f I₀ s)) *
        (ENNReal.ofReal (a ^ (2 - p)) * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p)) ^ (1 / 2 : ℝ) +
      ENNReal.ofReal (8 * positiveDyadicAmplitudeBound * (a ^ (1 - p) * G) * ∫ x, ‖f x‖) := by
  let F := badLengthTailMaximal S f I₀ k₀ s scale N
  have hF := (aemeasurable_badLengthTailMaximal S hf I₀ k₀ s scale N).enorm
  have hlow := integrable_interpolationLow_local hg hgi a
  have hhigh := integrable_interpolationHigh_local hg hgi a
  have hnorm (x : ℝ) : ‖g x‖ₑ = ‖interpolationLow g a x‖ₑ + ‖interpolationHigh g a x‖ₑ := by
    by_cases hx : ‖g x‖ ≤ a
    · simp [interpolationLow, interpolationHigh, hx, not_lt.mpr hx]
    · simp [interpolationLow, interpolationHigh, hx, lt_of_not_ge hx]
  have hlowpair : (∫⁻ x, ‖F x‖ₑ * ‖interpolationLow g a x‖ₑ) ≤
      eLpNorm F 2 volume * eLpNorm (interpolationLow g a) 2 volume := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
      hF hlow.aestronglyMeasurable.enorm
    simpa only [Pi.mul_apply, eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞),
      ENNReal.toReal_ofNat] using h
  calc
    _ = (∫⁻ x, ‖F x‖ₑ * ‖interpolationLow g a x‖ₑ) +
        ∫⁻ x, ‖F x‖ₑ * ‖interpolationHigh g a x‖ₑ := by
      simp_rw [hnorm, mul_add]
      exact lintegral_add_left' (hF.mul hlow.aestronglyMeasurable.enorm) _
    _ ≤ (eLpNorm F 2 volume * eLpNorm (interpolationLow g a) 2 volume) +
        ENNReal.ofReal (8 * positiveDyadicAmplitudeBound * (a ^ (1 - p) * G) * ∫ x, ‖f x‖) := by
      apply add_le_add hlowpair
      exact lintegral_nonstandard_pairing_le_of_averages_le hf hhigh I₀ k₀ s scale hlam N hN
        (mul_nonneg (Real.rpow_nonneg ha.le _) hG)
        (fun I hI ↦ intervalL1Average_interpolationHigh_le hg hgi ha hp hgp I (hgavg I hI))
    _ ≤ _ := add_le_add_left (mul_le_mul'
      (eLpNorm_nonstandard_badLengthTailMaximal_le hf I₀ k₀ s hk₀ scale hlam hparent hsub N hN)
      (eLpNorm_interpolationLow_le_rpow g ha (by linarith) hp2 hg)) _


end KrauseLaceyBadScale
end QuadraticCarleson
