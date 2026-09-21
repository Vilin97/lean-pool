/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyScalarNearPhysicalL2
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNonstandardLocalInterpolation

/-!
# Local interpolation for the scalar near-energy family

The positive local pairing majorant uses only the actual interval scale
and bad-input mass packing. We prove it below without either near-energy
or pointwise nonstandard classification. Its scalar-near specialization
combines with the already proved physical-suffix maximal L² estimate.

The interpolation helpers for the high/low test-function split are reused
unchanged. Every threshold, local p-mass hypothesis, and decay budget stays
explicit; no desired local oscillatory or sparse estimate is assumed.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyScalarNear

open KrauseLaceyBadScale KrauseLaceyGenerationLayers KrauseLaceyStoppingExtraction

attribute [local instance] Classical.propDecidable

/-- This is the existing actual source-oriented physical suffix maximum.
Only the name indicates its intended use with the scalar energy family. -/
noncomputable abbrev energyNonstandardSourceTailMaximal :=
  nonstandardSourceTailMaximal

/-- Nonnegativity of the finite-family physical maximal operator is
independent of scale identities, stopping geometry, and classification. -/
theorem badLengthTailMaximal_nonneg_unrestricted
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval) (x : ℝ) :
    0 ≤ badLengthTailMaximal S f I₀ k₀ s scale N x := by
  have hb : BddAbove (Set.range (fun ell : ℤ ↦
      ‖badLengthTailAction S f I₀ k₀ s scale N ell x‖)) := by
    refine ⟨∑ I ∈ N, ‖krauseLaceyLocalizedPiece 1 (scale I) I
      (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x‖, ?_⟩
    rintro _ ⟨ell, rfl⟩
    unfold badLengthTailAction
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro I hI
    split_ifs
    · exact le_rfl
    · rw [norm_zero]
      exact norm_nonneg _
  exact (norm_nonneg _).trans (le_ciSup hb (0 : ℤ))

theorem norm_localizedBadPiece_le_mass_of_scale
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    {I : RealInterval} (hscale : I.length = (2 : ℝ) ^ (scale I + 2)) (x : ℝ) :
    ‖krauseLaceyLocalizedPiece 1 (scale I) I
      (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x‖ ≤
      (8 * positiveDyadicAmplitudeBound / I.length) * intervalBadMass S f I₀ k₀ s scale I := by
  have hb := integrable_badScaleInput S hf I₀ k₀ (scale I + 2 - s)
  have h := (krauseLaceyPositiveKernel (scale I)).norm_applyIntegral_le
    (hb.indicator I.measurableSet_centralThird) x
  simp only [FiniteRangeKernel.applyIntegral, krauseLaceyPositiveKernel_apply,
    ← krauseLaceyLocalizedPiece_eq_positiveDyadicConvolution] at h
  have hid : (∫ t, ‖I.centralThird.indicator
      (badScaleInput S f I₀ k₀ (scale I + 2 - s)) t‖) = intervalBadMass S f I₀ k₀ s scale I := by
    simp only [norm_indicator_eq_indicator_norm, intervalBadMass]
    exact integral_indicator I.measurableSet_centralThird
  rw [hid] at h
  apply h.trans_eq
  change (positiveDyadicAmplitudeBound / (2 : ℝ) ^ (scale I - 1)) * _ = _
  rw [hscale, krauseLacey_scale_eq_eight_mul_radius]
  ring


theorem badLengthTailMaximal_le_massMajorant_of_scale
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (N : Finset RealInterval) (hscale : ∀ I ∈ N, I.length = (2 : ℝ) ^ (scale I + 2)) (x : ℝ) :
    badLengthTailMaximal S f I₀ k₀ s scale N x ≤
      ∑ I ∈ N, I.carrier.indicator (fun _ ↦
        (8 * positiveDyadicAmplitudeBound / I.length) * intervalBadMass S f I₀ k₀ s scale I) x := by
  apply ciSup_le
  intro ell
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  by_cases hx : x ∈ I.carrier
  · rw [Set.indicator_of_mem hx]
    split_ifs
    · exact norm_localizedBadPiece_le_mass_of_scale hf I₀ k₀ s scale (hscale I hI) x
    · rw [norm_zero]
      exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num)
        positiveDyadicAmplitudeBound_nonneg) I.length_pos.le)
        (intervalBadMass_nonneg S f I₀ k₀ s scale I)
  · rw [Set.indicator_of_notMem hx, krauseLaceyLocalizedPiece_eq_zero_of_notMem 1 (scale I) I _
      (hscale I hI) hx]
    simp


theorem lintegral_badLengthTail_pairing_le_sum_local_averages_of_scale
    {S : Finset RealInterval} {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (N : Finset RealInterval) (hscale : ∀ I ∈ N, I.length = (2 : ℝ) ^ (scale I + 2)) :
    (∫⁻ x, ‖badLengthTailMaximal S f I₀ k₀ s scale N x‖ₑ * ‖g x‖ₑ) ≤
      ENNReal.ofReal (∑ I ∈ N, 8 * positiveDyadicAmplitudeBound *
        intervalBadMass S f I₀ k₀ s scale I * intervalL1Average g I) := by
  let C := fun I : RealInterval ↦
    (8 * positiveDyadicAmplitudeBound / I.length) * intervalBadMass S f I₀ k₀ s scale I
  have hC (I : RealInterval) : 0 ≤ C I := mul_nonneg
    (div_nonneg (mul_nonneg (by norm_num) positiveDyadicAmplitudeBound_nonneg) I.length_pos.le)
    (intervalBadMass_nonneg S f I₀ k₀ s scale I)
  have hind (I : RealInterval) (x : ℝ) :
      ENNReal.ofReal (I.carrier.indicator (fun _ ↦ C I) x) * ‖g x‖ₑ =
        ENNReal.ofReal (C I) * I.carrier.indicator (fun x ↦ ‖g x‖ₑ) x := by
    by_cases hx : x ∈ I.carrier <;> simp [hx]
  calc
    _ ≤ ∫⁻ x, ∑ I ∈ N,
        ENNReal.ofReal (C I) * I.carrier.indicator (fun x ↦ ‖g x‖ₑ) x := by
      apply lintegral_mono
      intro x
      dsimp only
      simp_rw [← hind]
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg
        (fun I _ ↦ Set.indicator_nonneg (fun _ _ ↦ hC I) x),
        Real.enorm_of_nonneg (badLengthTailMaximal_nonneg_unrestricted S f I₀ k₀ s scale N x)]
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
        (badLengthTailMaximal_le_massMajorant_of_scale hf I₀ k₀ s scale N hscale x)) _
    _ = ∑ I ∈ N, ENNReal.ofReal (C I) * ∫⁻ x in I.carrier, ‖g x‖ₑ := by
      have hm (I : RealInterval) : AEMeasurable (fun x ↦
          ENNReal.ofReal (C I) * I.carrier.indicator (fun x ↦ ‖g x‖ₑ) x) volume :=
        aemeasurable_const.mul (hg.aestronglyMeasurable.enorm.indicator I.measurableSet_carrier)
      rw [lintegral_finsetSum' _ (fun I _ ↦ hm I)]
      apply Finset.sum_congr rfl
      intro I hI
      rw [lintegral_const_mul'' _
        (hg.aestronglyMeasurable.enorm.indicator I.measurableSet_carrier),
        lintegral_indicator I.measurableSet_carrier]
    _ = ∑ I ∈ N, ENNReal.ofReal (8 * positiveDyadicAmplitudeBound *
        intervalBadMass S f I₀ k₀ s scale I * intervalL1Average g I) := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [← ofReal_integral_norm_eq_lintegral_enorm hg.integrableOn,
        ← ENNReal.ofReal_mul (hC I), ← intervalL1Average_mul_length g I]
      congr 1
      dsimp [C]
      field_simp [I.length_pos.ne']
    _ = _ := (ENNReal.ofReal_sum_of_nonneg (fun I _ ↦ mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) positiveDyadicAmplitudeBound_nonneg)
        (intervalBadMass_nonneg S f I₀ k₀ s scale I)) (intervalL1Average_nonneg g I))).symm

theorem lintegral_badLengthTail_pairing_le_of_averages_le
    {S : Finset RealInterval} {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (N : Finset RealInterval) (hN : N ⊆ S)
    (hscale : ∀ I ∈ N, I.length = (2 : ℝ) ^ (scale I + 2))
    {G : ℝ} (hG : 0 ≤ G) (hgavg : ∀ I ∈ N, intervalL1Average g I ≤ G) :
    (∫⁻ x, ‖badLengthTailMaximal S f I₀ k₀ s scale N x‖ₑ * ‖g x‖ₑ) ≤
      ENNReal.ofReal (8 * positiveDyadicAmplitudeBound * G * ∫ x, ‖f x‖) := by
  apply (lintegral_badLengthTail_pairing_le_sum_local_averages_of_scale
    hf hg I₀ k₀ s scale N hscale).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∑ I ∈ N, 8 * positiveDyadicAmplitudeBound *
        intervalBadMass S f I₀ k₀ s scale I * G := by
      apply Finset.sum_le_sum
      intro I hI
      exact mul_le_mul_of_nonneg_left (hgavg I hI) (mul_nonneg
        (mul_nonneg (by norm_num) positiveDyadicAmplitudeBound_nonneg)
        (intervalBadMass_nonneg S f I₀ k₀ s scale I))
    _ = 8 * positiveDyadicAmplitudeBound * G * ∑ I ∈ N, intervalBadMass S f I₀ k₀ s scale I := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I hI
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_intervalBadInput_mass_le hf I₀ k₀ s scale hlam N
        hN
        hscale)
      (mul_nonneg (mul_nonneg (by norm_num) positiveDyadicAmplitudeBound_nonneg) hG)

/-- Exact equality with the all-integer maximal function: the scalar
family already lies above the source's lower physical scale `k₀ + s`. -/
theorem energyNonstandardSourceTailMaximal_eq_badLengthTailMaximal
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (N : Finset RealInterval) (hN : N ⊆ energyNonstandardIntervals S f I₀ k₀ s scale) :
    energyNonstandardSourceTailMaximal S f I₀ k₀ s scale N =
      badLengthTailMaximal S f I₀ k₀ s scale N := by
  have hn : N ⊆ intervals S f I₀ k₀ s scale := by
    rw [intervals_eq_energyNonstandardIntervals]
    exact hN
  exact funext (nonstandardSourceTailMaximal_eq_badLengthTailMaximal
    f I₀ k₀ s scale hlam N hn)

/-- The source physical-suffix pairing retains the exact local averages
and restricted bad-input masses. -/
theorem lintegral_energyNonstandard_pairing_le_sum_local_averages
    {S : Finset RealInterval} {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (N : Finset RealInterval) (hN : N ⊆ energyNonstandardIntervals S f I₀ k₀ s scale) :
    (∫⁻ x, ‖energyNonstandardSourceTailMaximal S f I₀ k₀ s scale N x‖ₑ * ‖g x‖ₑ) ≤
      ENNReal.ofReal (∑ I ∈ N, 8 * positiveDyadicAmplitudeBound *
        intervalBadMass S f I₀ k₀ s scale I * intervalL1Average g I) := by
  rw [energyNonstandardSourceTailMaximal_eq_badLengthTailMaximal
    f I₀ k₀ s scale hlam N hN]
  exact lintegral_badLengthTail_pairing_le_sum_local_averages_of_scale hf hg I₀ k₀ s scale N
    (fun I hI ↦ (Finset.mem_filter.mp (Finset.mem_filter.mp (hN hI)).1).2.1)

/-- The scalar near family inherits the predicate-independent `L¹`
pairing estimate through actual mass packing, uniformly in the gap. -/
theorem lintegral_energyNonstandard_pairing_le_of_averages_le
    {S : Finset RealInterval} {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (N : Finset RealInterval) (hN : N ⊆ energyNonstandardIntervals S f I₀ k₀ s scale)
    {G : ℝ} (hG : 0 ≤ G) (hgavg : ∀ I ∈ N, intervalL1Average g I ≤ G) :
    (∫⁻ x, ‖energyNonstandardSourceTailMaximal S f I₀ k₀ s scale N x‖ₑ * ‖g x‖ₑ) ≤
      ENNReal.ofReal (8 * positiveDyadicAmplitudeBound * G * ∫ x, ‖f x‖) := by
  rw [energyNonstandardSourceTailMaximal_eq_badLengthTailMaximal
    f I₀ k₀ s scale hlam N hN]
  have hNS : N ⊆ S := hN.trans ((Finset.filter_subset _ _).trans
    (energyEligibleIntervals_subset S f I₀ k₀ s scale))
  exact lintegral_badLengthTail_pairing_le_of_averages_le hf hg I₀ k₀ s scale hlam N hNS
    (fun I hI ↦ (Finset.mem_filter.mp (Finset.mem_filter.mp (hN hI)).1).2.1) hG hgavg

/-- On the actual two-function good family, the required `L¹` averages
follow from the stopping construction itself. -/
theorem lintegral_energyNonstandard_good_pairing_le
    {S : Finset RealInterval} {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier) :
    (∫⁻ x, ‖energyNonstandardSourceTailMaximal S f I₀ k₀ s scale
      (energyNonstandardIntervals S f I₀ k₀ s scale ∩ goodCollection S f g I₀) x‖ₑ * ‖g x‖ₑ) ≤
      ENNReal.ofReal (80 * positiveDyadicAmplitudeBound * intervalL1Average g I₀ *
        ∫ x, ‖f x‖) := by
  have h := lintegral_energyNonstandard_pairing_le_of_averages_le hf hg I₀ k₀ s scale hlam
    (energyNonstandardIntervals S f I₀ k₀ s scale ∩ goodCollection S f g I₀)
    Finset.inter_subset_left
    (mul_nonneg (by norm_num) (intervalL1Average_nonneg g I₀))
    (fun I hI ↦ (goodCollection_averages_le hsub (Finset.mem_inter.mp hI).2).2)
  convert h using 1
  congr 1
  ring

/-- Quantitative threshold interpolation for the scalar near family,
using the genuine source-oriented physical suffix maximum. The local
p-mass condition on the test function is explicit; it is not inferred
from merely an L¹ stopping condition. -/
theorem lintegral_energyNonstandard_pairing_le_threshold
    {S : Finset RealInterval} {f g : ℝ → ℂ} (hf : Integrable f)
    (hg : Measurable g) (hgi : Integrable g) {p a G : ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) (ha : 0 < a) (hG : 0 ≤ G)
    (hgp : Integrable (fun x ↦ ‖g x‖ ^ p))
    (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ) (hk₀ : 3 ≤ k₀)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ energyNonstandardIntervals S f I₀ k₀ s scale)
    (hgavg : ∀ I ∈ N, (∫ x in I.carrier, ‖g x‖ ^ p) ≤ G * I.length) :
    (∫⁻ x, ‖energyNonstandardSourceTailMaximal S f I₀ k₀ s scale N x‖ₑ * ‖g x‖ₑ) ≤
      ENNReal.ofReal ((4 * (s : ℝ) + 12) * Real.sqrt (nonstandardSignedEnergyBudget f I₀ s) +
        Real.sqrt (badRemovedEnergyBudget f I₀ s)) *
        (ENNReal.ofReal (a ^ (2 - p)) * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p)) ^ (1 / 2 : ℝ) +
      ENNReal.ofReal (8 * positiveDyadicAmplitudeBound * (a ^ (1 - p) * G) * ∫ x, ‖f x‖) := by
  let F := energyNonstandardSourceTailMaximal S f I₀ k₀ s scale N
  have hFm : AEMeasurable F volume := by
    dsimp only [F]
    rw [energyNonstandardSourceTailMaximal_eq_badLengthTailMaximal
      f I₀ k₀ s scale hlam N hN]
    exact aemeasurable_badLengthTailMaximal S hf I₀ k₀ s scale N
  have hF := hFm.enorm
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
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        hFm.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hlow.aestronglyMeasurable]
    simpa only [Pi.mul_apply, ENNReal.toReal_ofNat] using h
  calc
    _ = (∫⁻ x, ‖F x‖ₑ * ‖interpolationLow g a x‖ₑ) +
        ∫⁻ x, ‖F x‖ₑ * ‖interpolationHigh g a x‖ₑ := by
      simp_rw [hnorm, mul_add]
      exact lintegral_add_left' (hF.mul hlow.aestronglyMeasurable.enorm) _
    _ ≤ (eLpNorm F 2 volume * eLpNorm (interpolationLow g a) 2 volume) +
        ENNReal.ofReal (8 * positiveDyadicAmplitudeBound * (a ^ (1 - p) * G) * ∫ x, ‖f x‖) := by
      apply add_le_add hlowpair
      exact lintegral_energyNonstandard_pairing_le_of_averages_le hf hhigh I₀ k₀ s scale hlam N hN
        (mul_nonneg (Real.rpow_nonneg ha.le _) hG)
        (fun I hI ↦ intervalL1Average_interpolationHigh_le hg hgi ha hp hgp I (hgavg I hI))
    _ ≤ _ := add_le_add_left (mul_le_mul'
      (eLpNorm_energyNonstandardSourceTailMaximal_le hf I₀ k₀ s hk₀ scale hlam hparent hsub N hN)
      (eLpNorm_interpolationLow_le_rpow g ha (by linarith) hp2 hg)) _



end KrauseLaceyScalarNear
end QuadraticCarleson
