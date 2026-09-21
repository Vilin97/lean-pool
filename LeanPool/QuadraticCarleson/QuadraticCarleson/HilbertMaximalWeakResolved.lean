/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.HilbertRepresentativeBridge
import LeanPool.QuadraticCarleson.QuadraticCarleson.PositivePrincipalValueEndpoints

/-!
# Weak bounds and principal-value endpoint conclusions

The stopping good-part L² estimate and the maximal-function distribution bound give an explicit
weak (1,1) constant for the ordinary Hilbert maximal operator. The resulting uniform bound
closes the simultaneous principal-value existence and endpoint assertions.
-/

open Filter Function MeasureTheory Set FourierTransform
open scoped ENNReal Topology

namespace QuadraticCarleson.HilbertMaximalWeakResolved

open HilbertRepresentativeBridge HilbertMaximalWeakOneOne HilbertL2Fourier
open CalderonZygmundDyadicStopping HilbertPrincipalValueClosure


theorem lintegral_sq_enorm_stoppingGoodPart_le {f : ℝ → ℂ} (hf : Integrable f) :
    (∫⁻ x, ‖stoppingGoodPart f x‖ₑ ^ 2) ≤ 5 * ∫⁻ x, ‖f x‖ₑ := by
  have h := ENNReal.ofReal_le_ofReal (integral_sq_norm_stoppingGoodPart_le_five_l1 hf)
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5),
    ofReal_integral_eq_lintegral_ofReal (integrable_sq_norm_stoppingGoodPart hf)
      (ae_of_all _ fun x ↦ sq_nonneg _),
    ofReal_integral_eq_lintegral_ofReal hf.norm (ae_of_all _ fun x ↦ norm_nonneg _)] at h
  simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using h

theorem lintegral_sq_enorm_goodHilbert_le {f : ℝ → ℂ} (hf : Integrable f) :
    (∫⁻ x, ‖measurableStoppingGoodHilbertRepresentative f hf x‖ₑ ^ 2) ≤
      ENNReal.ofReal Real.pi ^ 2 * (5 * ∫⁻ x, ‖f x‖ₑ) := by
  have hae := ae_eq_measurableStoppingGoodHilbertRepresentative hf
  calc
    _ = ∫⁻ x, ‖stoppingGoodHilbertL2Representative f hf x‖ₑ ^ 2 := by
      apply lintegral_congr_ae
      filter_upwards [hae] with x hx
      rw [hx]
    _ = ‖ordinaryHilbertTransformL2 (stoppingGoodPartL2 f hf)‖ₑ ^ 2 := by
      rw [← eLpNorm_two_sq_lintegral _
        (aestronglyMeasurable_stoppingGoodHilbertL2Representative hf),
        eLpNorm_stoppingGoodHilbertL2Representative_eq_enorm hf]
    _ ≤ (ENNReal.ofReal Real.pi * ‖stoppingGoodPartL2 f hf‖ₑ) ^ 2 :=
      pow_le_pow_left' (enorm_stoppingGoodHilbertL2_le hf) 2
    _ = ENNReal.ofReal Real.pi ^ 2 * (∫⁻ x, ‖stoppingGoodPart f x‖ₑ ^ 2) := by
      rw [mul_pow, enorm_stoppingGoodPartL2_sq_eq_lintegral hf]
    _ ≤ _ := mul_le_mul' le_rfl (lintegral_sq_enorm_stoppingGoodPart_le hf)

theorem volume_maximal_gt_one_le_sq {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    volume {x | 1 < centeredHardyLittlewoodMaximal g x} ≤ 32 * ∫⁻ x, g x ^ 2 := by
  have hsub : {x | 1 < centeredHardyLittlewoodMaximal g x} ⊆
      {x | 1 ≤ (centeredHardyLittlewoodMaximal g x) ^ 2} := by
    intro x hx
    change 1 < centeredHardyLittlewoodMaximal g x at hx
    exact one_le_pow₀ hx.le
  calc
    _ ≤ volume {x | 1 ≤ (centeredHardyLittlewoodMaximal g x) ^ 2} := measure_mono hsub
    _ ≤ ∫⁻ x, (centeredHardyLittlewoodMaximal g x) ^ 2 := by
      simpa only [one_mul] using mul_meas_ge_le_lintegral₀
        ((measurable_centeredHardyLittlewoodMaximal hg).pow_const 2).aemeasurable 1
    _ ≤ _ := centeredHardyLittlewoodMaximal_sq_lintegral_le hg

/-- The output threshold used in the height-one weak-type estimate. -/
noncomputable def normalizedThreshold : ℝ := 32 + 20 * Real.pi⁻¹ + 44 / 3
/-- The measure-bound constant for the normalized weak-type estimate. -/
noncomputable def normalizedWeakConstant : ℝ :=
  160 * (Real.pi ^ 2 + 1) + 96 + 2 * (32 / 3 + 128)
/-- The weak-`(1,1)` constant obtained by rescaling the normalized estimate. -/
noncomputable def hilbertWeakConstant : ℝ := normalizedThreshold * normalizedWeakConstant

theorem normalizedThreshold_pos : 0 < normalizedThreshold := by
  unfold normalizedThreshold
  positivity

theorem normalizedWeakConstant_nonneg : 0 ≤ normalizedWeakConstant := by
  unfold normalizedWeakConstant
  positivity

theorem hilbertWeakConstant_nonneg : 0 ≤ hilbertWeakConstant :=
  mul_nonneg normalizedThreshold_pos.le normalizedWeakConstant_nonneg

/-- The Calderón–Zygmund decomposition at height one, now using the proved
Cotlar inequality for the good part and the proved bad-part estimate. -/
theorem normalized_weak_bound {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f) :
    volume {x | ENNReal.ofReal normalizedThreshold < quadraticHilbertMaximalTruncation 0 f x} ≤
      ENNReal.ofReal normalizedWeakConstant * ∫⁻ x, ‖f x‖ₑ := by
  let A := {x | 1 < centeredHardyLittlewoodMaximal
    (fun y ↦ ‖measurableStoppingGoodHilbertRepresentative f hfi y‖ₑ) x}
  let B := {x | 1 < centeredHardyLittlewoodMaximal (fun y ↦ ‖stoppingGoodPart f y‖ₑ) x}
  let D := {x | 32 < quadraticHilbertMaximalTruncation 0
    (fun y ↦ f y - stoppingGoodPart f y) x}
  let I := ∫⁻ x, ‖f x‖ₑ
  have hsub : {x | ENNReal.ofReal normalizedThreshold <
      quadraticHilbertMaximalTruncation 0 f x} ⊆ (A ∪ B) ∪ D := by
    intro x hx
    change ENNReal.ofReal normalizedThreshold < quadraticHilbertMaximalTruncation 0 f x at hx
    by_contra hn
    have hA : centeredHardyLittlewoodMaximal
        (fun y ↦ ‖measurableStoppingGoodHilbertRepresentative f hfi y‖ₑ) x ≤ 1 := by
      by_contra h
      exact hn (Or.inl (Or.inl (lt_of_not_ge h)))
    have hB : centeredHardyLittlewoodMaximal (fun y ↦ ‖stoppingGoodPart f y‖ₑ) x ≤ 1 := by
      by_contra h
      exact hn (Or.inl (Or.inr (lt_of_not_ge h)))
    have hD : quadraticHilbertMaximalTruncation 0
        (fun y ↦ f y - stoppingGoodPart f y) x ≤ 32 := by
      by_contra h
      exact hn (Or.inr (lt_of_not_ge h))
    apply (not_lt_of_ge ?_) hx
    calc
      quadraticHilbertMaximalTruncation 0 f x ≤
          quadraticHilbertMaximalTruncation 0 (stoppingGoodPart f) x +
            quadraticHilbertMaximalTruncation 0 (fun y ↦ f y - stoppingGoodPart f y) x :=
        quadraticHilbertMaximalTruncation_zero_le_good_add_bad hf hfi x
      _ ≤ (ENNReal.ofReal Real.pi⁻¹ * (20 * 1) + ENNReal.ofReal (44 / 3) * 1) + 32 := by
        apply add_le_add _ hD
        exact (quadraticHilbertMaximalTruncation_stoppingGoodPart_le_cotlar hf hfi x).trans
          (add_le_add (mul_le_mul' le_rfl (mul_le_mul' le_rfl hA)) (mul_le_mul' le_rfl hB))
      _ = ENNReal.ofReal normalizedThreshold := by
        simp (disch := positivity) only [normalizedThreshold, ENNReal.ofReal_add,
          ENNReal.ofReal_mul, ENNReal.ofReal_ofNat, mul_one]
        ring
  have hA : volume A ≤ 32 * (ENNReal.ofReal Real.pi ^ 2 * (5 * I)) :=
    (volume_maximal_gt_one_le_sq
      (measurable_measurableStoppingGoodHilbertRepresentative hfi).enorm).trans
      (mul_le_mul' le_rfl (lintegral_sq_enorm_goodHilbert_le hfi))
  have hB : volume B ≤ 32 * (5 * I) :=
    (volume_maximal_gt_one_le_sq (measurable_stoppingGoodPart_of_measurable hf).enorm).trans
      (mul_le_mul' le_rfl (lintegral_sq_enorm_stoppingGoodPart_le hfi))
  have hD : volume D ≤ 96 * I + 2 * (ENNReal.ofReal (32 / 3) * I + 128 * I) := by
    calc
      _ ≤ 32 * volume D := le_mul_of_one_le_left' (by norm_num)
      _ ≤ _ := quadraticHilbertMaximalTruncation_badPart_weak_bound_one hf hfi
  calc
    _ ≤ volume ((A ∪ B) ∪ D) := measure_mono hsub
    _ ≤ (volume A + volume B) + volume D :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ (32 * (ENNReal.ofReal Real.pi ^ 2 * (5 * I)) + 32 * (5 * I)) +
        (96 * I + 2 * (ENNReal.ofReal (32 / 3) * I + 128 * I)) :=
      add_le_add (add_le_add hA hB) hD
    _ = ENNReal.ofReal normalizedWeakConstant * I := by
      simp (disch := positivity) only [normalizedWeakConstant, ENNReal.ofReal_add,
        ENNReal.ofReal_mul, ENNReal.ofReal_pow, ENNReal.ofReal_ofNat, ENNReal.ofReal_one]
      ring


/-- Unconditional weak `(1,1)` for the supremum over every positive sharp
ordinary Hilbert truncation, on every measurable integrable input. -/
theorem ordinaryHilbertMaximal_weak_bound {f : ℝ → ℂ}
    (hf : Measurable f) (hfi : Integrable f) {a : ℝ} (ha : 0 < a) :
    ENNReal.ofReal a * volume {x | ENNReal.ofReal a < quadraticHilbertMaximalTruncation 0 f x} ≤
      ENNReal.ofReal hilbertWeakConstant * ∫⁻ x, ‖f x‖ₑ := by
  let c : ℝ := normalizedThreshold / a
  have hc : 0 < c := div_pos normalizedThreshold_pos ha
  have hca : c * a = normalizedThreshold := div_mul_cancel₀ _ ha.ne'
  have hcnorm : ‖(c : ℂ)‖ₑ = ENNReal.ofReal c := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  have hn := normalized_weak_bound (f := fun y ↦ (c : ℂ) * f y)
    (measurable_const.mul hf) (hfi.const_mul (c : ℂ))
  have hset : {x | ENNReal.ofReal normalizedThreshold <
      quadraticHilbertMaximalTruncation 0 (fun y ↦ (c : ℂ) * f y) x} =
      {x | ENNReal.ofReal a < quadraticHilbertMaximalTruncation 0 f x} := by
    ext x
    simp only [mem_ofPred_eq, quadraticHilbertMaximalTruncation_zero_const_mul, hcnorm]
    rw [← hca, ENNReal.ofReal_mul hc.le]
    exact ENNReal.mul_lt_mul_iff_right (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top
  rw [hset] at hn
  have hmass : (∫⁻ y, ‖(c : ℂ) * f y‖ₑ) = ENNReal.ofReal c * ∫⁻ y, ‖f y‖ₑ := by
    simp only [enorm_mul, hcnorm]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [hmass] at hn
  calc
    _ ≤ ENNReal.ofReal a * (ENNReal.ofReal normalizedWeakConstant *
        (ENNReal.ofReal c * ∫⁻ y, ‖f y‖ₑ)) := mul_le_mul' le_rfl hn
    _ = ENNReal.ofReal hilbertWeakConstant * ∫⁻ y, ‖f y‖ₑ := by
      have hac : a * c = normalizedThreshold := by rw [mul_comm, hca]
      rw [show ENNReal.ofReal a * (ENNReal.ofReal normalizedWeakConstant *
        (ENNReal.ofReal c * ∫⁻ y, ‖f y‖ₑ)) =
        ((ENNReal.ofReal a * ENNReal.ofReal c) * ENNReal.ofReal normalizedWeakConstant) *
          ∫⁻ y, ‖f y‖ₑ by ring]
      rw [← ENNReal.ofReal_mul ha.le, hac,
        ← ENNReal.ofReal_mul normalizedThreshold_pos.le]
      rfl

theorem hasUniformZeroHilbertMaximalWeakBound :
    PositiveFullOperatorEndpoint.HasUniformZeroHilbertMaximalWeakBound hilbertWeakConstant := by
  refine ⟨hilbertWeakConstant_nonneg, fun f hf hfi ↦ ?_⟩
  refine ⟨mul_nonneg hilbertWeakConstant_nonneg ENNReal.toReal_nonneg, fun a ha ↦ ?_⟩
  rw [ENNReal.ofReal_mul hilbertWeakConstant_nonneg,
    ENNReal.ofReal_toReal hfi.hasFiniteIntegral.ne]
  exact ordinaryHilbertMaximal_weak_bound hf hfi ha

/-- Discharges the exact classical interface used by the principal-value
closure and the positive quadratic endpoint theorems. -/
theorem hasUniformHilbertMaximalWeakBound :
    HasUniformHilbertMaximalWeakBound (ENNReal.ofReal hilbertWeakConstant) :=
  PositivePrincipalValueEndpoints.uniformHilbertMaximalWeakBound_of_all_integrable
    hasUniformZeroHilbertMaximalWeakBound

theorem ae_forall_real_exists_quadraticPrincipalValue (f : L0Infinity) :
    ∀ᵐ x, ∀ lam : ℝ, ∃ z : ℂ, HasQuadraticPrincipalValue lam f x z :=
  HilbertPrincipalValueClosure.ae_forall_real_exists_quadraticPrincipalValue
    hasUniformHilbertMaximalWeakBound f


open PositivePrincipalValueEndpoints

/-- The full-modulation principal-value endpoint, with its last ordinary
Hilbert hypothesis discharged by the unconditional weak theorem. -/
theorem full_principalValue_endpoint :
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ f : L0Infinity,
      (∀ᵐ x, ∀ lam : ℝ,
        HasQuadraticPrincipalValue lam f x (principalValueRepresentative lam f x)) ∧
      ∀ α : ℝ, 0 < α →
        volume {x | ENNReal.ofReal α < fullPrincipalValueMaximal f x} ≤
          K * ∫⁻ x, ENNReal.ofReal ((‖f x‖ / α) * paperLog 1 (‖f x‖ / α)) :=
  PositivePrincipalValueEndpoints.full_principalValue_endpoint hasUniformHilbertMaximalWeakBound

/-- The lacunary principal-value endpoint now needs only the independent
individual frozen-block estimate; no ordinary Hilbert hypothesis remains. -/
theorem lacunary_principalValue_endpoint
    {CB : ℝ} (hB : LacunaryOscillatoryScaling.HasUniformL0LogSquaredFrozenBlockWeakBounds CB) :
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ f : L0Infinity,
      (∀ᵐ x, ∀ m : ℤ, HasQuadraticPrincipalValue (dyadicModulation m) f x
        (principalValueRepresentative (dyadicModulation m) f x)) ∧
      ∀ α : ℝ, 0 < α →
        volume {x | ENNReal.ofReal α < lacunaryPrincipalValueMaximal f x} ≤
          K * ∫⁻ x, ENNReal.ofReal
            ((‖f x‖ / α) * paperLog 2 (‖f x‖ / α) ^ 2 * paperLog 4 (‖f x‖ / α)) :=
  PositivePrincipalValueEndpoints.lacunary_principalValue_endpoint
    hasUniformHilbertMaximalWeakBound hB



end QuadraticCarleson.HilbertMaximalWeakResolved
