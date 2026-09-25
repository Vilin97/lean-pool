/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticL2Extension

/-!
# Transferring the adjoint bound to the integral operator

The elementary `TT*` duality argument is carried out on the actual integral
actions, then extended to all measurable `L²` inputs by spatial truncation.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal ComplexConjugate

namespace QuadraticCarleson

/-- Cauchy--Schwarz for the actual complex integral pairing, in squared
extended-moment form. -/
theorem enorm_integral_pairing_sq_le {f g : ℝ → ℂ}
    (hf : Measurable f) (hg : Measurable g) :
    ‖∫ x, f x * conj (g x)‖ₑ ^ 2 ≤
      (∫⁻ x, ‖f x‖ₑ ^ 2) * ∫⁻ x, ‖g x‖ₑ ^ 2 := by
  have hnorm : ‖∫ x, f x * conj (g x)‖ₑ ≤ ∫⁻ x, ‖f x‖ₑ * ‖g x‖ₑ := by
    apply (enorm_integral_le_lintegral_enorm _).trans_eq
    apply lintegral_congr
    intro x
    rw [enorm_mul]
    simp only [← ofReal_norm, RCLike.norm_conj]
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure ℝ)
    (p := 2) (q := 2) (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    hf.enorm.aemeasurable hg.enorm.aemeasurable
  simp only [ENNReal.rpow_two, Pi.mul_apply] at hh
  have hsqrt (v : ℝ≥0∞) : (v ^ (1 / (2 : ℝ))) ^ 2 = v := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc
    _ ≤ ((∫⁻ x, ‖f x‖ₑ ^ 2) ^ (1 / (2 : ℝ)) *
        (∫⁻ x, ‖g x‖ₑ ^ 2) ^ (1 / (2 : ℝ))) ^ 2 := by
      gcongr
      exact hnorm.trans hh
    _ = _ := by rw [mul_pow, hsqrt, hsqrt]

namespace FiniteRangeKernel

theorem integrable_energy (K : FiniteRangeKernel)
    {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (fun t ↦ ‖K.applyIntegral f t‖ ^ 2) := by
  have hi := K.integrable_applyIntegral hf
  apply (hi.norm.const_mul (K.bound * ∫ y, ‖f y‖)).mono'
    (hi.aestronglyMeasurable.norm.pow 2)
  filter_upwards [] with t
  dsimp only [Pi.pow_apply]
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hh := mul_le_mul_of_nonneg_right (K.norm_applyIntegral_le hf t)
    (norm_nonneg (K.applyIntegral f t))
  nlinarith

/-- The output second moment is exactly its self-pairing. -/
theorem sq_lintegral_eq_enorm_pairing (K : FiniteRangeKernel)
    {f : ℝ → ℂ} (hf : Integrable f) :
    (∫⁻ t, ‖K.applyIntegral f t‖ₑ ^ 2) =
      ‖∫ t, K.applyIntegral f t * conj (K.applyIntegral f t)‖ₑ := by
  simp_rw [Complex.mul_conj']
  simp_rw [← Complex.ofReal_pow]
  rw [integral_complex_ofReal]
  rw [← ofReal_norm, Complex.norm_real,
    Real.norm_of_nonneg (integral_nonneg (fun _ ↦ sq_nonneg _)),
    ofReal_integral_eq_lintegral_ofReal (K.integrable_energy hf)
      (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _))]
  apply lintegral_congr
  intro t
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- A bound for the integral adjoint implies the same second-moment bound for
the forward integral operator on measurable integrable tests. -/
theorem sq_lintegral_bound_of_adjoint (K : FiniteRangeKernel) (A : ℝ≥0∞)
    (hbound : ∀ g : ℝ → ℂ, Measurable g → Integrable g →
      (∫⁻ t, ‖K.adjoint.applyIntegral g t‖ₑ ^ 2) ≤ A * ∫⁻ t, ‖g t‖ₑ ^ 2)
    {f : ℝ → ℂ} (hfm : Measurable f) (hf : Integrable f) :
    (∫⁻ t, ‖K.applyIntegral f t‖ₑ ^ 2) ≤ A * ∫⁻ t, ‖f t‖ₑ ^ 2 := by
  let E : ℝ≥0∞ := ∫⁻ t, ‖K.applyIntegral f t‖ₑ ^ 2
  have hEtop : E ≠ ⊤ := by rw [show E = _ from K.sq_lintegral_eq_enorm_pairing hf]; finiteness
  by_cases hEzero : E = 0
  · change E ≤ _
    rw [hEzero]
    exact bot_le
  have hpair : E = ‖∫ t, f t * conj (K.adjoint.applyIntegral (K.applyIntegral f) t)‖ₑ := by
    rw [show E = _ from K.sq_lintegral_eq_enorm_pairing hf,
      K.integral_pairing_adjoint hf (K.integrable_applyIntegral hf)]
  have hsq : E ^ 2 ≤ ((∫⁻ t, ‖f t‖ₑ ^ 2) * A) * E := by
    calc
      E ^ 2 ≤ (∫⁻ t, ‖f t‖ₑ ^ 2) *
          ∫⁻ t, ‖K.adjoint.applyIntegral (K.applyIntegral f) t‖ₑ ^ 2 := by
        rw [hpair]
        exact enorm_integral_pairing_sq_le hfm
          (K.adjoint.measurable_applyIntegral (K.measurable_applyIntegral hfm))
      _ ≤ (∫⁻ t, ‖f t‖ₑ ^ 2) * (A * E) :=
        mul_le_mul' le_rfl (hbound (K.applyIntegral f)
          (K.measurable_applyIntegral hfm) (K.integrable_applyIntegral hf))
      _ = _ := by ring
  change E ≤ _
  calc
    E = E ^ 2 * E⁻¹ := by rw [pow_two, mul_assoc, ENNReal.mul_inv_cancel hEzero hEtop, mul_one]
    _ ≤ (((∫⁻ t, ‖f t‖ₑ ^ 2) * A) * E) * E⁻¹ := mul_le_mul' hsq le_rfl
    _ = A * ∫⁻ t, ‖f t‖ₑ ^ 2 := by
      rw [mul_assoc, ENNReal.mul_inv_cancel hEzero hEtop, mul_one, mul_comm]

/-- Any uniform positive quadratic-form majorant for the correlation gives
the corresponding forward `L²` estimate. This version accommodates the sum
of the near-diagonal and off-diagonal averaging majorants. -/
theorem sq_lintegral_le_of_correlation_form_bound_memLp
    (K : FiniteRangeKernel) (A : ℝ≥0∞)
    (hbound : ∀ g : ℝ → ℝ≥0∞, Measurable g →
      (∫⁻ x, ∫⁻ y, ‖K.correlation x y‖ₑ * g x * g y) ≤ A * ∫⁻ x, g x ^ 2)
    {f : ℝ → ℂ} (hfm : Measurable f) (hf : MemLp f 2) :
    (∫⁻ t, ‖K.applyIntegral f t‖ₑ ^ 2) ≤ A * ∫⁻ t, ‖f t‖ₑ ^ 2 := by
  apply K.sq_lintegral_bound_of_integrable A ?_ hfm
    (hf.locallyIntegrable (by norm_num))
  intro g hgm hgi
  apply K.sq_lintegral_bound_of_adjoint A ?_ hgm hgi
  intro h hhm hhi
  exact (K.adjoint_energy_le_correlation_enorm hhi).trans (hbound _ hhm.enorm)

/-- The symmetric correlation-kernel majorant controls the actual forward
operator on every measurable `L²` input. -/
theorem sq_lintegral_le_of_selectedAverageKernel_memLp {N : ℕ}
    (K : FiniteRangeKernel) (r : Fin N → ℝ) (hr : ∀ i, 0 < r i)
    {σ : ℝ → Fin N} (hσ : Measurable σ) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hbound : ∀ x y, ‖K.correlation x y‖ₑ ≤ C *
      (selectedAverageKernel r σ x y + selectedAverageKernel r σ y x))
    {f : ℝ → ℂ} (hfm : Measurable f) (hf : MemLp f 2) :
    (∫⁻ t, ‖K.applyIntegral f t‖ₑ ^ 2) ≤ (66 * C) * ∫⁻ t, ‖f t‖ₑ ^ 2 := by
  apply K.sq_lintegral_bound_of_integrable (66 * C) ?_ hfm
    (hf.locallyIntegrable (by norm_num))
  intro g hgm hgi
  apply K.sq_lintegral_bound_of_adjoint (66 * C) ?_ hgm hgi
  intro h hhm hhi
  exact K.adjoint_sq_lintegral_le_of_selectedAverageKernel r hr hσ C hC hbound hhm hhi

/-- The integral action depends only on the almost-everywhere class of the
input, pointwise at every output location. -/
theorem applyIntegral_congr_ae (K : FiniteRangeKernel) {f g : ℝ → ℂ}
    (hfg : f =ᵐ[volume] g) : K.applyIntegral f = K.applyIntegral g := by
  funext x
  apply integral_congr_ae
  filter_upwards [hfg] with t ht
  rw [ht]

/-- Remove the measurable-representative condition from an `L²` estimate. -/
theorem sq_lintegral_bound_of_measurable_memLp (K : FiniteRangeKernel) (A : ℝ≥0∞)
    (hbound : ∀ g : ℝ → ℂ, Measurable g → MemLp g 2 →
      (∫⁻ t, ‖K.applyIntegral g t‖ₑ ^ 2) ≤ A * ∫⁻ t, ‖g t‖ₑ ^ 2)
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    (∫⁻ t, ‖K.applyIntegral f t‖ₑ ^ 2) ≤ A * ∫⁻ t, ‖f t‖ₑ ^ 2 := by
  let g := hf.aestronglyMeasurable.mk f
  have hgm : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have heq : f =ᵐ[volume] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : MemLp g 2 := hf.ae_eq heq
  rw [K.applyIntegral_congr_ae heq]
  have hint : (∫⁻ t, ‖g t‖ₑ ^ 2) = ∫⁻ t, ‖f t‖ₑ ^ 2 := by
    apply lintegral_congr_ae
    filter_upwards [heq] with t ht
    rw [ht]
  exact (hbound g hgm hg).trans_eq (congrArg (fun v ↦ A * v) hint)

/-- The full operator-level `L²` conclusion from a correlation quadratic-form
bound. The input has exactly the `MemLp f 2` hypothesis. -/
theorem sq_lintegral_le_of_correlation_form_bound
    (K : FiniteRangeKernel) (A : ℝ≥0∞)
    (hbound : ∀ g : ℝ → ℝ≥0∞, Measurable g →
      (∫⁻ x, ∫⁻ y, ‖K.correlation x y‖ₑ * g x * g y) ≤ A * ∫⁻ x, g x ^ 2)
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    (∫⁻ t, ‖K.applyIntegral f t‖ₑ ^ 2) ≤ A * ∫⁻ t, ‖f t‖ₑ ^ 2 := by
  apply K.sq_lintegral_bound_of_measurable_memLp A ?_ hf
  intro g hgm hg
  exact K.sq_lintegral_le_of_correlation_form_bound_memLp A hbound hgm hg

/-- The full forward operator bound from a symmetric selected-radius
correlation majorant, with no extra measurability or `L¹` input hypotheses. -/
theorem sq_lintegral_le_of_selectedAverageKernel {N : ℕ}
    (K : FiniteRangeKernel) (r : Fin N → ℝ) (hr : ∀ i, 0 < r i)
    {σ : ℝ → Fin N} (hσ : Measurable σ) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hbound : ∀ x y, ‖K.correlation x y‖ₑ ≤ C *
      (selectedAverageKernel r σ x y + selectedAverageKernel r σ y x))
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    (∫⁻ t, ‖K.applyIntegral f t‖ₑ ^ 2) ≤ (66 * C) * ∫⁻ t, ‖f t‖ₑ ^ 2 := by
  apply K.sq_lintegral_bound_of_measurable_memLp (66 * C) ?_ hf
  intro g hgm hg
  exact K.sq_lintegral_le_of_selectedAverageKernel_memLp r hr hσ C hC hbound hgm hg

end FiniteRangeKernel
end QuadraticCarleson
