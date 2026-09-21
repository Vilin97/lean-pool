/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticCenteredMaximal
import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticL2Operator

/-!
# Symmetric averaging bounds for the quadratic `TT*` argument

The correlation estimate is majorized by centered averages at a radius selected
by either endpoint. The bound here is independent of the number of radii and
their size. It is the positive-kernel part of the operator-level argument.
-/

open MeasureTheory Set Metric
open scoped ENNReal NNReal
open scoped ComplexConjugate

namespace QuadraticCarleson

/-- A square majorant valid also when either extended value is infinite. -/
theorem ennreal_mul_le_add_sq (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  by_cases ha : a = ⊤
  · subst a
    simp
  by_cases hb : b = ⊤
  · subst b
    simp
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  exact_mod_cast (show (a : ℝ) * (b : ℝ) ≤ (a : ℝ) ^ 2 + (b : ℝ) ^ 2 by
    nlinarith [sq_nonneg ((a : ℝ) - (b : ℝ)), mul_nonneg a.2 b.2])

/-- The finite centered maximal operator controls its quadratic pairing with
the input. The nonoptimal numerical constant avoids square roots. -/
theorem lintegral_mul_finiteCenteredMaximal_le {N : ℕ}
    (r : Fin N → ℝ) (hr : ∀ i, 0 < r i) {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ x, f x * finiteCenteredMaximal r f x) ≤ 33 * ∫⁻ x, f x ^ 2 := by
  calc
    _ ≤ ∫⁻ x, f x ^ 2 + finiteCenteredMaximal r f x ^ 2 :=
      lintegral_mono (fun x ↦ ennreal_mul_le_add_sq _ _)
    _ = (∫⁻ x, f x ^ 2) + ∫⁻ x, finiteCenteredMaximal r f x ^ 2 :=
      lintegral_add_left (hf.pow_const 2) _
    _ ≤ (∫⁻ x, f x ^ 2) + 32 * ∫⁻ x, f x ^ 2 :=
      add_le_add le_rfl (finiteCenteredMaximal_sq_lintegral_le r hr hf)
    _ = _ := by ring

/-- The normalized averaging kernel whose radius is selected at its first
endpoint. -/
noncomputable def selectedAverageKernel {N : ℕ} (r : Fin N → ℝ)
    (σ : ℝ → Fin N) (x y : ℝ) : ℝ≥0∞ :=
  (closedBall x (r (σ x))).indicator (fun _ ↦ (ENNReal.ofReal (2 * r (σ x)))⁻¹) y

theorem measurable_selectedAverageKernel {N : ℕ} (r : Fin N → ℝ)
    {σ : ℝ → Fin N} (hσ : Measurable σ) :
    Measurable (Function.uncurry (selectedAverageKernel r σ)) := by
  have hr : Measurable (fun x ↦ r (σ x)) := (measurable_of_finite r).comp hσ
  have hs : MeasurableSet {z : ℝ × ℝ | dist z.2 z.1 ≤ r (σ z.1)} :=
    measurableSet_le (measurable_snd.dist measurable_fst) (hr.comp measurable_fst)
  have hm := (((hr.comp measurable_fst).const_mul 2).ennreal_ofReal.inv).indicator hs
  convert hm using 1
  funext z
  simp only [Function.uncurry, selectedAverageKernel, Set.indicator, mem_closedBall,
    mem_ofPred_eq, Pi.inv_apply, Function.comp_apply]

/-- Integrating the selected averaging kernel recovers the corresponding
centered average exactly. -/
theorem lintegral_selectedAverageKernel_mul {N : ℕ} (r : Fin N → ℝ)
    (σ : ℝ → Fin N) {f : ℝ → ℝ≥0∞} (hf : Measurable f) (x : ℝ) :
    (∫⁻ y, selectedAverageKernel r σ x y * f y) = centeredAverage (r (σ x)) f x := by
  unfold selectedAverageKernel centeredAverage
  have hid (y : ℝ) :
      (closedBall x (r (σ x))).indicator (fun _ ↦ (ENNReal.ofReal (2 * r (σ x)))⁻¹) y * f y =
      (closedBall x (r (σ x))).indicator
        (fun y ↦ (ENNReal.ofReal (2 * r (σ x)))⁻¹ * f y) y := by
    by_cases hy : y ∈ closedBall x (r (σ x)) <;> simp [Set.indicator, hy]
  simp_rw [hid]
  rw [lintegral_indicator measurableSet_closedBall,
    lintegral_const_mul _ hf]
  rw [div_eq_mul_inv, mul_comm]

/-- The pairing for an arbitrary measurable selected radius is bounded by the
finite centered maximal estimate. -/
theorem selectedAverageKernel_pairing_le {N : ℕ} (r : Fin N → ℝ)
    (hr : ∀ i, 0 < r i) (σ : ℝ → Fin N) {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ x, ∫⁻ y, selectedAverageKernel r σ x y * f x * f y) ≤
      33 * ∫⁻ x, f x ^ 2 := by
  calc
    _ = ∫⁻ x, f x * centeredAverage (r (σ x)) f x := by
      apply lintegral_congr
      intro x
      simp_rw [show ∀ y, selectedAverageKernel r σ x y * f x * f y =
        f x * (selectedAverageKernel r σ x y * f y) by intro y; ring]
      have hrow : Measurable (fun y ↦ selectedAverageKernel r σ x y * f y) :=
        (measurable_const.indicator measurableSet_closedBall).mul hf
      rw [lintegral_const_mul _ hrow, lintegral_selectedAverageKernel_mul r σ hf]
    _ ≤ ∫⁻ x, f x * finiteCenteredMaximal r f x := by
      apply lintegral_mono
      intro x
      exact mul_le_mul' le_rfl (le_iSup (fun i ↦ centeredAverage (r i) f x) (σ x))
    _ ≤ _ := lintegral_mul_finiteCenteredMaximal_le r hr hf

/-- The symmetric selected-radius averaging majorant has a uniform quadratic
form bound. This is the positive-kernel estimate used by `TT*`. -/
theorem symmetric_selectedAverageKernel_pairing_le {N : ℕ} (r : Fin N → ℝ)
    (hr : ∀ i, 0 < r i) {σ : ℝ → Fin N} (hσ : Measurable σ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, ∫⁻ y, (selectedAverageKernel r σ x y + selectedAverageKernel r σ y x) *
      f x * f y) ≤ 66 * ∫⁻ x, f x ^ 2 := by
  have hm := measurable_selectedAverageKernel r hσ
  have hjoint : Measurable (fun z : ℝ × ℝ ↦
      selectedAverageKernel r σ z.1 z.2 * f z.1 * f z.2) :=
    (hm.mul (hf.comp measurable_fst)).mul (hf.comp measurable_snd)
  have hswap := lintegral_lintegral_swap
    (f := fun x y ↦ selectedAverageKernel r σ x y * f x * f y)
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) hjoint.aemeasurable
  have heq : (∫⁻ x, ∫⁻ y, selectedAverageKernel r σ y x * f x * f y) =
      ∫⁻ x, ∫⁻ y, selectedAverageKernel r σ x y * f x * f y := by
    rw [hswap]
    apply lintegral_congr
    intro x
    apply lintegral_congr
    intro y
    ring
  calc
    _ = (∫⁻ x, ∫⁻ y, selectedAverageKernel r σ x y * f x * f y) +
        ∫⁻ x, ∫⁻ y, selectedAverageKernel r σ y x * f x * f y := by
      simp_rw [add_mul]
      rw [← lintegral_add_left hjoint.lintegral_prod_right' _]
      apply lintegral_congr
      intro x
      exact lintegral_add_left ((measurable_const.indicator measurableSet_closedBall).mul
        measurable_const |>.mul hf) _
    _ = 2 * (∫⁻ x, ∫⁻ y, selectedAverageKernel r σ x y * f x * f y) := by
      rw [heq]
      ring
    _ ≤ 2 * (33 * ∫⁻ x, f x ^ 2) :=
      mul_le_mul' le_rfl (selectedAverageKernel_pairing_le r hr σ hf)
    _ = _ := by ring

namespace FiniteRangeKernel

/-- The exact `TT*` identity bounds the adjoint energy by the absolute
correlation quadratic form. -/
theorem adjoint_energy_le_correlation_enorm (K : FiniteRangeKernel)
    {g : ℝ → ℂ} (hg : Integrable g) :
    (∫⁻ t, ‖K.adjoint.applyIntegral g t‖ₑ ^ 2) ≤
      ∫⁻ x, ∫⁻ y, ‖K.correlation x y‖ₑ * ‖g x‖ₑ * ‖g y‖ₑ := by
  have heq : (∫⁻ t, ‖K.adjoint.applyIntegral g t‖ₑ ^ 2) =
      ‖∫ t, ((‖K.adjoint.applyIntegral g t‖ ^ 2 : ℝ) : ℂ)‖ₑ := by
    rw [integral_complex_ofReal, ← ofReal_norm, Complex.norm_real,
      Real.norm_of_nonneg (integral_nonneg (fun _ ↦ sq_nonneg _)),
      ofReal_integral_eq_lintegral_ofReal (K.integrable_adjoint_energy hg)
        (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _))]
    apply lintegral_congr
    intro t
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [heq, K.adjoint_energy_eq_correlation_pairing hg]
  calc
    _ ≤ ∫⁻ x, ‖(∫ y, K.correlation x y * g y) * conj (g x)‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x, ∫⁻ y, ‖K.correlation x y‖ₑ * ‖g x‖ₑ * ‖g y‖ₑ := by
      apply lintegral_mono
      intro x
      have hconj : ‖conj (g x)‖ₑ = ‖g x‖ₑ := by
        simp only [← ofReal_norm, RCLike.norm_conj]
      dsimp only
      rw [enorm_mul, hconj]
      calc
        _ ≤ (∫⁻ y, ‖K.correlation x y * g y‖ₑ) * ‖g x‖ₑ :=
          mul_le_mul' (enorm_integral_le_lintegral_enorm _) le_rfl
        _ = ∫⁻ y, ‖K.correlation x y‖ₑ * ‖g x‖ₑ * ‖g y‖ₑ := by
          rw [← lintegral_mul_const' _ _ (by finiteness)]
          apply lintegral_congr
          intro y
          rw [enorm_mul]
          ring

/-- Operator-level adjoint `L²` decay from the symmetric centered averaging
majorant. The constant is independent of the finite family and selector. -/
theorem adjoint_sq_lintegral_le_of_selectedAverageKernel {N : ℕ}
    (K : FiniteRangeKernel) (r : Fin N → ℝ) (hr : ∀ i, 0 < r i)
    {σ : ℝ → Fin N} (hσ : Measurable σ) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hbound : ∀ x y, ‖K.correlation x y‖ₑ ≤ C *
      (selectedAverageKernel r σ x y + selectedAverageKernel r σ y x))
    {g : ℝ → ℂ} (hgm : Measurable g) (hg : Integrable g) :
    (∫⁻ t, ‖K.adjoint.applyIntegral g t‖ₑ ^ 2) ≤
      (66 * C) * ∫⁻ t, ‖g t‖ₑ ^ 2 := by
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, ‖K.correlation x y‖ₑ * ‖g x‖ₑ * ‖g y‖ₑ :=
      K.adjoint_energy_le_correlation_enorm hg
    _ ≤ ∫⁻ x, ∫⁻ y, C * ((selectedAverageKernel r σ x y +
        selectedAverageKernel r σ y x) * ‖g x‖ₑ * ‖g y‖ₑ) := by
      apply lintegral_mono
      intro x
      apply lintegral_mono
      intro y
      calc
        _ ≤ (C * (selectedAverageKernel r σ x y + selectedAverageKernel r σ y x)) *
            ‖g x‖ₑ * ‖g y‖ₑ := mul_le_mul' (mul_le_mul' (hbound x y) le_rfl) le_rfl
        _ = _ := by ring
    _ = C * (∫⁻ x, ∫⁻ y, (selectedAverageKernel r σ x y +
        selectedAverageKernel r σ y x) * ‖g x‖ₑ * ‖g y‖ₑ) := by
      simp_rw [lintegral_const_mul' _ _ hC]
    _ ≤ C * (66 * ∫⁻ x, ‖g x‖ₑ ^ 2) :=
      mul_le_mul' le_rfl (symmetric_selectedAverageKernel_pairing_le r hr hσ hgm.enorm)
    _ = _ := by ring

end FiniteRangeKernel

end QuadraticCarleson
