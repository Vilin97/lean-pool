/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryVerySmallOperator
public import LeanPool.QuadraticCarleson.QuadraticCarleson.FiniteModulationKernelComparison

/-!
# The canonical lacunary very-small endpoint estimate

The actual sum of very-small scale outputs is estimated by Markov on the
complement of the canonical fivefold exceptional set. The exceptional set
costs at most five times the input L¹ mass. Since the stopping decomposition
is normalized at height one, the general global threshold bound retains this
exceptional term; the paper uses the resulting threshold-one estimate.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace LacunaryVerySmallEndpoint

open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open PositiveLowFullEstimate LacunaryVerySmallOperator LacunaryVerySmallRange


/-- The explicit constant from the genuine cancellation and geometric sum. -/
noncomputable def verySmallL1Constant : ℝ≥0∞ :=
  ENNReal.ofReal (6 * lowKernelDerivativeConstant * verySmallGeometricConstant)

theorem verySmallL1Constant_lt_top : verySmallL1Constant < ∞ := ENNReal.ofReal_lt_top

/-- Including the fivefold stopping-set cost. -/
noncomputable def verySmallEndpointConstant : ℝ≥0∞ := 5 + verySmallL1Constant

theorem verySmallEndpointConstant_lt_top : verySmallEndpointConstant < ∞ :=
  ENNReal.add_lt_top.mpr ⟨by finiteness, verySmallL1Constant_lt_top⟩

/-- The exceptional set is the actual canonical stopping family, not an
arbitrary family with an assumed packing bound. -/
theorem volume_canonicalFivefoldExceptionalSet_le {f : ℝ → ℂ} (hfi : Integrable f) :
    volume (fivefoldExceptionalSet (stoppingCenter (f := f)) stoppingLength) ≤
      5 * ∫⁻ x, ‖f x‖ₑ := by
  apply (volume_fivefoldExceptionalSet_le
    (stoppingCenter (f := f)) stoppingLength).trans
  apply mul_le_mul' le_rfl
  simpa only [volume_stoppingCell_interval, stoppingLength, ofReal_norm] using
    tsum_volume_stoppingCell_le_lintegral_norm hfi

/-- Chebyshev on precisely the complement where the proved L¹ estimate
applies. This bound is uniform in every positive cutoff sequence. -/
theorem lacunaryVerySmallLowContribution_compl_levelSet_mul_le
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {B : ℕ → ℕ} (hB : ∀ k, 0 < B k) (c : ℕ) (a : ℝ≥0∞) :
    a * volume ({x | a < lacunaryVerySmallLowContribution f B c x} ∩
      (fivefoldExceptionalSet (stoppingCenter (f := f)) stoppingLength)ᶜ) ≤
        verySmallL1Constant * ∫⁻ x, ‖f x‖ₑ := by
  let E := fivefoldExceptionalSet (stoppingCenter (f := f)) stoppingLength
  have hm := mul_meas_ge_le_lintegral (μ := volume.restrict Eᶜ)
    (measurable_lacunaryVerySmallLowContribution hf B c) a
  rw [Measure.restrict_apply
    (measurableSet_le measurable_const (measurable_lacunaryVerySmallLowContribution hf B c))]
    at hm
  apply le_trans ?_ (hm.trans (lintegral_lacunaryVerySmallLowContribution_compl_le
    hf hfi hB c))
  apply mul_le_mul' le_rfl
  apply measure_mono
  intro x hx
  have hlt : a < lacunaryVerySmallLowContribution f B c x := hx.1
  exact ⟨hlt.le, hx.2⟩

/-- The global threshold estimate keeps the normalized stopping-set cost
explicit. No scaling identity for the nonlinear stopping decomposition is
assumed. -/
theorem lacunaryVerySmallLowContribution_levelSet_mul_le
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {B : ℕ → ℕ} (hB : ∀ k, 0 < B k) (c : ℕ) (a : ℝ≥0∞) :
    a * volume {x | a < lacunaryVerySmallLowContribution f B c x} ≤
      (5 * a + verySmallL1Constant) * ∫⁻ x, ‖f x‖ₑ := by
  let E := fivefoldExceptionalSet (stoppingCenter (f := f)) stoppingLength
  let S := {x | a < lacunaryVerySmallLowContribution f B c x}
  have hs : S ⊆ E ∪ (S ∩ Eᶜ) := by
    intro x hx
    by_cases he : x ∈ E
    · exact Or.inl he
    · exact Or.inr ⟨hx, he⟩
  calc
    a * volume S ≤ a * (volume E + volume (S ∩ Eᶜ)) :=
      mul_le_mul' le_rfl ((measure_mono hs).trans (measure_union_le _ _))
    _ = a * volume E + a * volume (S ∩ Eᶜ) := mul_add _ _ _
    _ ≤ a * (5 * ∫⁻ x, ‖f x‖ₑ) +
        verySmallL1Constant * ∫⁻ x, ‖f x‖ₑ :=
      add_le_add (mul_le_mul' le_rfl (volume_canonicalFivefoldExceptionalSet_le hfi))
        (lacunaryVerySmallLowContribution_compl_levelSet_mul_le hf hfi hB c a)
    _ = _ := by ring

/-- The paper's normalized very-small weak-(1,1) estimate, including the
entire fivefold exceptional set. -/
theorem lacunaryVerySmallLowContribution_levelSet_one_le
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {B : ℕ → ℕ} (hB : ∀ k, 0 < B k) (c : ℕ) :
    volume {x | 1 < lacunaryVerySmallLowContribution f B c x} ≤
      verySmallEndpointConstant * ∫⁻ x, ‖f x‖ₑ := by
  simpa only [one_mul, mul_one, verySmallEndpointConstant] using
    lacunaryVerySmallLowContribution_levelSet_mul_le hf hfi hB c 1

/-- For positive finite thresholds, the exceptional-set and Markov costs
are respectively `5` and `C/a`. -/
theorem lacunaryVerySmallLowContribution_levelSet_le
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {B : ℕ → ℕ} (hB : ∀ k, 0 < B k) (c : ℕ)
    {a : ℝ≥0∞} (ha : a ≠ 0) (hat : a ≠ ∞) :
    volume {x | a < lacunaryVerySmallLowContribution f B c x} ≤
      (5 + verySmallL1Constant / a) * ∫⁻ x, ‖f x‖ₑ := by
  have h := lacunaryVerySmallLowContribution_levelSet_mul_le hf hfi hB c a
  rw [mul_comm a] at h
  calc
    _ ≤ ((5 * a + verySmallL1Constant) * ∫⁻ x, ‖f x‖ₑ) / a :=
      (ENNReal.le_div_iff_mul_le (Or.inl ha) (Or.inl hat)).mpr h
    _ = (5 * (a * a⁻¹) + verySmallL1Constant * a⁻¹) * ∫⁻ x, ‖f x‖ₑ := by
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by rw [ENNReal.mul_inv_cancel ha hat, mul_one]; rfl

/-- In the range of thresholds below one, the fixed normalized decomposition
also has the usual uniform weak-(1,1) bound. -/
theorem lacunaryVerySmallLowContribution_levelSet_mul_le_of_le_one
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {B : ℕ → ℕ} (hB : ∀ k, 0 < B k) (c : ℕ)
    {a : ℝ≥0∞} (ha : a ≤ 1) :
    a * volume {x | a < lacunaryVerySmallLowContribution f B c x} ≤
      verySmallEndpointConstant * ∫⁻ x, ‖f x‖ₑ := by
  apply (lacunaryVerySmallLowContribution_levelSet_mul_le hf hfi hB c a).trans
  apply mul_le_mul' _ le_rfl
  exact add_le_add (by simpa only [mul_one] using mul_le_mul' le_rfl ha) le_rfl

/-- The normalized source-domain specialization. -/
theorem lacunaryVerySmallLowContribution_L0Infinity_levelSet_one_le
    (f : L0Infinity) {B : ℕ → ℕ} (hB : ∀ k, 0 < B k) (c : ℕ) :
    volume {x | 1 < lacunaryVerySmallLowContribution f B c x} ≤
      verySmallEndpointConstant * ∫⁻ x, ‖f x‖ₑ :=
  lacunaryVerySmallLowContribution_levelSet_one_le f.measurable_toFun f.integrable hB c

/-- The paper's exact cutoff `B_k = 20 · 2^(2^k)` needs no further hypotheses. -/
theorem paperLacunaryVerySmallLowContribution_levelSet_one_le
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f) (c : ℕ) :
    volume {x | 1 < lacunaryVerySmallLowContribution f
      (fun k ↦ 20 * 2 ^ (2 ^ k)) c x} ≤
        verySmallEndpointConstant * ∫⁻ x, ‖f x‖ₑ :=
  lacunaryVerySmallLowContribution_levelSet_one_le hf hfi (fun _ ↦ by positivity) c


end LacunaryVerySmallEndpoint
end QuadraticCarleson
