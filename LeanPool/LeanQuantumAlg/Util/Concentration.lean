/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Common
/-!
# Probabilistic exponential concentration

The engine behind exponential concentration of quantum kernels (Thanasilp et al. 2022):
a `[0,1]`-valued random variable with an exponentially small mean has an exponentially
small variance, and hence (by Chebyshev) concentrates exponentially around its mean.
Quantum-free; built on Mathlib's `variance` and Chebyshev inequality.
-/

@[expose] public section

namespace QuantumAlg

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- For a `[0,1]`-valued random variable on a probability space, the variance is at most
the mean (since `X² ≤ X`). -/
theorem variance_le_mean [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : MemLp X 2 μ) (h0 : 0 ≤ᵐ[μ] X) (h1 : X ≤ᵐ[μ] 1) :
    variance X μ ≤ ∫ ω, X ω ∂μ := by
  refine (variance_le_expectation_sq hX.aestronglyMeasurable).trans ?_
  have hsq : Integrable (fun ω => X ω ^ 2) μ :=
    (memLp_two_iff_integrable_sq hX.aestronglyMeasurable).1 hX
  have hint : Integrable X μ := hX.integrable (by norm_num)
  refine integral_mono_ae hsq hint ?_
  filter_upwards [h0, h1] with ω hω0 hω1
  simp only [Pi.one_apply] at hω1
  calc X ω ^ 2 = X ω * X ω := by rw [pow_two]
    _ ≤ 1 * X ω := mul_le_mul_of_nonneg_right hω1 hω0
    _ = X ω := one_mul _

/-- **Probabilistic exponential concentration** of a family of random variables
`X n : Ω n → ℝ` (each on a probability space `μ n`): the probability of deviating from
the mean by `δ` is at most `C / (bⁿ δ²)` for some `b > 1`. -/
def ExpConcentratedProb {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) (X : (n : ℕ) → Ω n → ℝ) : Prop :=
  ∃ b : ℝ, 1 < b ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (δ : ℝ), 0 < δ →
    (μ n) {ω | δ ≤ |X n ω - ∫ x, X n x ∂(μ n)|} ≤ ENNReal.ofReal (C / (b ^ n * δ ^ 2))

/-- An exponentially small variance gives probabilistic exponential concentration
(Chebyshev applied uniformly in `n`). -/
theorem expConcentratedProb_of_variance_le {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : (n : ℕ) → Ω n → ℝ) (hmem : ∀ n, MemLp (X n) 2 (μ n))
    {b : ℝ} (hb : 1 < b) {C : ℝ} (hC : 0 ≤ C)
    (hvar : ∀ n, variance (X n) (μ n) ≤ C / b ^ n) :
    ExpConcentratedProb μ X := by
  refine ⟨b, hb, C, hC, fun n δ hδ => ?_⟩
  refine (meas_ge_le_variance_div_sq (hmem n) hδ).trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [← div_div]
  gcongr
  exact hvar n

/-- A `[0,1]`-valued family with exponentially small mean concentrates exponentially. -/
theorem expConcentratedProb_of_mean_le {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : (n : ℕ) → Ω n → ℝ) (hmem : ∀ n, MemLp (X n) 2 (μ n))
    (h0 : ∀ n, 0 ≤ᵐ[μ n] X n) (h1 : ∀ n, X n ≤ᵐ[μ n] 1)
    {b : ℝ} (hb : 1 < b) {C : ℝ} (hC : 0 ≤ C)
    (hmean : ∀ n, ∫ ω, X n ω ∂(μ n) ≤ C / b ^ n) :
    ExpConcentratedProb μ X := by
  refine expConcentratedProb_of_variance_le μ X hmem hb hC (fun n => ?_)
  exact (variance_le_mean (hmem n) (h0 n) (h1 n)).trans (hmean n)

/-- Under exponential concentration, the deviation probability vanishes as `n → ∞`
(for each fixed `δ > 0`): the landscape becomes flat and a polynomial shot budget cannot
resolve the kernel. -/
theorem ExpConcentratedProb.tendsto_zero {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {μ : (n : ℕ) → Measure (Ω n)} {X : (n : ℕ) → Ω n → ℝ}
    (h : ExpConcentratedProb μ X) {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto
      (fun n => (μ n) {ω | δ ≤ |X n ω - ∫ x, X n x ∂(μ n)|}) Filter.atTop (nhds 0) := by
  obtain ⟨b, hb, C, hC, hbound⟩ := h
  have hreal : Filter.Tendsto (fun n => C / (b ^ n * δ ^ 2)) Filter.atTop (nhds 0) := by
    have hinv : Filter.Tendsto (fun n => (b ^ n)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hb)
    have hmul := hinv.const_mul (C / δ ^ 2)
    rw [mul_zero] at hmul
    have hfun : (fun n => C / (b ^ n * δ ^ 2)) = (fun n => (C / δ ^ 2) * (b ^ n)⁻¹) := by
      funext n
      have hbn : (b : ℝ) ^ n ≠ 0 := (pow_pos (lt_trans one_pos hb) n).ne'
      have hδ2 : (δ : ℝ) ^ 2 ≠ 0 := (pow_pos hδ 2).ne'
      field_simp
    rw [hfun]; exact hmul
  have hcr : Filter.Tendsto (fun n => ENNReal.ofReal (C / (b ^ n * δ ^ 2)))
      Filter.atTop (nhds 0) := by
    have := (ENNReal.continuous_ofReal.tendsto 0).comp hreal
    simpa [Function.comp_def] using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcr
    (fun _ => zero_le) (fun n => hbound n δ hδ)

end QuantumAlg
