/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticFixedHeightAveragingAmplitude

/-!
# Concrete fixed-height positive dyadic quadratic kernels

This is the dyadic-cutoff specialization of the finite annular maximal
theorem. Every amplitude and height hypothesis is derived from the paper's
actual cutoff and its exact oscillatory scale-selection rule.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson

/-- The outer support radius at the paper's selected oscillatory scale. -/
noncomputable def fixedHeightRadius (lam : ℝ) (height : ℕ) (hlam : lam ≠ 0) : ℝ :=
  (2 : ℝ) ^ (oscillatoryScaleIndex lam height hlam - 1)

theorem fixedHeightRadius_pos (lam : ℝ) (height : ℕ) (hlam : lam ≠ 0) :
    0 < fixedHeightRadius lam height hlam := zpow_pos (by norm_num) _

/-- The exact scale choice gives the common quadratic height interval
`[2^(2h)/4, 2^(2h)]` for the outer annular radius. -/
theorem fixedHeightRadius_height {lam : ℝ} (hlam : 0 < lam) (height : ℕ) :
    (2 : ℝ) ^ (2 * height) / 4 ≤ lam * fixedHeightRadius lam height hlam.ne' ^ 2 ∧
      lam * fixedHeightRadius lam height hlam.ne' ^ 2 ≤ 4 * ((2 : ℝ) ^ (2 * height) / 4) := by
  let j := oscillatoryScaleIndex lam height hlam.ne'
  have hs := oscillatoryScaleIndex_spec lam height hlam.ne'
  change (2 : ℝ) ^ height ≤ (2 : ℝ) ^ j * Real.sqrt |lam| ∧
    (2 : ℝ) ^ j * Real.sqrt |lam| < (2 : ℝ) ^ (height + 1) at hs
  have hj : (2 : ℝ) ^ j = 2 * (2 : ℝ) ^ (j - 1) := by
    calc
      _ = (2 : ℝ) ^ ((j - 1) + 1) := by congr 1; ring
      _ = _ := by rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]; ring
  have heq : ((2 : ℝ) ^ j * Real.sqrt |lam|) ^ 2 =
      4 * (lam * fixedHeightRadius lam height hlam.ne' ^ 2) := by
    rw [mul_pow, Real.sq_sqrt (abs_nonneg _), abs_of_pos hlam, hj]
    dsimp [fixedHeightRadius, j]
    ring
  have hlow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ height) hs.1 2
  have hupp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ j * Real.sqrt |lam|) hs.2.le 2
  have hpow : ((2 : ℝ) ^ height) ^ 2 = (2 : ℝ) ^ (2 * height) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [heq, hpow] at hlow
  rw [heq, pow_succ (2 : ℝ) height, mul_pow, hpow] at hupp
  constructor <;> nlinarith

/-- The actual positive half of a fixed-height dyadic quadratic kernel. -/
noncomputable def positiveFixedHeightQuadraticKernel
    (lam : ℝ) (height : ℕ) (hlam : lam ≠ 0) : ℝ → ℂ :=
  annularQuadraticKernel (positiveDyadicAmplitude (oscillatoryScaleIndex lam height hlam)) lam

/-- Concrete finite positive-modulation estimate with an explicit small
parameter. No amplitude, derivative, support, or correlation hypothesis is
left to its caller. -/
theorem finite_positiveFixedHeightQuadraticKernel_maximal_sq_lintegral_le
    (n height : ℕ) (lam : Fin (n + 1) → ℝ) (hlam : ∀ i, 0 < lam i)
    {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    (hdecay : 1 ≤ ((2 : ℝ) ^ (2 * height) / 4) * u ^ 5)
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    (∫⁻ x, finiteConvolutionMaximal
      (fun i ↦ positiveFixedHeightQuadraticKernel (lam i) height (hlam i).ne') f x ^ 2) ≤
      ENNReal.ofReal (4437295368 * positiveDyadicAmplitudeBound ^ 2 * u) * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  apply finite_annularQuadraticKernel_maximal_sq_lintegral_le n
    (fun i ↦ positiveDyadicAmplitude (oscillatoryScaleIndex (lam i) height (hlam i).ne'))
    (fun i ↦ positiveDyadicAmplitudeDerivative (oscillatoryScaleIndex (lam i) height (hlam i).ne'))
    (fun i ↦ fixedHeightRadius (lam i) height (hlam i).ne') lam
    (fun i ↦ fixedHeightRadius_pos _ _ _) (by positivity)
    positiveDyadicAmplitudeBound_nonneg hu hu1 hdecay
    (fun i ↦ fixedHeightRadius_height (hlam i) height)
    (fun i ↦ hasDerivAt_positiveDyadicAmplitude _)
    (fun i ↦ continuous_positiveDyadicAmplitudeDerivative _)
    (fun i ↦ positiveDyadicAmplitude_support_subset _)
    (fun i ↦ norm_positiveDyadicAmplitude_le _)
    (fun i ↦ norm_positiveDyadicAmplitudeDerivative_le _) hf

/-- A dyadic small parameter admissible at every positive oscillation height.
It gives a deliberately nonoptimal but strictly exponential decay rate. -/
theorem fixedHeight_dyadic_decay_parameter (height : ℕ) (hh : 1 ≤ height) :
    1 ≤ ((2 : ℝ) ^ (2 * height) / 4) * (1 / (2 : ℝ) ^ ((height - 1) / 5)) ^ 5 := by
  have hexp : 5 * ((height - 1) / 5) + 2 ≤ 2 * height := by omega
  have hp : (2 : ℝ) ^ (5 * ((height - 1) / 5) + 2) ≤ (2 : ℝ) ^ (2 * height) :=
    pow_le_pow_right₀ (by norm_num) hexp
  have hid : ((2 : ℝ) ^ (2 * height) / 4) * (1 / (2 : ℝ) ^ ((height - 1) / 5)) ^ 5 =
      (2 : ℝ) ^ (2 * height) / (2 : ℝ) ^ (5 * ((height - 1) / 5) + 2) := by
    rw [pow_add]
    have he : ((height - 1) / 5) * 5 = 5 * ((height - 1) / 5) := by omega
    rw [one_div_pow, ← pow_mul, he]
    norm_num
    ring
  rw [hid]
  exact (one_le_div (by positivity)).mpr hp

/-- The actual positive-half dyadic fixed-height finite maximal `L²` decay
estimate, with no unproved analytic hypotheses. -/
theorem finite_positiveFixedHeightQuadraticKernel_maximal_sq_decay
    (n height : ℕ) (hh : 1 ≤ height) (lam : Fin (n + 1) → ℝ) (hlam : ∀ i, 0 < lam i)
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    (∫⁻ x, finiteConvolutionMaximal
      (fun i ↦ positiveFixedHeightQuadraticKernel (lam i) height (hlam i).ne') f x ^ 2) ≤
      ENNReal.ofReal (4437295368 * positiveDyadicAmplitudeBound ^ 2 /
        (2 : ℝ) ^ ((height - 1) / 5)) * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  convert finite_positiveFixedHeightQuadraticKernel_maximal_sq_lintegral_le n height lam hlam
    (by positivity : 0 < 1 / (2 : ℝ) ^ ((height - 1) / 5))
    ((div_le_one (by positivity : 0 < (2 : ℝ) ^ ((height - 1) / 5))).mpr
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
    (fixedHeight_dyadic_decay_parameter height hh) hf using 1
  congr 2
  ring

end QuadraticCarleson
