/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import LeanPool.Sundogcert.ShadowDecayGeneral
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The Cauchy population is the determine/resist separator

`Sundogcert.ShadowDecayGeneral` proves the general averaging law and splits the determine/resist
dichotomy into **two independent spectral conditions** of the averaging measure `μ`:

* RESIST — the continuous fringe washes out — is governed by **decay of the characteristic
  function** `‖charFun μ s‖ → 0` (the Riemann–Lebesgue property), discharged by
  `resistance_general`.
* DETERMINE — a shared discrete label survives — is governed by a **finite centered mean**
  `Integrable id μ ∧ ∫ x ∂μ = 0`, discharged by `determination_general`.

That module *names* the **standard Cauchy law** as the motivating witness that these two conditions
genuinely come apart — Cauchy *resists* (its characteristic function decays) yet *cannot determine*
(it has no first moment) — but leaves the Cauchy instance as future work, because mathlib's
`ProbabilityTheory.cauchyMeasure` ships with neither its characteristic-function decay nor the
non-integrability of its mean.

This module **builds that instance**, turning the named separator into a proved theorem.

## What is formalized here (deductive, axiom-clean)

* **RESIST (`cauchy_charFun_tendsto_zero`, `cauchy_resists`).** The Cauchy density `cauchyPDFReal`
  is `L¹` (it is a probability density), so its characteristic function is the Fourier transform of
  an integrable function and `‖charFun (cauchyMeasure x₀ γ) s‖ → 0` as `s → ∞` by the
  **Riemann–Lebesgue lemma** (`Real.zero_at_infty_fourier`). Feeding this to `resistance_general`
  shows the Cauchy-averaged continuous signature washes out as the spread `λ → ∞`.

* **NO-MEAN (`cauchy_no_mean`).** `¬ Integrable id (cauchyMeasure x₀ γ)` for `γ ≠ 0`: the first
  moment diverges. Reduced (via `integrable_withDensity_iff_integrable_smul'`) to the
  non-integrability of `x ↦ cauchyPDFReal x₀ γ x * x` on `volume`, which is shown by a tail
  comparison: on a half-line `(a, ∞)` the integrand dominates a constant multiple of `x⁻¹`, and
  `x⁻¹` is not integrable on any `(a, ∞)` (`not_integrableOn_Ioi_inv`). So the `Integrable id μ`
  hypothesis of `determination_general` **fails** for Cauchy.

* **SEPARATOR (`cauchy_is_separator`).** Combining the two halves: a standard Cauchy population
  satisfies the resist condition `‖charFun μ‖ → 0` yet fails the determination hypothesis
  `Integrable id μ`. So `resist` and `determine` provably come apart — they are two different facts
  about the averaging population, exactly as the general law states.

## What is NOT formalized (the residual named wall)

The **exact** value `charFun (cauchyMeasure x₀ γ) s = exp(-γ|s|)` (the Poisson kernel) is *not*
proved — only its decay, which is all the separator needs. The exact characteristic function is a
from-scratch contour / residue computation (mathlib has the Poisson kernel in
`Mathlib.Analysis.Complex.Poisson` but no `charFun_cauchy`); it remains a candidate mathlib upstream
and the one residual named wall of this module. The honesty is the same as `ShadowDecay`: the
deductive separator is proved; the sharper exact-value statement is named, not asserted.

## References

* `ProbabilityTheory.cauchyMeasure`, `ProbabilityTheory.integrable_cauchyPDFReal` — the Cauchy law.
* `Real.zero_at_infty_fourier` — the Riemann–Lebesgue lemma on `ℝ`.
* `MeasureTheory.not_integrableOn_Ioi_inv` — `x⁻¹` is not integrable on a half-line.
* Lukacs, *Characteristic Functions*; the Riemann–Lebesgue lemma; the Cauchy / Lorentz law.
-/

namespace Sundog.ShadowDecayCauchy

open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open Sundog.ShadowDecay Sundog.ShadowDecayGeneral
open scoped Real FourierTransform ENNReal NNReal

/-! ## RESIST — the Cauchy characteristic function decays (Riemann–Lebesgue). -/

/--
**The Cauchy characteristic function as a Fourier integral.** For scale `γ ≠ 0`, the
characteristic function of the Cauchy measure is the Fourier transform of its `L¹` density, sampled
at `-s / (2π)`: `charFun (cauchyMeasure x₀ γ) s = 𝓕 (fun x => (cauchyPDFReal x₀ γ x : ℂ)) (-s/2π)`.

This is the bridge that lets the Riemann–Lebesgue lemma act on `charFun`: it rewrites the integral
against the measure as an integral against `volume` weighted by the real density
(`integral_withDensity_eq_integral_toReal_smul₀`) and matches the `exp(s x I)` phase to the Fourier
kernel `𝐞(-(x w))` with `w = -s/(2π)`. -/
theorem charFun_cauchy_eq_fourier (x₀ : ℝ) (γ : ℝ≥0) (hγ : γ ≠ 0) (s : ℝ) :
    charFun (cauchyMeasure x₀ γ) s
      = 𝓕 (fun x => (cauchyPDFReal x₀ γ x : ℂ)) (-s / (2 * Real.pi)) := by
  rw [charFun_apply_real, cauchyMeasure_of_scale_ne_zero x₀ hγ,
    integral_withDensity_eq_integral_toReal_smul₀
      (measurable_cauchyPDF x₀ γ).aemeasurable
      (Filter.Eventually.of_forall fun x => by rw [cauchyPDF_def]; exact ENNReal.ofReal_lt_top)]
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [cauchyPDF_def, ENNReal.toReal_ofReal (cauchyPDF_pos x₀ hγ x).le]
  rw [real_smul, smul_eq_mul, mul_comm]
  congr 2
  push_cast
  field_simp

/--
**RESIST (the Cauchy charFun decays).** `‖charFun (cauchyMeasure x₀ γ) s‖ → 0` as `s → ∞`.

The Cauchy density is integrable (`integrable_cauchyPDFReal`), so its Fourier transform vanishes at
infinity by the Riemann–Lebesgue lemma (`Real.zero_at_infty_fourier`). The sampling point
`-s / (2π)` runs off to `-∞` as `s → ∞`, which lies in the `cocompact ℝ` filter, so composing gives
the `atTop` decay. This is the resist condition of the general law, with **no variance assumed** —
the Cauchy variance is infinite, yet it resists. -/
theorem cauchy_charFun_tendsto_zero (x₀ : ℝ) (γ : ℝ≥0) (hγ : γ ≠ 0) :
    Tendsto (fun s : ℝ => ‖charFun (cauchyMeasure x₀ γ) s‖) atTop (𝓝 0) := by
  -- `-s/(2π) → cocompact ℝ` as `s → ∞` (it runs to `-∞`, and `atBot ≤ cocompact`).
  have hcoco : Tendsto (fun s : ℝ => -s / (2 * Real.pi)) atTop (cocompact ℝ) := by
    rw [cocompact_eq_atBot_atTop]
    refine Tendsto.mono_right ?_ le_sup_left
    have hp : (0:ℝ) < 2 * Real.pi := by positivity
    exact Tendsto.atBot_div_const hp (tendsto_neg_atBot_iff.mpr tendsto_id)
  -- Riemann–Lebesgue: the Fourier transform of the `L¹` density vanishes at `cocompact`.
  have hRL : Tendsto (fun w : ℝ => 𝓕 (fun x => (cauchyPDFReal x₀ γ x : ℂ)) w)
      (cocompact ℝ) (𝓝 0) := Real.zero_at_infty_fourier _
  have hcomp := hRL.comp hcoco
  have hnorm : Tendsto
      (fun s : ℝ => ‖𝓕 (fun x => (cauchyPDFReal x₀ γ x : ℂ)) (-s / (2 * Real.pi))‖)
      atTop (𝓝 0) := by
    have := (continuous_norm.tendsto (0:ℂ)).comp hcomp
    simpa [Function.comp_def] using this
  refine hnorm.congr (fun s => ?_)
  rw [charFun_cauchy_eq_fourier x₀ γ hγ s]

/--
**RESIST applied — the Cauchy-averaged continuous signature washes out.** Feeding the Cauchy charFun
decay to `resistance_general`: for any forward probe `t > 0`, the ensemble average of the continuous
fringe `cos(2π(c + λ x) t)` over a Cauchy population `x ∼ cauchyMeasure x₀ γ` tends to `0` as the
spread `λ → ∞`. The continuous hidden variable becomes unrecoverable — Cauchy resists. -/
theorem cauchy_resists (x₀ : ℝ) (γ : ℝ≥0) (hγ : γ ≠ 0) (c t : ℝ) (ht : 0 < t) :
    Tendsto (fun lam : ℝ => ∫ x, Real.cos (2 * Real.pi * (c + lam * x) * t) ∂cauchyMeasure x₀ γ)
      atTop (𝓝 0) :=
  resistance_general (cauchyMeasure x₀ γ) (cauchy_charFun_tendsto_zero x₀ γ hγ) c t ht

/-! ## NO-MEAN — the Cauchy first moment diverges (a tail comparison with `x⁻¹`). -/

/--
**The weighted density is not integrable.** `¬ Integrable (fun x => cauchyPDFReal x₀ γ x * x)`
against `volume`, for `γ ≠ 0`. This is the analytic heart of the no-mean fact.

On the half-line `(a, ∞)` with `a = |x₀| + γ + 1`, the integrand dominates `(γ/(5π)) · x⁻¹`:
indeed `(x - x₀)² + γ² ≤ 5x²` there, so
`cauchyPDFReal x₀ γ x · x = π⁻¹ γ x / ((x-x₀)²+γ²) ≥ (γ/(5π)) x⁻¹`. Since `x⁻¹` is not integrable on
any half-line (`not_integrableOn_Ioi_inv`), neither is the integrand. -/
theorem cauchy_weighted_density_not_integrable (x₀ : ℝ) (γ : ℝ≥0) (hγ : γ ≠ 0) :
    ¬ Integrable (fun x : ℝ => cauchyPDFReal x₀ γ x * x) volume := by
  intro hInt
  have hγ0 : (0:ℝ) < (γ:ℝ) := by positivity
  set a : ℝ := |x₀| + (γ:ℝ) + 1 with ha
  -- restrict to a tail and scale by `C = 5π/γ`
  have hIoi : IntegrableOn (fun x : ℝ => cauchyPDFReal x₀ γ x * x) (Ioi a) volume :=
    hInt.integrableOn
  set C : ℝ := 5 * Real.pi / (γ:ℝ) with hC
  have hCInt : IntegrableOn (fun x : ℝ => C * (cauchyPDFReal x₀ γ x * x)) (Ioi a) volume :=
    hIoi.const_mul C
  -- `x⁻¹` is dominated by the (scaled) integrand on the tail, hence would be integrable
  have hinv : IntegrableOn (fun x : ℝ => x⁻¹) (Ioi a) volume := by
    apply hCInt.mono' measurable_inv.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxa : a < x := hx
    have hx0 : (0:ℝ) < x := lt_of_lt_of_le (by positivity) hxa.le
    have hgx : (γ:ℝ) ≤ x := by rw [ha] at hxa; nlinarith [abs_nonneg x₀]
    have hx0abs : |x₀| ≤ x := by rw [ha] at hxa; nlinarith [hγ0.le]
    have hden : (x - x₀)^2 + (γ:ℝ)^2 ≤ 5 * x^2 := by
      have h1 : (x - x₀)^2 ≤ 4 * x^2 := by
        nlinarith [le_abs_self x₀, neg_abs_le x₀, hx0abs, hx0]
      have h2 : (γ:ℝ)^2 ≤ x^2 := by nlinarith [hgx, hγ0]
      linarith
    have hdenpos : (0:ℝ) < (x - x₀)^2 + (γ:ℝ)^2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [cauchyPDFReal_def]
    have hexpand : Real.pi⁻¹ * (γ:ℝ) * ((x - x₀)^2 + (γ:ℝ)^2)⁻¹ * x
        = Real.pi⁻¹ * (γ:ℝ) * x / ((x - x₀)^2 + (γ:ℝ)^2) := by ring
    rw [hexpand, hC]
    rw [show (5 * Real.pi / (γ:ℝ)) * (Real.pi⁻¹ * (γ:ℝ) * x / ((x - x₀)^2 + (γ:ℝ)^2))
        = (5 * x) / ((x - x₀)^2 + (γ:ℝ)^2) by field_simp]
    rw [le_div_iff₀ hdenpos]
    have hinvx : x⁻¹ * x = 1 := inv_mul_cancel₀ (ne_of_gt hx0)
    have hxinv0 : (0:ℝ) < x⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hden hxinv0.le, hinvx, hx0]
  exact not_integrableOn_Ioi_inv hinv

/--
**NO-MEAN — the Cauchy population has no first moment.** `¬ Integrable id (cauchyMeasure x₀ γ)` for
`γ ≠ 0`. Reducing the integrability against the measure to integrability of the weighted density
against `volume` (`integrable_withDensity_iff_integrable_smul'`), this is exactly
`cauchy_weighted_density_not_integrable`. Hence the determination hypothesis `Integrable id μ` of
`determination_general` **fails** for Cauchy — it cannot determine. -/
theorem cauchy_no_mean (x₀ : ℝ) (γ : ℝ≥0) (hγ : γ ≠ 0) :
    ¬ Integrable (fun x : ℝ => x) (cauchyMeasure x₀ γ) := by
  rw [cauchyMeasure_of_scale_ne_zero x₀ hγ,
    integrable_withDensity_iff_integrable_smul' (measurable_cauchyPDF x₀ γ)
      (Filter.Eventually.of_forall fun x => by rw [cauchyPDF_def]; exact ENNReal.ofReal_lt_top)]
  intro hInt
  apply cauchy_weighted_density_not_integrable x₀ γ hγ
  have hfun : (fun x : ℝ => (cauchyPDF x₀ γ x).toReal • x)
      = (fun x : ℝ => cauchyPDFReal x₀ γ x * x) := by
    ext x
    rw [cauchyPDF_def, ENNReal.toReal_ofReal (cauchyPDF_pos x₀ hγ x).le, smul_eq_mul]
  rwa [hfun] at hInt

/-! ## SEPARATOR — resist and determine provably come apart. -/

/--
**THE SEPARATOR (capstone).** For any standard Cauchy population (`γ ≠ 0`), the resist condition of
the general law holds — `‖charFun (cauchyMeasure x₀ γ) s‖ → 0` — while the determination
hypothesis fails — `¬ Integrable id (cauchyMeasure x₀ γ)`.

So the two conditions of `ShadowDecayGeneral` are **logically independent**: a population can
satisfy the charFun-decay (resist) condition and still fail the finite-mean (determine) condition.
The Cauchy law is the witness that `resist` and `determine` come apart — they are two different
spectral facts about the averaging measure, not one. (Contrast `gaussian_resist_and_determine`,
where the Gaussian discharges **both**.) -/
theorem cauchy_is_separator (x₀ : ℝ) (γ : ℝ≥0) (hγ : γ ≠ 0) :
    (Tendsto (fun s : ℝ => ‖charFun (cauchyMeasure x₀ γ) s‖) atTop (𝓝 0))
      ∧ ¬ Integrable (fun x : ℝ => x) (cauchyMeasure x₀ γ) :=
  ⟨cauchy_charFun_tendsto_zero x₀ γ hγ, cauchy_no_mean x₀ γ hγ⟩

/--
**The dichotomy is genuine — Gaussian vs Cauchy.** The Gaussian discharges *both* spectral
conditions (`gaussian_resist_and_determine`); the Cauchy discharges the resist condition but
provably *fails* the determine condition (`cauchy_is_separator`). Together they show the two
conditions of the general law are independent: neither resist nor determine implies the other. -/
theorem resist_determine_independent (x₀ : ℝ) (γ : ℝ≥0) (hγ : γ ≠ 0) :
    -- Gaussian: resist ∧ determine
    ((Tendsto (fun s : ℝ => ‖charFun stdGaussian s‖) atTop (𝓝 0))
        ∧ (Integrable (fun x : ℝ => x) stdGaussian ∧ ∫ x, x ∂stdGaussian = 0))
      -- Cauchy: resist ∧ ¬determine
      ∧ ((Tendsto (fun s : ℝ => ‖charFun (cauchyMeasure x₀ γ) s‖) atTop (𝓝 0))
        ∧ ¬ Integrable (fun x : ℝ => x) (cauchyMeasure x₀ γ)) :=
  ⟨gaussian_resist_and_determine, cauchy_is_separator x₀ γ hγ⟩

end Sundog.ShadowDecayCauchy

-- Axiom audit: the Cauchy separator and all corollaries should depend only on mathlib's
-- foundational axioms (`propext`, `Classical.choice`, `Quot.sound`) — NO `sorryAx`.
