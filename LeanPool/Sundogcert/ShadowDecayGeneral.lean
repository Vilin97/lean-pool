/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import LeanPool.Sundogcert.ShadowDecay

/-!
# The determine/resist dichotomy is the characteristic-function spectrum of the averaging kernel

`Sundogcert.ShadowDecay` proves the lossy-averaging dichotomy for ONE population — the standard
Gaussian. This file extracts the **general law** behind it and shows the two halves are governed by
**two different spectral conditions** of the averaging measure `μ`, not one.

Averaging the continuous fringe `cos(2π(c + λ x) t)` over an arbitrary population `x ∼ μ` factors,
for EVERY probability measure `μ`, through `μ`'s **characteristic function** `charFun μ`:

  `∫ cos(2π(c + λ x) t) ∂μ = Re[ exp(2π i c t) · charFun μ (2π λ t) ]`     (`shadow_decay_charFun`)

The Gaussian's Debye–Waller damping `exp(-2π²λ²t²)` is just `Re charFun` for `μ = N(0,1)`; the law
holds for any `μ`. From this single identity the dichotomy splits into **independent** conditions:

* **RESIST** (the continuous signal washes out): governed by **decay of `‖charFun μ‖`**. If
  `‖charFun μ s‖ → 0` as `s → ∞` (the Riemann–Lebesgue property — true of every
  absolutely-continuous population: Gaussian, uniform, AND the heavy-tailed **Cauchy**, whose
  variance is infinite), then the averaged shadow `→ 0` as `λ → ∞` (`resistance_general`).
  Resistance is a property of the charFun SPECTRUM, not of the variance.

* **DETERMINE** (a shared discrete label survives): governed by a **finite centered mean**
  `∫ x ∂μ = 0` with `x` integrable (`determination_general`). This is a SEPARATE condition: it asks
  for a first moment, which `‖charFun‖ → 0` neither implies nor is implied by.

**The separation made concrete (the Cauchy witness).** A standard Cauchy population *resists*
(`charFun = exp(-|s|) → 0`, a Poisson kernel) yet *cannot determine* (it has no mean — its sample
average is itself Cauchy and never concentrates). So `resist` and `determine` come apart: they are
two different facts about `μ`, as a population-swap experiment confirms numerically (Gaussian /
uniform / Cauchy wash; a lattice population whose `charFun = cos` does not).

## What is and is NOT formalized here

* **IS formalized (deductive):** the general identity `shadow_decay_charFun`; the resist corollary
  from the *named* hypothesis `‖charFun μ‖ → 0`; the determine corollary from the *named* hypotheses
  `Integrable id μ ∧ ∫ x ∂μ = 0`; and the proof that the **Gaussian discharges both** (so the
  `ShadowDecay` results are recovered as the `μ = N(0,1)` instance).

* **Proved in sibling pillars (built after this file):** the **Cauchy separator** is now a theorem
  in `Sundogcert.ShadowDecayCauchy` — it discharges the resist hypothesis by Riemann–Lebesgue
  (`cauchy_charFun_tendsto_zero`) and *refutes* the determine hypothesis by a tail comparison with
  `x⁻¹` (`cauchy_no_mean`), giving `cauchy_is_separator : resist ∧ ¬ Integrable id`. The clean
  AC-resist / lattice-survive brackets of the `‖charFun‖ → 0` boundary are in
  `Sundogcert.ShadowDecayLattice`. So the separator the Cauchy witness names is no longer
  empirical-only — it is machine-checked and axiom-clean (build-enforced in `AxiomAudit`).

* **The one residual named wall:** the **exact** Cauchy characteristic function
  `charFun (cauchyMeasure x₀ γ) s = exp(-γ|s|)` (the Poisson kernel) is still *not* proved — only
  its *decay*, which is all the resist condition needs. mathlib has the Poisson kernel in
  `Mathlib.Analysis.Complex.Poisson` but no `charFun_cauchy` lemma; the exact value remains a
  candidate mathlib-upstream. Same honesty as `ShadowDecay`'s imported wall: the mechanism and the
  separator are proved; only the sharper exact-value statement is named.

## References

* `MeasureTheory.charFun_apply_real`, `MeasureTheory.norm_charFun_le_one` — the char. function.
* `MeasureTheory.integral_re` / `integral_im` — pulling `Re`/`Im` through a Bochner integral.
* `ProbabilityTheory.charFun_gaussianReal` — discharges the Gaussian resist hypothesis.
* Lukacs, *Characteristic Functions*; Debye (1913) / Waller (1923); the Riemann–Lebesgue lemma.
-/

namespace Sundog.ShadowDecayGeneral

open MeasureTheory ProbabilityTheory Complex Filter Topology
open Sundog.ShadowDecay
open scoped Real

/-! ## The general identity — averaging factors through `charFun μ` for ANY population. -/

/-- The fringe cosine `x ↦ cos (s x)` is integrable against any finite measure (real part of the
bounded integrand `exp(s x I)`). The `μ`-general form of `integrable_cos_gaussian`. -/
lemma integrable_cos (μ : Measure ℝ) [IsFiniteMeasure μ] (s : ℝ) :
    Integrable (fun x : ℝ => Real.cos (s * x)) μ :=
  (integrable_cexp_mul_I μ s).re.congr (Filter.Eventually.of_forall fun x => re_cexp_mul_I s x)

/-- The fringe sine `x ↦ sin (s x)` is integrable against any finite measure. -/
lemma integrable_sin (μ : Measure ℝ) [IsFiniteMeasure μ] (s : ℝ) :
    Integrable (fun x : ℝ => Real.sin (s * x)) μ :=
  (integrable_cexp_mul_I μ s).im.congr (Filter.Eventually.of_forall fun x => im_cexp_mul_I s x)

/-- `∫ cos (s x) ∂μ` is the **real part** of the characteristic function `charFun μ s`. -/
lemma integral_cos_charFun (μ : Measure ℝ) [IsFiniteMeasure μ] (s : ℝ) :
    ∫ x, Real.cos (s * x) ∂μ = (charFun μ s).re := by
  have hint := integrable_cexp_mul_I μ s
  have h1 : (charFun μ s).re = ∫ x, RCLike.re (Complex.exp (↑s * ↑x * I)) ∂μ := by
    rw [charFun_apply_real, ← RCLike.re_to_complex, integral_re hint]
  rw [h1]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (re_cexp_mul_I s x).symm)

/-- `∫ sin (s x) ∂μ` is the **imaginary part** of the characteristic function `charFun μ s`. -/
lemma integral_sin_charFun (μ : Measure ℝ) [IsFiniteMeasure μ] (s : ℝ) :
    ∫ x, Real.sin (s * x) ∂μ = (charFun μ s).im := by
  have hint := integrable_cexp_mul_I μ s
  have h1 : (charFun μ s).im = ∫ x, RCLike.im (Complex.exp (↑s * ↑x * I)) ∂μ := by
    rw [charFun_apply_real, ← RCLike.im_to_complex, integral_im hint]
  rw [h1]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (im_cexp_mul_I s x).symm)

/--
**The general averaging law (cos/sin form).** For ANY probability measure `μ`, the ensemble-averaged
continuous signature factors through the characteristic function of the averaging population:
`∫ cos(2π(c + λ x) t) ∂μ = cos(2π c t)·Re[charFun μ (2π λ t)] − sin(2π c t)·Im[charFun μ (2π λ t)]`.

Derivation: with `A = 2π c t`, `s = 2π λ t`, expand `cos(A + s x) = cos A cos(s x) − sin A sin(s x)`
and average; `∫ cos(s x) = Re charFun`, `∫ sin(s x) = Im charFun` (`integral_cos/sin_charFun`). -/
theorem shadow_decay_general (μ : Measure ℝ) [IsProbabilityMeasure μ] (c lam t : ℝ) :
    ∫ x, Real.cos (2 * Real.pi * (c + lam * x) * t) ∂μ
      = Real.cos (2 * Real.pi * c * t) * (charFun μ (2 * Real.pi * lam * t)).re
        - Real.sin (2 * Real.pi * c * t) * (charFun μ (2 * Real.pi * lam * t)).im := by
  set A : ℝ := 2 * Real.pi * c * t with hA
  set s : ℝ := 2 * Real.pi * lam * t with hs
  have hpt : ∀ x : ℝ, 2 * Real.pi * (c + lam * x) * t = A + s * x := by
    intro x; rw [hA, hs]; ring
  simp_rw [hpt]
  have hsplit : ∀ x : ℝ,
      Real.cos (A + s * x) = Real.cos A * Real.cos (s * x) - Real.sin A * Real.sin (s * x) :=
    fun x => Real.cos_add _ _
  simp_rw [hsplit]
  rw [integral_sub ((integrable_cos μ s).const_mul _) ((integrable_sin μ s).const_mul _),
    integral_const_mul, integral_const_mul, integral_cos_charFun, integral_sin_charFun]

/--
**The general averaging law (characteristic-function form) — the headline.** For any probability
measure `μ`, `∫ cos(2π(c + λ x) t) ∂μ = Re[ exp(2π i c t) · charFun μ (2π λ t) ]`. The averaged
shadow is the real part of the undamped phasor `exp(2π i c t)` scaled by the population's
characteristic function — the determine/resist behavior is entirely encoded in `charFun μ`. -/
theorem shadow_decay_charFun (μ : Measure ℝ) [IsProbabilityMeasure μ] (c lam t : ℝ) :
    ∫ x, Real.cos (2 * Real.pi * (c + lam * x) * t) ∂μ
      = (Complex.exp (((2 * Real.pi * c * t : ℝ) : ℂ) * I)
          * charFun μ (2 * Real.pi * lam * t)).re := by
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  exact shadow_decay_general μ c lam t

/-- **Consistency lock — the general law recovers `ShadowDecay.debye_waller`.** Specializing the
general law's `charFun` form to `μ = N(0,1)` reproduces the proven Gaussian Debye–Waller RHS:
`Re charFun = exp(-2π²λ²t²)` and `Im charFun = 0`. Routed through the common integral, so any drift
between the abstract statement and the proven Gaussian instance is a kernel-caught contradiction. -/
theorem general_recovers_debye_waller (c lam t : ℝ) :
    Real.cos (2 * Real.pi * c * t) * (charFun stdGaussian (2 * Real.pi * lam * t)).re
        - Real.sin (2 * Real.pi * c * t) * (charFun stdGaussian (2 * Real.pi * lam * t)).im
      = Real.cos (2 * Real.pi * c * t)
          * Real.exp (-2 * Real.pi ^ 2 * lam ^ 2 * t ^ 2) := by
  rw [← shadow_decay_general stdGaussian c lam t]
  exact debye_waller c lam t

/-! ## RESIST — governed by decay of `‖charFun μ‖` (Riemann–Lebesgue), not by variance. -/

/--
**RESISTANCE (general).** If the averaging population's characteristic function decays,
`‖charFun μ s‖ → 0` as `s → ∞` (the Riemann–Lebesgue property of any absolutely-continuous `μ`),
then for any fixed forward probe `t > 0` the averaged continuous signature washes out as the spread
grows: `∫ cos(2π(c + λ x) t) ∂μ → 0` as `λ → ∞`. The bound is `|shadow| ≤ ‖charFun μ (2π λ t)‖`
(the phasor has unit modulus), so resistance is exactly the charFun decay, independent of moments.
-/
theorem resistance_general (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hRL : Tendsto (fun s : ℝ => ‖charFun μ s‖) atTop (𝓝 0))
    (c t : ℝ) (ht : 0 < t) :
    Tendsto (fun lam : ℝ => ∫ x, Real.cos (2 * Real.pi * (c + lam * x) * t) ∂μ) atTop (𝓝 0) := by
  have harg : Tendsto (fun lam : ℝ => 2 * Real.pi * lam * t) atTop atTop := by
    have hc : (0 : ℝ) < 2 * Real.pi * t := by positivity
    refine (Tendsto.const_mul_atTop hc tendsto_id).congr (fun lam => by simp only [id_eq]; ring)
  have hg : Tendsto (fun lam : ℝ => ‖charFun μ (2 * Real.pi * lam * t)‖) atTop (𝓝 0) :=
    hRL.comp harg
  refine squeeze_zero_norm (fun lam => ?_) hg
  rw [shadow_decay_charFun μ c lam t, Real.norm_eq_abs]
  calc |(Complex.exp (((2 * Real.pi * c * t : ℝ) : ℂ) * I)
            * charFun μ (2 * Real.pi * lam * t)).re|
      ≤ ‖Complex.exp (((2 * Real.pi * c * t : ℝ) : ℂ) * I)
            * charFun μ (2 * Real.pi * lam * t)‖ := abs_re_le_norm _
    _ = ‖charFun μ (2 * Real.pi * lam * t)‖ := by
        rw [norm_mul, norm_exp_ofReal_mul_I, one_mul]

/-- **The Gaussian discharges the resist hypothesis.** `‖charFun N(0,1) s‖ = exp(-s²/2) → 0`, so the
standard normal is absolutely-continuous-with-decaying-charFun and `resistance_general` applies —
recovering `ShadowDecay.resistance`. -/
theorem gaussian_charFun_tendsto_zero :
    Tendsto (fun s : ℝ => ‖charFun stdGaussian s‖) atTop (𝓝 0) := by
  have hnorm : ∀ s : ℝ, ‖charFun stdGaussian s‖ = Real.exp (-s ^ 2 / 2) := by
    intro s
    have hc : charFun stdGaussian s = Complex.exp (((-s ^ 2 / 2 : ℝ) : ℂ)) := by
      rw [charFun_apply_real]; exact integral_cexp_stdGaussian s
    rw [hc, Complex.norm_exp, Complex.ofReal_re]
  simp_rw [hnorm]
  have hsq : Tendsto (fun s : ℝ => s ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have hbot : Tendsto (fun s : ℝ => -s ^ 2 / 2) atTop atBot := by
    have := (hsq.const_mul_atTop (show (0:ℝ) < 1/2 by norm_num))
    refine (tendsto_neg_atBot_iff.mpr this).congr (fun s => by ring)
  exact Real.tendsto_exp_atBot.comp hbot

/-- **The Gaussian resists** — the abstract law applied to `μ = N(0,1)` reproduces `ShadowDecay`'s
continuous wash-out, now as a corollary of charFun decay. -/
theorem gaussian_resists (c t : ℝ) (ht : 0 < t) :
    Tendsto (fun lam : ℝ => ∫ x, Real.cos (2 * Real.pi * (c + lam * x) * t) ∂stdGaussian)
      atTop (𝓝 0) :=
  resistance_general stdGaussian gaussian_charFun_tendsto_zero c t ht

/-! ## DETERMINE — governed by a finite centered mean (a SEPARATE condition). -/

/--
**DETERMINATION (general).** A shared label `d` carried identically by every unit survives averaging
exactly — `∫ (d + λ c x) ∂μ = d` — provided the population has an **integrable, centered** spread
(`Integrable id μ` and `∫ x ∂μ = 0`). This is the determine condition: it asks for a finite first
moment, which is logically independent of the resist condition `‖charFun μ‖ → 0`. (The Cauchy
population satisfies resist but FAILS this — it has no mean.) -/
theorem determination_general (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : ℝ => x) μ) (hmean : ∫ x, x ∂μ = 0) (d lam c : ℝ) :
    ∫ x, (d + lam * c * x) ∂μ = d := by
  rw [integral_add (integrable_const d) (hint.const_mul (lam * c)),
    integral_const, integral_const_mul, hmean]
  simp

/-- **The Gaussian determines** — discharges the finite-centered-mean condition
(`gaussian_mean_zero`, `IsGaussian.integrable_id`), recovering `ShadowDecay.determination`. -/
theorem gaussian_determines (d lam c : ℝ) :
    ∫ x, (d + lam * c * x) ∂stdGaussian = d :=
  determination_general stdGaussian
    (by unfold stdGaussian; exact IsGaussian.integrable_id) gaussian_mean_zero d lam c

/--
**THE DICHOTOMY, made explicit.** The Gaussian discharges BOTH spectral conditions — charFun decay
(resist) and finite centered mean (determine). They are stated as *separate* hypotheses precisely
because they are different facts about `μ`: `resistance_general` needs only the first, and
`determination_general` needs only the second. The Cauchy population (future work) discharges the
first but not the second, witnessing that neither implies the other. -/
theorem gaussian_resist_and_determine :
    (Tendsto (fun s : ℝ => ‖charFun stdGaussian s‖) atTop (𝓝 0))
      ∧ (Integrable (fun x : ℝ => x) stdGaussian ∧ ∫ x, x ∂stdGaussian = 0) :=
  ⟨gaussian_charFun_tendsto_zero,
   ⟨by unfold stdGaussian; exact IsGaussian.integrable_id, gaussian_mean_zero⟩⟩

end Sundog.ShadowDecayGeneral

-- Axiom audit: the general law and all corollaries should depend only on mathlib's foundational
-- axioms (`propext`, `Classical.choice`, `Quot.sound`) — NO `sorryAx`.
