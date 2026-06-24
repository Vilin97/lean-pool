/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Lossy averaging — a continuous signal resists, a shared discrete label survives

A second worked example of the discipline in `Sundogcert.Certificate`: **machine-check a deductive
core, name the imported wall.** The certificate's lossiness is finite-field algebra (a parity-check
shadow loses a secret); this is its real-analysis sibling. A lossy *averaging* shadow **washes a
continuous variable** (a Gaussian / Debye–Waller decay) while **keeping a shared discrete label**
(exact, at every spread `λ`) — both halves of the dichotomy, proved.

## What is and is NOT formalized

* **IS formalized (deductive):** the Gaussian-averaging decay. If a population of units carries a
  continuous fringe signal `cos(2π c t)` and the frequency `c` is spread Gaussianly,
  `c_i = c⋆ + λ ξ_i` with `ξ ∼ N(0,1)`, then the ensemble-averaged shadow is
  `S(t) = cos(2π c⋆ t) · exp(-2π² λ² t²)`. The damping `exp(-2π² λ² t²)` is the **Debye–Waller**
  factor: `1` at `λ = 0` (no loss, `c⋆` recoverable), tending to `0` as `λ → ∞` for any probe
  `t ≠ 0` (the continuous signal is washed out — it RESISTS recovery from the averaged shadow).

* **NOT formalized (the imported wall):** that a *real* system instantiates this structure — a
  genuine population with an honest lossiness knob `λ` — is a modeling assumption, not a theorem.
  It is the analogue of the certificate's imported hardness: the mechanism is proved; that the world
  realizes it is named, not proved.

* **ALSO formalized (the determination half):** a shared discrete label carried identically by every
  unit survives the same averaging EXACTLY, at every spread `λ` (`determination`) — the per-unit
  zero-mean noise averages out. Lossy averaging keeps the discrete and washes the continuous.

## The one imported analytic input

The CORE (`gaussianCos_integral`) is **PROVED from mathlib**, not assumed: it is the real part
of the standard-normal characteristic function `charFun (gaussianReal 0 1) s = exp(-s²/2)`
(`ProbabilityTheory.charFun_gaussianReal`). Everything else is elementary algebra plus one limit;
there are no axioms beyond mathlib's.

## References

* `ProbabilityTheory.charFun_gaussianReal` — characteristic function of `N(μ, v)`.
* `MeasureTheory.charFun_apply_real` — `charFun μ t = ∫ x, exp(t x I) ∂μ`.
* `MeasureTheory.integral_re` / `integral_im` — pulling `Re` / `Im` through a Bochner integral.
-/

namespace Sundog.ShadowDecay

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped Real

/-- The **standard normal** measure `N(0,1)` on `ℝ`. The averaging population's spread variable
`ξ` is distributed according to `stdGaussian`. -/
noncomputable def stdGaussian : Measure ℝ := gaussianReal 0 1

instance : IsProbabilityMeasure stdGaussian := by
  unfold stdGaussian; infer_instance

/-- The integrand `x ↦ exp(s x I)` of the characteristic function is integrable against any finite
measure: it is continuous and bounded by `1` in norm. -/
lemma integrable_cexp_mul_I (μ : Measure ℝ) [IsFiniteMeasure μ] (s : ℝ) :
    Integrable (fun x : ℝ => Complex.exp (↑s * ↑x * I)) μ := by
  refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun x => ?_)
  have hsx : (↑s * ↑x : ℂ) = ((s * x : ℝ) : ℂ) := by push_cast; ring
  rw [hsx, norm_exp_ofReal_mul_I]

/-- Pointwise: the real part of the characteristic-function integrand is the fringe cosine. -/
lemma re_cexp_mul_I (s x : ℝ) :
    RCLike.re (Complex.exp (↑s * ↑x * I)) = Real.cos (s * x) := by
  have hsx : (↑s * ↑x : ℂ) = ((s * x : ℝ) : ℂ) := by push_cast; ring
  rw [hsx, RCLike.re_to_complex, exp_ofReal_mul_I_re]

/-- Pointwise: the imaginary part of the characteristic-function integrand is the fringe sine. -/
lemma im_cexp_mul_I (s x : ℝ) :
    RCLike.im (Complex.exp (↑s * ↑x * I)) = Real.sin (s * x) := by
  have hsx : (↑s * ↑x : ℂ) = ((s * x : ℝ) : ℂ) := by push_cast; ring
  rw [hsx, RCLike.im_to_complex, exp_ofReal_mul_I_im]

/-- The fringe integrand `x ↦ cos (s x)` is integrable against the standard Gaussian: it is the real
part of an integrable bounded function (used by `debye_waller`). -/
lemma integrable_cos_gaussian (s : ℝ) :
    Integrable (fun x : ℝ => Real.cos (s * x)) stdGaussian := by
  have h := (integrable_cexp_mul_I stdGaussian s).re
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  exact re_cexp_mul_I s x

/-- The fringe integrand `x ↦ sin (s x)` is integrable against the standard Gaussian: it is the
imaginary part of an integrable bounded function (used by `debye_waller`). -/
lemma integrable_sin_gaussian (s : ℝ) :
    Integrable (fun x : ℝ => Real.sin (s * x)) stdGaussian := by
  have h := (integrable_cexp_mul_I stdGaussian s).im
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  exact im_cexp_mul_I s x

/-- Helper: the integral identity `∫ x, exp(s x I) ∂N(0,1) = exp(-s²/2)` (the complex
characteristic function specialized to the standard normal). -/
lemma integral_cexp_stdGaussian (s : ℝ) :
    ∫ x, Complex.exp (↑s * ↑x * I) ∂stdGaussian = Complex.exp (((-s ^ 2 / 2 : ℝ) : ℂ)) := by
  have hcf : charFun stdGaussian s = Complex.exp (((-s ^ 2 / 2 : ℝ) : ℂ)) := by
    unfold stdGaussian
    rw [charFun_gaussianReal]
    congr 1
    push_cast
    ring
  rwa [charFun_apply_real] at hcf

/--
**CORE (make-or-break) — the Gaussian characteristic function, real part.**

The standard-normal expectation of `cos (s ξ)` equals `exp(-s² / 2)`:
`∫ x, cos (s x) ∂N(0,1) = exp(-s² / 2)`.

This is the real part of the standard-normal characteristic function
`E[exp(I s ξ)] = exp(-s² / 2)` (`ProbabilityTheory.charFun_gaussianReal` at `μ = 0`, `v = 1`).
**PROVED from mathlib** — this is the single imported analytic fact, and it is a derived theorem,
not an axiom. -/
theorem gaussianCos_integral (s : ℝ) :
    ∫ x, Real.cos (s * x) ∂stdGaussian = Real.exp (-s ^ 2 / 2) := by
  have hcf := integral_cexp_stdGaussian s
  have hint := integrable_cexp_mul_I stdGaussian s
  -- Take the real part of both sides of the integral identity.
  have hre : RCLike.re (∫ x, Complex.exp (↑s * ↑x * I) ∂stdGaussian)
      = RCLike.re (Complex.exp (((-s ^ 2 / 2 : ℝ) : ℂ))) := by rw [hcf]
  -- LHS: pull `Re` inside the integral, then `Re (exp (s x I)) = cos (s x)`.
  rw [← integral_re hint] at hre
  -- RHS: `Re (exp (↑(-s²/2))) = exp(-s²/2)`.
  rw [RCLike.re_to_complex, Complex.exp_ofReal_re] at hre
  rw [← hre]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact (re_cexp_mul_I s x).symm

/--
**The sin signature averages to zero** (odd-function / imaginary-part companion of the CORE).

`∫ x, sin (s x) ∂N(0,1) = 0`. It is the imaginary part of the standard-normal characteristic
function `exp(-s²/2)`, whose argument is real, so the imaginary part vanishes. This is the term that
drops out of `cos(A + B) = cos A cos B - sin A sin B` after averaging. -/
theorem gaussianSin_integral (s : ℝ) :
    ∫ x, Real.sin (s * x) ∂stdGaussian = 0 := by
  have hcf := integral_cexp_stdGaussian s
  have hint := integrable_cexp_mul_I stdGaussian s
  have him : RCLike.im (∫ x, Complex.exp (↑s * ↑x * I) ∂stdGaussian)
      = RCLike.im (Complex.exp (((-s ^ 2 / 2 : ℝ) : ℂ))) := by rw [hcf]
  rw [← integral_im hint] at him
  rw [RCLike.im_to_complex, Complex.exp_ofReal_im] at him
  rw [← him]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact (im_cexp_mul_I s x).symm

/--
**DEBYE_WALLER — the ensemble-averaged continuous signature.**

Averaging the continuous fringe `cos (2π (c + λ ξ) t)` over the standard-normal population spread
`ξ ∼ N(0,1)` factors into the undamped signature times the Debye–Waller damping:
`∫ x, cos (2π (c + λ x) t) ∂N(0,1) = cos (2π c t) · exp(-2π² λ² t²)`.

Derivation: with `A = 2π c t` and `s = 2π λ t`, `cos (A + s x) = cos A cos (s x) - sin A sin (s x)`.
The `cos (s x)` term averages to `exp(-s²/2) = exp(-2π² λ² t²)` (the CORE) and the `sin (s x)` term
averages to `0` (`gaussianSin_integral`). -/
theorem debye_waller (c lam t : ℝ) :
    ∫ x, Real.cos (2 * Real.pi * (c + lam * x) * t) ∂stdGaussian
      = Real.cos (2 * Real.pi * c * t) * Real.exp (-2 * Real.pi ^ 2 * lam ^ 2 * t ^ 2) := by
  set A : ℝ := 2 * Real.pi * c * t with hA
  set s : ℝ := 2 * Real.pi * lam * t with hs
  have hpt : ∀ x : ℝ, 2 * Real.pi * (c + lam * x) * t = A + s * x := by
    intro x; rw [hA, hs]; ring
  simp_rw [hpt]
  have hsplit : ∀ x : ℝ,
      Real.cos (A + s * x)
        = Real.cos A * Real.cos (s * x) - Real.sin A * Real.sin (s * x) := by
    intro x; rw [Real.cos_add]
  simp_rw [hsplit]
  rw [integral_sub ((integrable_cos_gaussian s).const_mul _)
      ((integrable_sin_gaussian s).const_mul _),
    integral_const_mul, integral_const_mul, gaussianCos_integral, gaussianSin_integral]
  have hexp : Real.exp (-s ^ 2 / 2) = Real.exp (-2 * Real.pi ^ 2 * lam ^ 2 * t ^ 2) := by
    congr 1; rw [hs]; ring
  rw [hexp]; ring

/--
**RESISTANCE — the continuous signature is washed out as the spread grows.**

For any fixed nonzero probe `t`, the Debye–Waller amplitude vanishes as the population spread
`λ → ∞`: `Tendsto (fun λ => exp(-2π² λ² t²)) atTop (𝓝 0)`. As the lossy averaging widens, the
continuous fringe amplitude → 0 — the continuous hidden variable becomes unrecoverable from the
averaged shadow. -/
theorem resistance (t : ℝ) (ht : t ≠ 0) :
    Tendsto (fun lam : ℝ => Real.exp (-2 * Real.pi ^ 2 * lam ^ 2 * t ^ 2)) atTop (𝓝 0) := by
  have hpos : 0 < 2 * Real.pi ^ 2 * t ^ 2 := by positivity
  -- `λ² → atTop`, hence `(2π²t²)·λ² → atTop`, hence its negation `→ atBot`.
  have hsq : Tendsto (fun lam : ℝ => lam ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have hmul : Tendsto (fun lam : ℝ => 2 * Real.pi ^ 2 * t ^ 2 * lam ^ 2) atTop atTop :=
    hsq.const_mul_atTop hpos
  have hneg : Tendsto
      (fun lam : ℝ => -(2 * Real.pi ^ 2 * t ^ 2 * lam ^ 2)) atTop atBot :=
    tendsto_neg_atBot_iff.mpr hmul
  -- Compose with `exp → 0` at `-∞` and match the exponent algebraically.
  have hcomp := Real.tendsto_exp_atBot.comp hneg
  refine hcomp.congr (fun lam => ?_)
  change Real.exp (-(2 * Real.pi ^ 2 * t ^ 2 * lam ^ 2))
      = Real.exp (-2 * Real.pi ^ 2 * lam ^ 2 * t ^ 2)
  congr 1; ring

/--
**LOSSINESS_ESSENTIAL — without loss, nothing is suppressed.**

At zero spread `λ = 0` the Debye–Waller damping is `exp(0) = 1` (undamped) for every probe `t`: an
un-averaged (injective) shadow loses nothing, so the continuous signature is fully recoverable. It
is precisely the lossiness `λ > 0` that produces the resistance of `resistance`. -/
theorem lossiness_essential (t : ℝ) :
    Real.exp (-2 * Real.pi ^ 2 * (0 : ℝ) ^ 2 * t ^ 2) = 1 := by
  norm_num

/-- Consistency check: `DEBYE_WALLER` at `λ = 0` returns the undamped signature `cos (2π c t)` — the
`LOSSINESS_ESSENTIAL` endpoint, where the continuous `c` is fully recoverable. -/
theorem debye_waller_lossless (c t : ℝ) :
    ∫ x, Real.cos (2 * Real.pi * (c + 0 * x) * t) ∂stdGaussian
      = Real.cos (2 * Real.pi * c * t) := by
  rw [debye_waller c 0 t, lossiness_essential, mul_one]

/-! ## The DETERMINATION half — a shared discrete label survives averaging, at every spread `λ`. -/

/-- The standard normal has mean zero: `∫ x ∂N(0,1) = 0`. The per-unit spread noise is centred. -/
theorem gaussian_mean_zero : ∫ x, x ∂stdGaussian = 0 := by
  unfold stdGaussian
  exact integral_id_gaussianReal

/--
**DETERMINATION — a shared label survives averaging exactly, at every spread `λ`.**

A label `d` carried *identically* by every unit (a shared sign / class, not per-unit noise) is
recovered exactly by the ensemble average: `∫ x, (d + λ c x) ∂N(0,1) = d`, because the per-unit
zero-mean noise `λ c ξ` averages out (`gaussian_mean_zero`). Unlike the continuous Debye–Waller
decay of `resistance`, this is INDEPENDENT of `λ`: the shared label is never washed out — it is
determined at every population spread. -/
theorem determination (d lam c : ℝ) :
    ∫ x, (d + lam * c * x) ∂stdGaussian = d := by
  have hx : Integrable (fun x : ℝ => x) stdGaussian := by
    unfold stdGaussian; exact IsGaussian.integrable_id
  rw [integral_add (integrable_const d) (hx.const_mul (lam * c)),
    integral_const, integral_const_mul, gaussian_mean_zero]
  simp

/--
**The discrete class is determined for ALL `λ`.** Since the shared label is recovered exactly, its
sign (a discrete class) is read off the averaged shadow regardless of the population spread `λ`,
the exact opposite of the continuous variable's Debye–Waller wash-out (`resistance`). -/
theorem determination_sign (d lam c : ℝ) :
    (0 < ∫ x, (d + lam * c * x) ∂stdGaussian) ↔ (0 < d) := by
  rw [determination]

end Sundog.ShadowDecay

-- Axiom audit of the headline results: the CORE and all four target theorems should depend only on
-- mathlib's foundational axioms (`propext`, `Classical.choice`, `Quot.sound`) — NO `sorryAx`.
