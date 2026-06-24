/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Gauge-invariant circulation — the Aharonov–Bohm "exact-but-topological" core

A standalone, machine-checked formalization of the **gauge-invariance** at the heart of
the Aharonov–Bohm effect and Faraday's law of induction (Aharonov & Bohm 1959; standard
electromagnetism, Jackson / Griffiths; fully public, textbook material).

A fourth worked example of the discipline used elsewhere in this cert collection:
**machine-check a deductive core, name the imported wall.** The first three are
finite-field algebra (a parity-check map), real-analysis Gaussian averaging (a
Debye–Waller damping), and geometric optics (the minimum-deviation prism); this is the
vector-calculus / topology sibling.

## What is PROVED here (the deductive core)

The observable Aharonov–Bohm phase is the line integral of the vector potential `A`
around a CLOSED loop. A gauge transformation `A → A + grad χ` shifts this observable by
the circulation of a **gradient field** around the loop. The core theorem is that this
circulation is **zero**:

For a `C¹` gauge function `χ : E → ℝ` (`E` a real inner-product space) and a `C¹` closed
loop `γ : ℝ → E` with `γ 0 = γ 1`,

  `∫ t in 0..1, deriv (fun t => χ (γ t)) t = 0`.

The proof is the fundamental theorem of calculus on the composite `χ ∘ γ`:
`∫₀¹ (χ ∘ γ)' = (χ ∘ γ)(1) − (χ ∘ γ)(0) = χ (γ 1) − χ (γ 0) = 0`, the last step by the
closed-loop hypothesis `γ 0 = γ 1`. This is the topological "zero-out": the gauge term
contributes nothing to the loop observable, so the observable depends only on the enclosed
flux, never on the gauge choice.

We prove:

* `gauge_circulation_zero` (THE CORE) — the gradient/gauge circulation around the closed
  loop vanishes, via `intervalIntegral.integral_deriv_eq_sub` plus `γ 0 = γ 1`.
* `gauge_integrand_eq` (PHYSICAL / faithfulness) — the chain rule identifying the abstract
  integrand with the physical `⟨grad χ (γ t), γ'(t)⟩`: the line-element pairing
  `⟨∇χ, dℓ⟩` that the circulation integral really is.
* `gauge_invariant_loop` (COROLLARY) — adding the gradient/gauge contribution leaves the
  closed-loop integral of any base field unchanged: `∫ (A-contrib + gauge-contrib)
  = ∫ A-contrib`. The Aharonov–Bohm observable is gauge-invariant.

## The IMPORTED WALL (named, NOT proved here)

The pure circulation geometry above is what this module certifies. The following are
physical facts taken as given, NOT derived:

* that the physical **vector potential** `A` enters the observable as a line integral
  around the loop;
* that `grad χ` is exactly the **gauge freedom** `A → A + grad χ` of electromagnetism;
* that the observable **Aharonov–Bohm phase** (equivalently the loop EMF in Faraday's law)
  IS this loop integral of `A`;
* that the loop is **closed around the enclosed flux** `Φ`, so the surviving,
  gauge-independent observable is the topological period (the `H¹` flux `Φ`), not the
  gauge potential itself.

The method proves the gauge-invariance geometry — that a gradient's closed-loop
circulation is zero. That nature realizes this as the Aharonov–Bohm effect / Faraday's law
is named, not proved.
-/

namespace Sundog.FaradayAB

open MeasureTheory intervalIntegral
open scoped RealInnerProductSpace Gradient

-- The ambient field `E` is a real inner-product space (complete, so the Riesz gradient
-- `∇` exists). `χ : E → ℝ` is the scalar gauge function; `γ : ℝ → E` is the loop.
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- **THE DEDUCTIVE CORE — gauge / gradient circulation around a closed loop is zero.**

For a `C¹` gauge function `χ : E → ℝ` and a `C¹` closed loop `γ` with `γ 0 = γ 1`, the
circulation of the gauge term `grad χ` around the loop — written here in potential form as
the integral of the derivative of `χ ∘ γ` over `[0,1]` — vanishes:

  `∫ t in 0..1, deriv (fun t => χ (γ t)) t = 0`.

Proof: `χ ∘ γ` is `C¹` (composition of `C¹` maps), so it is differentiable on `[0,1]` and
its derivative is continuous, hence interval-integrable. The fundamental theorem of
calculus (`intervalIntegral.integral_deriv_eq_sub`) gives `(χ ∘ γ)(1) − (χ ∘ γ)(0)`, which
is `χ (γ 1) − χ (γ 0) = 0` by the closed-loop hypothesis `γ 0 = γ 1`.

This is the topological "zero-out": the gauge contribution to the loop observable is
exactly zero, so the Aharonov–Bohm phase depends only on the enclosed flux, not the gauge.

(The core needs no completeness of `E`: it is pure FTC on the scalar potential `χ ∘ γ`.
Completeness is only required for the Riesz `∇` in the faithfulness lemma below.) -/
theorem gauge_circulation_zero {χ : E → ℝ} {γ : ℝ → E}
    (hχ : ContDiff ℝ 1 χ) (hγ : ContDiff ℝ 1 γ) (hloop : γ 0 = γ 1) :
    ∫ t in (0 : ℝ)..1, deriv (fun t => χ (γ t)) t = 0 := by
  -- the composite loop potential `f t = χ (γ t)` is `C¹`
  have hcomp : ContDiff ℝ 1 (fun t => χ (γ t)) := hχ.comp hγ
  -- `C¹` ⟹ differentiable everywhere, in particular on `[[0,1]]`
  have hdiff : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ (fun t => χ (γ t)) x :=
    fun x _ => (hcomp.differentiable (by norm_num)).differentiableAt
  -- `C¹` ⟹ its derivative is continuous, hence interval-integrable on `0..1`
  have hcont : Continuous (deriv (fun t => χ (γ t))) := hcomp.continuous_deriv (le_refl 1)
  have hint : IntervalIntegrable (deriv (fun t => χ (γ t))) volume 0 1 :=
    hcont.intervalIntegrable 0 1
  -- FTC: the integral telescopes to the endpoint difference
  rw [integral_deriv_eq_sub hdiff hint]
  -- closed loop: `χ (γ 1) − χ (γ 0) = 0` because `γ 0 = γ 1`
  rw [hloop]
  ring

/-- **PHYSICAL / faithfulness — the integrand is the line-element pairing `⟨∇χ, γ'⟩`.**

The abstract integrand `deriv (fun t => χ (γ t)) t` of the core equals the physical
inner product `⟨grad χ (γ t), γ'(t)⟩` — the `⟨∇χ, dℓ⟩` line-element that the circulation of
the gauge field really is.

Proof: the chain rule (`HasFDerivAt.comp_hasDerivAt`) gives
`deriv (χ ∘ γ) t = fderiv χ (γ t) (γ'(t))`, and the gradient–fderiv Riesz relation
(`inner_gradient_left`) rewrites `fderiv χ (γ t) v = ⟨∇χ (γ t), v⟩`. The differentiability
of `χ` and `γ` are the imported `C¹` hypotheses, carried explicitly. -/
theorem gauge_integrand_eq {χ : E → ℝ} {γ : ℝ → E}
    (hχ : Differentiable ℝ χ) (hγ : Differentiable ℝ γ) (t : ℝ) :
    deriv (fun t => χ (γ t)) t = ⟪∇ χ (γ t), deriv γ t⟫ := by
  -- chain rule at `t`: `γ` has derivative `deriv γ t`, `χ` has Fréchet deriv at `γ t`
  have hγt : HasDerivAt γ (deriv γ t) t := (hγ t).hasDerivAt
  have hχt : HasFDerivAt χ (fderiv ℝ χ (γ t)) (γ t) := (hχ (γ t)).hasFDerivAt
  have hchain : HasDerivAt (fun t => χ (γ t))
      (fderiv ℝ χ (γ t) (deriv γ t)) t :=
    hχt.comp_hasDerivAt t hγt
  -- read off `deriv (χ ∘ γ) t = fderiv χ (γ t) (γ' t)`
  rw [hchain.deriv]
  -- Riesz: `fderiv χ x v = ⟨∇χ x, v⟩`
  rw [inner_gradient_left]

omit [CompleteSpace E] in
/-- **COROLLARY — the Aharonov–Bohm loop observable is gauge-invariant.**

Let `Aint : ℝ → ℝ` be the integrand contribution of any base field `A` along the loop, and
`χ` a `C¹` gauge function on a `C¹` closed loop `γ`. Adding the gauge contribution
`deriv (χ ∘ γ)` to the integrand leaves the closed-loop integral unchanged:

  `∫₀¹ (Aint t + deriv (fun t => χ (γ t)) t) dt = ∫₀¹ Aint t dt`.

The added gauge term integrates to zero by `gauge_circulation_zero`, so the loop observable
(the Aharonov–Bohm phase / loop EMF) is independent of the gauge choice `A → A + grad χ`. -/
theorem gauge_invariant_loop {χ : E → ℝ} {γ : ℝ → E} {Aint : ℝ → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hγ : ContDiff ℝ 1 γ) (hloop : γ 0 = γ 1)
    (hA : IntervalIntegrable Aint volume 0 1) :
    ∫ t in (0 : ℝ)..1, (Aint t + deriv (fun t => χ (γ t)) t)
      = ∫ t in (0 : ℝ)..1, Aint t := by
  -- the gauge term is interval-integrable (its derivative is continuous, as in the core)
  have hcomp : ContDiff ℝ 1 (fun t => χ (γ t)) := hχ.comp hγ
  have hcont : Continuous (deriv (fun t => χ (γ t))) := hcomp.continuous_deriv (le_refl 1)
  have hgauge : IntervalIntegrable (deriv (fun t => χ (γ t))) volume 0 1 :=
    hcont.intervalIntegrable 0 1
  -- split the integral of the sum, then kill the gauge term via the core
  rw [integral_add hA hgauge, gauge_circulation_zero hχ hγ hloop, add_zero]

/-!
## The topological closure — the surviving observable IS the enclosed flux

The gauge half above shows the gauge term washes out of the closed-loop observable. This
second half names the surviving observable: it is the enclosed flux (the topological
period of the loop), realized as the winding/residue integral of the flux-line field.

The Aharonov–Bohm vector potential of an infinitely thin flux line through the point `c`
is, in complex form, the vortex field `z ↦ (z - c)⁻¹` (up to the real factor `Φ/2π`; with
`A = (Φ/2π) grad θ` and `θ = arg (z - c)`). Its line integral around an enclosing circle is
the topological flux count `2πi`, the SAME for every radius `R > 0`: it depends only on the
enclosed singularity (the flux), never on the chosen path. That is "exact-but-topological":
the observable equals the enclosed flux / `H¹` period, and is path-independent.

### The IMPORTED WALL (named, NOT proved here)

* that the vortex field `z ↦ (z - c)⁻¹` is the physical Aharonov–Bohm / flux-line vector
  potential of a flux line through `c`;
* that the value `2πi` encodes the enclosed flux `Φ` (the topological `H¹` period of the
  punctured plane), in units where `Φ` is read off from the winding factor;
* that the physical observable is the real circulation of the potential around the loop.

The method proves the contour-integral / winding identity below. That nature realizes the
value `2πi` as the enclosed Aharonov–Bohm flux is named here, not proved.
-/

open Complex
open scoped Real

/-- **THE TOPOLOGICAL CLOSURE — the loop integral of the flux-line field equals the flux.**

The line integral of the Aharonov–Bohm vortex field `z ↦ (z - c)⁻¹` around the circle
`C(c, R)` of any positive radius `R` is the topological flux count `2 * π * I`:

  `(∮ z in C(c, R), (z - c)⁻¹) = 2 * π * I`.

Proof: the pole `c` lies inside the enclosing circle (`Metric.mem_ball_self hR`, valid since
`R > 0`), so the residue identity `circleIntegral.integral_sub_inv_of_mem_ball` applies with
`w = c`, giving the winding value `2 * π * I`.

This is the surviving, gauge-independent observable of the Aharonov–Bohm effect: the
enclosed flux, read off as the `H¹` period of the punctured plane. -/
theorem loop_integral_eq_flux (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (∮ z in C(c, R), (z - c)⁻¹) = 2 * π * I :=
  circleIntegral.integral_sub_inv_of_mem_ball (Metric.mem_ball_self hR)

/-- **PATH-INDEPENDENCE — the loop value depends only on the enclosed flux, not the radius.**

For any two positive radii `R₁, R₂`, the flux-line field has the SAME loop integral around
`C(c, R₁)` and `C(c, R₂)`:

  `(∮ z in C(c, R₁), (z - c)⁻¹) = (∮ z in C(c, R₂), (z - c)⁻¹)`.

Proof: both sides equal `2 * π * I` by `loop_integral_eq_flux`. The observable is therefore
a topological invariant of the loop class around the flux — "exact-but-topological": it sees
only the enclosed singularity (the flux / `H¹` period), never the chosen path. -/
theorem loop_integral_path_independent (c : ℂ) {R₁ R₂ : ℝ}
    (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) :
    (∮ z in C(c, R₁), (z - c)⁻¹) = ∮ z in C(c, R₂), (z - c)⁻¹ :=
  (loop_integral_eq_flux c hR₁).trans (loop_integral_eq_flux c hR₂).symm

end Sundog.FaradayAB

-- Axiom audit: the deductive core and its corollary should depend only on mathlib's
-- foundational axioms (`propext`, `Classical.choice`, `Quot.sound`) — NO `sorryAx`.

-- Axiom audit for the topological closure (loop = enclosed flux): same foundational
-- axioms only (`propext`, `Classical.choice`, `Quot.sound`) — NO `sorryAx`.
