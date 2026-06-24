/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import LeanPool.Sundogcert.ShadowDecayGeneral
import LeanPool.Sundogcert.ShadowDecayCauchy
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# The characteristic-function decay is the sharp resist boundary: AC resists, lattice survives

`Sundogcert.ShadowDecayGeneral` proves the determine/resist law and shows that **RESIST** — the
averaged continuous fringe `cos(2π(c + λ x) t)` washes out as the spread `λ → ∞` — is governed by
the single spectral condition

  `‖charFun μ s‖ → 0`   as `s → ∞`   (`resistance_general`),

the **decay of the characteristic function** (the Rajchman / Riemann–Lebesgue condition). This file
shows that condition is the sharp dividing line between two clean families of populations:

* **ABSOLUTELY-CONTINUOUS populations resist.** Any `μ = volume.withDensity f` with `f` an
  integrable density has `‖charFun μ s‖ → 0` by the **Riemann–Lebesgue lemma**
  (`absCont_charFun_tendsto_zero`),
  so it resists (`absCont_resists`). This generalizes the Gaussian, uniform, and Cauchy examples
  (`ShadowDecayCauchy` is the heavy-tailed instance — infinite variance, yet still resists).

* **LATTICE / ATOMIC populations survive.** The symmetric two-point (Rademacher) measure
  `twoPoint a = ½(δ₋ₐ + δₐ)` has characteristic function `charFun = cos(a·)` (`twoPoint_charFun`),
  which **recurs to its supremum `1`** at `t = kπ/|a|` and therefore does NOT decay
  (`twoPoint_does_not_resist`). It fails the hypothesis of `resistance_general`, and concretely
  the averaged shadow `cos(2π c t)·cos(2π λ a t)` recurs to `cos(2π c t) ≠ 0` along `λ = k/(a t)`,
  so the continuous signal **SURVIVES** (`twoPoint_shadow_survives`).

The separation is **orthogonal to variance.** The Cauchy population has *infinite* variance yet
resists (`ShadowDecayCauchy.cauchy_resists`); the bounded two-point has *finite everything* yet
survives. What decides resistance is the charFun spectrum, not any moment.

## What is and is NOT claimed

* **IS proved (deductive, axiom-clean):**
  - `AC ⟹ resist`: one clean direction, via Riemann–Lebesgue (`absCont_resists`).
  - `lattice ⟹ survive`: the other clean direction, via the recurrence of `cos` (the two-point
    `charFun` does not decay, `twoPoint_does_not_resist`; the shadow recurs,
    `twoPoint_shadow_survives`).
  - The capstone `resist_separates_ac_from_lattice`: AC sits on the resist side of the
    `‖charFun‖ → 0` boundary, the two-point sits on the survive side — they bracket it.

## What is NOT claimed (the residual named wall)

We do **NOT** claim `resist ↔ absolutely continuous`. That equivalence is **false**: there exist
*singular-continuous* **Rajchman** measures whose characteristic function decays (so they resist)
despite having no density at all. The honest, provable content is exactly the spectral framing of
`ShadowDecayGeneral` together with its two clean brackets:

  (i)  resist is governed by `‖charFun μ‖ → 0` (the Rajchman/spectral condition — the framing);
  (ii) AC `⟹` resist (Riemann–Lebesgue, proved here);
  (iii) lattice/atomic `⟹` survive (the recurrence of `cos`, proved here).

The **full Rajchman characterization** — precisely which singular measures have decaying
characteristic function — is subtle (it is not captured by absolute continuity, nor by any moment
condition) and is **not formalized**. AC and lattice are the two clean families that *bracket* the
boundary; the exact location of the boundary among singular measures is the named residual.

## References

* `MeasureTheory.charFun_dirac` — the characteristic function of a Dirac mass.
* `Real.zero_at_infty_fourier` — the Riemann–Lebesgue lemma on `ℝ`.
* `Sundogcert.ShadowDecayGeneral.resistance_general` — resist from charFun decay.
* `Sundogcert.ShadowDecayCauchy` — the infinite-variance AC instance (variance-orthogonality).
* Feller, *An Introduction to Probability Theory*, Vol. II (lattice vs. non-lattice laws);
  Lyons, *Seventy years of Rajchman measures* (the residual Rajchman characterization).
-/

namespace Sundog.ShadowDecayLattice

open MeasureTheory ProbabilityTheory Complex Filter Topology
open Sundog.ShadowDecay Sundog.ShadowDecayGeneral
open scoped Real FourierTransform ENNReal NNReal

/-! ## AC SIDE — any absolutely-continuous population resists (Riemann–Lebesgue). -/

/-- The AC population with density `f`: `volume.withDensity (ENNReal.ofReal ∘ f)`. The `withDensity`
of Lebesgue measure by a nonnegative integrable density `f`. We carry `f : ℝ → ℝ` (rather than an
`ℝ≥0∞` density) so the Fourier transform of `(f x : ℂ)` is literally the bridge target. -/
noncomputable def absContMeasure (f : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (f x))

/-- The density of `absContMeasure f`, written so the `withDensity`/Fourier bridge lemmas fire. -/
lemma absContMeasure_eq (f : ℝ → ℝ) :
    absContMeasure f = volume.withDensity (fun x => ENNReal.ofReal (f x)) := rfl

/--
**The AC characteristic function as a Fourier integral.** For a nonnegative density `f`, the
characteristic function of `absContMeasure f` is the Fourier transform of its `L¹` density, sampled
at `-s / (2π)`: `charFun (absContMeasure f) s = 𝓕 (fun x => (f x : ℂ)) (-s/(2π))`.

This is the bridge that lets the Riemann–Lebesgue lemma act on `charFun`. It is the
density-parametric generalization of `ShadowDecayCauchy.charFun_cauchy_eq_fourier`. -/
theorem charFun_absCont_eq_fourier (f : ℝ → ℝ) (hf_meas : Measurable f)
    (hf_nonneg : ∀ x, 0 ≤ f x) (s : ℝ) :
    charFun (absContMeasure f) s = 𝓕 (fun x => (f x : ℂ)) (-s / (2 * Real.pi)) := by
  have hmeas : Measurable (fun x => ENNReal.ofReal (f x)) :=
    ENNReal.measurable_ofReal.comp hf_meas
  rw [charFun_apply_real, absContMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hmeas.aemeasurable
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (hf_nonneg x)]
  rw [real_smul, smul_eq_mul, mul_comm]
  congr 2
  push_cast
  field_simp

/--
**RESIST (the AC charFun decays).** `‖charFun (absContMeasure f) s‖ → 0` as `s → ∞`, for any
nonnegative density `f`. The Fourier transform of `(f x : ℂ)` vanishes at infinity by the
**Riemann–Lebesgue lemma** (`Real.zero_at_infty_fourier`); the sampling point `-s / (2π)` runs to
`-∞` as `s → ∞`, which lies in `cocompact ℝ`. This is the resist condition of the general law, with
**no moment assumed** — it is the spectral (Rajchman/RL) condition alone. -/
theorem absCont_charFun_tendsto_zero (f : ℝ → ℝ) (hf_meas : Measurable f)
    (hf_nonneg : ∀ x, 0 ≤ f x) :
    Tendsto (fun s : ℝ => ‖charFun (absContMeasure f) s‖) atTop (𝓝 0) := by
  -- `-s/(2π) → cocompact ℝ` as `s → ∞` (it runs to `-∞`, and `atBot ≤ cocompact`).
  have hcoco : Tendsto (fun s : ℝ => -s / (2 * Real.pi)) atTop (cocompact ℝ) := by
    rw [cocompact_eq_atBot_atTop]
    refine Tendsto.mono_right ?_ le_sup_left
    have hp : (0:ℝ) < 2 * Real.pi := by positivity
    exact Tendsto.atBot_div_const hp (tendsto_neg_atBot_iff.mpr tendsto_id)
  -- Riemann–Lebesgue: the Fourier transform of the density vanishes at `cocompact`.
  have hRL : Tendsto (fun w : ℝ => 𝓕 (fun x => (f x : ℂ)) w) (cocompact ℝ) (𝓝 0) :=
    Real.zero_at_infty_fourier _
  have hcomp := hRL.comp hcoco
  have hnorm : Tendsto
      (fun s : ℝ => ‖𝓕 (fun x => (f x : ℂ)) (-s / (2 * Real.pi))‖) atTop (𝓝 0) := by
    have := (continuous_norm.tendsto (0:ℂ)).comp hcomp
    simpa [Function.comp_def] using this
  refine hnorm.congr (fun s => ?_)
  rw [charFun_absCont_eq_fourier f hf_meas hf_nonneg s]

/--
**AC RESISTS — the absolutely-continuous-averaged continuous signature washes out.** Feeding the AC
charFun decay to `resistance_general`: for any forward probe `t > 0`, the ensemble average of the
continuous fringe `cos(2π(c + λ x) t)` over an absolutely continuous population
`x ∼ absContMeasure f` tends to `0` as the spread `λ → ∞`. The continuous hidden variable becomes
unrecoverable — every AC population resists. -/
theorem absCont_resists (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x)
    [IsProbabilityMeasure (absContMeasure f)] (c t : ℝ) (ht : 0 < t) :
    Tendsto (fun lam : ℝ => ∫ x, Real.cos (2 * Real.pi * (c + lam * x) * t) ∂absContMeasure f)
      atTop (𝓝 0) :=
  resistance_general (absContMeasure f) (absCont_charFun_tendsto_zero f hf_meas hf_nonneg) c t ht

/-! ## LATTICE SIDE — the symmetric two-point (Rademacher) population survives. -/

/-- The **symmetric two-point (Rademacher) measure** `½(δ₋ₐ + δₐ)`: a fair coin landing on `±a`. A
lattice/atomic population — the archetype of a non-Rajchman law (its charFun is `cos`). -/
noncomputable def twoPoint (a : ℝ) : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac (-a) + (1 / 2 : ℝ≥0∞) • Measure.dirac a

/-- `twoPoint a` is a probability measure: total mass `½ + ½ = 1`. -/
instance instIsProbabilityMeasureTwoPoint (a : ℝ) : IsProbabilityMeasure (twoPoint a) where
  measure_univ := by
    rw [twoPoint, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), Measure.dirac_apply_of_mem (Set.mem_univ _)]
    simp only [smul_eq_mul, mul_one]
    rw [ENNReal.div_add_div_same]
    rw [show (1 : ℝ≥0∞) + 1 = 2 by norm_num, ENNReal.div_self two_ne_zero (by simp)]

/-- Integrating a function bounded in `enorm` against `twoPoint a` evaluates at the two atoms:
`∫ g ∂(twoPoint a) = ½ (g (-a) + g a)`. The `½ + ½` weighting of the two Diracs. We require only
that `g` is bounded at the two atoms (`‖g (±a)‖ₑ < ∞`, always true for `ℂ`/`ℝ`-valued `g`). -/
lemma integral_twoPoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (a : ℝ) (g : ℝ → E) (hgm : StronglyMeasurable g) :
    ∫ x, g x ∂twoPoint a = (1 / 2 : ℝ) • (g (-a) + g a) := by
  have hin : ∀ b : ℝ, Integrable g ((1 / 2 : ℝ≥0∞) • Measure.dirac b) := by
    intro b
    exact (integrable_dirac' hgm (by simp)).smul_measure (by simp)
  rw [twoPoint, integral_add_measure (hin (-a)) (hin a),
    integral_smul_measure, integral_smul_measure, integral_dirac' g _ hgm,
    integral_dirac' g _ hgm]
  have htr : (1 / 2 : ℝ≥0∞).toReal = (1 / 2 : ℝ) := by
    rw [ENNReal.toReal_div]; norm_num
  rw [htr, smul_add]

/--
**The two-point characteristic function is `cos`.** `charFun (twoPoint a) t = cos (a t)` (as a real
cosine, coerced to `ℂ`): the symmetric two-point / Rademacher law has the cosine as its
characteristic function. Computation: `charFun = ½(exp(-i a t) + exp(i a t)) = cos(a t)` by
`charFun_dirac` at the two atoms and Euler's formula. -/
theorem twoPoint_charFun (a t : ℝ) :
    charFun (twoPoint a) t = Complex.cos (↑a * ↑t) := by
  rw [charFun_apply_real]
  have hgm : StronglyMeasurable (fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * I)) := by
    fun_prop
  rw [integral_twoPoint a _ hgm, Complex.real_smul]
  -- the two atoms `±a` give `exp(± i a t)`; `cos z = (exp(z I) + exp(-z I))/2` assembles them.
  rw [Complex.cos]
  have hneg : (t : ℂ) * ((-a : ℝ) : ℂ) * I = -(↑a * ↑t * I) := by push_cast; ring
  have hpos : (t : ℂ) * (a : ℂ) * I = ↑a * ↑t * I := by ring
  rw [hneg, hpos]
  rw [show (-(↑a * ↑t) * I : ℂ) = -(↑a * ↑t * I) by ring]
  rw [show ((1 / 2 : ℝ) : ℂ) = 1 / 2 by norm_num]
  ring

/--
**The two-point `charFun` recurs to its supremum — it does NOT decay.** For `a ≠ 0`,
`¬ Tendsto (fun s => ‖charFun (twoPoint a) s‖) atTop (𝓝 0)`. The characteristic function is
`cos(a s)`, whose modulus returns to `1` at `s = k π / |a|` for every `k`. So the lattice population
**fails** the resist hypothesis of `resistance_general`: it is a non-Rajchman law.

Proof: if `‖charFun (twoPoint a) ·‖ → 0` at `atTop`, then evaluating along the divergent sequence
`s_k = k π / |a|` would give `0`; but there `‖cos(a s_k)‖ = ‖cos(± k π)‖ = 1`, a constant sequence
tending to `1 ≠ 0` — contradiction by uniqueness of limits. -/
theorem twoPoint_does_not_resist (a : ℝ) (ha : a ≠ 0) :
    ¬ Tendsto (fun s : ℝ => ‖charFun (twoPoint a) s‖) atTop (𝓝 0) := by
  intro hT
  -- the recurrence sequence `s_k = k π / |a| → ∞`.
  set u : ℕ → ℝ := fun k => (k : ℝ) * Real.pi / |a| with hu
  have habs : (0:ℝ) < |a| := abs_pos.mpr ha
  have hudiv : Tendsto u atTop atTop := by
    have hpia : (0:ℝ) < Real.pi / |a| := by positivity
    have : Tendsto (fun k : ℕ => (k : ℝ) * (Real.pi / |a|)) atTop atTop :=
      Tendsto.atTop_mul_const hpia tendsto_natCast_atTop_atTop
    refine this.congr (fun k => ?_); rw [hu]; ring
  -- along `u`, the norm is constantly `1`.
  have hval : ∀ k : ℕ, ‖charFun (twoPoint a) (u k)‖ = 1 := by
    intro k
    rw [twoPoint_charFun]
    have harg : (a : ℝ) * u k = (if 0 < a then (k : ℝ) else -(k : ℝ)) * Real.pi := by
      rw [hu]
      rcases lt_or_gt_of_ne ha with h | h
      · rw [if_neg (not_lt.mpr h.le), abs_of_neg h]; field_simp
      · rw [if_pos h, abs_of_pos h]; field_simp
    rw [show ((a : ℝ) : ℂ) * ((u k : ℝ) : ℂ) = (((a * u k : ℝ)) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_cos, Complex.norm_real, harg]
    rcases lt_or_gt_of_ne ha with h | h
    · rw [if_neg (not_lt.mpr h.le), show (-(k : ℝ)) * Real.pi = -((k : ℝ) * Real.pi) by ring,
        Real.cos_neg, Real.cos_nat_mul_pi]
      simp
    · rw [if_pos h, Real.cos_nat_mul_pi]; simp
  -- but the composed limit would be `0`, contradicting the constant `1`.
  have hcomp : Tendsto (fun k : ℕ => ‖charFun (twoPoint a) (u k)‖) atTop (𝓝 0) := hT.comp hudiv
  rw [tendsto_congr hval] at hcomp
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  exact one_ne_zero (tendsto_nhds_unique h1 hcomp)

/-! ## SURVIVE — the two-point shadow recurs and does not wash out. -/

/--
**The two-point averaged shadow factors as a product of cosines (the recurrence relation).** For the
symmetric two-point population, the ensemble-averaged continuous fringe is
`∫ cos(2π(c + λ x) t) ∂(twoPoint a) = cos(2π c t) · cos(2π λ a t)`. The second factor
`cos(2π λ a t)`
oscillates forever in `λ` — it is the recurrence that prevents wash-out. -/
theorem twoPoint_shadow_eq (a c lam t : ℝ) :
    ∫ x, Real.cos (2 * Real.pi * (c + lam * x) * t) ∂twoPoint a
      = Real.cos (2 * Real.pi * c * t) * Real.cos (2 * Real.pi * lam * a * t) := by
  have hgm : StronglyMeasurable
      (fun x : ℝ => Real.cos (2 * Real.pi * (c + lam * x) * t)) := by fun_prop
  rw [integral_twoPoint a _ hgm, smul_eq_mul]
  set A : ℝ := 2 * Real.pi * c * t with hA
  set B : ℝ := 2 * Real.pi * lam * a * t with hB
  have hL : 2 * Real.pi * (c + lam * (-a)) * t = A - B := by rw [hA, hB]; ring
  have hR : 2 * Real.pi * (c + lam * a) * t = A + B := by rw [hA, hB]; ring
  rw [hL, hR, Real.cos_sub, Real.cos_add]
  ring

/--
**SURVIVE — the two-point continuous shadow does NOT wash out.** For `a ≠ 0`, a probe `t > 0`, and a
phase `c` with `cos(2π c t) ≠ 0`, the averaged continuous fringe does not tend to `0` as the spread
`λ → ∞`:
`¬ Tendsto (fun λ => ∫ cos(2π(c + λ x) t) ∂(twoPoint a)) atTop (𝓝 0)`.

The shadow equals `cos(2π c t) · cos(2π λ a t)` (`twoPoint_shadow_eq`); the recurrence factor
returns to `±1` at `λ = k / (a t)`, so the shadow recurs to `± cos(2π c t) ≠ 0` infinitely often
and cannot
converge to `0`. Contrast the AC case (`absCont_resists`), where the shadow washes out: the lattice
population's continuous signal SURVIVES the lossy averaging. -/
theorem twoPoint_shadow_survives (a c t : ℝ) (ha : a ≠ 0) (ht : 0 < t)
    (hc : Real.cos (2 * Real.pi * c * t) ≠ 0) :
    ¬ Tendsto (fun lam : ℝ => ∫ x, Real.cos (2 * Real.pi * (c + lam * x) * t) ∂twoPoint a)
      atTop (𝓝 0) := by
  intro hT
  -- recurrence sequence `λ_k = k / |a t| → +∞`, along which `λ_k · a · t = ± k`.
  have hat : a * t ≠ 0 := mul_ne_zero ha (ne_of_gt ht)
  have habs : (0:ℝ) < |a * t| := abs_pos.mpr hat
  set v : ℕ → ℝ := fun k => (k : ℝ) / |a * t| with hv
  have hvdiv : Tendsto v atTop atTop := by
    have hpos : (0:ℝ) < 1 / |a * t| := by positivity
    have : Tendsto (fun k : ℕ => (k : ℝ) * (1 / |a * t|)) atTop atTop :=
      Tendsto.atTop_mul_const hpos tendsto_natCast_atTop_atTop
    refine this.congr (fun k => ?_); rw [hv]; ring
  -- along `v`, the shadow is constantly `cos(2π c t)`.
  have hval : ∀ k : ℕ,
      (∫ x, Real.cos (2 * Real.pi * (c + v k * x) * t) ∂twoPoint a)
        = Real.cos (2 * Real.pi * c * t) := by
    intro k
    rw [twoPoint_shadow_eq]
    have hk : 2 * Real.pi * v k * a * t
        = (if 0 < a * t then (k : ℝ) else -(k : ℝ)) * (2 * Real.pi) := by
      rw [hv]
      rcases lt_or_gt_of_ne hat with h | h
      · rw [if_neg (not_lt.mpr h.le), abs_of_neg h]; field_simp
      · rw [if_pos h, abs_of_pos h]; field_simp
    rw [hk]
    rcases lt_or_gt_of_ne hat with h | h
    · rw [if_neg (not_lt.mpr h.le),
        show (-(k : ℝ)) * (2 * Real.pi) = -((k : ℝ) * (2 * Real.pi)) by ring,
        Real.cos_neg, Real.cos_nat_mul_two_pi, mul_one]
    · rw [if_pos h, Real.cos_nat_mul_two_pi, mul_one]
  -- but the composed limit would be `0`, contradicting the constant `cos(2π c t) ≠ 0`.
  have hcomp : Tendsto (fun k : ℕ =>
      ∫ x, Real.cos (2 * Real.pi * (c + v k * x) * t) ∂twoPoint a) atTop (𝓝 0) :=
    hT.comp hvdiv
  rw [tendsto_congr hval] at hcomp
  have hconst : Tendsto (fun _ : ℕ => Real.cos (2 * Real.pi * c * t)) atTop
      (𝓝 (Real.cos (2 * Real.pi * c * t))) := tendsto_const_nhds
  exact hc (tendsto_nhds_unique hconst hcomp)

/-! ## CAPSTONE — the charFun-decay condition separates AC (resist) from lattice (survive). -/

/--
**THE SHARP BOUNDARY (capstone) — charFun decay separates AC from lattice.**

The resist condition of the general law is the spectral condition `‖charFun μ s‖ → 0`. This capstone
shows that condition is the sharp dividing line bracketed by the two clean families:

* an **absolutely-continuous** population `absContMeasure f` (`f` a nonnegative integrable density)
  **satisfies** the resist condition (`absCont_charFun_tendsto_zero`, by Riemann–Lebesgue), so it
  resists;
* the **lattice** population `twoPoint a` (`a ≠ 0`) **fails** the resist condition
  (`twoPoint_does_not_resist`, its characteristic function is `cos(a·)`, which recurs to `1`), so it
  survives.

AC sits on the resist side of the boundary, the two-point on the survive side — they bracket it.

**What is NOT claimed.** This is `AC ⟹ resist` and `lattice ⟹ survive`, NOT `resist ↔ AC`. The
latter is false: singular-continuous **Rajchman** measures also resist (their characteristic
function decays
while they have no density). The full Rajchman characterization of which singular measures resist is
subtle and is not captured here — AC and lattice are the two clean *brackets*, not a complete
dichotomy. -/
theorem resist_separates_ac_from_lattice
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x)
    (a : ℝ) (ha : a ≠ 0) :
    -- AC sits on the resist side: its charFun decays
    (Tendsto (fun s : ℝ => ‖charFun (absContMeasure f) s‖) atTop (𝓝 0))
      -- the lattice two-point sits on the survive side: its charFun does NOT decay
      ∧ ¬ Tendsto (fun s : ℝ => ‖charFun (twoPoint a) s‖) atTop (𝓝 0) :=
  ⟨absCont_charFun_tendsto_zero f hf_meas hf_nonneg, twoPoint_does_not_resist a ha⟩

/--
**The separation is ORTHOGONAL to variance** (composed with `ShadowDecayCauchy`). What governs
resistance is the characteristic-function spectrum, NOT any moment:

* the **Cauchy** population has *infinite* variance — indeed no first moment at all
  (`ShadowDecayCauchy.cauchy_no_mean`) — yet it **resists**
  (`ShadowDecayCauchy.cauchy_charFun_tendsto_zero`), because it is absolutely continuous and its
  charFun decays;
* the bounded **two-point** population has *finite everything* yet **survives**
  (`twoPoint_does_not_resist`), because its charFun `cos(a·)` does not decay.

So resistance cannot be read off the variance: an infinite-variance law resists while a
bounded law survives. The deciding quantity is the charFun decay alone. -/
theorem resist_orthogonal_to_variance
    (x₀ : ℝ) (γ : ℝ≥0) (hγ : γ ≠ 0) (a : ℝ) (ha : a ≠ 0) :
    -- Cauchy: infinite variance (no mean) yet resists (charFun decays)
    ((Tendsto (fun s : ℝ => ‖charFun (cauchyMeasure x₀ γ) s‖) atTop (𝓝 0))
        ∧ ¬ Integrable (fun x : ℝ => x) (cauchyMeasure x₀ γ))
      -- two-point: bounded (finite everything) yet survives (charFun does not decay)
      ∧ ¬ Tendsto (fun s : ℝ => ‖charFun (twoPoint a) s‖) atTop (𝓝 0) :=
  ⟨Sundog.ShadowDecayCauchy.cauchy_is_separator x₀ γ hγ, twoPoint_does_not_resist a ha⟩

end Sundog.ShadowDecayLattice

-- Axiom audit: the AC-resist / lattice-survive separation and all corollaries should depend only on
-- mathlib's foundational axioms (`propext`, `Classical.choice`, `Quot.sound`) — NO `sorryAx`.
