/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.MeasureTheory.MulLpAlgebra
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# The symbol of a multiplication operator takes values in the spectrum

For a σ-finite measure `ρ` and a bounded measurable symbol `g`, the values of `g` lie in the
spectrum of `mulLp ρ g` **almost everywhere**:

```text
∀ᵐ x ∂ρ, g x ∈ spectrum ℂ (mulLp ρ g).
```

Equivalently, the essential range of the symbol is contained in the spectrum.  (The reverse
inclusion is also true but is not needed here, so it is not proved.)

## Why this is the load-bearing step

It is what lets the symbol be **corestricted to the spectrum**: once `g` almost everywhere takes
values in `spectrum ℂ (mulLp ρ g)`, a continuous `f : C(spectrum ℂ (mulLp ρ g), ℂ)` can be
composed with it, and `f ↦ mulLp ρ (f ∘ g)` becomes a `⋆`-algebra homomorphism out of
`C(spectrum ℂ (mulLp ρ g), ℂ)` -- exactly the shape that uniqueness of the continuous functional
calculus consumes.  Without it there is no way to even *state* the composition.

## The argument

If `z` is outside the spectrum then `algebraMap ℂ _ z - mulLp ρ g` is invertible, hence bounded
below: `‖F‖ ≤ ‖T‖ * ‖(z - g) · F‖` with `T` the inverse.  Were `ρ (g ⁻¹' ball z ε)` positive for
`ε := 1 / (‖T‖ + 1)`, σ-finiteness would supply a measurable `S` inside that preimage with
`0 < ρ S < ∞`, and its normalised indicator `F` would satisfy `‖(z - g) · F‖ ≤ ε * ‖F‖`, forcing
`1 ≤ ‖T‖ * ε = ‖T‖ / (‖T‖ + 1) < 1`.

Passing from "each point off the spectrum has a null ball around it" to "the whole complement is
null" is where second countability enters, via `TopologicalSpace.isOpen_iUnion_countable`: the
balls cover the open complement, so countably many of them already do, and a countable union of
null sets is null.  **σ-finiteness is genuinely needed** -- without it there need be no set of
positive finite measure inside the preimage, and the indicator would not be in `L²`.

## Main results

* `TauCeti.exists_measure_preimage_ball_eq_zero`: a point off the spectrum has a ball around it
  whose preimage is null.
* `TauCeti.ae_mem_spectrum_mulLp`: **the symbol takes values in the spectrum almost
  everywhere.**

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

@[expose] public section

open MeasureTheory

namespace TauCeti

variable {α : Type*} [MeasurableSpace α]

section Spectrum

variable (ρ : Measure α) [SigmaFinite ρ] {g : α → ℂ} (hg : Measurable g) {C : ℝ}
variable (hgC : ∀ x, ‖g x‖ ≤ C)

omit [SigmaFinite ρ] in
include hg hgC in
/-- **Subtracting a scalar from a multiplication operator multiplies by the shifted symbol.** -/
theorem algebraMap_sub_mulLp (z : ℂ) {h : α → ℂ} (hh : Measurable h) {C' : ℝ}
    (hhC : ∀ x, ‖h x‖ ≤ C') (heq : ∀ x, h x = z - g x) :
    algebraMap ℂ (Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ) z - mulLp ρ hg hgC = mulLp ρ hh hhC := by
  refine ContinuousLinearMap.ext fun F => Lp.ext ?_
  have hsm : (algebraMap ℂ (Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ) z - mulLp ρ hg hgC) F
      = z • F - mulLp ρ hg hgC F := by
    rw [Algebra.algebraMap_eq_smul_one]
    simp
  rw [hsm]
  filter_upwards [coeFn_mulLp ρ hh hhC F, Lp.coeFn_sub (z • F) (mulLp ρ hg hgC F),
    Lp.coeFn_smul z F, coeFn_mulLp ρ hg hgC F] with x h1 h2 h3 h4
  rw [h1, h2, Pi.sub_apply, h3, Pi.smul_apply, h4, smul_eq_mul, heq x, sub_mul]

include hg hgC in
/-- **A point off the spectrum has a ball around it whose preimage under the symbol is null.**

This is the quantitative core: invertibility of `z - mulLp ρ g` bounds the operator below, and an
indicator supported where `g` is within `ε` of `z` violates that bound once `ε` is small enough.
σ-finiteness is what produces a set of positive *finite* measure to build the indicator on. -/
theorem exists_measure_preimage_ball_eq_zero {z : ℂ} (hz : z ∉ spectrum ℂ (mulLp ρ hg hgC)) :
    ∃ ε > 0, ρ (g ⁻¹' Metric.ball z ε) = 0 := by
  classical
  set a : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ := mulLp ρ hg hgC with ha
  obtain ⟨u, hu⟩ : IsUnit (algebraMap ℂ (Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ) z - a) :=
    not_not.mp (by simpa [spectrum.mem_iff] using hz)
  set T : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ := ↑u⁻¹ with hT
  -- The inverse bounds `z - a` below.
  have hinv : ∀ F : Lp ℂ 2 ρ, T ((algebraMap ℂ (Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ) z - a) F) = F := by
    intro F
    have := congrArg (fun S : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ => S F) u.inv_mul
    simpa [hT, hu] using this
  have hbelow : ∀ F : Lp ℂ 2 ρ,
      ‖F‖ ≤ ‖T‖ * ‖(algebraMap ℂ (Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ) z - a) F‖ := by
    intro F
    calc ‖F‖ = ‖T ((algebraMap ℂ (Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ) z - a) F)‖ := by rw [hinv F]
      _ ≤ ‖T‖ * ‖(algebraMap ℂ (Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ) z - a) F‖ := T.le_opNorm _
  set ε : ℝ := 1 / (‖T‖ + 1) with hε
  have hTpos : (0 : ℝ) < ‖T‖ + 1 := by positivity
  have hεpos : 0 < ε := by positivity
  refine ⟨ε, hεpos, ?_⟩
  by_contra hne
  -- σ-finiteness gives a set of positive finite measure inside the preimage.
  have hSmeas : MeasurableSet (g ⁻¹' Metric.ball z ε) := hg Metric.isOpen_ball.measurableSet
  obtain ⟨S, hSm, hSsub, hSpos, hSfin⟩ :=
    Measure.exists_subset_measure_lt_top (μ := ρ) (r := 0) hSmeas (pos_iff_ne_zero.mpr hne)
  set F : Lp ℂ 2 ρ := indicatorConstLp 2 hSm hSfin.ne (1 : ℂ) with hF
  have hFpos : 0 < ‖F‖ := by
    rw [hF, norm_indicatorConstLp (by norm_num) (by norm_num), norm_one, one_mul]
    refine Real.rpow_pos_of_pos ?_ _
    rw [measureReal_def]
    exact ENNReal.toReal_pos hSpos.ne' hSfin.ne
  -- The shifted symbol, cut down to `S`, is uniformly small.
  set h : α → ℂ := Set.indicator S (fun x => z - g x) with hh
  have hhm : Measurable h := (measurable_const.sub hg).indicator hSm
  have hhb : ∀ x, ‖h x‖ ≤ ε := by
    intro x
    by_cases hx : x ∈ S
    · rw [hh, Set.indicator_of_mem hx, norm_sub_rev]
      exact le_of_lt (by rw [← dist_eq_norm]; exact Metric.mem_ball.mp (hSsub hx))
    · rw [hh, Set.indicator_of_notMem hx, norm_zero]
      exact hεpos.le
  -- On `F`, multiplying by the cut-down symbol is the same as multiplying by the shifted one.
  have hzgm : Measurable fun x => z - g x := measurable_const.sub hg
  have hzgb : ∀ x, ‖z - g x‖ ≤ ‖z‖ + C := fun x =>
    (norm_sub_le _ _).trans (by linarith [hgC x])
  have hagree : (algebraMap ℂ (Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ) z - a) F = mulLp ρ hhm hhb F := by
    rw [ha, algebraMap_sub_mulLp ρ hg hgC z hzgm hzgb fun _ => rfl]
    refine Lp.ext ?_
    filter_upwards [coeFn_mulLp ρ hzgm hzgb F, coeFn_mulLp ρ hhm hhb F,
      indicatorConstLp_coeFn_notMem (p := 2) (hs := hSm) (hμs := hSfin.ne) (c := (1 : ℂ))]
      with x h1 h2 h3
    rw [h1, h2]
    by_cases hx : x ∈ S
    · rw [hh, Set.indicator_of_mem hx]
    · rw [hh, Set.indicator_of_notMem hx, h3 hx, mul_zero, mul_zero]
  -- Put the two estimates together.
  have hsmall : ‖(algebraMap ℂ (Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ) z - a) F‖ ≤ ε * ‖F‖ := by
    rw [hagree]
    calc ‖mulLp ρ hhm hhb F‖ ≤ ‖mulLp ρ hhm hhb‖ * ‖F‖ := (mulLp ρ hhm hhb).le_opNorm _
      _ ≤ |ε| * ‖F‖ := by
          gcongr
          exact norm_mulLp_le ρ hhm hhb
      _ = ε * ‖F‖ := by rw [abs_of_pos hεpos]
  have hchain : 1 * ‖F‖ ≤ (‖T‖ * ε) * ‖F‖ := by
    rw [one_mul, mul_assoc]
    refine (hbelow F).trans ?_
    gcongr
  have hone : (1 : ℝ) ≤ ‖T‖ * ε := le_of_mul_le_mul_right hchain hFpos
  rw [hε, mul_one_div, one_le_div hTpos] at hone
  linarith

include hg hgC in
/-- **The symbol of a multiplication operator takes values in the spectrum almost everywhere.**

The complement of the spectrum is open, and `exists_measure_preimage_ball_eq_zero` puts a ball
with null preimage around each of its points.  `ℂ` is second countable, so countably many of
those balls already cover the complement, and a countable union of null sets is null. -/
theorem ae_mem_spectrum_mulLp : ∀ᵐ x ∂ρ, g x ∈ spectrum ℂ (mulLp ρ hg hgC) := by
  classical
  rw [ae_iff]
  set V : Set ℂ := (spectrum ℂ (mulLp ρ hg hgC))ᶜ with hV
  have hVopen : IsOpen V := (spectrum.isClosed (mulLp ρ hg hgC)).isOpen_compl
  choose! ε hεpos hεnull using fun z (hz : z ∉ spectrum ℂ (mulLp ρ hg hgC)) =>
    exists_measure_preimage_ball_eq_zero ρ hg hgC hz
  set s : V → Set ℂ := fun w => Metric.ball (w : ℂ) (ε (w : ℂ)) with hs
  obtain ⟨T, hTc, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable s fun _ => Metric.isOpen_ball
  have hcover : V ⊆ ⋃ w ∈ T, s w := by
    intro z hz
    rw [hTeq]
    exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, Metric.mem_ball_self (hεpos z hz)⟩
  have hsub : {x | g x ∉ spectrum ℂ (mulLp ρ hg hgC)} ⊆ ⋃ w ∈ T, g ⁻¹' s w := by
    intro x hx
    have := hcover (show g x ∈ V from hx)
    simpa only [Set.preimage_iUnion, Set.mem_iUnion, Set.mem_preimage] using this
  refine measure_mono_null hsub ?_
  rw [measure_biUnion_null_iff hTc]
  exact fun w _ => hεnull (w : ℂ) w.2

end Spectrum

end TauCeti
