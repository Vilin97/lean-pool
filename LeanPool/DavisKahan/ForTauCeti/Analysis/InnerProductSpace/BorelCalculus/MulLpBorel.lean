/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.BorelNatural
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.DiagMeasureMulLp

/-!
# The bounded Borel calculus of a multiplication operator

For a multiplication operator `mulLp ρ g` and a bounded Borel `h : ℂ → ℂ`,

```text
h(mulLp ρ g) = mulLp ρ (h ∘ g).
```

This is the Borel analogue of `cfc_mulLp`, and unlike that result it needs no continuity of `h`
anywhere: the Borel calculus is defined by the polarised diagonal integrals, the diagonal
measure of a vector `F` is `g_* (|F|² · ρ)` (`map_val_diagMeasure_mulLp`), and integrating
`h` against that measure *is* the matrix element of `mulLp ρ (h ∘ g)`.  Polarisation
(`inner_polarization`) then recovers every matrix element from the diagonal ones.

The statement quantifies over an arbitrary symbol `h'` almost everywhere equal to `h ∘ g`, so
call sites never have to match a composition syntactically.

The corollary that the uniqueness argument consumes is `specProjC_mulLp`: **the spectral
projection of a Borel set `S ⊆ ℂ` acts on the model as multiplication by the indicator of
`g ⁻¹' S`.**  This is what turns "range of a spectral projection" into "functions supported on
a slice" and lets the level sets of a multiplicity datum be counted by generators.

## Main results

* `TauCeti.BorelCalculus.inner_mulLp_left` and `inner_mulLp_self`: matrix elements of a
  multiplication operator as integrals.
* `TauCeti.BorelCalculus.integral_comp_val_diagMeasure_mulLp`: the diagonal integral of a
  pulled-back symbol, computed on the base space.
* `TauCeti.BorelCalculus.borelCalculus_comp_val_mulLp`: **the Borel calculus of a
  multiplication operator is multiplication by the composed symbol.**
* `TauCeti.BorelCalculus.specProjC_mulLp`: **spectral projections of the model are indicator
  multiplications.**

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

@[expose] public section

open scoped InnerProductSpace ENNReal

open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace BorelCalculus

variable {α : Type*} [MeasurableSpace α]

section MatrixElements

/-- The matrix element of a multiplication operator against a vector on the left. -/
theorem inner_mulLp_left (ρ : Measure α) {h : α → ℂ} (hm : Measurable h) {C : ℝ}
    (hC : ∀ x, ‖h x‖ ≤ C) (F G : Lp ℂ 2 ρ) :
    ⟪mulLp ρ hm hC F, G⟫_ℂ
      = ∫ x, (starRingEnd ℂ) (h x * (F : α → ℂ) x) * (G : α → ℂ) x ∂ρ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulLp ρ hm hC F] with x hx
  rw [RCLike.inner_apply, hx]
  ring

/-- The diagonal matrix element of a multiplication operator: a weighted integral of the
symbol against the squared modulus. -/
theorem inner_mulLp_self (ρ : Measure α) {h : α → ℂ} (hm : Measurable h) {C : ℝ}
    (hC : ∀ x, ‖h x‖ ≤ C) (F : Lp ℂ 2 ρ) :
    ⟪F, mulLp ρ hm hC F⟫_ℂ = ∫ x, h x * ((‖(F : α → ℂ) x‖ : ℂ)) ^ 2 ∂ρ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulLp ρ hm hC F] with x hx
  rw [RCLike.inner_apply, hx]
  have hz : (starRingEnd ℂ) ((F : α → ℂ) x) * ((F : α → ℂ) x)
      = ((‖(F : α → ℂ) x‖ : ℂ)) ^ 2 := RCLike.conj_mul _
  linear_combination h x * hz

end MatrixElements

section BorelMulLp

variable (ρ : Measure α) [SigmaFinite ρ] {g : α → ℂ} (hg : Measurable g) {C : ℝ}
variable (hgC : ∀ x, ‖g x‖ ≤ C)

include hg hgC in
/-- **The diagonal integral of a pulled-back symbol, computed on the base space.**  Integrating
`h ∘ (↑)` against the scalar spectral measure of `F` is integrating `h ∘ g` against
`|F|² · ρ`. -/
theorem integral_comp_val_diagMeasure_mulLp {h : ℂ → ℂ} (hm : Measurable h) (F : Lp ℂ 2 ρ) :
    ∫ w, h (w : ℂ) ∂(diagMeasure (isStarNormal_mulLp ρ hg hgC) F)
      = ∫ x, h (g x) * ((‖(F : α → ℂ) x‖ : ℂ)) ^ 2 ∂ρ := by
  have h1 := integral_map (μ := diagMeasure (isStarNormal_mulLp ρ hg hgC) F)
    (φ := (Subtype.val : spectrum ℂ (mulLp ρ hg hgC) → ℂ))
    measurable_subtype_coe.aemeasurable (f := h) hm.aestronglyMeasurable
  rw [← h1, map_val_diagMeasure_mulLp ρ hg hgC F,
    integral_map hg.aemeasurable hm.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀ (aemeasurable_enorm_sq ρ F)
      (Filter.Eventually.of_forall fun _ => by finiteness)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Complex.real_smul, ENNReal.toReal_pow, toReal_enorm]
  push_cast
  ring

include hg hgC in
/-- The diagonal integral of a pulled-back symbol is the diagonal matrix element of
multiplication by any symbol almost everywhere equal to the composition. -/
theorem integral_comp_val_diagMeasure_eq_inner_mulLp {h : ℂ → ℂ} (hm : Measurable h)
    {h' : α → ℂ} (hm' : Measurable h') {C' : ℝ} (hC' : ∀ x, ‖h' x‖ ≤ C')
    (heq : ∀ᵐ x ∂ρ, h' x = h (g x)) (F : Lp ℂ 2 ρ) :
    ∫ w, h (w : ℂ) ∂(diagMeasure (isStarNormal_mulLp ρ hg hgC) F)
      = ⟪F, mulLp ρ hm' hC' F⟫_ℂ := by
  rw [integral_comp_val_diagMeasure_mulLp ρ hg hgC hm F, inner_mulLp_self ρ hm' hC' F]
  refine integral_congr_ae ?_
  filter_upwards [heq] with x hx
  rw [hx]

include hg hgC in
/-- **The bounded Borel calculus of a multiplication operator is multiplication by the composed
symbol.**  Stated for an arbitrary symbol almost everywhere equal to `h ∘ g`, so call sites
never match a composition syntactically. -/
theorem borelCalculus_comp_val_mulLp {h : ℂ → ℂ} (hm : Measurable h) {C' : ℝ}
    (hC : ∀ z, ‖h z‖ ≤ C') {h' : α → ℂ} (hm' : Measurable h') {C'' : ℝ}
    (hC' : ∀ x, ‖h' x‖ ≤ C'') (heq : ∀ᵐ x ∂ρ, h' x = h (g x)) :
    borelCalculus (isStarNormal_mulLp ρ hg hgC) (isBddMeasurable_comp_val hm hC)
      = mulLp ρ hm' hC' := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  refine ext_inner_left ℂ fun ψ => ?_
  rw [inner_borelCalculus, pair_def]
  have hint : ∀ F : Lp ℂ 2 ρ,
      ∫ w, h (w : ℂ) ∂(diagMeasure (isStarNormal_mulLp ρ hg hgC) F)
        = ⟪F, mulLp ρ hm' hC' F⟫_ℂ := fun F =>
    integral_comp_val_diagMeasure_eq_inner_mulLp ρ hg hgC hm hm' hC' heq F
  rw [hint (ξ + ψ), hint (ξ + Complex.I • ψ), hint (ξ - ψ), hint (ξ - Complex.I • ψ)]
  exact inner_polarization (mulLp ρ hm' hC') ψ ξ

include hg hgC in
/-- **The spectral projection of a Borel set acts on the model as multiplication by the
indicator of its preimage under the symbol.** -/
theorem specProjC_mulLp {S : Set ℂ} (hS : MeasurableSet S) :
    specProjC (isStarNormal_mulLp ρ hg hgC) hS
      = mulLp ρ ((measurable_indicator_one hS).comp hg)
          (fun x => norm_indicator_one_le (g x)) := by
  rw [specProjC_def]
  exact borelCalculus_comp_val_mulLp ρ hg hgC (measurable_indicator_one hS)
    norm_indicator_one_le ((measurable_indicator_one hS).comp hg)
    (fun x => norm_indicator_one_le (g x)) (Filter.Eventually.of_forall fun x => rfl)

end BorelMulLp

end BorelCalculus
end TauCeti
