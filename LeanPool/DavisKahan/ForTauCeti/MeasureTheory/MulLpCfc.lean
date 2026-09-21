/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.MeasureTheory.LpComp
public import LeanPool.DavisKahan.ForTauCeti.MeasureTheory.MulLpSpectrum
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# The functional calculus of a multiplication operator is multiplication by the composed symbol

For a σ-finite measure `ρ` and a bounded measurable symbol `g`,

```text
cfc f (mulLp ρ g) = mulLp ρ (f ∘ g)
```

for every `f` continuous on the spectrum.

## Why this is not `map_cfc`

`StarAlgHomClass.map_cfc` transports the functional calculus along a homomorphism of the
*algebras*: it answers "what does `φ` do to `f(a)`".  Here the algebra is fixed and the change
happens in the *symbol*, so nothing about `map_cfc` applies.  What does apply is **uniqueness**:
`f ↦ mulLp ρ (f ∘ g)` is itself a continuous `⋆`-algebra homomorphism out of
`C(spectrum ℂ (mulLp ρ g), ℂ)` sending the coordinate to `mulLp ρ g`, and
`cfcHom_eq_of_continuous_of_map_id` says there is only one such map.

The obstruction to even *writing down* that homomorphism is that `f` is defined on the spectrum
while `g` takes values in `ℂ`.  `TauCeti.ae_mem_spectrum_mulLp` removes it: the symbol may be
replaced, without changing the operator, by one that takes values in the spectrum everywhere.
The replacement needs a basepoint, so the degenerate case of an **empty** spectrum is split off
first -- and there it is genuinely degenerate, since a complex Banach algebra with an
empty-spectrum element is a subsingleton and the claim is `Subsingleton.elim`.

## Main results

* `TauCeti.mulLpStarHom`: the `⋆`-algebra homomorphism `f ↦ mulLp ρ (f ∘ ĝ)`.
* `TauCeti.continuous_mulLpStarHom`: it is continuous, with norm at most `1`.
* `TauCeti.cfc_mulLp`: **the functional calculus of a multiplication operator.**

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

public section

open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti

variable {α : Type*} [MeasurableSpace α]

section StarHom

variable {s : Set ℂ} [CompactSpace ↥s] {ĝ : α → ↥s}

omit [CompactSpace ↥s] in
/-- A continuous function on `s` composed with a measurable `s`-valued map is measurable. -/
theorem measurable_comp_contMap (hĝ : Measurable ĝ) (f : C(↥s, ℂ)) :
    Measurable fun x => f (ĝ x) :=
  (map_continuous f).measurable.comp hĝ

omit [MeasurableSpace α] in
/-- The composed symbol is bounded by the sup norm of the function, `s` being compact. -/
theorem norm_comp_contMap_le (ĝ : α → ↥s) (f : C(↥s, ℂ)) (x : α) : ‖f (ĝ x)‖ ≤ ‖f‖ :=
  f.norm_coe_le_norm _

variable (ρ : Measure α)

/-- **Multiplication by a composed symbol, as a `⋆`-algebra homomorphism.**

Every obligation is the corresponding law from `MulLpAlgebra` with its almost-everywhere
hypothesis discharged by `rfl`: composition with a fixed `ĝ` is applied pointwise, so it
commutes with every pointwise operation on `C(s, ℂ)` on the nose. -/
noncomputable def mulLpStarHom (hĝ : Measurable ĝ) :
    C(↥s, ℂ) →⋆ₐ[ℂ] (Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ) where
  toFun f := mulLp ρ (measurable_comp_contMap hĝ f) (norm_comp_contMap_le ĝ f)
  map_one' := by
    refine mulLp_eq_one ρ _ _ ?_
    exact Filter.Eventually.of_forall fun _ => rfl
  map_mul' f₁ f₂ := by
    refine mulLp_eq_comp ρ _ _ _ _ _ _ ?_
    exact Filter.Eventually.of_forall fun _ => rfl
  map_zero' := by
    refine mulLp_eq_zero ρ _ _ ?_
    exact Filter.Eventually.of_forall fun _ => rfl
  map_add' f₁ f₂ := by
    refine mulLp_eq_add ρ _ _ _ _ _ _ ?_
    exact Filter.Eventually.of_forall fun _ => rfl
  commutes' r := by
    refine mulLp_eq_algebraMap ρ _ _ r ?_
    exact Filter.Eventually.of_forall fun _ => rfl
  map_star' f := by
    refine (star_mulLp ρ _ _ _ _ ?_).symm
    exact Filter.Eventually.of_forall fun _ => rfl

/-- The homomorphism, unfolded. -/
theorem mulLpStarHom_apply (hĝ : Measurable ĝ) (f : C(↥s, ℂ)) :
    mulLpStarHom ρ hĝ f = mulLp ρ (measurable_comp_contMap hĝ f) (norm_comp_contMap_le ĝ f) :=
  (rfl)

/-- **The homomorphism is continuous**, with norm at most `1`: multiplication by a symbol
bounded by `‖f‖` is an operator of norm at most `‖f‖`. -/
theorem continuous_mulLpStarHom (hĝ : Measurable ĝ) : Continuous (mulLpStarHom ρ hĝ) := by
  refine AddMonoidHomClass.continuous_of_bound (mulLpStarHom ρ hĝ) 1 fun f => ?_
  rw [one_mul, mulLpStarHom_apply]
  exact (norm_mulLp_le ρ _ _).trans_eq (abs_of_nonneg (norm_nonneg f))

end StarHom

section Cfc

variable (ρ : Measure α) [SigmaFinite ρ] {g : α → ℂ} (hg : Measurable g) {C : ℝ}
variable (hgC : ∀ x, ‖g x‖ ≤ C)

include hg hgC in
/-- **The functional calculus of a multiplication operator is multiplication by the composed
symbol.**

Stated for an arbitrary symbol `h` that is almost everywhere `f ∘ g`, so that a call site never
has to match a composition syntactically -- the same convention as the rest of the `mulLp` API. -/
theorem cfc_mulLp {f : ℂ → ℂ} (hf : ContinuousOn f (spectrum ℂ (mulLp ρ hg hgC)))
    {h : α → ℂ} (hh : Measurable h) {C' : ℝ} (hhC : ∀ x, ‖h x‖ ≤ C')
    (heq : ∀ᵐ x ∂ρ, h x = f (g x)) :
    cfc f (mulLp ρ hg hgC) = mulLp ρ hh hhC := by
  classical
  have hna : IsStarNormal (mulLp ρ hg hgC) := isStarNormal_mulLp ρ hg hgC
  have hae : ∀ᵐ x ∂ρ, g x ∈ spectrum ℂ (mulLp ρ hg hgC) := ae_mem_spectrum_mulLp ρ hg hgC
  set a : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ := mulLp ρ hg hgC with ha
  rcases Set.eq_empty_or_nonempty (spectrum ℂ a) with hemp | ⟨z₀, hz₀⟩
  · -- An element with empty spectrum forces the algebra to be a subsingleton.
    have hsub : Subsingleton (Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ) := by
      by_contra hcon
      have : Nontrivial (Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ) := not_subsingleton_iff_nontrivial.mp hcon
      obtain ⟨z, hz⟩ := spectrum.nonempty a
      rw [hemp] at hz
      exact hz
    exact Subsingleton.elim _ _
  · -- Corestrict the symbol to the spectrum; off the spectrum it is sent to the basepoint.
    have hspecMeas : MeasurableSet (spectrum ℂ a) := (spectrum.isClosed a).measurableSet
    set g' : α → ℂ := fun x => if g x ∈ spectrum ℂ a then g x else z₀ with hg'
    have hg'm : Measurable g' := Measurable.ite (hg hspecMeas) hg measurable_const
    have hg'mem : ∀ x, g' x ∈ spectrum ℂ a := by
      intro x
      by_cases hx : g x ∈ spectrum ℂ a
      · simp [hg', hx]
      · simpa [hg', hx] using hz₀
    have hgg' : g' =ᵐ[ρ] g := by
      filter_upwards [hae] with x hx
      simp [hg', hx]
    set ĝ : α → ↥(spectrum ℂ a) := fun x => ⟨g' x, hg'mem x⟩ with hĝdef
    have hĝm : Measurable ĝ := hg'm.subtype_mk
    -- The two homomorphisms agree on the coordinate, hence everywhere.
    have hid : mulLpStarHom ρ hĝm ((ContinuousMap.id ℂ).restrict (spectrum ℂ a)) = a := by
      rw [mulLpStarHom_apply]
      exact mulLp_congr_ae ρ _ hg _ hgC hgg'
    have hcfcHom : cfcHom hna = mulLpStarHom ρ hĝm :=
      cfcHom_eq_of_continuous_of_map_id hna _ (continuous_mulLpStarHom ρ hĝm) hid
    rw [cfc_apply f a hna hf, hcfcHom, mulLpStarHom_apply]
    refine mulLp_congr_ae ρ _ hh _ hhC ?_
    filter_upwards [hgg', heq] with x h1 h2
    change f (g' x) = h x
    rw [h1, h2]

end Cfc

end TauCeti
