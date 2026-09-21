/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.DiagonalMeasure
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

/-!
# The functional calculus is natural under a unitary intertwiner

If a unitary `e` intertwines two normal operators, `e (a x) = b (e x)`, then it intertwines their
whole continuous functional calculi:

```text
e (f(a) x) = f(b) (e x)   for every `f` continuous on the spectrum.
```

Mathlib supplies both moving parts, which is what makes this short:

* `LinearIsometryEquiv.conjStarAlgEquiv` turns the unitary into a `⋆`-algebra equivalence of the
  two endomorphism algebras, and the intertwining hypothesis says exactly that it sends `a` to
  `b`.
* `StarAlgHomClass.map_cfc` says `⋆`-algebra homomorphisms commute with the continuous functional
  calculus.

## Why it is here

This is the first half of the open **uniqueness** question for the multiplicity classification:
it is what makes the *measure class* of a multiplicity datum an invariant of the operator rather
than of the presentation.  The measure statement is
`map_val_diagMeasure_eq_of_intertwines`; both sides are pushed forward to `ℂ` because the two
measures live on the *spectrum subtypes* of `a` and of `b`, which are equal as sets but are
different types.

It follows from the naturality theorem because `diagMeasure` is characterised by
`∫ f d(diagMeasure ha ξ) = ⟪ξ, f(a) ξ⟫` on continuous symbols, a unitary preserves inner
products, and a finite Borel measure on `ℂ` is determined by the integrals of bounded continuous
real functions (`MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure`).

The *level sets* need naturality of the **Borel** calculus rather than the continuous one, and
a dimension count over the measure algebra.  That is the real Hahn--Hellinger; it is not done
here but in `BorelNatural.lean` and `MultiplicityLevelUniqueness.lean`, built on this module.

## Main results

* `TauCeti.BorelCalculus.conjStarAlgEquiv_eq_of_intertwines`: intertwining, as an equation
  between `⋆`-algebra images.
* `TauCeti.BorelCalculus.isStarNormal_of_intertwines`: normality transports.
* `TauCeti.BorelCalculus.cfc_apply_of_intertwines`: **the naturality theorem.**
* `TauCeti.BorelCalculus.map_val_diagMeasure_eq_of_intertwines`: **the scalar spectral measure is
  a unitary invariant.**

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

public section

open scoped InnerProductSpace

open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace BorelCalculus

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {a : H →L[ℂ] H} {b : K →L[ℂ] K}

/-- **The intertwining hypothesis, as an equation between `⋆`-algebra images.**  A unitary
intertwines `a` and `b` exactly when the induced `⋆`-algebra equivalence of the endomorphism
algebras sends `a` to `b`. -/
theorem conjStarAlgEquiv_eq_of_intertwines (e : H ≃ₗᵢ[ℂ] K) (he : ∀ x, e (a x) = b (e x)) :
    e.conjStarAlgEquiv a = b := by
  refine ContinuousLinearMap.ext fun y => ?_
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, he, LinearIsometryEquiv.apply_symm_apply]

/-- A unitarily conjugate of a normal operator is normal. -/
theorem isStarNormal_of_intertwines (ha : IsStarNormal a) (e : H ≃ₗᵢ[ℂ] K)
    (he : ∀ x, e (a x) = b (e x)) : IsStarNormal b := by
  rw [← conjStarAlgEquiv_eq_of_intertwines e he]
  refine ⟨?_⟩
  rw [← map_star]
  exact (ha.star_comm_self).map e.conjStarAlgEquiv

/-- **The continuous functional calculus is natural under a unitary intertwiner.** -/
theorem cfc_apply_of_intertwines (ha : IsStarNormal a) (e : H ≃ₗᵢ[ℂ] K)
    (he : ∀ x, e (a x) = b (e x)) {f : ℂ → ℂ} (hf : ContinuousOn f (spectrum ℂ a)) (x : H) :
    e (cfc f a x) = cfc f b (e x) := by
  have hb : IsStarNormal b := isStarNormal_of_intertwines ha e he
  have hrw : (e.conjStarAlgEquiv : (H →L[ℂ] H) → (K →L[ℂ] K))
      = fun x => ((e : H →L[ℂ] K) ∘L x) ∘L (e.symm : K →L[ℂ] H) :=
    funext fun x => LinearIsometryEquiv.conjStarAlgEquiv_apply e x
  have hφ : Continuous (e.conjStarAlgEquiv : (H →L[ℂ] H) → (K →L[ℂ] K)) := by
    rw [hrw]
    fun_prop
  have hmap := StarAlgHomClass.map_cfc (R := ℂ) (S := ℂ) e.conjStarAlgEquiv f a hf hφ ha
    (by rw [conjStarAlgEquiv_eq_of_intertwines e he]; exact hb)
  rw [conjStarAlgEquiv_eq_of_intertwines e he] at hmap
  have h2 := congrArg (fun T : K →L[ℂ] K => T (e x)) hmap
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply] at h2
  exact h2

/-- **The scalar spectral measure is a unitary invariant.**

A unitary intertwining two normal operators carries the scalar spectral measure of a vector to
that of its image.  Both sides are pushed forward to `ℂ` because the two measures live on the
*spectrum subtypes* of `a` and of `b`, which are equal as sets but are different types.

This is what makes the **measure class** of a multiplicity datum an invariant of the operator
rather than of the presentation. -/
theorem map_val_diagMeasure_eq_of_intertwines (ha : IsStarNormal a) (e : H ≃ₗᵢ[ℂ] K)
    (he : ∀ x, e (a x) = b (e x)) (ξ : H) :
    Measure.map (Subtype.val : spectrum ℂ b → ℂ)
        (diagMeasure (isStarNormal_of_intertwines ha e he) (e ξ))
      = Measure.map (Subtype.val : spectrum ℂ a → ℂ) (diagMeasure ha ξ) := by
  have hb : IsStarNormal b := isStarNormal_of_intertwines ha e he
  have hfa : IsFiniteMeasure
      (Measure.map (Subtype.val : spectrum ℂ a → ℂ) (diagMeasure ha ξ)) :=
    Measure.isFiniteMeasure_map _ _
  have hfb : IsFiniteMeasure
      (Measure.map (Subtype.val : spectrum ℂ b → ℂ) (diagMeasure hb (e ξ))) :=
    Measure.isFiniteMeasure_map _ _
  refine MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure fun g => ?_
  have hgc : Continuous fun z : ℂ => ((g z : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp g.continuous
  rw [integral_map measurable_subtype_coe.aemeasurable
      g.continuous.aestronglyMeasurable,
    integral_map measurable_subtype_coe.aemeasurable
      g.continuous.aestronglyMeasurable]
  have hEa : ∫ w : spectrum ℂ a, g (w : ℂ) ∂(diagMeasure ha ξ)
      = (⟪ξ, cfc (fun z : ℂ => ((g z : ℝ) : ℂ)) a ξ⟫_ℂ).re := by
    have hG := integral_diagMeasure_ofReal ha ξ
      (⟨fun w : spectrum ℂ a => g (w : ℂ), g.continuous.comp continuous_subtype_val⟩ :
        C(spectrum ℂ a, ℝ))
    simp only [ContinuousMap.coe_mk] at hG
    rw [hG, cfc_apply (f := fun z : ℂ => ((g z : ℝ) : ℂ)) (a := a) ha hgc.continuousOn]
    exact congrArg (fun T : H →L[ℂ] H => (⟪ξ, T ξ⟫_ℂ).re)
      (congrArg (cfcHom ha) (ContinuousMap.ext fun _ => by simp))
  have hEb : ∫ w : spectrum ℂ b, g (w : ℂ) ∂(diagMeasure hb (e ξ))
      = (⟪e ξ, cfc (fun z : ℂ => ((g z : ℝ) : ℂ)) b (e ξ)⟫_ℂ).re := by
    have hG := integral_diagMeasure_ofReal hb (e ξ)
      (⟨fun w : spectrum ℂ b => g (w : ℂ), g.continuous.comp continuous_subtype_val⟩ :
        C(spectrum ℂ b, ℝ))
    simp only [ContinuousMap.coe_mk] at hG
    rw [hG, cfc_apply (f := fun z : ℂ => ((g z : ℝ) : ℂ)) (a := b) hb hgc.continuousOn]
    exact congrArg (fun T : K →L[ℂ] K => (⟪e ξ, T (e ξ)⟫_ℂ).re)
      (congrArg (cfcHom hb) (ContinuousMap.ext fun _ => by simp))
  rw [hEa, hEb, ← cfc_apply_of_intertwines ha e he hgc.continuousOn ξ,
    LinearIsometryEquiv.inner_map_map]

end BorelCalculus
end TauCeti
