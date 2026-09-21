/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Complexification.FunctionalCalculus

/-!
# The spectrum survives complexification

For a real Hilbert space `E`, `complexify : (E →L[ℝ] E) → (Eℂ →L[ℂ] Eℂ)` is an injective
unital `⋆`-algebra map (`complexifyStarAlgHom`).  This file proves that it also **reflects**
invertibility, and deduces that it preserves the real spectrum on the nose:

* `isUnit_complexify_iff` : `IsUnit (complexify T) ↔ IsUnit T`;
* `spectrum_complexify` : `spectrum ℝ (complexify T) = spectrum ℝ T`;
* `mem_spectrum_complexify_iff` : the real points of the complex spectrum.

The two halves of the first statement are asymmetric:

* **forward** is formal — a unital ring map carries units to units;
* **backward** is the content — an inverse of `complexify T` must be shown to *come from* a
  real operator, and `realify` is that operator.  The proof does **not** need the usual
  "the inverse of a conjugation-fixed operator is conjugation-fixed" argument: evaluating both
  unit equations at `ofReal x` and taking real parts gives the two real identities directly.

## Which real algebra structure

`spectrum ℝ` on `Eℂ →L[ℂ] Eℂ` is taken with respect to the scoped `complexOperatorRealAlgebra`
(`Algebra.complexToReal`), the one the real continuous functional calculus of
`Complexification/FunctionalCalculus.lean` is registered against.  A globally available second
real structure, `ContinuousLinearMap.algebra`, exists on the same type and is only
*propositionally* equal to it, so a consumer of `spectrum_complexify` must have this namespace's
scope open.  See `algebraMap_complexOperator`.

## Provenance

The mathematics is moved, not restated, from `TauCeti.DavisKahan.Experimental.Foundation.`
`RealComplexification` in `DavisKahan/SpectralTheory/Complexification/Spectrum.lean`, which
depended on nothing in the paper library and is where this argument was first proved.  That
module still carries its own copies in its own namespace; re-grounding it on these is
separate, mechanical work.  A third copy, in `DavisKahan/Experimental/MathAhead/`
`HiddenFoundations/RealSylvesterDescent.lean`, was deleted with that staging file on
2026-08-27.
-/

public section

namespace TauCeti
namespace RealComplexification

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Complexification is a unital ring map, so it carries units to units. -/
theorem isUnit_complexify_of_isUnit {T : E →L[ℝ] E} (h : IsUnit T) :
    IsUnit (complexify T) := by
  obtain ⟨u, rfl⟩ := h
  have hmul : ∀ S T : E →L[ℝ] E, complexify (S * T) = complexify S * complexify T :=
    fun S T => complexify_comp S T
  have hone : complexify (1 : E →L[ℝ] E) = 1 := complexify_id
  exact ⟨⟨complexify (u : E →L[ℝ] E), complexify (↑u⁻¹ : E →L[ℝ] E),
      by rw [← hmul, u.mul_inv, hone], by rw [← hmul, u.inv_mul, hone]⟩, rfl⟩

omit [CompleteSpace E] in
/-- **Complexification reflects invertibility.**

The inverse of `complexify T` restricts to an inverse of `T`: `realify` of it works on both
sides, because evaluating each unit equation at `ofReal x` and taking real parts gives exactly
the two real identities. -/
theorem isUnit_of_isUnit_complexify {T : E →L[ℝ] E} (h : IsUnit (complexify T)) :
    IsUnit T := by
  obtain ⟨u, hu⟩ := h
  have hmul : complexify T * (↑u⁻¹ : RealComplexification E →L[ℂ] RealComplexification E) = 1 := by
    rw [← hu]; exact u.mul_inv
  have hinv : (↑u⁻¹ : RealComplexification E →L[ℂ] RealComplexification E) * complexify T = 1 := by
    rw [← hu]; exact u.inv_mul
  refine ⟨⟨T, realify (↑u⁻¹ : RealComplexification E →L[ℂ] RealComplexification E), ?_, ?_⟩, rfl⟩
  · -- `T * realify u⁻¹ = 1`, from `complexify T * u⁻¹ = 1` evaluated at `ofReal x`.
    apply ContinuousLinearMap.ext
    intro x
    have hx : complexify T ((↑u⁻¹ : RealComplexification E →L[ℂ] RealComplexification E)
        (ofReal x)) = ofReal x :=
      congrArg (fun S : RealComplexification E →L[ℂ] RealComplexification E => S (ofReal x)) hmul
    have hre := congrArg re hx
    rw [re_complexify] at hre
    simpa [realify_apply] using hre
  · -- `realify u⁻¹ * T = 1`, from `u⁻¹ * complexify T = 1` evaluated at `ofReal x`.
    apply ContinuousLinearMap.ext
    intro x
    have hx : (↑u⁻¹ : RealComplexification E →L[ℂ] RealComplexification E)
        (complexify T (ofReal x)) = ofReal x :=
      congrArg (fun S : RealComplexification E →L[ℂ] RealComplexification E => S (ofReal x)) hinv
    rw [complexify_ofReal] at hx
    have hre := congrArg re hx
    simpa [realify_apply] using hre

omit [CompleteSpace E] in
/-- Invertibility is preserved and reflected by complexification. -/
theorem isUnit_complexify_iff {T : E →L[ℝ] E} : IsUnit (complexify T) ↔ IsUnit T :=
  ⟨isUnit_of_isUnit_complexify, isUnit_complexify_of_isUnit⟩

omit [CompleteSpace E] in
/-- **The real points of the complex spectrum survive complexification.** -/
theorem mem_spectrum_complexify_iff (T : E →L[ℝ] E) (r : ℝ) :
    (r : ℂ) ∈ spectrum ℂ (complexify T) ↔ r ∈ spectrum ℝ T := by
  simp only [spectrum.mem_iff]
  rw [← complexify_algebraMapComplex, ← complexify_sub, isUnit_complexify_iff]

omit [CompleteSpace E] in
/-- **The real spectrum survives complexification**, as an equality of subsets of `ℝ`.

This is the statement that lets the real continuous functional calculus of the complexified
algebra be read as a calculus for the real operator: the two symbol algebras
`C(spectrum ℝ T, ℝ)` and `C(spectrum ℝ (complexify T), ℝ)` are the same object. -/
theorem spectrum_complexify (T : E →L[ℝ] E) :
    spectrum ℝ (complexify T) = spectrum ℝ T := by
  ext r
  simp only [spectrum.mem_iff, algebraMap_complexOperator]
  rw [← complexify_algebraMapComplex, ← complexify_sub, isUnit_complexify_iff]

end

end RealComplexification
end TauCeti
