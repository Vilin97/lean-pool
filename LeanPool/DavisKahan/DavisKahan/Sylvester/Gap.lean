/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sylvester.ClosedSylvesterEquation
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.UnitaryTransport

/-!
# Form-bounded gap configurations for the unbounded Sylvester equation

The interval/exterior configuration says one block has spectrum inside a compact
interval while the other stays a fixed distance away from it.  The predicate is
symmetric in the two blocks: either orientation is allowed.

`FormBoundedSylvesterGap` collects every gap configuration the `sin Θ` endpoint
needs.  Its two ordered constructors let both diagonal blocks be genuinely
unbounded; only the interval/exterior constructor requires a bounded spectral
block.

## Two spellings of the same configurations

This module states the ordered configurations as **operator-form bounds** —
`TauCeti.LinearPMap.SemiboundedBelow`/`TauCeti.LinearPMap.SemiboundedAbove` — and the interval/exterior configuration
over `LinearPMap.realSpectrum`.  `SpectralIntervalExteriorGap` and
`SpectralSylvesterGap` (`SinTheta/Unbounded/IntervalExterior.lean`,
`Sylvester/Unbounded/AllGap.lean`) instead state all three configurations as
**spectral containments** in `Set.Ici`/`Set.Iic`, which is the form Davis--Kahan
1970 uses.

For self-adjoint blocks the two describe the same configurations — a form bound
`⟪Ax, x⟫ ≥ c‖x‖²` and a spectral containment `spectrum A ⊆ Set.Ici c` are the
spectral theorem apart — but they are different propositions, and **only one
direction is proved here**:

* `formBoundedSylvesterGap_of_spectral` gives `SpectralSylvesterGap → `
  `FormBoundedSylvesterGap` in **every** configuration, the ordered branches by
  `semiboundedBelow_of_spectrum_subset_Ici` and its mirror
  (`SpectralTheory/OrderedHalfLine.lean`), the interval branch by
  `realSpectrum_eq_spectraSpectrum`;
* the converse holds for the **interval/exterior branch only**
  (`SpectralSylvesterGap.intervalExterior_of_formBounded`).  Recovering a
  spectral containment from a form bound is the half of the spectral theorem
  this tree does not have.

**So the form-bounded predicate is the weaker hypothesis, and a theorem stated
over it is the stronger theorem** — which is exactly how the endpoints are
arranged: `davisKahan1970_sylvester_complex` takes this predicate, and
`davisKahan1970_sylvester_of_spectrumGap` is available at the spectral one.

Neither predicate carries an unqualified name.  They are equivalent mathematics
stated two ways, so a bare `SylvesterGap` would leave a reader asking which one
it is; each name says how its ordered configurations are given.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan
namespace Sylvester

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Interval/exterior configuration for two partial maps, over
`LinearPMap.realSpectrum`: one block has real spectrum inside a compact interval
and the other stays a distance `δ` away from it.  The predicate is symmetric in
the two blocks.

It needs neither a dense domain nor a closed graph — only the two real spectra —
so it is stated over `LinearPMap` and the closedness hypotheses live with the
theorems that consume the gap.

`SpectralIntervalExteriorGap` is the same configuration spelled through
`ofReal ⁻¹' LinearPMap.spectrum`; `realSpectrum_eq_spectraSpectrum` identifies
the two spectra, and `sylvesterIntervalExteriorGap_of_realSpectrum` transports
this predicate to that one. -/
def RealSpectrumIntervalExteriorGap
    (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (β α δ : ℝ) : Prop :=
  (TauCeti.LinearPMap.realSpectrum A ⊆ Set.Icc β α ∧
    TauCeti.LinearPMap.realSpectrum B ⊆ {x | x ≤ β - δ ∨ α + δ ≤ x}) ∨
  (TauCeti.LinearPMap.realSpectrum B ⊆ Set.Icc β α ∧
    TauCeti.LinearPMap.realSpectrum A ⊆ {x | x ≤ β - δ ∨ α + δ ≤ x})

/-- Every gap configuration the `sin Θ` endpoint needs, over the canonical
partial-map representation, with the two ordered configurations given as
operator-form bounds.  The ordered constructors allow both diagonal blocks to be
genuinely unbounded; only the interval/exterior constructor has a bounded
spectral block.

For self-adjoint blocks `TauCeti.LinearPMap.SemiboundedBelow A c` and
`ofReal ⁻¹' spectrum A ⊆ Set.Ici c` describe the same configuration but are
different propositions.  `SpectralSylvesterGap` is the spectral spelling and
implies this one (`formBoundedSylvesterGap_of_spectral`); the converse is proved
for the `intervalExterior` constructor only. -/
inductive FormBoundedSylvesterGap
    (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (δ : ℝ) : Prop where
  | intervalExterior
      {β α : ℝ}
      (hβα : β ≤ α)
      (hgap : RealSpectrumIntervalExteriorGap A B β α δ)
  | leftAboveRightBelow
      (c : ℝ)
      (hA : TauCeti.LinearPMap.SemiboundedBelow A (c + δ))
      (hB : TauCeti.LinearPMap.SemiboundedAbove B c)
  | leftBelowRightAbove
      (c : ℝ)
      (hA : TauCeti.LinearPMap.SemiboundedAbove A c)
      (hB : TauCeti.LinearPMap.SemiboundedBelow B (c + δ))

/-! ## Unitary invariance

Every configuration of the gap is a statement about the real spectrum or about
an operator form, and a unitary equivalence preserves both.  Both slots are
covered separately rather than jointly so that a caller conjugating only one
block does not have to insert an identity conjugation on the other.

This is what carries the source separation hypothesis across the reflection in
the ambient double-angle theorem: there the perturbed operator is the reflection
conjugate of the unperturbed one, and its reducing restriction is the conjugate
of the original restriction.  Every constructor, including both half-infinite
ones, transports; nothing collapses to the bounded-interval case. -/

variable {E' F' : Type v}
  [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F']

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] in
/-- The interval/exterior configuration is invariant under conjugating the left
block by a unitary. -/
theorem RealSpectrumIntervalExteriorGap.unitaryConj_left
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F} {β α δ : ℝ}
    (W : E ≃ₗᵢ[𝕜] E') (h : RealSpectrumIntervalExteriorGap A B β α δ) :
    RealSpectrumIntervalExteriorGap (TauCeti.LinearPMap.unitaryConj W A) B β α δ := by
  rw [RealSpectrumIntervalExteriorGap, TauCeti.LinearPMap.realSpectrum_unitaryConj]
  exact h

omit [CompleteSpace E] [CompleteSpace F] in
/-- The interval/exterior configuration is invariant under conjugating the right
block by a unitary. -/
theorem RealSpectrumIntervalExteriorGap.unitaryConj_right
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F} {β α δ : ℝ}
    (V : F ≃ₗᵢ[𝕜] F') (h : RealSpectrumIntervalExteriorGap A B β α δ) :
    RealSpectrumIntervalExteriorGap A (TauCeti.LinearPMap.unitaryConj V B) β α δ := by
  rw [RealSpectrumIntervalExteriorGap, TauCeti.LinearPMap.realSpectrum_unitaryConj]
  exact h

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] in
/-- **The form-bounded gap is invariant under a unitary conjugation of the left
block**, in every configuration. -/
theorem FormBoundedSylvesterGap.unitaryConj_left
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F} {δ : ℝ}
    (W : E ≃ₗᵢ[𝕜] E') (h : FormBoundedSylvesterGap A B δ) :
    FormBoundedSylvesterGap (TauCeti.LinearPMap.unitaryConj W A) B δ := by
  cases h with
  | intervalExterior hβα hgap =>
      exact .intervalExterior hβα (hgap.unitaryConj_left W)
  | leftAboveRightBelow c hA hB =>
      exact .leftAboveRightBelow c
        (TauCeti.LinearPMap.semiboundedBelow_unitaryConj_of W hA) hB
  | leftBelowRightAbove c hA hB =>
      exact .leftBelowRightAbove c
        (TauCeti.LinearPMap.semiboundedAbove_unitaryConj_of W hA) hB

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The form-bounded gap is invariant under a unitary conjugation of the right
block**, in every configuration. -/
theorem FormBoundedSylvesterGap.unitaryConj_right
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F} {δ : ℝ}
    (V : F ≃ₗᵢ[𝕜] F') (h : FormBoundedSylvesterGap A B δ) :
    FormBoundedSylvesterGap A (TauCeti.LinearPMap.unitaryConj V B) δ := by
  cases h with
  | intervalExterior hβα hgap =>
      exact .intervalExterior hβα (hgap.unitaryConj_right V)
  | leftAboveRightBelow c hA hB =>
      exact .leftAboveRightBelow c hA
        (TauCeti.LinearPMap.semiboundedAbove_unitaryConj_of V hB)
  | leftBelowRightAbove c hA hB =>
      exact .leftBelowRightAbove c hA
        (TauCeti.LinearPMap.semiboundedBelow_unitaryConj_of V hB)

/-! ## Transport along an equality of reducing subspaces

A spectral development can produce the same reducing restriction under two
different names for one subspace -- `selfAdjointSpectralSubspace A hA Bᶜ hB.compl`
and `(selfAdjointSpectralSubspace A hA B hB)ᗮ`, for instance.  Those are equal
submodules but distinct *types*, so the restrictions are not interchangeable by
`rw`.  `HasOrthogonalProjection`, `CompleteSpace` and `ReducesSubspace` are all
`Prop`s, so substituting the subspace equality identifies everything else. -/

omit [CompleteSpace E] in
/-- The gap survives renaming the right-hand reducing subspace. -/
theorem FormBoundedSylvesterGap.reducingRestriction_congr_right
    {G : Type v} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] 
    {X : E →ₗ.[𝕜] E} {A : G →ₗ.[𝕜] G} {p q : Submodule 𝕜 G}
    [p.HasOrthogonalProjection] [q.HasOrthogonalProjection]
     [CompleteSpace q]
    (h : p = q)
    (hp : TauCeti.LinearPMap.ReducesSubspace A p)
    (hq : TauCeti.LinearPMap.ReducesSubspace A q) {δ : ℝ}
    (hgap : FormBoundedSylvesterGap X
      (TauCeti.LinearPMap.reducingRestriction A p hp) δ) :
    FormBoundedSylvesterGap X
      (TauCeti.LinearPMap.reducingRestriction A q hq) δ := by
  subst h; exact hgap

omit [CompleteSpace E] in
/-- The gap survives renaming the left-hand reducing subspace. -/
theorem FormBoundedSylvesterGap.reducingRestriction_congr_left
    {G : Type v} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] 
    {X : E →ₗ.[𝕜] E} {A : G →ₗ.[𝕜] G} {p q : Submodule 𝕜 G}
    [p.HasOrthogonalProjection] [q.HasOrthogonalProjection]
     [CompleteSpace q]
    (h : p = q)
    (hp : TauCeti.LinearPMap.ReducesSubspace A p)
    (hq : TauCeti.LinearPMap.ReducesSubspace A q) {δ : ℝ}
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A p hp) X δ) :
    FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A q hq) X δ := by
  subst h; exact hgap

end Sylvester
end DavisKahan
end TauCeti
