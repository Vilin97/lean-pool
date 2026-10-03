/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.RealSpectrumBorelSymbols
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The diagonal spectral measure of a self-adjoint operator, on its real spectrum

`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean` builds
`TauCeti.BorelCalculus.diagMeasure`, the scalar spectral measure of a vector, as a measure on
`spectrum ℂ a`.  `ForTauCeti/Analysis/InnerProductSpace/RealSpectrumBorelSymbols.lean` has
already moved the *symbol* side of the cyclic multiplication model to `spectrum ℝ a`.  This
module moves the *measure* side.

The two sides are independent.  A symbol is a function, so it transports by reindexing; a
measure is not, and it transports by pushforward.  Both transports run along one map,
`TauCeti.realSpectrumHomeomorph ha : spectrum ℂ a ≃ₜ spectrum ℝ a`, which is a Borel
isomorphism because both spectra carry the subspace Borel σ-algebra.

## What is delivered

`realSpectrumDiagMeasure ha ξ` is the pushforward of `diagMeasure ha.isStarNormal ξ` along the
homeomorphism, and `measurePreserving_realSpectrumHomeomorph` says the homeomorphism is
measure-preserving between the two.  Because the map is a Borel *isomorphism*, the same
statement holds in the other direction
(`measurePreserving_realSpectrumHomeomorph_symm`), and that is what upgrades the `Lp`
transport from a linear isometry to a linear isometric *equivalence*:

```text
realSpectrumDiagMeasureLpEquiv ha ξ :
  Lp ℂ 2 (realSpectrumDiagMeasure ha ξ) ≃ₗᵢ[ℂ] Lp ℂ 2 (diagMeasure ha.isStarNormal ξ)
```

Mathlib supplies `MeasureTheory.Lp.compMeasurePreservingₗᵢ` in each direction; what it does not
supply is the equivalence, because `Lp.compMeasurePreserving_comp_apply` composes the two
underlying maps into a composite whose *function argument* is `f ∘ f'` rather than `id`.  The
private lemma `lp_compMeasurePreserving_eq_self_of_eq_id` closes exactly that gap, by
substituting the function equality before appealing to
`MeasureTheory.Lp.compMeasurePreserving_id_apply`; `MeasurePreserving` is a `Prop`, so the
accompanying measure-preservation proof needs no transport.

## What is deliberately not delivered

Nothing here touches `BorelCalculus/`.  `cyclicIsometry` still lands in
`Lp ℂ 2 (diagMeasure ha.isStarNormal ξ)`, and restating it over the real spectrum is a
separate step: it is now the single composition
`(cyclicIsometry ha.isStarNormal ξ).comp (realSpectrumDiagMeasureLpEquiv ha ξ).toLinearIsometry`,
which has its own compile budget because `range_cyclicIsometry` is where the refuted
lower-the-scalars route died.

## Main results

* `TauCeti.BorelCalculus.realSpectrumDiagMeasure`: the real-spectrum diagonal measure, as a
  pushforward, with `realSpectrumDiagMeasure_eq_map` as its characteristic lemma and
  `instIsFiniteMeasure_realSpectrumDiagMeasure` recording finiteness.
* `TauCeti.BorelCalculus.measurePreserving_realSpectrumHomeomorph` and
  `TauCeti.BorelCalculus.measurePreserving_realSpectrumHomeomorph_symm`: the measure-preserving
  statement, in both directions.
* `TauCeti.BorelCalculus.realSpectrumDiagMeasure_apply` and
  `TauCeti.BorelCalculus.integral_realSpectrumDiagMeasure`: the change-of-variables identities
  on sets and on integrals.
* `TauCeti.BorelCalculus.realSpectrumDiagMeasureLpEquiv`: **the deliverable** — the `ℂ`-linear
  isometric equivalence of the two `L²` spaces, with `realSpectrumDiagMeasureLpEquiv_apply`,
  `coeFn_realSpectrumDiagMeasureLpEquiv` and `coeFn_realSpectrumDiagMeasureLpEquiv_symm`
  naming its two underlying maps and their almost-everywhere values.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.); written here, new for
  this library.
* Extraction class: **new**.  The pushforward and the measure-preservation statement are
  immediate; the only assembled brick is the `Lp` equivalence, built from Mathlib's
  `Lp.compMeasurePreservingₗᵢ` in both directions.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

@[expose] public section

open MeasureTheory

namespace TauCeti
namespace BorelCalculus

section LpHelper

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Composing an `L²` class with a measure-preserving self-map that is the identity function
returns the class unchanged.

`MeasureTheory.Lp.compMeasurePreserving_id_apply` states this only for the literal function
`id`, and `MeasureTheory.Lp.compMeasurePreserving_comp_apply` produces a composite `f ∘ f'`
instead.  Substituting the function equality is what bridges them; the measure-preservation
argument needs no transport, `MeasurePreserving` being a `Prop`. -/
private theorem lp_compMeasurePreserving_eq_self_of_eq_id (f : α → α)
    (hmp : MeasurePreserving f μ μ) (hf : f = id) (F : Lp ℂ 2 μ) :
    Lp.compMeasurePreserving f hmp F = F := by
  subst hf
  exact Lp.compMeasurePreserving_id_apply F

end LpHelper

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {a : H →L[ℂ] H}

section Measure

/-- **The diagonal spectral measure of a self-adjoint operator, on its real spectrum.**

This is `diagMeasure ha.isStarNormal ξ` pushed forward along
`realSpectrumHomeomorph ha : spectrum ℂ a ≃ₜ spectrum ℝ a`.  It is the measure that
`realSpectrumBddSymbols a` is square-integrated against, and the real-spectrum counterpart of
the scalar spectral measure the cyclic multiplication model runs on. -/
noncomputable def realSpectrumDiagMeasure (ha : IsSelfAdjoint a) (ξ : H) :
    Measure (spectrum ℝ a) :=
  (diagMeasure ha.isStarNormal ξ).map (realSpectrumHomeomorph ha)

private theorem realSpectrumDiagMeasure_eq_map_aux (ha : IsSelfAdjoint a) (ξ : H) :
    realSpectrumDiagMeasure ha ξ
      = (diagMeasure ha.isStarNormal ξ).map (realSpectrumHomeomorph ha) := rfl

/-- The real-spectrum diagonal measure is the pushforward of the diagonal measure: the
characteristic lemma, so no consumer needs the body. -/
theorem realSpectrumDiagMeasure_eq_map (ha : IsSelfAdjoint a) (ξ : H) :
    realSpectrumDiagMeasure ha ξ
      = (diagMeasure ha.isStarNormal ξ).map (realSpectrumHomeomorph ha) :=
  realSpectrumDiagMeasure_eq_map_aux ha ξ

/-- The real-spectrum diagonal measure is finite, being the pushforward of a finite measure. -/
instance instIsFiniteMeasure_realSpectrumDiagMeasure (ha : IsSelfAdjoint a) (ξ : H) :
    IsFiniteMeasure (realSpectrumDiagMeasure ha ξ) := by
  rw [realSpectrumDiagMeasure_eq_map]
  exact Measure.isFiniteMeasure_map _ _

end Measure

section MeasurePreserving

/-- **The measure-preserving statement.**

`realSpectrumHomeomorph ha` carries the diagonal measure of `ξ` on `spectrum ℂ a` to its
real-spectrum counterpart on `spectrum ℝ a`.  Measurability is continuity of the
homeomorphism, and the pushforward identity is the definition of the target measure. -/
theorem measurePreserving_realSpectrumHomeomorph (ha : IsSelfAdjoint a) (ξ : H) :
    MeasurePreserving (realSpectrumHomeomorph ha) (diagMeasure ha.isStarNormal ξ)
      (realSpectrumDiagMeasure ha ξ) :=
  ⟨measurable_realSpectrumHomeomorph ha, (realSpectrumDiagMeasure_eq_map ha ξ).symm⟩

/-- **The measure-preserving statement, backward direction.**

The inverse homeomorphism carries the real-spectrum diagonal measure back.  This direction is
available only because the transport is along a Borel *isomorphism*, and it is what turns the
`L²` transport into an equivalence rather than a bare isometry. -/
theorem measurePreserving_realSpectrumHomeomorph_symm (ha : IsSelfAdjoint a) (ξ : H) :
    MeasurePreserving (realSpectrumHomeomorph ha).symm (realSpectrumDiagMeasure ha ξ)
      (diagMeasure ha.isStarNormal ξ) :=
  MeasurePreserving.symm (realSpectrumHomeomorph ha).toMeasurableEquiv
    (measurePreserving_realSpectrumHomeomorph ha ξ)

/-- **Change of variables on sets.**  The real-spectrum diagonal measure of a set is the
diagonal measure of its preimage under the homeomorphism. -/
theorem realSpectrumDiagMeasure_apply (ha : IsSelfAdjoint a) (ξ : H) (s : Set (spectrum ℝ a)) :
    realSpectrumDiagMeasure ha ξ s
      = diagMeasure ha.isStarNormal ξ (realSpectrumHomeomorph ha ⁻¹' s) :=
  ((measurePreserving_realSpectrumHomeomorph ha ξ).measure_preimage_equiv
    (f := (realSpectrumHomeomorph ha).toMeasurableEquiv) s).symm

/-- **Change of variables on integrals.**  Integrating against the real-spectrum diagonal
measure is integrating the reindexed integrand against the diagonal measure.  This is the form
in which the transport meets the defining property `integral_diagMeasure` of the diagonal
measure. -/
theorem integral_realSpectrumDiagMeasure (ha : IsSelfAdjoint a) (ξ : H)
    (g : spectrum ℝ a → ℂ) :
    ∫ x, g x ∂(realSpectrumDiagMeasure ha ξ)
      = ∫ z, g (realSpectrumHomeomorph ha z) ∂(diagMeasure ha.isStarNormal ξ) :=
  ((measurePreserving_realSpectrumHomeomorph ha ξ).integral_comp'
    (f := (realSpectrumHomeomorph ha).toMeasurableEquiv) g).symm

end MeasurePreserving

section LpTransport

/-- **The `L²` transport, and the deliverable of this module.**

Composition with `realSpectrumHomeomorph ha` is a `ℂ`-linear isometric equivalence from `L²`
of the real-spectrum diagonal measure onto `L²` of the diagonal measure, with composition
along the inverse homeomorphism as its inverse.  Both directions are
`MeasureTheory.Lp.compMeasurePreservingₗᵢ`; what is proved here is that they invert each
other, which is where the measure-preservation statement is used in both directions.

With this in hand, restating the cyclic multiplication model over the real spectrum is the
single composition of `cyclicIsometry` with this equivalence -- no further measure theory. -/
noncomputable def realSpectrumDiagMeasureLpEquiv (ha : IsSelfAdjoint a) (ξ : H) :
    Lp ℂ 2 (realSpectrumDiagMeasure ha ξ) ≃ₗᵢ[ℂ] Lp ℂ 2 (diagMeasure ha.isStarNormal ξ) where
  toLinearMap :=
    Lp.compMeasurePreservingₗ ℂ (realSpectrumHomeomorph ha)
      (measurePreserving_realSpectrumHomeomorph ha ξ)
  invFun :=
    Lp.compMeasurePreservingₗ ℂ (realSpectrumHomeomorph ha).symm
      (measurePreserving_realSpectrumHomeomorph_symm ha ξ)
  left_inv F := by
    refine (Lp.compMeasurePreserving_comp_apply (E := ℂ) (p := 2) F
      (measurePreserving_realSpectrumHomeomorph ha ξ)
      (measurePreserving_realSpectrumHomeomorph_symm ha ξ)).symm.trans ?_
    exact lp_compMeasurePreserving_eq_self_of_eq_id _ _
      (funext fun x => (realSpectrumHomeomorph ha).apply_symm_apply x) F
  right_inv F := by
    refine (Lp.compMeasurePreserving_comp_apply (E := ℂ) (p := 2) F
      (measurePreserving_realSpectrumHomeomorph_symm ha ξ)
      (measurePreserving_realSpectrumHomeomorph ha ξ)).symm.trans ?_
    exact lp_compMeasurePreserving_eq_self_of_eq_id _ _
      (funext fun z => (realSpectrumHomeomorph ha).symm_apply_apply z) F
  norm_map' := (Lp.norm_compMeasurePreserving · (measurePreserving_realSpectrumHomeomorph ha ξ))

private theorem realSpectrumDiagMeasureLpEquiv_apply_aux (ha : IsSelfAdjoint a) (ξ : H)
    (F : Lp ℂ 2 (realSpectrumDiagMeasure ha ξ)) :
    realSpectrumDiagMeasureLpEquiv ha ξ F
      = Lp.compMeasurePreserving (realSpectrumHomeomorph ha)
          (measurePreserving_realSpectrumHomeomorph ha ξ) F := rfl

/-- The equivalence is Mathlib's composition-with-a-measure-preserving-map, in the direction
that reindexes a real-spectrum class into a complex-spectrum one. -/
theorem realSpectrumDiagMeasureLpEquiv_apply (ha : IsSelfAdjoint a) (ξ : H)
    (F : Lp ℂ 2 (realSpectrumDiagMeasure ha ξ)) :
    realSpectrumDiagMeasureLpEquiv ha ξ F
      = Lp.compMeasurePreserving (realSpectrumHomeomorph ha)
          (measurePreserving_realSpectrumHomeomorph ha ξ) F :=
  realSpectrumDiagMeasureLpEquiv_apply_aux ha ξ F

private theorem realSpectrumDiagMeasureLpEquiv_symm_apply_aux (ha : IsSelfAdjoint a) (ξ : H)
    (G : Lp ℂ 2 (diagMeasure ha.isStarNormal ξ)) :
    (realSpectrumDiagMeasureLpEquiv ha ξ).symm G
      = Lp.compMeasurePreserving (realSpectrumHomeomorph ha).symm
          (measurePreserving_realSpectrumHomeomorph_symm ha ξ) G := rfl

/-- The inverse equivalence is composition with the inverse homeomorphism. -/
theorem realSpectrumDiagMeasureLpEquiv_symm_apply (ha : IsSelfAdjoint a) (ξ : H)
    (G : Lp ℂ 2 (diagMeasure ha.isStarNormal ξ)) :
    (realSpectrumDiagMeasureLpEquiv ha ξ).symm G
      = Lp.compMeasurePreserving (realSpectrumHomeomorph ha).symm
          (measurePreserving_realSpectrumHomeomorph_symm ha ξ) G :=
  realSpectrumDiagMeasureLpEquiv_symm_apply_aux ha ξ G

/-- **The pointwise description of the transport.**  As a function on `spectrum ℂ a`, the
image class is the original one read at the real part of the spectral point, almost everywhere
for the diagonal measure. -/
theorem coeFn_realSpectrumDiagMeasureLpEquiv (ha : IsSelfAdjoint a) (ξ : H)
    (F : Lp ℂ 2 (realSpectrumDiagMeasure ha ξ)) :
    (realSpectrumDiagMeasureLpEquiv ha ξ F : spectrum ℂ a → ℂ)
      =ᵐ[diagMeasure ha.isStarNormal ξ]
        (F : spectrum ℝ a → ℂ) ∘ realSpectrumHomeomorph ha := by
  rw [realSpectrumDiagMeasureLpEquiv_apply]
  exact Lp.coeFn_compMeasurePreserving F (measurePreserving_realSpectrumHomeomorph ha ξ)

/-- The pointwise description of the inverse transport, almost everywhere for the
real-spectrum diagonal measure. -/
theorem coeFn_realSpectrumDiagMeasureLpEquiv_symm (ha : IsSelfAdjoint a) (ξ : H)
    (G : Lp ℂ 2 (diagMeasure ha.isStarNormal ξ)) :
    ((realSpectrumDiagMeasureLpEquiv ha ξ).symm G : spectrum ℝ a → ℂ)
      =ᵐ[realSpectrumDiagMeasure ha ξ]
        (G : spectrum ℂ a → ℂ) ∘ (realSpectrumHomeomorph ha).symm := by
  rw [realSpectrumDiagMeasureLpEquiv_symm_apply]
  exact Lp.coeFn_compMeasurePreserving G (measurePreserving_realSpectrumHomeomorph_symm ha ξ)

end LpTransport

end BorelCalculus
end TauCeti
