/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.RealSpectrumIntertwining
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.SeparableCyclic
public import LeanPool.DavisKahan.ForTauCeti.MeasureTheory.LpSliceSum

/-!
# The cyclic decomposition of a Hilbert space, over the real spectrum

`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/CyclicDecomposition.lean` and
`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/SeparableCyclic.lean` decompose `H` into an
orthogonal family of cyclic subspaces and identify each with `L²` of a scalar spectral measure on
`spectrum ℂ a`.  This module restates those decompositions over `spectrum ℝ a` for a self-adjoint
`a`, and adds the diagonality statement: on each summand the operator is multiplication by the
**real** spectral parameter.

## Why the decomposition costs one lemma and not a new Zorn argument

Orthogonality is *not* re-proved here, and neither is totality.  `TauCeti.BorelCalculus`'s
`realSpectrumCyclicIsometry ha ξ` is by construction `cyclicIsometry ha.isStarNormal ξ`
precomposed with the isometric **equivalence** `realSpectrumDiagMeasureLpEquiv ha ξ`, and
`TauCeti.isHilbertSum_comp_linearIsometryEquiv` already says a Hilbert sum survives precomposing
every summand embedding with an equivalence -- it changes neither the pairwise inner products nor
the ranges.  So the whole decomposition transports by one application of an existing lemma, with
the index family `ξ` reused verbatim: the index type is untouched by the change of spectrum,
because the transport acts inside each summand and not on the indexing.

The diagonality statement is the intertwining law
`realSpectrumCyclicIsometry_realSpectrumCoordMulLp`, read once per index.  Its shape is exactly
the hypothesis `hA` of `TauCeti.operatorUnitaryEquiv_of_isHilbertSum`.

## Why the base measure stays complex

`map_ofReal_realSpectrumDiagMeasure` records that pushing the real-spectrum diagonal measure off
its subtype **into `ℂ`** returns literally the measure that `exists_hasMultiplicityModel` already
uses.  This is now the intended base-measure route: `TauCeti.MultiplicityDatum 𝕜` keeps
`base : Measure ℂ` for both scalar fields, while only its `L²` operator is field-indexed.
Consequently no push-forward into `Measure ℝ` is required to obtain a real multiplication model.

## Main results

* `TauCeti.BorelCalculus.exists_isHilbertSum_lp_realSpectrumDiagMeasure`: the cyclic
  decomposition over the real spectrum, indexed by an arbitrary type and with no separability
  hypothesis.
* `TauCeti.BorelCalculus.exists_linearIsometryEquiv_lp_realSpectrumDiagMeasure`: the same as an
  `ℓ²`-sum presentation of `H`.
* `TauCeti.BorelCalculus.exists_countable_isHilbertSum_lp_realSpectrumDiagMeasure`: the
  `ℕ`-indexed form, on a separable space.
* `TauCeti.BorelCalculus.exists_countable_isHilbertSum_realSpectrumCoordMulLp`: **the
  deliverable** -- the `ℕ`-indexed decomposition together with the statement that `a` acts on
  each summand as multiplication by the real spectral parameter.
* `TauCeti.BorelCalculus.map_ofReal_realSpectrumDiagMeasure`: the measured obstruction described
  above.

## What is deliberately not delivered

This module does not build the real multiplicity normal form.  The field-indexed
`TauCeti.MultiplicityDatum 𝕜` is defined in `BorelCalculus/MultiplicityModel`; this file supplies
the real-spectrum decomposition that a later real model theorem consumes.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.); written here, new for
  this library.
* Extraction class: **new**.  Each decomposition statement is one application of
  `TauCeti.isHilbertSum_comp_linearIsometryEquiv` to the corresponding complex-spectrum
  statement; the diagonality statement is `realSpectrumCyclicIsometry_realSpectrumCoordMulLp`.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

public section

open MeasureTheory

universe u

namespace TauCeti
namespace BorelCalculus

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {a : H →L[ℂ] H}

section Transport

private theorem realSpectrumCyclicIsometry_eq_comp_aux (ha : IsSelfAdjoint a) {ι : Type*}
    (ξ : ι → H) :
    (fun i => (cyclicIsometry ha.isStarNormal (ξ i)).comp
        (realSpectrumDiagMeasureLpEquiv ha (ξ i)).toLinearIsometry)
      = fun i => realSpectrumCyclicIsometry ha (ξ i) :=
  funext fun i =>
    LinearIsometry.ext fun F => (realSpectrumCyclicIsometry_apply ha (ξ i) F).symm

/-- **A cyclic Hilbert sum decomposition transports to the real spectrum.**

Given any family `ξ` whose complex-spectrum cyclic models assemble `H` as a Hilbert sum, the
real-spectrum models of the *same* family do too.  The index family is reused verbatim: the
transport is an equivalence inside each summand and touches neither the index type nor the
orthogonality bookkeeping. -/
theorem isHilbertSum_lp_realSpectrumDiagMeasure_of_isHilbertSum (ha : IsSelfAdjoint a)
    {ι : Type*} {ξ : ι → H}
    (hsum : IsHilbertSum ℂ (fun i => Lp ℂ 2 (diagMeasure ha.isStarNormal (ξ i)))
      (fun i => cyclicIsometry ha.isStarNormal (ξ i))) :
    IsHilbertSum ℂ (fun i => Lp ℂ 2 (realSpectrumDiagMeasure ha (ξ i)))
      (fun i => realSpectrumCyclicIsometry ha (ξ i)) := by
  rw [← realSpectrumCyclicIsometry_eq_comp_aux ha ξ]
  exact isHilbertSum_comp_linearIsometryEquiv hsum fun i =>
    realSpectrumDiagMeasureLpEquiv ha (ξ i)

end Transport

section Decomposition

/-- **The cyclic decomposition of a Hilbert space under a self-adjoint operator, over its real
spectrum.**

`H` is the Hilbert sum of the `L²` spaces of the **real-spectrum** scalar spectral measures of a
family of vectors, embedded by `realSpectrumCyclicIsometry`.  As in the complex-spectrum
statement the index type is arbitrary and no separability hypothesis is used. -/
theorem exists_isHilbertSum_lp_realSpectrumDiagMeasure (ha : IsSelfAdjoint a) :
    ∃ (ι : Type u) (ξ : ι → H),
      IsHilbertSum ℂ (fun i => Lp ℂ 2 (realSpectrumDiagMeasure ha (ξ i)))
        (fun i => realSpectrumCyclicIsometry ha (ξ i)) := by
  obtain ⟨ι, ξ, hsum⟩ := exists_isHilbertSum_lp_diagMeasure ha.isStarNormal
  exact ⟨ι, ξ, isHilbertSum_lp_realSpectrumDiagMeasure_of_isHilbertSum ha hsum⟩

/-- **The real-spectrum multiplication model, globally.**  Every complex Hilbert space carrying a
bounded self-adjoint operator is isometrically the `ℓ²`-sum of `L²` spaces of scalar spectral
measures **on the real spectrum**.  No separability hypothesis is used. -/
theorem exists_linearIsometryEquiv_lp_realSpectrumDiagMeasure (ha : IsSelfAdjoint a) :
    ∃ (ι : Type u) (ξ : ι → H),
      Nonempty (H ≃ₗᵢ[ℂ] lp (fun i => Lp ℂ 2 (realSpectrumDiagMeasure ha (ξ i))) 2) := by
  obtain ⟨ι, ξ, hsum⟩ := exists_isHilbertSum_lp_realSpectrumDiagMeasure ha
  exact ⟨ι, ξ, ⟨hsum.linearIsometryEquiv⟩⟩

/-- **The real-spectrum cyclic decomposition of a separable space, indexed by `ℕ`.**

This is `exists_countable_isHilbertSum_lp_diagMeasure_complex` transported; in particular the
enumeration
and the zero-padding of `SeparableCyclic.lean` are reused rather than repeated, because the
transport does not touch the index. -/
theorem exists_countable_isHilbertSum_lp_realSpectrumDiagMeasure
    [TopologicalSpace.SeparableSpace H] (ha : IsSelfAdjoint a) :
    ∃ ξ : ℕ → H, IsHilbertSum ℂ (fun n => Lp ℂ 2 (realSpectrumDiagMeasure ha (ξ n)))
      (fun n => realSpectrumCyclicIsometry ha (ξ n)) := by
  obtain ⟨ξ, hsum⟩ := exists_countable_isHilbertSum_lp_diagMeasure_complex ha.isStarNormal
  exact ⟨ξ, isHilbertSum_lp_realSpectrumDiagMeasure_of_isHilbertSum ha hsum⟩

end Decomposition

section Diagonal

/-- **The real-spectrum diagonalisation of a self-adjoint operator on a separable space.**

There is a countable family of vectors such that `H` is the Hilbert sum of the `L²` spaces of
their real-spectrum scalar spectral measures, and on each summand `a` acts as multiplication by
the **real** spectral parameter.

The second component is `realSpectrumCyclicIsometry_realSpectrumCoordMulLp` read once per index,
and it is stated in exactly the shape of the hypothesis `hA` of
`TauCeti.operatorUnitaryEquiv_of_isHilbertSum`, which is what a consumer building a unitary
equivalence to a concrete multiplication operator needs. -/
theorem exists_countable_isHilbertSum_realSpectrumCoordMulLp
    [TopologicalSpace.SeparableSpace H] (ha : IsSelfAdjoint a) :
    ∃ ξ : ℕ → H,
      IsHilbertSum ℂ (fun n => Lp ℂ 2 (realSpectrumDiagMeasure ha (ξ n)))
        (fun n => realSpectrumCyclicIsometry ha (ξ n)) ∧
      ∀ (n : ℕ) (F : Lp ℂ 2 (realSpectrumDiagMeasure ha (ξ n))),
        a (realSpectrumCyclicIsometry ha (ξ n) F)
          = realSpectrumCyclicIsometry ha (ξ n) (realSpectrumCoordMulLp ha (ξ n) F) := by
  obtain ⟨ξ, hsum⟩ := exists_countable_isHilbertSum_lp_realSpectrumDiagMeasure ha
  exact ⟨ξ, hsum, fun n F =>
    (realSpectrumCyclicIsometry_realSpectrumCoordMulLp ha (ξ n) F).symm⟩

end Diagonal

section Obstruction

/-- **The real-spectrum model collapses onto the complex one when read back into `ℂ`.**

Pushing the real-spectrum diagonal measure off its subtype into `ℂ` gives literally the measure
`exists_hasMultiplicityModel` already builds its `TauCeti.MultiplicityDatum` from -- because
`coe_realSpectrumHomeomorph` identifies the transported real coordinate with the complex
coordinate on the nose, so the two push-forwards agree pointwise, not merely almost everywhere.

The statement is load-bearing for planning because it rules out `Measure ℝ` as a necessary
axis.  A real-valued multiplication model can reuse this same `Measure ℂ` base and instantiate
`MultiplicityDatum ℝ`; only the operator value field changes. -/
theorem map_ofReal_realSpectrumDiagMeasure (ha : IsSelfAdjoint a) (ξ : H) :
    (realSpectrumDiagMeasure ha ξ).map (fun x : spectrum ℝ a => ((x : ℝ) : ℂ))
      = (diagMeasure ha.isStarNormal ξ).map (fun z : spectrum ℂ a => (z : ℂ)) := by
  rw [realSpectrumDiagMeasure_eq_map,
    Measure.map_map measurable_realCoord (measurable_realSpectrumHomeomorph ha)]
  exact Measure.map_congr (Filter.Eventually.of_forall fun z => coe_realSpectrumHomeomorph ha z)

end Obstruction

end BorelCalculus
end TauCeti
