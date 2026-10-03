/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.RealSpectrumCyclicModel

/-!
# The intertwining law of the cyclic model, on the real spectrum

`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/CyclicModel.lean` proves the intertwining
law `cyclicIsometry_coordMulLp`: the cyclic isometry carries multiplication by the **complex**
coordinate on `L²(μ_ξ)` to the action of `a` on `H`.
`ForTauCeti/Analysis/InnerProductSpace/RealSpectrumCyclicModel.lean` moved the isometry and its
range to `spectrum ℝ a`, and deliberately left the intertwining law behind: over the real
spectrum the natural operator is multiplication by the **real** coordinate
`x ↦ (x : ℝ) : ℂ`, which is a different operator on the nose -- a different function, on a
different domain, on a different `L²` space.  This module supplies that operator and proves the
law for it.

## What the transport actually costs

Nothing beyond one pointwise identity.  Both coordinate multiplications are `MemLp.toLp` of a
pointwise product, so the whole question is whether the two multipliers agree after transport,
and they do: `realSpectrumHomeomorph` *is* the real-part map on the spectrum, and
`coe_realSpectrumHomeomorph` says the real part of a point of the complex spectrum of a
self-adjoint operator, read back into `ℂ`, is that point again.  So on the nose

```text
((realSpectrumHomeomorph ha z : ℝ) : ℂ) = (z : ℂ)
```

and the two multipliers are literally equal at every transported point -- no almost-everywhere
argument on the multiplier, and no density argument.  The one measure-theoretic step is that an
almost-everywhere identity for `realSpectrumDiagMeasure` pulls back to one for `diagMeasure`,
which is `MeasurePreserving.quasiMeasurePreserving` applied to
`measurePreserving_realSpectrumHomeomorph`.

The boundedness data is reused rather than re-chosen: the real coordinate is the complex
coordinate read through `(realSpectrumHomeomorph ha).symm`, so
`(isBddMeasurable_coord (a := a)).chooseBound` bounds it too, and the operator norm bound is the
same constant as in `BorelCalculus/CyclicModel.lean`.

## Main results

* `TauCeti.BorelCalculus.isRealSpectrumBddMeasurable_realCoord`: the real coordinate symbol is
  admissible, with `measurable_realCoord` and `norm_realCoord_le` as its two halves.
* `TauCeti.BorelCalculus.realSpectrumCoordMulLp`: **multiplication by the real coordinate**, as
  a bounded operator on `Lp ℂ 2 (realSpectrumDiagMeasure ha ξ)`; the real-spectrum analogue of
  `coordMulLp`, defined the same way, with `realSpectrumCoordMulLp_apply` and
  `coeFn_realSpectrumCoordMulLp` as its characteristic equations.
* `TauCeti.BorelCalculus.realSpectrumDiagMeasureLpEquiv_realSpectrumCoordMulLp`: **the two
  coordinate multiplications agree after transport** -- the `L²` transport conjugates the real
  one into the complex one.  This is the whole content of the mission.
* `TauCeti.BorelCalculus.realSpectrumCyclicIsometry_realSpectrumCoordMulLp`: **the intertwining
  law on the real spectrum**, and `realSpectrumCyclicIsometry_realSpectrumCoordMulLp_comp` its
  operator form.
* `TauCeti.BorelCalculus.apply_mem_cyclicSubspace_of_realSpectrum`: invariance of the cyclic
  subspace, re-derived from the real-spectrum model alone.

## What is deliberately not delivered

Nothing here builds a multiplicity datum.  The cyclic *decomposition* and the field-indexed
`MultiplicityDatum ℝ` are separate families: the latter still has `base : Measure ℂ`, so changing
the spectral base to `Measure ℝ` is neither required nor supplied by this module.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.); written here, new for
  this library.
* Extraction class: **new**.  The definition mirrors `TauCeti.BorelCalculus.coordMulLp` field
  for field; the transport lemma is `coe_realSpectrumHomeomorph` under
  `coeFn_realSpectrumDiagMeasureLpEquiv`, and the law itself is then
  `cyclicIsometry_coordMulLp` unchanged.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

@[expose] public section

open MeasureTheory

namespace TauCeti
namespace BorelCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {a : H →L[ℂ] H}

section Symbol

omit [CompleteSpace H] in
/-- The real coordinate symbol -- the inclusion of the real spectrum into `ℂ` -- is measurable,
being continuous for the subspace topology. -/
theorem measurable_realCoord : Measurable (fun x : spectrum ℝ a => ((x : ℝ) : ℂ)) :=
  (Complex.continuous_ofReal.comp continuous_subtype_val).measurable

/-- **The real coordinate is bounded by the complex coordinate's bound.**  A point of
`spectrum ℝ a` is the real part of a point of `spectrum ℂ a`, and reading it back into `ℂ`
returns that point, so the bound chosen for the complex coordinate serves unchanged.  Reusing
the constant is what keeps the operator norm bound below identical to the complex one. -/
theorem norm_realCoord_le (ha : IsSelfAdjoint a) (x : spectrum ℝ a) :
    ‖((x : ℝ) : ℂ)‖ ≤ (isBddMeasurable_coord (a := a)).chooseBound := by
  rw [← realSpectrumHomeomorph_symm_apply_coe ha x]
  exact (isBddMeasurable_coord (a := a)).norm_le_chooseBound _

/-- **The real coordinate symbol is admissible** for the real-spectrum bounded Borel symbol
algebra: measurable and uniformly bounded. -/
theorem isRealSpectrumBddMeasurable_realCoord (ha : IsSelfAdjoint a) :
    IsRealSpectrumBddMeasurable (fun x : spectrum ℝ a => ((x : ℝ) : ℂ)) :=
  ⟨measurable_realCoord, (isBddMeasurable_coord (a := a)).chooseBound,
    (isBddMeasurable_coord (a := a)).chooseBound_nonneg, norm_realCoord_le ha⟩

end Symbol

section Multiplication

/-- The real coordinate multiple of an `L²` class is again `L²`, because the real spectrum is
bounded.  This is `memLp_coord_mul` with the real coordinate in place of the complex one. -/
theorem memLp_realCoord_mul (ha : IsSelfAdjoint a) (ξ : H)
    (F : Lp ℂ 2 (realSpectrumDiagMeasure ha ξ)) :
    MemLp (fun x : spectrum ℝ a => ((x : ℝ) : ℂ) * F x) 2 (realSpectrumDiagMeasure ha ξ) := by
  refine MemLp.mono' ((Lp.memLp F).norm.const_mul
    (isBddMeasurable_coord (a := a)).chooseBound) ?_ ?_
  · exact (measurable_realCoord (a := a)).aestronglyMeasurable.mul (Lp.aestronglyMeasurable F)
  · filter_upwards with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_realCoord_le ha x) (norm_nonneg _)

/-- **The bound that makes real coordinate multiplication a bounded operator.**  Squaring both
sides turns it into `∫ ‖x F x‖² ≤ C² ∫ ‖F x‖²`, which is `integral_mono` against the uniform
bound on the real coordinate.  The proof is `norm_toLp_coord_mul_le` with the real coordinate
substituted; the constant is the same one. -/
theorem norm_toLp_realCoord_mul_le (ha : IsSelfAdjoint a) (ξ : H)
    (F : Lp ℂ 2 (realSpectrumDiagMeasure ha ξ)) :
    ‖MemLp.toLp (fun x : spectrum ℝ a => ((x : ℝ) : ℂ) * F x) (memLp_realCoord_mul ha ξ F)‖
      ≤ (isBddMeasurable_coord (a := a)).chooseBound * ‖F‖ := by
  set C := (isBddMeasurable_coord (a := a)).chooseBound with hCdef
  have hC0 : 0 ≤ C := (isBddMeasurable_coord (a := a)).chooseBound_nonneg
  have hmeas : AEStronglyMeasurable (fun x : spectrum ℝ a => ((x : ℝ) : ℂ) * F x)
      (realSpectrumDiagMeasure ha ξ) :=
    (measurable_realCoord (a := a)).aestronglyMeasurable.mul (Lp.aestronglyMeasurable F)
  have hint1 : Integrable (fun x : spectrum ℝ a => ‖((x : ℝ) : ℂ) * F x‖ ^ 2)
      (realSpectrumDiagMeasure ha ξ) :=
    (memLp_two_iff_integrable_sq_norm hmeas).mp (memLp_realCoord_mul ha ξ F)
  have hint2 : Integrable
      (fun x : spectrum ℝ a => ‖(F : spectrum ℝ a → ℂ) x‖ ^ 2) (realSpectrumDiagMeasure ha ξ) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable F)).mp (Lp.memLp F)
  have hsq : ‖MemLp.toLp (fun x : spectrum ℝ a => ((x : ℝ) : ℂ) * F x)
      (memLp_realCoord_mul ha ξ F)‖ ^ 2 ≤ (C * ‖F‖) ^ 2 := by
    rw [norm_toLp_two_sq]
    calc ∫ x, ‖((x : ℝ) : ℂ) * F x‖ ^ 2 ∂(realSpectrumDiagMeasure ha ξ)
        ≤ ∫ x, C ^ 2 * ‖(F : spectrum ℝ a → ℂ) x‖ ^ 2 ∂(realSpectrumDiagMeasure ha ξ) := by
          refine integral_mono hint1 (hint2.const_mul _) fun x => ?_
          rw [norm_mul, mul_pow]
          have hx := norm_realCoord_le ha x
          have hsqx : ‖((x : ℝ) : ℂ)‖ ^ 2 ≤ C ^ 2 := by
            nlinarith [norm_nonneg (((x : ℝ) : ℂ))]
          nlinarith [sq_nonneg ‖(F : spectrum ℝ a → ℂ) x‖]
      _ = C ^ 2 * ∫ x, ‖(F : spectrum ℝ a → ℂ) x‖ ^ 2 ∂(realSpectrumDiagMeasure ha ξ) :=
          integral_const_mul _ _
      _ = (C * ‖F‖) ^ 2 := by rw [← norm_Lp_two_sq]; ring
  nlinarith [norm_nonneg (MemLp.toLp (fun x : spectrum ℝ a => ((x : ℝ) : ℂ) * F x)
    (memLp_realCoord_mul ha ξ F)), mul_nonneg hC0 (norm_nonneg F)]

/-- **Multiplication by the real coordinate**, as a bounded operator on `L²` of the
real-spectrum diagonal measure of `ξ`.

This is the real-spectrum analogue of `TauCeti.BorelCalculus.coordMulLp`, built the same way:
`LinearMap.mkContinuous` of the pointwise product, with the bound
`(isBddMeasurable_coord (a := a)).chooseBound`.  It is *not* `coordMulLp` transported -- the
multiplier is the real coordinate `x ↦ (x : ℝ) : ℂ` on `spectrum ℝ a`, a different function on
a different domain.  That the two nevertheless correspond under the `L²` transport is
`realSpectrumDiagMeasureLpEquiv_realSpectrumCoordMulLp`. -/
noncomputable def realSpectrumCoordMulLp (ha : IsSelfAdjoint a) (ξ : H) :
    Lp ℂ 2 (realSpectrumDiagMeasure ha ξ) →L[ℂ] Lp ℂ 2 (realSpectrumDiagMeasure ha ξ) :=
  LinearMap.mkContinuous
    { toFun := fun F => MemLp.toLp (fun x : spectrum ℝ a => ((x : ℝ) : ℂ) * F x)
        (memLp_realCoord_mul ha ξ F)
      map_add' := fun F G => by
        rw [← MemLp.toLp_add (memLp_realCoord_mul ha ξ F) (memLp_realCoord_mul ha ξ G)]
        refine (MemLp.toLp_eq_toLp_iff _ _).2 ?_
        filter_upwards [Lp.coeFn_add F G] with x hx
        simp only [Pi.add_apply, hx]
        ring
      map_smul' := fun c F => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul c (memLp_realCoord_mul ha ξ F)]
        refine (MemLp.toLp_eq_toLp_iff _ _).2 ?_
        filter_upwards [Lp.coeFn_smul c F] with x hx
        simp only [Pi.smul_apply, hx, smul_eq_mul]
        ring }
    (isBddMeasurable_coord (a := a)).chooseBound (norm_toLp_realCoord_mul_le ha ξ)

private theorem realSpectrumCoordMulLp_apply_aux (ha : IsSelfAdjoint a) (ξ : H)
    (F : Lp ℂ 2 (realSpectrumDiagMeasure ha ξ)) :
    realSpectrumCoordMulLp ha ξ F
      = MemLp.toLp (fun x : spectrum ℝ a => ((x : ℝ) : ℂ) * F x)
          (memLp_realCoord_mul ha ξ F) := rfl

/-- Real coordinate multiplication, unfolded: the characteristic equation, so no consumer needs
the body of the definition. -/
theorem realSpectrumCoordMulLp_apply (ha : IsSelfAdjoint a) (ξ : H)
    (F : Lp ℂ 2 (realSpectrumDiagMeasure ha ξ)) :
    realSpectrumCoordMulLp ha ξ F
      = MemLp.toLp (fun x : spectrum ℝ a => ((x : ℝ) : ℂ) * F x)
          (memLp_realCoord_mul ha ξ F) :=
  realSpectrumCoordMulLp_apply_aux ha ξ F

/-- Real coordinate multiplication really is pointwise multiplication by the real coordinate,
almost everywhere for the real-spectrum diagonal measure. -/
theorem coeFn_realSpectrumCoordMulLp (ha : IsSelfAdjoint a) (ξ : H)
    (F : Lp ℂ 2 (realSpectrumDiagMeasure ha ξ)) :
    (realSpectrumCoordMulLp ha ξ F : spectrum ℝ a → ℂ)
      =ᵐ[realSpectrumDiagMeasure ha ξ] fun x => ((x : ℝ) : ℂ) * F x := by
  rw [realSpectrumCoordMulLp_apply]
  exact MemLp.coeFn_toLp _

end Multiplication

section Transport

/-- **The two coordinate multiplications agree after transport.**

The `L²` transport `realSpectrumDiagMeasureLpEquiv` conjugates multiplication by the real
coordinate on `L²` of the real-spectrum diagonal measure into multiplication by the complex
coordinate on `L²` of the diagonal measure.

This is the single new fact the real-spectrum intertwining law needs, and it is where
`realSpectrumHomeomorph` being *the real-part map on the spectrum* is used: at a point `z` of
`spectrum ℂ a` the transported multiplier is `((realSpectrumHomeomorph ha z : ℝ) : ℂ)`, which
`coe_realSpectrumHomeomorph` identifies with `(z : ℂ)` on the nose.  The only measure theory is
that an almost-everywhere identity for the pushforward pulls back along the measure-preserving
homeomorphism. -/
theorem realSpectrumDiagMeasureLpEquiv_realSpectrumCoordMulLp (ha : IsSelfAdjoint a) (ξ : H)
    (F : Lp ℂ 2 (realSpectrumDiagMeasure ha ξ)) :
    realSpectrumDiagMeasureLpEquiv ha ξ (realSpectrumCoordMulLp ha ξ F)
      = coordMulLp ha.isStarNormal ξ (realSpectrumDiagMeasureLpEquiv ha ξ F) := by
  have hpull := (measurePreserving_realSpectrumHomeomorph ha ξ).quasiMeasurePreserving.ae_eq_comp
    (coeFn_realSpectrumCoordMulLp ha ξ F)
  refine Lp.ext ?_
  filter_upwards [coeFn_realSpectrumDiagMeasureLpEquiv ha ξ (realSpectrumCoordMulLp ha ξ F),
    hpull, coeFn_coordMulLp ha.isStarNormal ξ (realSpectrumDiagMeasureLpEquiv ha ξ F),
    coeFn_realSpectrumDiagMeasureLpEquiv ha ξ F] with z h1 h2 h3 h4
  simp only [Function.comp_apply] at h1 h2 h4
  rw [h1, h2, h3, h4, coe_realSpectrumHomeomorph ha z]

end Transport

section Intertwining

/-- **The intertwining law of the cyclic model, on the real spectrum.**

The real-spectrum cyclic isometry carries multiplication by the **real** coordinate on
`L²` of the real-spectrum diagonal measure to the action of `a` on `H`:

```text
Φ_ℝ (x · F) = a (Φ_ℝ F)   for every F in L²(spectrum ℝ a, μ_ξ).
```

With `range_realSpectrumCyclicIsometry` this says that `a`, restricted to the cyclic subspace
generated by `ξ`, *is* multiplication by the real spectral parameter -- which is the statement
a real-parameter spectral multiplicity theory is phrased against.

No density argument is re-run: the law is `cyclicIsometry_coordMulLp` composed with
`realSpectrumDiagMeasureLpEquiv_realSpectrumCoordMulLp`, and the latter is a pointwise identity
of multipliers. -/
theorem realSpectrumCyclicIsometry_realSpectrumCoordMulLp (ha : IsSelfAdjoint a) (ξ : H)
    (F : Lp ℂ 2 (realSpectrumDiagMeasure ha ξ)) :
    realSpectrumCyclicIsometry ha ξ (realSpectrumCoordMulLp ha ξ F)
      = a (realSpectrumCyclicIsometry ha ξ F) := by
  rw [realSpectrumCyclicIsometry_apply, realSpectrumCyclicIsometry_apply,
    realSpectrumDiagMeasureLpEquiv_realSpectrumCoordMulLp]
  exact cyclicIsometry_coordMulLp ha.isStarNormal ξ (realSpectrumDiagMeasureLpEquiv ha ξ F)

/-- **The intertwining law in operator form.**  The same statement as a composition of
continuous linear maps, which is the shape a consumer building a unitary equivalence
consumes. -/
theorem realSpectrumCyclicIsometry_realSpectrumCoordMulLp_comp (ha : IsSelfAdjoint a) (ξ : H) :
    (realSpectrumCyclicIsometry ha ξ).toContinuousLinearMap.comp
        (realSpectrumCoordMulLp ha ξ)
      = a.comp (realSpectrumCyclicIsometry ha ξ).toContinuousLinearMap :=
  ContinuousLinearMap.ext (realSpectrumCyclicIsometry_realSpectrumCoordMulLp ha ξ)

/-- **The cyclic subspace is invariant under its operator**, re-derived from the real-spectrum
model alone.  This is `apply_mem_cyclicSubspace` with the real coordinate supplying the
preimage, and it is the first consumer showing the real-spectrum model is as usable as the
complex one. -/
theorem apply_mem_cyclicSubspace_of_realSpectrum (ha : IsSelfAdjoint a) (ξ : H) {y : H}
    (hy : y ∈ cyclicSubspace ha.isStarNormal ξ) : a y ∈ cyclicSubspace ha.isStarNormal ξ := by
  obtain ⟨F, rfl⟩ := exists_realSpectrumCyclicIsometry_eq ha ξ hy
  rw [← realSpectrumCyclicIsometry_realSpectrumCoordMulLp ha ξ F]
  exact realSpectrumCyclicIsometry_mem_cyclicSubspace ha ξ _

end Intertwining

end BorelCalculus
end TauCeti
