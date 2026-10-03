/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.DiagMeasureMulLp
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.DiagMeasureNatural
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.MultiplicityModel

/-!
# The measure class of a multiplicity datum is a unitary invariant

Unitarily equivalent multiplicity models have equivalent base measures:

```text
OperatorUnitaryEquiv D.operator E.operator  →  MeasureEquiv D.base E.base.
```

This is the **measure-class half** of uniqueness for the multiplicity classification.  Together
with `operatorUnitaryEquiv_of_measureEquiv_complex`, which goes the other way, it says the measure
class
of a datum is exactly the part of the datum that the operator sees -- as far as measures go.
The level sets are the other half; they are settled in
`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/MultiplicityLevelUniqueness.lean`, which
combines both halves into the biconditional
`operatorUnitaryEquiv_iff_measureEquiv_and_level`.

## The argument, and the asymmetry that makes it work

Three ingredients, each already proved:

* `exists_measureEquiv_map_val_diagMeasure_mulLp` -- the model has a **maximal vector**, whose
  scalar spectral measure has exactly the measure class of `Prod.fst _* D.measure`.
* `map_val_diagMeasure_eq_of_intertwines` -- the scalar spectral measure is carried along by a
  unitary intertwiner.
* `map_val_diagMeasure_mulLp_absolutelyContinuous` -- *every* vector's spectral measure is
  dominated by the model's measure.

Note that the third is the weak statement and the first is the strong one, and that is enough:
the image `e F₀` of a maximal vector need not be maximal on the far side, and nothing here claims
it is.  Each direction of the final equivalence uses a maximal vector on **its own** side and the
cheap domination on the other.

The passage from `Prod.fst _* D.measure` to `D.base` is bookkeeping, but one step of it is not
formal: `Prod.fst _* D.measure` is `∑ₖ base|_{level k}`, whose null sets are those of
`base|_{level 0}` by antitonicity, and *that* is the class of `base` only because of the datum
field `base_supported_level_zero`.  Without that field the statement below is false, not merely
unproved.

## Main results

* `TauCeti.BorelCalculus.measureEquiv_map_fst_measure`: the model measure, pushed to `ℂ`, has the
  class of the base measure.
* `TauCeti.BorelCalculus.measureEquiv_base_of_operatorUnitaryEquiv`: **the measure class is a
  unitary invariant.**

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

@[expose] public section

open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace BorelCalculus

section Datum

/-- The symbol of the model operator, as a function on `ℂ × ℕ`. -/
noncomputable def datumSymbol (D : MultiplicityDatum ℂ) : ℂ × ℕ → ℂ :=
  fun p => coordTrunc D.bound p.1

/-- The model symbol, unfolded.  Stated so that consumers outside this module can rewrite with
it without the definition having to be exposed. -/
theorem datumSymbol_def (D : MultiplicityDatum ℂ) :
    datumSymbol D = fun p => coordTrunc D.bound p.1 := (rfl)

/-- The model symbol agrees with the first coordinate wherever the model measure lives. -/
theorem ae_datumSymbol_eq_fst (D : MultiplicityDatum ℂ) :
    ∀ᵐ p ∂D.measure, datumSymbol D p = p.1 := by
  filter_upwards [D.ae_norm_le_bound] with p hp
  rw [datumSymbol_def]
  exact coordTrunc_eq_self hp

/-- The model symbol is measurable. -/
theorem measurable_datumSymbol (D : MultiplicityDatum ℂ) : Measurable (datumSymbol D) :=
  (measurable_coordTrunc D.bound).comp measurable_fst

/-- The model symbol is bounded by the datum's bound. -/
theorem norm_datumSymbol_le (D : MultiplicityDatum ℂ) (p : ℂ × ℕ) :
    ‖datumSymbol D p‖ ≤ D.bound :=
  norm_coordTrunc_le D.bound_nonneg p.1

/-- The model operator really is multiplication by the model symbol. -/
theorem operator_eq_mulLp_datumSymbol (D : MultiplicityDatum ℂ) :
    D.operator = mulLp D.measure (measurable_datumSymbol D) (norm_datumSymbol_le D) :=
  operator_eq_mulLp_of_le D.bound_nonneg le_rfl

/-- **The model symbol and the coordinate projection push the model measure to the same
place**, the truncation being invisible where the model measure lives. -/
theorem map_datumSymbol_eq_map_fst (D : MultiplicityDatum ℂ) :
    D.measure.map (datumSymbol D) = D.measure.map Prod.fst := by
  refine Measure.map_congr ?_
  filter_upwards [D.ae_norm_le_bound] with p hp
  exact coordTrunc_eq_self hp

/-- **The model measure, pushed to `ℂ`, has the measure class of the base measure.**

Forgetting the slice index turns the model measure into `∑ₖ base|_{level k}`.  That is dominated
by `base` term by term, and it dominates `base` because its zeroth term already does: `base` is
carried by `level 0`, which is the field `base_supported_level_zero`.  **Without that field this
is false**, mass outside `level 0` contributing to no term at all. -/
theorem measureEquiv_map_fst_measure (D : MultiplicityDatum ℂ) :
    MeasureEquiv (D.measure.map Prod.fst) D.base := by
  rw [MultiplicityDatum.measure_def, map_fst_sliceSum]
  constructor
  · refine Measure.AbsolutelyContinuous.mk fun t ht h0 => ?_
    rw [Measure.sum_apply _ ht, ENNReal.tsum_eq_zero]
    intro k
    rw [Measure.restrict_apply ht]
    exact measure_mono_null Set.inter_subset_left h0
  · refine Measure.AbsolutelyContinuous.mk fun t ht h0 => ?_
    rw [Measure.sum_apply _ ht, ENNReal.tsum_eq_zero] at h0
    have h00 := h0 0
    rw [Measure.restrict_apply ht] at h00
    have hsub : t ⊆ (t ∩ D.level 0) ∪ (D.level 0)ᶜ := by
      intro x hx
      by_cases hk : x ∈ D.level 0
      · exact Or.inl ⟨hx, hk⟩
      · exact Or.inr hk
    exact measure_mono_null hsub
      (measure_union_null h00 D.base_supported_level_zero)

/-- The model symbol pushes the model measure onto the base measure class. -/
theorem measureEquiv_map_datumSymbol (D : MultiplicityDatum ℂ) :
    MeasureEquiv (D.measure.map (datumSymbol D)) D.base := by
  rw [map_datumSymbol_eq_map_fst]
  exact measureEquiv_map_fst_measure D

end Datum

section Invariance

/-- **One direction of the invariance**, isolated because the proof runs it twice with the roles
of the two data exchanged.

A maximal vector on the `D` side is transported by the intertwiner to *some* vector on the `E`
side -- not necessarily a maximal one -- and the cheap domination is all that is asked of it. -/
theorem absolutelyContinuous_base_of_intertwines {D E : MultiplicityDatum ℂ}
    (e : Lp ℂ 2 D.measure ≃ₗᵢ[ℂ] Lp ℂ 2 E.measure)
    (he : ∀ x, e (mulLp D.measure (measurable_datumSymbol D) (norm_datumSymbol_le D) x)
      = mulLp E.measure (measurable_datumSymbol E) (norm_datumSymbol_le E) (e x)) :
    D.base ≪ E.base := by
  have haD : IsStarNormal
      (mulLp D.measure (measurable_datumSymbol D) (norm_datumSymbol_le D)) :=
    isStarNormal_mulLp D.measure (measurable_datumSymbol D) (norm_datumSymbol_le D)
  obtain ⟨F₀, hF₀⟩ := exists_measureEquiv_map_val_diagMeasure_mulLp D.measure
    (measurable_datumSymbol D) (norm_datumSymbol_le D)
  -- The spectral measure of `F₀` is carried across by the intertwiner.
  have hnat := map_val_diagMeasure_eq_of_intertwines haD e he F₀
  -- On the far side it is dominated by the model measure of `E`.
  have hdom := map_val_diagMeasure_mulLp_absolutelyContinuous E.measure
    (measurable_datumSymbol E) (norm_datumSymbol_le E) (e F₀)
  have hchain : D.measure.map (datumSymbol D) ≪ E.measure.map (datumSymbol E) := by
    refine hF₀.2.trans ?_
    rw [← hnat]
    exact hdom
  exact ((measureEquiv_map_datumSymbol D).2.trans hchain).trans
    (measureEquiv_map_datumSymbol E).1

/-- **The measure class of a multiplicity datum is a unitary invariant.**

This is the measure-class half of uniqueness for the multiplicity classification, and the
converse of the measure half of `operatorUnitaryEquiv_of_measureEquiv_complex`. -/
theorem measureEquiv_base_of_operatorUnitaryEquiv {D E : MultiplicityDatum ℂ}
    (h : OperatorUnitaryEquiv D.operator E.operator) : MeasureEquiv D.base E.base := by
  rw [operator_eq_mulLp_datumSymbol D, operator_eq_mulLp_datumSymbol E] at h
  obtain ⟨e, he⟩ := h.exists_intertwiner
  refine ⟨absolutelyContinuous_base_of_intertwines e he,
    absolutelyContinuous_base_of_intertwines e.symm fun y => ?_⟩
  have hy := he (e.symm y)
  rw [e.apply_symm_apply] at hy
  rw [← hy, e.symm_apply_apply]

end Invariance

end BorelCalculus
end TauCeti
