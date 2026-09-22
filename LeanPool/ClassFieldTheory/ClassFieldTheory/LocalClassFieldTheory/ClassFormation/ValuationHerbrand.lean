/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandFiniteness
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.ValueGroupCohomology

/-! # Valuation Herbrand -/
namespace LocalClassFieldTheory

open LocalFieldTheory

open CyclicCohomology

/-!
# The valuation sequence and Herbrand quotients

This file applies the Herbrand-quotient multiplicativity theorem to the actual
valuation sequence from integer units through field units to the value group.

All three actions are the concrete actions from `ValuationReal`: the Galois
action on integer and field units, and the trivial action on the value group.
-/

noncomputable section

open scoped ValuativeRel
open CyclicCohomology.ProfiniteCohomology.Herbrand
open IsNonarchimedeanLocalField

variable (K L : Type) [Field K] [ValuativeRel K]
  [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure (ValuativeRel.valuation L).integer
    (ValuativeRel.valuation K).integer L]

omit [FiniteDimensional K L] in
/-- The actual valuation sequence has equivariant maps, is exact at field
units, is injective on integer units, and is surjective onto the value group. -/
theorem valuationHerbrand_shortExact :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    letI := galoisGroupFieldUnitsMulDistribMulAction K L
    letI := galoisGroupValueGroupMulDistribMulAction K L
    (∀ (σ : Gal(L/K)) (x : (ValuativeRel.valuation L).integerˣ),
        integerUnitsToFieldUnits L (σ • x) =
          σ • integerUnitsToFieldUnits L x) ∧
      (∀ (σ : Gal(L/K)) (x : Lˣ),
        valuationUnitsMulHom L (σ • x) =
          σ • valuationUnitsMulHom L x) ∧
      (∀ x : Lˣ, valuationUnitsMulHom L x = 1 ↔
        ∃ y : (ValuativeRel.valuation L).integerˣ,
          integerUnitsToFieldUnits L y = x) ∧
      Function.Injective (integerUnitsToFieldUnits L) ∧
      Function.Surjective (valuationUnitsMulHom L) := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let := galoisGroupFieldUnitsMulDistribMulAction K L
  let := galoisGroupValueGroupMulDistribMulAction K L
  exact ⟨integerUnitsToFieldUnits_galoisGroup_equivariant K L,
    valuationUnitsMulHom_galoisGroup_equivariant K L,
    valuationUnitsMulHom_eq_one_iff_exists_integerUnit L,
    integerUnitsToFieldUnits_injective L,
    valuationUnitsMulHom_surjective L⟩

omit [ValuativeRel K] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure (ValuativeRel.valuation L).integer
      (ValuativeRel.valuation K).integer L] in
/-- The Herbrand quotient of the trivially acted-on value group is defined:
its degree-zero group is finite cyclic and its degree-minus-one group is
trivial. -/
theorem galoisGroupValueGroup_herbrandQuotientDefined
    (g : Gal(L/K)) :
    letI := galoisGroupValueGroupMulDistribMulAction K L
    HerbrandQuotientDefined (Gal(L/K)) (Multiplicative Int) g := by
  exact ⟨galoisGroupValueGroupHerbrandH0Finite K L,
    galoisGroupValueGroupHerbrandHMinusOneFinite K L g⟩

/-- Herbrand-quotient multiplicativity for the actual valuation sequence.  Once the
Herbrand quotient of the integer-unit term is defined, the value-group term
is already defined by `galoisGroupValueGroup_herbrandQuotientDefined`; hence the
field-unit quotient is defined and

`h(G,Lˣ) = h(G,(valuation integer ring of L)ˣ) * h(G,ℤ)`.

The only non-derived finiteness input is `hU`, the two finite low-degree
Herbrand quotients for the actual integer-unit action. -/
theorem valuationHerbrand_multiplicativity_of_integerUnits_defined
    (g : Gal(L/K))
    (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g)
    (hU :
      letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
      HerbrandQuotientDefined (Gal(L/K))
        (ValuativeRel.valuation L).integerˣ g) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    letI := galoisGroupFieldUnitsMulDistribMulAction K L
    letI := galoisGroupValueGroupMulDistribMulAction K L
    let hZ : HerbrandQuotientDefined (Gal(L/K)) (Multiplicative Int) g :=
      galoisGroupValueGroup_herbrandQuotientDefined K L g
    ∃ hField : HerbrandQuotientDefined (Gal(L/K)) Lˣ g,
      @herbrandQuotient (Gal(L/K)) Lˣ _ _ _
          (galoisGroupFieldUnitsMulDistribMulAction K L) g hField.1 hField.2 =
        @herbrandQuotient (Gal(L/K))
            (ValuativeRel.valuation L).integerˣ _ _ _
            (galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L)
            g hU.1 hU.2 *
          @herbrandQuotient (Gal(L/K)) (Multiplicative Int) _ _ _
            (galoisGroupValueGroupMulDistribMulAction K L) g hZ.1 hZ.2 := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let := galoisGroupFieldUnitsMulDistribMulAction K L
  let := galoisGroupValueGroupMulDistribMulAction K L
  let hZ : HerbrandQuotientDefined (Gal(L/K)) (Multiplicative Int) g :=
    galoisGroupValueGroup_herbrandQuotientDefined K L g
  let hseq := valuationHerbrand_shortExact K L
  let hField := herbrandQuotientDefined_middle_of_left_right
    (G := Gal(L/K))
    (A := (ValuativeRel.valuation L).integerˣ)
    (B := Lˣ) (C := Multiplicative Int)
    (integerUnitsToFieldUnits L) (valuationUnitsMulHom L)
    hseq.1 hseq.2.1 hseq.2.2.1 hseq.2.2.2.1 hseq.2.2.2.2
    g hg hU hZ
  refine ⟨hField, ?_⟩
  let : Finite
      (HerbrandH0 (Gal(L/K)) (ValuativeRel.valuation L).integerˣ) := hU.1
  let : Finite
      (HerbrandHMinusOne (Gal(L/K))
        (ValuativeRel.valuation L).integerˣ g) := hU.2
  let : Finite (HerbrandH0 (Gal(L/K)) Lˣ) := hField.1
  let : Finite (HerbrandHMinusOne (Gal(L/K)) Lˣ g) := hField.2
  let : Finite
      (HerbrandH0 (Gal(L/K)) (Multiplicative Int)) := hZ.1
  let : Finite
      (HerbrandHMinusOne (Gal(L/K)) (Multiplicative Int) g) := hZ.2
  exact herbrandQuotient_multiplicative_of_shortExact
    (G := Gal(L/K))
    (A := (ValuativeRel.valuation L).integerˣ)
    (B := Lˣ) (C := Multiplicative Int)
    (integerUnitsToFieldUnits L) (valuationUnitsMulHom L)
    hseq.1 hseq.2.1 hseq.2.2.1 hseq.2.2.2.1 hseq.2.2.2.2
    g hg

end
end LocalClassFieldTheory
