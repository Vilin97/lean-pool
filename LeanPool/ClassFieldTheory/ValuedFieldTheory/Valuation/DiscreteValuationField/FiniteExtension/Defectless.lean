/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.Extensions
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.RamificationInertia.Basic
/-!
# Defectlessness from a finite extension of valuation rings

The local Dedekind fundamental identity only needs discretely valued fields.
Completeness and Henselianity play no role once the target valuation ring is a
finite module over the base valuation ring.
-/

@[expose] public section

noncomputable
section

namespace ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v w x

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]

/-- A valued extension of discretely valued fields is defectless when its
target valuation ring is finite over the base valuation ring. -/
theorem isDefectless_of_moduleFinite
    (base : DVF.{u, v} K) (target : DVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    IsDefectless base target := by
  classical
  let : FaithfulSMul base.valuationSubring target.valuationSubring :=
    FaithfulSMul.of_field_isFractionRing
      base.valuationSubring target.valuationSubring K L
  have hprimes :=
    IsLocalRing.primesOver_eq target.valuationSubring base.maximalIdeal_ne_bot
  have hq : target.maximalIdeal ∈ base.maximalIdeal.primesOver target.valuationSubring := by
    rw [hprimes]
    exact Set.mem_singleton target.maximalIdeal
  let : target.maximalIdeal.LiesOver base.maximalIdeal := hq.2
  let : Subsingleton (base.maximalIdeal.primesOver target.valuationSubring) :=
    Set.Subsingleton.coe_sort (by
      rw [hprimes]
      exact Set.subsingleton_singleton)
  have hsum :=
    Ideal.sum_ramification_inertia_eq_finrank base.maximalIdeal target.valuationSubring
  rw [Fintype.sum_subsingleton _ ⟨target.maximalIdeal, hq⟩] at hsum
  change Module.finrank K L =
    Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal *
      target.maximalIdeal.inertiaDeg base.valuationSubring
  rw [Ideal.ramificationIdx'_eq_ramificationIdx
      base.maximalIdeal target.maximalIdeal base.maximalIdeal_ne_bot,
    IsFractionRing.finrank_eq base.valuationSubring K target.valuationSubring L]
  exact hsum.symm

end ValuationTheory.DiscreteValuationField.ValuedExtension

end
