/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.Ideal.Quotient.Operations
/-!
# Higher-unit subgroups at finite places
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable
section

namespace ClassFieldTheory

universe u

/-- Reduction of a local integral unit modulo the `n`-th power of the maximal
ideal. -/
def rayLocalHigherUnitMap
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (v.adicCompletionIntegers K).units →*
      ((v.adicCompletionIntegers K) ⧸
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)ˣ :=
  (Units.map
      (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal
          (v.adicCompletionIntegers K)) ^ n)).toMonoidHom).comp
    (v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.toMonoidHom

/-- The `n`-th higher-unit subgroup at a finite place. -/
def rayLocalHigherUnitGroup
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Subgroup (v.adicCompletion K)ˣ :=
  Subgroup.map
    (v.adicCompletionIntegers K).units.subtype
    (rayLocalHigherUnitMap v n).ker

end ClassFieldTheory
