/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.ValuedAdicComplete
public import Mathlib.NumberTheory.NumberField.ProductFormula
/-!
# Canonical structures on finite completions

This module installs the complete discrete valuation, characteristic-zero,
and finite residue-field structures used by finite-place class-field
arithmetic.
-/

@[expose] public section

open scoped NumberField ValuativeRel
open NumberField IsDedekindDomain

noncomputable
section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

/-- The distinguished valuation on a finite completion of a number field is
complete discrete. -/
noncomputable instance finitePlaceAdicCompletion_isCompleteDiscrete
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete
      (Valued.v :
        Valuation (v₀.adicCompletion K)
          (WithZero (Multiplicative ℤ))) where
  isRankOneDiscrete := inferInstance
  isAdicComplete :=
    ValuationTheory.Valuations.rankOneDiscreteValuationSubring_isAdicComplete

/-- A finite completion of a number field has characteristic zero. -/
noncomputable instance finitePlaceAdicCompletion_charZero
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    CharZero (v₀.adicCompletion K) :=
  charZero_of_injective_algebraMap
    (algebraMap K (v₀.adicCompletion K)).injective

/-- The residue field of a finite completion of a number field is finite. -/
noncomputable instance finitePlaceAdicCompletion_residueFinite
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    Finite
      (IsLocalRing.ResidueField
        (Valued.v :
          Valuation (v₀.adicCompletion K)
            (WithZero (Multiplicative ℤ))).valuationSubring) := by
  change Finite (Valued.ResidueField (v₀.adicCompletion K))
  exact _root_.finite_adicCompletion_residueField K v₀

end GlobalClassFieldTheory.ClassFieldAxiom

end
