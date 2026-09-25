/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.MixedCharacteristicStructure.IntegralLattice
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormalizedIntegerValuation
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Padic.NonarchimedeanLocalField
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationExtension
/-!
# Comparison of the chosen and canonical valuations on the p-adic field

The concrete local-field package on `ℚ_[p]` uses the DVR valuation obtained
from `ℤ_[p]`, whereas mathlib's nonarchimedean-local-field API uses
`ValuativeRel.valuation ℚ_[p]`.  This file proves that these are equivalent
valuations and makes the comparison usable when transporting valuation
extensions.
-/

@[expose] public section

noncomputable section

open scoped ValuativeRel

namespace LocalFieldTheory
namespace DiscreteValuationField
namespace Examples
namespace Qp

universe u v

/-- The DVR valuation on `ℚ_[p]` obtained from `ℤ_[p]` is equivalent to the
canonical valuation attached to the p-adic valuative relation. -/
theorem padicDVRValuation_isEquiv_valuativeRelValuation
    (p : ℕ) [Fact p.Prime] :
    (padicDVRValuation p).IsEquiv
      (ValuativeRel.valuation ℚ_[p]) := by
  apply _root_.Valuation.isEquiv_of_val_le_one
  intro a
  have hcanonical :
      ValuativeRel.valuation ℚ_[p] a ≤ 1 ↔ ‖a‖ ≤ 1 := by
    simpa only [_root_.Valuation.mem_integer_iff] using
      LocalFieldTheory.Padic.integer_mem_iff_norm_le_one p a
  exact
    (LocalFieldTheory.DiscreteValuationField.LocalField.padicDVRValuation_le_one_iff_norm_le_one
      p a).trans
      hcanonical.symm

/-- The valuation selected by the concrete p-adic local-field package is
equivalent to mathlib's canonical valuation on `ℚ_[p]`. -/
theorem padicLocalField_valuation_isEquiv_valuativeRelValuation
    (p : ℕ) [Fact p.Prime] :
    (padicLocalField p).toCompleteDVF.valuation.IsEquiv
      (ValuativeRel.valuation ℚ_[p]) := by
  change
    (padicDVRValuation p).IsEquiv
      (ValuativeRel.valuation ℚ_[p])
  exact padicDVRValuation_isEquiv_valuativeRelValuation p

/-- The chosen valuation in `padicLocalField p` is equivalent to the
canonical complete-DVF valuation supplied by the topology-first local-field
structure on `ℚ_[p]`. -/
theorem padicLocalField_valuation_isEquiv_localCompleteDVF
    (p : ℕ) [Fact p.Prime] :
    (padicLocalField p).toCompleteDVF.valuation.IsEquiv
      (LocalFieldTheory.localCompleteDVF ℚ_[p]).valuation := by
  rw [LocalFieldTheory.localCompleteDVF_valuation_eq]
  exact padicLocalField_valuation_isEquiv_valuativeRelValuation p

/-- Symmetric comparison, oriented for transporting canonical local-field
valuation extensions to the chosen p-adic DVR valuation. -/
theorem localCompleteDVF_valuation_isEquiv_padicLocalField
    (p : ℕ) [Fact p.Prime] :
    (LocalFieldTheory.localCompleteDVF ℚ_[p]).valuation.IsEquiv
      (padicLocalField p).toCompleteDVF.valuation :=
  (padicLocalField_valuation_isEquiv_localCompleteDVF p).symm

/-- Any valuation extension of the canonical complete-DVF valuation on
`ℚ_[p]` is also an extension of the valuation selected by
`padicLocalField p`. -/
theorem padicLocalFieldValuation_hasExtension_of_localCompleteDVF
    (p : ℕ) [Fact p.Prime]
    {E : Type u} [Field E] [Algebra ℚ_[p] E]
    {Gamma : Type v} [LinearOrderedCommGroupWithZero Gamma]
    (wE : _root_.Valuation E Gamma)
    [(LocalFieldTheory.localCompleteDVF ℚ_[p]).valuation.HasExtension wE] :
    (padicLocalField p).toCompleteDVF.valuation.HasExtension wE :=
  ValuationTheory.DiscreteValuationField.ValuedExtension.hasExtension_of_isEquiv_base
    (padicLocalField_valuation_isEquiv_localCompleteDVF p)

/-- Conversely, any valuation extension of the valuation selected by
`padicLocalField p` is also an extension of the canonical complete-DVF
valuation on `ℚ_[p]`. -/
theorem localCompleteDVFValuation_hasExtension_of_padicLocalField
    (p : ℕ) [Fact p.Prime]
    {E : Type u} [Field E] [Algebra ℚ_[p] E]
    {Gamma : Type v} [LinearOrderedCommGroupWithZero Gamma]
    (wE : _root_.Valuation E Gamma)
    [(padicLocalField p).toCompleteDVF.valuation.HasExtension wE] :
    (LocalFieldTheory.localCompleteDVF ℚ_[p]).valuation.HasExtension wE :=
  ValuationTheory.DiscreteValuationField.ValuedExtension.hasExtension_of_isEquiv_base
    (localCompleteDVF_valuation_isEquiv_padicLocalField p)

end Qp
end Examples
end DiscreteValuationField
end LocalFieldTheory
