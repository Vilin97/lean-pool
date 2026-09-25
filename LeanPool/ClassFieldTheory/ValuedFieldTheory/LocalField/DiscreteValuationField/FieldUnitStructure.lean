/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.IwasawaPrincipalUnits
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.MixedCharacteristicStructure.Core
/-!
# Topological structure of local-field units

This file assembles the valuation, Teichmuller, and principal-unit factors in
the canonical factor order.  All topologies are the ones carried directly by
the given `WithZero (Multiplicative ℤ)`-valued valuation.
-/

@[expose] public section

noncomputable
section

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace LocalField

variable {K : Type u} [Field K]

open CompleteDVF.higherPrincipalUnitGroup renaming
  fieldUnitsContinuousMulEquivUniformizerRootsPrincipalUnitsOfWithZeroValuation →
    fieldUnitsEquivUniformizerRootsPrincipalUnits in
/-- The local-field structure theory, the mixed-characteristic field-unit structure theorem.  In
mixed characteristic the
first principal units are a finite cyclic `p`-group times
`[K : ℚ_p]` copies of `ℤ_p`; adjoining the valuation and Teichmuller factors
gives the displayed topological decomposition of `Kˣ` in the canonical factor order. -/
noncomputable def chosenFieldUnitsStructureMixedCharacteristic
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v) :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    let d := Module.finrank ℚ_[F.residueCharacteristic] K
    Σ a : ℕ,
      Multiplicative ℤ ×
          (Multiplicative (ZMod (Nat.card F.residueField - 1)) ×
            Multiplicative
      (ZMod (F.residueCharacteristic ^ a) ×
                (Fin d → ℤ_[F.residueCharacteristic]))) ≃ₜ* Kˣ := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  letI : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let d := Module.finrank ℚ_[F.residueCharacteristic] K
  let hex :=
    WithZeroValuation.exists_valuationSubring_valuation_eq_exp_neg_one_of_surjective
      v hv
  let π := Classical.choose hex
  have hπval : v (π : K) = WithZero.exp (-1 : ℤ) :=
    Classical.choose_spec hex
  have hπ : v.IsUniformizer (π : K) :=
    WithZeroValuation.isUniformizer_of_valuation_eq_exp_neg_one
      v (π : K) hπval
  obtain ⟨a, e⟩ :=
    chosenMixedFirstPrincipalUnitStructureOfWithZeroValuation
      v hv
  exact ⟨a,
    fieldUnitsEquivUniformizerRootsPrincipalUnits
      v hπ
      (Multiplicative
        (ZMod (F.residueCharacteristic ^ a) ×
          (Fin d → ℤ_[F.residueCharacteristic]))) e⟩

open CompleteDVF.higherPrincipalUnitGroup renaming
  adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation →
    adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation in
/-- The exact principal-unit factor in the equal-characteristic field-unit structure theorem,
reindexed from
the prime-to-`p` degrees and residue-basis coordinates by `ℕ`. -/
noncomputable def chosenFirstPrincipalUnitStructureEqualCharacteristic
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)]
    [CharP K (ofWithZeroValuation v).residueCharacteristic] :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Multiplicative (ℕ → ℤ_[F.residueCharacteristic]) ≃ₜ*
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        F.toCompleteDVF 1 := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let hex := F.toCompleteDVF.exists_uniformizer
  let π := Classical.choose hex
  have hπ : v.IsUniformizer (π : K) := Classical.choose_spec hex
  let : ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete
      (Valued.v : _root_.Valuation K
        (WithZero (Multiplicative ℤ))) := by
    change ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v
    infer_instance
  let E :=
    (CompleteDVF.higherPrincipalUnitGroup.iwasawaGlobalAdicPrincipalUnitsContinuousAddEquiv
      F hπ).trans
      (adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation
        v)
  let I := iwasawaPadicIntProductContinuousAddEquivNat
    F.residueCharacteristic
    (CompleteDVF.higherPrincipalUnitGroup.iwasawaResidueRank F)
    F.residueCharacteristic_prime.pos
    Module.finrank_pos
  let eAdd : (ℕ → ℤ_[F.residueCharacteristic]) ≃ₜ+
      Additive
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          F.toCompleteDVF 1) :=
    I.symm.trans E
  exact LocalFieldTheory.DiscreteValuationField.continuousMulEquivOfAdditiveTarget eAdd

open CompleteDVF.higherPrincipalUnitGroup renaming
  fieldUnitsContinuousMulEquivUniformizerRootsPrincipalUnitsOfWithZeroValuation →
    fieldUnitsEquivUniformizerRootsPrincipalUnits in
/-- The local-field structure theory, the equal-characteristic field-unit structure theorem.  In
equal characteristic the
Iwasawa generators identify the first principal units with a countable
product of `ℤ_p`; adjoining the valuation and Teichmuller factors gives the
canonical topological decomposition of `Kˣ`. -/
noncomputable def chosenFieldUnitsStructureEqualCharacteristic
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)]
    [CharP K (ofWithZeroValuation v).residueCharacteristic] :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Multiplicative ℤ ×
        (Multiplicative (ZMod (Nat.card F.residueField - 1)) ×
          Multiplicative (ℕ → ℤ_[F.residueCharacteristic])) ≃ₜ* Kˣ := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let hex := F.toCompleteDVF.exists_uniformizer
  let π := Classical.choose hex
  have hπ : v.IsUniformizer (π : K) := Classical.choose_spec hex
  let ePrincipal :=
    chosenFirstPrincipalUnitStructureEqualCharacteristic v
  exact
    fieldUnitsEquivUniformizerRootsPrincipalUnits
      v hπ (Multiplicative (ℕ → ℤ_[F.residueCharacteristic])) ePrincipal

end LocalField
end LocalFieldTheory.DiscreteValuationField
