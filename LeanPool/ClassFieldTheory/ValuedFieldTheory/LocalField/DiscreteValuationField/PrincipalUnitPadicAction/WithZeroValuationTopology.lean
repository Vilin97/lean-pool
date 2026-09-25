/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.DenominatorValuation
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.AdicPadicModule
/-!
# Principal-unit topology from a normalized valuation

For a complete discrete valuation with value group `WithZero (Multiplicative ℤ)`, the
inherited topology agrees with the canonical adic model, so the p-adic action and addition are
continuous on the original principal-unit carrier.
-/

@[expose] public section

noncomputable
section

open scoped BigOperators

universe u v

namespace LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace CompleteDVF
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
namespace higherPrincipalUnitGroup

open LubinTate
open LubinTate.Valuations

variable {K : Type u} [Field K]

open Internal

/-- Compare the type-level adic model with the principal-unit carrier under
the canonical topology of a normalized complete discrete valuation. -/
noncomputable def adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] :
    let F : LocalField.{u, 0} K := LocalField.ofWithZeroValuation v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    AdicPrincipalUnits F.toCompleteDVF ≃ₜ+
      Additive
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          F.toCompleteDVF) 1) := by
  let F : LocalField.{u, 0} K := LocalField.ofWithZeroValuation v
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  letI : ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete
      (Valued.v : _root_.Valuation K
        (WithZero (Multiplicative ℤ))) := by
    change ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v
    infer_instance
  let π := chosenPrincipalUnitPadicUniformizer F.toCompleteDVF
  have hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K) :=
    chosenPrincipalUnitPadicUniformizer_isUniformizer F.toCompleteDVF
  have hadic :
      (inferInstance : TopologicalSpace F.toCompleteDVF.valuationSubring) =
        (LubinTate.Valuations.uniformizerPowerIdeal π 1).adicTopology := by
    have hmax :
        (inferInstance : TopologicalSpace F.toCompleteDVF.valuationSubring) =
          F.toCompleteDVF.maximalIdeal.adicTopology := by
      exact ValuationTheory.Valuations.rankOneDiscreteValuationSubring_isAdic
        (K := K) (Gamma := WithZero (Multiplicative ℤ))
    have hideal : LubinTate.Valuations.uniformizerPowerIdeal π 1 =
        F.toCompleteDVF.maximalIdeal := by
      rw [LubinTate.Valuations.uniformizerPowerIdeal, pow_one,
        ← F.toCompleteDVF.maximalIdeal_eq_span_uniformizer hπ]
    simpa only [hideal] using hmax
  let carrierTopology
      (t : TopologicalSpace F.toCompleteDVF.valuationSubring) :
      TopologicalSpace
        (Additive
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
            F.toCompleteDVF) 1)) :=
    letI : TopologicalSpace F.toCompleteDVF.valuationSubring := t
    inferInstance
  have hcarrier :
      (inferInstance : TopologicalSpace
        (Additive
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
            F.toCompleteDVF) 1))) =
        principalUnitAdicTopology F.toCompleteDVF := by
    change carrierTopology
        (inferInstance : TopologicalSpace F.toCompleteDVF.valuationSubring) =
      carrierTopology
        ((LubinTate.Valuations.uniformizerPowerIdeal π 1).adicTopology)
    exact congrArg carrierTopology hadic
  have hcontinuousAdic :
      @Continuous
        (AdicPrincipalUnits F.toCompleteDVF)
        (Additive
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
            F.toCompleteDVF) 1))
        inferInstance
        (principalUnitAdicTopology F.toCompleteDVF)
        (AdicPrincipalUnits.equiv F.toCompleteDVF) :=
    continuous_induced_dom
  have hcontinuousAdic_symm :
      @Continuous
        (Additive
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
            F.toCompleteDVF) 1))
        (AdicPrincipalUnits F.toCompleteDVF)
        (principalUnitAdicTopology F.toCompleteDVF)
        inferInstance
        (AdicPrincipalUnits.equiv F.toCompleteDVF).symm :=
    continuous_induced_rng.2 (continuous_id_of_le le_rfl)
  have hcontinuous : Continuous
      (AdicPrincipalUnits.equiv F.toCompleteDVF) := by
    exact Eq.mpr
      (congrArg
        (fun t : TopologicalSpace
            (Additive
              ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
                F.toCompleteDVF) 1)) =>
          @Continuous
            (AdicPrincipalUnits F.toCompleteDVF)
            (Additive
              ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
                F.toCompleteDVF) 1))
            inferInstance t
            (AdicPrincipalUnits.equiv F.toCompleteDVF))
        hcarrier)
      hcontinuousAdic
  have hcontinuous_symm : Continuous
      (AdicPrincipalUnits.equiv F.toCompleteDVF).symm := by
    exact Eq.mpr
      (congrArg
        (fun t : TopologicalSpace
            (Additive
              ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
                F.toCompleteDVF) 1)) =>
          @Continuous
            (Additive
              ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
                F.toCompleteDVF) 1))
            (AdicPrincipalUnits F.toCompleteDVF)
            t inferInstance
            (AdicPrincipalUnits.equiv F.toCompleteDVF).symm)
        hcarrier)
      hcontinuousAdic_symm
  exact ContinuousAddEquiv.mk'
    { toEquiv := AdicPrincipalUnits.equiv F.toCompleteDVF
      continuous_toFun := hcontinuous
      continuous_invFun := hcontinuous_symm }
    (fun _ _ => rfl)

/--
The continuous additive comparison from adic principal units to the underlying local-field model
preserves `ℤ_p`-scalar multiplication.
-/
@[simp] theorem adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] :
    let F : LocalField.{u, 0} K := LocalField.ofWithZeroValuation v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    ∀ (a : ℤ_[F.residueCharacteristic])
      (x : AdicPrincipalUnits F.toCompleteDVF),
      adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation v
          (a • x) =
        a • adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation
          v x := by
  let F : LocalField.{u, 0} K := LocalField.ofWithZeroValuation v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  dsimp only
  intro a x
  exact (AdicPrincipalUnits.linearEquivUnderlying F).map_smul a x

/-- The same canonical action is jointly continuous for the topology carried
directly by a standard `ℤᵐ⁰`-valued complete discrete valuation.  The bridge
is the equality between the inherited valuation topology on the valuation
ring and its maximal-ideal adic topology. -/
theorem principalUnitPadicContinuousSMulOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] :
    let F : LocalField.{u, 0} K := LocalField.ofWithZeroValuation v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    ContinuousSMul ℤ_[F.residueCharacteristic]
      (Additive ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        F.toCompleteDVF) 1)) := by
  let F : LocalField.{u, 0} K := LocalField.ofWithZeroValuation v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let e :=
    adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation v
  refine ⟨?_⟩
  have hpair : Continuous fun z : ℤ_[F.residueCharacteristic] ×
      Additive
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          F.toCompleteDVF) 1) =>
      (z.1, e.symm z.2) :=
    continuous_fst.prodMk (e.continuous_symm.comp continuous_snd)
  have htransport := e.continuous.comp (continuous_smul.comp hpair)
  exact htransport

/-- Continuous addition on `Additive U^1` for the direct normalized
valuation topology. -/
theorem principalUnitPadicContinuousAddOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] :
    let F : LocalField.{u, 0} K := LocalField.ofWithZeroValuation v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    ContinuousAdd (Additive
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        F.toCompleteDVF) 1)) := by
  let F : LocalField.{u, 0} K := LocalField.ofWithZeroValuation v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let e :=
    adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation v
  refine ⟨?_⟩
  have hpair : Continuous fun z :
      Additive
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
            F.toCompleteDVF) 1) ×
        Additive
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
            F.toCompleteDVF) 1) =>
      (e.symm z.1, e.symm z.2) :=
    (e.continuous_symm.comp continuous_fst).prodMk
      (e.continuous_symm.comp continuous_snd)
  have htransport := e.continuous.comp (continuous_add.comp hpair)
  exact htransport

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
