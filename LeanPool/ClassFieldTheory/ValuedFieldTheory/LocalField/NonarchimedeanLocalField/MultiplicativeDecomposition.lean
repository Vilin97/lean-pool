/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ProfiniteUnits
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence
public import Mathlib.Topology.LocallyConstant.Basic
/-!
# Topological decomposition of a local multiplicative group

This file packages the normalized valuation and the unit factor in the standard
decomposition of `Kˣ` as continuous homomorphisms. After fixing a
noncanonical uniformizer internally, the resulting parameter-free map lets
downstream separation arguments avoid carrying a uniformizer parameter.
-/

@[expose] public section

noncomputable section

universe u

namespace LocalFieldTheory.IsNonarchimedeanLocalField

open scoped ValuativeRel WithZero

/-- Equality under the normalized valuation is equality under the field valuation. -/
theorem valuationUnitsMulHom_eq_iff_valuation_eq
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x y : Kˣ) :
    valuationUnitsMulHom K x = valuationUnitsMulHom K y ↔
      ValuativeRel.valuation K (x : K) = ValuativeRel.valuation K (y : K) := by
  constructor
  · intro h
    apply (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).injective
    have h' := congrArg
      (fun z : Multiplicative Int => (z : WithZero (Multiplicative Int))) h
    simpa [valuationUnitsMulHom] using h'
  · intro h
    simp [valuationUnitsMulHom, h]

/-- The normalized valuation on `Kˣ`, viewed multiplicatively, is continuous. -/
theorem valuationUnitsMulHom_continuous
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Continuous (valuationUnitsMulHom K) := by
  apply IsLocallyConstant.continuous
  apply IsLocallyConstant.iff_isOpen_fiber_apply.mpr
  intro x
  have hset :
      (valuationUnitsMulHom K) ⁻¹' {valuationUnitsMulHom K x} =
        {y : Kˣ | ValuativeRel.valuation K (y : K) =
          ValuativeRel.valuation K (x : K)} := by
    ext y
    exact valuationUnitsMulHom_eq_iff_valuation_eq K y x
  rw [hset]
  have hopen :=
    (Valuation.isOpen_sphere (v := ValuativeRel.valuation K)
      (r := (ValuativeRel.valuation K).restrict (x : K)) (by simp)).preimage
      Units.continuous_val
  simpa only [Set.preimage_ofPred_eq, Valuation.restrict_inj] using hopen

/-- The normalized valuation as a continuous multiplicative homomorphism. -/
def valuationUnitsContinuousMonoidHom
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Kˣ →ₜ* Multiplicative Int where
  toMonoidHom := valuationUnitsMulHom K
  continuous_toFun := valuationUnitsMulHom_continuous K

/-- The unit factor of one is one. -/
@[simp]
theorem uniformizerUnitFactor_one
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) :
    uniformizerUnitFactor K ϖ hϖ 1 = 1 := by
  apply integerUnitsToFieldUnits_injective K
  rw [integerUnitsToFieldUnits_uniformizerUnitFactor]
  rw [valuationMap_ofMul_one]
  simp

/-- The unit factor respects multiplication. -/
theorem uniformizerUnitFactor_mul
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (x y : Kˣ) :
    uniformizerUnitFactor K ϖ hϖ (x * y) =
      uniformizerUnitFactor K ϖ hϖ x * uniformizerUnitFactor K ϖ hϖ y := by
  apply integerUnitsToFieldUnits_injective K
  rw [map_mul]
  simp only [integerUnitsToFieldUnits_uniformizerUnitFactor]
  rw [valuationMap_ofMul_mul, zpow_add]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ac_rfl

/-- The unit factor in the uniformizer decomposition as a homomorphism. -/
def uniformizerUnitFactorMonoidHom
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) :
    Kˣ →* 𝒪[K]ˣ where
  toFun := uniformizerUnitFactor K ϖ hϖ
  map_one' := uniformizerUnitFactor_one K ϖ hϖ
  map_mul' := uniformizerUnitFactor_mul K ϖ hϖ

/-- The unit factor in the uniformizer decomposition is continuous. -/
theorem uniformizerUnitFactor_continuous
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) :
    Continuous (uniformizerUnitFactor K ϖ hϖ) := by
  have hpow : Continuous
      (fun n : Multiplicative Int => ϖ ^ Multiplicative.toAdd n) :=
    continuous_of_discreteTopology
  have hexponent : Continuous
      (fun x : Kˣ => ϖ ^ valuationMap K (Additive.ofMul x)) := by
    change Continuous
      (fun x : Kˣ => ϖ ^ Multiplicative.toAdd (valuationUnitsMulHom K x))
    exact hpow.comp (valuationUnitsMulHom_continuous K)
  have hquotient : Continuous
      (fun x : Kˣ => x / ϖ ^ valuationMap K (Additive.ofMul x)) :=
    by
      apply (continuous_id.mul hexponent.inv).congr
      intro x
      change x * (ϖ ^ valuationMap K (Additive.ofMul x))⁻¹ =
        x / ϖ ^ valuationMap K (Additive.ofMul x)
      rw [div_eq_mul_inv]
  change Continuous (uniformizerUnitFactorMonoidHom K ϖ hϖ)
  apply Continuous.of_coeHom_comp
  rw [Topology.IsEmbedding.subtypeVal.continuous_iff]
  have hval := Units.continuous_val.comp hquotient
  convert hval using 1
  funext x
  exact (integerUnitsToFieldUnits_apply K
    (uniformizerUnitFactor K ϖ hϖ x)).symm.trans
      (congrArg Units.val
        (integerUnitsToFieldUnits_uniformizerUnitFactor K ϖ hϖ x))

/-- The unit factor in the uniformizer decomposition as a continuous homomorphism. -/
def uniformizerUnitFactorContinuousMonoidHom
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) :
    Kˣ →ₜ* 𝒪[K]ˣ where
  toMonoidHom := uniformizerUnitFactorMonoidHom K ϖ hϖ
  continuous_toFun := uniformizerUnitFactor_continuous K ϖ hϖ

/-- The fixed noncanonical uniformizer used by the parameter-free unit map. -/
def chosenLocalUniformizer
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Kˣ :=
  Classical.choose (valuationMap_uniformiser K)

/-- The chosen local uniformizer has normalized valuation one. -/
theorem chosenLocalUniformizer_spec
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    valuationMap K (Additive.ofMul (chosenLocalUniformizer K)) = 1 :=
  Classical.choose_spec (valuationMap_uniformiser K)

/-- A parameter-free continuous projection from `Kˣ` to its unit factor. -/
def localUnitFactorContinuousMonoidHom
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Kˣ →ₜ* 𝒪[K]ˣ :=
  uniformizerUnitFactorContinuousMonoidHom K (chosenLocalUniformizer K)
    (chosenLocalUniformizer_spec K)

end LocalFieldTheory.IsNonarchimedeanLocalField
