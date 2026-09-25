/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentUniformizerNormalization
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UniformizerPrincipalQuotient
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnits
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FiniteParameters
/-!
# LubinTate the explicit norm-subgroup computation: cardinality of the standard Lubin--Tate quotient

At repository level `n`, reduction modulo `T^(n+1)` identifies the quotient
of the power-series unit group by its explicit higher-unit kernel with the
units of the truncated power-series ring.  Its elements are parametrized by
one nonzero constant coefficient and `n` arbitrary further coefficients, so
the quotient has cardinality `(q - 1) q^n`.

The power-series/integer-ring equivalence, the light quotient equivalence
from the unramified norm-index formula, and the normalized Laurent uniformizer then give
the same cardinality for `K^x / (<T^-1> U^(n+1))`.
-/

@[expose] public section

noncomputable
section


open scoped LaurentSeries PowerSeries ValuativeRel WithZero

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable {K : Type u} [Field K]

private noncomputable def unitParameterReduction
    (F : LocalField.{u, v} K) (n : ℕ) :
    equalCharacteristicLubinTateUnitParameter F n →
      (equalCharacteristicLubinTateTruncatedRing F n)ˣ :=
  fun a => equalCharacteristicLubinTateUnitReduction F n
    (equalCharacteristicLubinTateUnitParameterUnit F n a)

private theorem unitParameterReduction_injective
    (F : LocalField.{u, v} K) (n : ℕ) :
    Function.Injective (unitParameterReduction F n) := by
  intro a b hab
  apply equalCharacteristicLubinTateUnitParameter_eq_of_coeff_eq F n a b
  intro i hi
  have hmk := congrArg Units.val hab
  change equalCharacteristicLubinTateTruncatedRingMk F n
      (equalCharacteristicLubinTateUnitParameterSeries F n a) =
    equalCharacteristicLubinTateTruncatedRingMk F n
      (equalCharacteristicLubinTateUnitParameterSeries F n b) at hmk
  have hdvd : PowerSeries.X ^ (n + 1) ∣
      equalCharacteristicLubinTateUnitParameterSeries F n a -
        equalCharacteristicLubinTateUnitParameterSeries F n b := by
    rw [← Ideal.mem_span_singleton,
      ← equalCharacteristicLubinTateTruncatedRingMk_eq_iff F n]
    exact hmk
  have hz := PowerSeries.X_pow_dvd_iff.mp hdvd i
    (Nat.lt_succ_iff.mpr hi)
  rw [map_sub, sub_eq_zero] at hz
  exact hz

private theorem unitParameterReduction_surjective
    (F : LocalField.{u, v} K) (n : ℕ) :
    Function.Surjective (unitParameterReduction F n) := by
  intro z
  obtain ⟨u, hu⟩ :=
    equalCharacteristicLubinTateUnitReduction_surjective F n z
  let a : equalCharacteristicLubinTateUnitParameter F n :=
    equalCharacteristicLubinTateUnitParameterOfCoefficients F n
      (Units.map (PowerSeries.constantCoeff (R := F.residueField)) u)
      (fun i => PowerSeries.coeff (i + 1) (u : F.residueField⟦X⟧))
  refine ⟨a, ?_⟩
  change equalCharacteristicLubinTateUnitReduction F n
      (equalCharacteristicLubinTateUnitParameterUnit F n a) = z
  rw [← hu]
  apply Units.ext
  change equalCharacteristicLubinTateTruncatedRingMk F n
      (equalCharacteristicLubinTateUnitParameterSeries F n a) =
    equalCharacteristicLubinTateTruncatedRingMk F n
      (u : F.residueField⟦X⟧)
  rw [equalCharacteristicLubinTateTruncatedRingMk_eq_iff,
    Ideal.mem_span_singleton]
  apply PowerSeries.X_pow_dvd_iff.mpr
  intro j hj
  rw [map_sub, sub_eq_zero]
  cases j with
  | zero =>
      rw [equalCharacteristicLubinTateUnitParameterSeries_coeff_zero]
      change PowerSeries.constantCoeff (u : F.residueField⟦X⟧) =
        PowerSeries.coeff 0 (u : F.residueField⟦X⟧)
      exact (PowerSeries.coeff_zero_eq_constantCoeff_apply _).symm
  | succ j =>
      have hjn : j < n := by omega
      have hcoeff :=
        equalCharacteristicLubinTateUnitParameterSeries_coeff_succ
          F n a ⟨j, hjn⟩
      change PowerSeries.coeff (j + 1)
          (equalCharacteristicLubinTateUnitParameterSeries F n a) =
        a.higherCoeff ⟨j, hjn⟩ at hcoeff
      rw [hcoeff]
      rfl

private noncomputable def unitParameterReductionEquiv
    (F : LocalField.{u, v} K) (n : ℕ) :
    equalCharacteristicLubinTateUnitParameter F n ≃
      (equalCharacteristicLubinTateTruncatedRing F n)ˣ :=
  Equiv.ofBijective (unitParameterReduction F n)
    ⟨unitParameterReduction_injective F n,
      unitParameterReduction_surjective F n⟩

private theorem truncatedUnitsFinite
    (F : LocalField.{u, v} K) (n : ℕ) :
    Finite (equalCharacteristicLubinTateTruncatedRing F n)ˣ :=
  Finite.of_equiv (equalCharacteristicLubinTateUnitParameter F n)
    (unitParameterReductionEquiv F n)

private theorem unitQuotientFinite
    (F : LocalField.{u, v} K) (n : ℕ) :
    Finite
      (F.residueField⟦X⟧ˣ ⧸
        equalCharacteristicLubinTateHigherUnitSubgroup F n) := by
  let : Finite (equalCharacteristicLubinTateTruncatedRing F n)ˣ :=
    truncatedUnitsFinite F n
  exact
    Finite.of_equiv (equalCharacteristicLubinTateTruncatedRing F n)ˣ
      (equalCharacteristicLubinTateUnitQuotientEquivTruncatedUnits
        F n).symm.toEquiv

/-- The explicit unit quotient at repository level `n` has order
`(q - 1) q^n`, where `q` is the residue-field cardinality. -/
theorem equalCharacteristicLubinTateUnitQuotient_natCard
    (F : LocalField.{u, v} K) (n : ℕ) :
    letI : Finite
        (F.residueField⟦X⟧ˣ ⧸
          equalCharacteristicLubinTateHigherUnitSubgroup F n) :=
      unitQuotientFinite F n
    Nat.card
        (F.residueField⟦X⟧ˣ ⧸
          equalCharacteristicLubinTateHigherUnitSubgroup F n) =
      (Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n := by
  let : Finite
      (F.residueField⟦X⟧ˣ ⧸
        equalCharacteristicLubinTateHigherUnitSubgroup F n) :=
    unitQuotientFinite F n
  let : Finite (equalCharacteristicLubinTateTruncatedRing F n)ˣ :=
    truncatedUnitsFinite F n
  calc
    Nat.card
        (F.residueField⟦X⟧ˣ ⧸
          equalCharacteristicLubinTateHigherUnitSubgroup F n) =
        Nat.card (equalCharacteristicLubinTateTruncatedRing F n)ˣ :=
      Nat.card_congr
        (equalCharacteristicLubinTateUnitQuotientEquivTruncatedUnits
          F n).toEquiv
    _ = Nat.card (equalCharacteristicLubinTateUnitParameter F n) :=
      Nat.card_congr
        (unitParameterReductionEquiv F n).symm
    _ = (Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n :=
      equalCharacteristicLubinTateUnitParameter_natCard F n

/-- The canonical power-series unit quotient is the integer-unit quotient of
the Laurent valuation ring at the same depth. -/
private noncomputable def
    unitQuotientCard_powerSeriesQuotientEquivLaurentIntegerQuotient
    (F : LocalField.{u, v} K) (n : ℕ) :
    letI : ValuativeRel F.residueField⸨X⸩ :=
      equalCharacteristicLaurentValuativeRel F
    F.residueField⟦X⟧ˣ ⧸
        equalCharacteristicLubinTateHigherUnitSubgroup F n ≃*
      IntegerUnitsPrincipalQuot F.residueField⸨X⸩ (n + 1) := by
  let B := F.residueField⸨X⸩
  letI : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
  let e := equalCharacteristicPowerSeriesUnitsEquivLaurentInteger
    F.residueField
  let phi : F.residueField⟦X⟧ˣ →*
      IntegerUnitsPrincipalQuot B (n + 1) :=
    (integerUnitsPrincipalQuotMk B (n + 1)).comp e.toMonoidHom
  have hsurjective : Function.Surjective phi := by
    intro q
    obtain ⟨a, rfl⟩ :=
      integerUnitsPrincipalQuotMk_surjective B (n + 1) q
    refine ⟨e.symm a, ?_⟩
    change integerUnitsPrincipalQuotMk B (n + 1)
      (e (e.symm a)) = integerUnitsPrincipalQuotMk B (n + 1) a
    rw [e.apply_symm_apply]
  have hker : MonoidHom.ker phi =
      equalCharacteristicLubinTateHigherUnitSubgroup F n := by
    ext a
    change integerUnitsPrincipalQuotMk B (n + 1) (e a) = 1 ↔
      a ∈ equalCharacteristicLubinTateHigherUnitSubgroup F n
    rw [integerUnitsPrincipalQuotMk_eq_one_iff]
    exact
      (equalCharacteristicPowerSeriesUnitsEquivLaurentInteger_mem_iff
        F.residueField (n + 1) a).trans
        (mem_equalCharacteristicLubinTateHigherUnitSubgroup F n a).symm
  exact
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective phi hsurjective)

private theorem uniformizerPrincipalQuotientFinite
    (F : LocalField.{u, v} K) (n : ℕ) :
    letI : ValuativeRel F.residueField⸨X⸩ :=
      equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField F.residueField⸨X⸩ :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    Finite
      (F.residueField⸨X⸩ˣ ⧸
        LocalFieldTheory.uniformizerPrincipalSubgroup F.residueField⸨X⸩
          (equalCharacteristicLaurentUniformizerUnit F)⁻¹ 1 (n + 1)) := by
  let B := F.residueField⸨X⸩
  let pi : Bˣ := (equalCharacteristicLaurentUniformizerUnit F)⁻¹
  let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField B :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  let : Finite
      (F.residueField⟦X⟧ˣ ⧸
        equalCharacteristicLubinTateHigherUnitSubgroup F n) :=
    unitQuotientFinite F n
  let : Finite (IntegerUnitsPrincipalQuot B (n + 1)) :=
    Finite.of_equiv
      (F.residueField⟦X⟧ˣ ⧸
        equalCharacteristicLubinTateHigherUnitSubgroup F n)
      (unitQuotientCard_powerSeriesQuotientEquivLaurentIntegerQuotient
        F n).toEquiv
  have hpi : valuationMap B (Additive.ofMul pi) = 1 := by
    simpa [B, pi] using
      equalCharacteristicLaurentUniformizerUnit_inv_valuationMap F
  exact Finite.of_equiv (IntegerUnitsPrincipalQuot B (n + 1))
    (LocalFieldTheory.uniformizerPrincipalQuotientEquivIntegerUnitsPrincipalQuotient
      B pi hpi (n + 1)).symm.toEquiv

/-- The standard subgroup generated by the normalized Laurent uniformizer
and `U^(n+1)` has quotient cardinality `(q - 1) q^n`. -/
theorem equalCharacteristicLubinTateUniformizerPrincipalQuotient_natCard
    (F : LocalField.{u, v} K) (n : ℕ) :
    letI : ValuativeRel F.residueField⸨X⸩ :=
      equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField F.residueField⸨X⸩ :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    letI : Finite
        (F.residueField⸨X⸩ˣ ⧸
          LocalFieldTheory.uniformizerPrincipalSubgroup F.residueField⸨X⸩
            (equalCharacteristicLaurentUniformizerUnit F)⁻¹ 1 (n + 1)) :=
      uniformizerPrincipalQuotientFinite F n
    Nat.card
        (F.residueField⸨X⸩ˣ ⧸
          LocalFieldTheory.uniformizerPrincipalSubgroup F.residueField⸨X⸩
            (equalCharacteristicLaurentUniformizerUnit F)⁻¹ 1 (n + 1)) =
      (Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n := by
  let B := F.residueField⸨X⸩
  let pi : Bˣ := (equalCharacteristicLaurentUniformizerUnit F)⁻¹
  let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField B :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  let : Finite
      (Bˣ ⧸
        LocalFieldTheory.uniformizerPrincipalSubgroup B pi 1 (n + 1)) := by
    simpa [B, pi] using uniformizerPrincipalQuotientFinite F n
  let : Finite
      (F.residueField⟦X⟧ˣ ⧸
        equalCharacteristicLubinTateHigherUnitSubgroup F n) :=
    unitQuotientFinite F n
  let : Finite (IntegerUnitsPrincipalQuot B (n + 1)) :=
    Finite.of_equiv
      (F.residueField⟦X⟧ˣ ⧸
        equalCharacteristicLubinTateHigherUnitSubgroup F n)
      (unitQuotientCard_powerSeriesQuotientEquivLaurentIntegerQuotient
        F n).toEquiv
  have hpi : valuationMap B (Additive.ofMul pi) = 1 := by
    simpa [B, pi] using
      equalCharacteristicLaurentUniformizerUnit_inv_valuationMap F
  calc
    Nat.card
        (Bˣ ⧸ LocalFieldTheory.uniformizerPrincipalSubgroup B pi 1 (n + 1)) =
        Nat.card (IntegerUnitsPrincipalQuot B (n + 1)) :=
      Nat.card_congr
        (LocalFieldTheory.uniformizerPrincipalQuotientEquivIntegerUnitsPrincipalQuotient
          B pi hpi (n + 1)).toEquiv
    _ = Nat.card
        (F.residueField⟦X⟧ˣ ⧸
          equalCharacteristicLubinTateHigherUnitSubgroup F n) :=
      Nat.card_congr
        (unitQuotientCard_powerSeriesQuotientEquivLaurentIntegerQuotient
          F n).symm.toEquiv
    _ = (Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n :=
      equalCharacteristicLubinTateUnitQuotient_natCard F n

end EqualCharacteristic
end LubinTate
