/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.Core
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.UnitQuotientGalois
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.Core
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.BaseChange
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.Unramified
/-!
# Equal-characteristic Lubin--Tate upper filtration

This file identifies the image of the `k`-th higher-unit subgroup under the
explicit finite-level Artin map `a ↦ [a⁻¹]` with the actual upper
ramification group `G^k`.
-/

noncomputable section

open scoped LaurentSeries PowerSeries

universe u v

namespace LocalClassFieldTheory

open RamificationTheory.LocalField
open LubinTate

open LocalFieldTheory.DiscreteValuationField
open LubinTate.EqualCharacteristic

variable {K : Type u} [Field K]

private noncomputable def artinUnitParameter
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateUnitParameter F n :=
  equalCharacteristicLubinTateUnitParameterOfCoefficients F n
    (Units.map (PowerSeries.constantCoeff (R := F.residueField)) a)
    (fun i => PowerSeries.coeff (i + 1)
      (a : F.residueField⟦X⟧))

private theorem artinUnitParameter_coeff
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : F.residueField⟦X⟧ˣ) (j : ℕ) (hj : j ≤ n) :
    PowerSeries.coeff j
        (equalCharacteristicLubinTateUnitParameterSeries F n
          (artinUnitParameter F n a)) =
      PowerSeries.coeff j (a : F.residueField⟦X⟧) := by
  cases j with
  | zero =>
      rw [equalCharacteristicLubinTateUnitParameterSeries_coeff_zero]
      change PowerSeries.constantCoeff (a : F.residueField⟦X⟧) =
        PowerSeries.coeff 0 (a : F.residueField⟦X⟧)
      exact (PowerSeries.coeff_zero_eq_constantCoeff_apply _).symm
  | succ j =>
      have hjn : j < n := by omega
      have hcoeff :=
        equalCharacteristicLubinTateUnitParameterSeries_coeff_succ
          F n (artinUnitParameter F n a) ⟨j, hjn⟩
      change PowerSeries.coeff (j + 1)
          (equalCharacteristicLubinTateUnitParameterSeries F n
            (artinUnitParameter F n a)) =
        (artinUnitParameter F n a).higherCoeff ⟨j, hjn⟩ at hcoeff
      rw [hcoeff]
      rfl

private theorem artinUnitParameter_reduction
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateUnitReduction F n
        (equalCharacteristicLubinTateUnitParameterUnit F n
          (artinUnitParameter F n a)) =
      equalCharacteristicLubinTateUnitReduction F n a := by
  apply Units.ext
  change equalCharacteristicLubinTateTruncatedRingMk F n
      (equalCharacteristicLubinTateUnitParameterSeries F n
        (artinUnitParameter F n a)) =
    equalCharacteristicLubinTateTruncatedRingMk F n
      (a : F.residueField⟦X⟧)
  rw [equalCharacteristicLubinTateTruncatedRingMk_eq_iff,
    Ideal.mem_span_singleton]
  apply PowerSeries.X_pow_dvd_iff.mpr
  intro j hj
  rw [map_sub, sub_eq_zero]
  exact artinUnitParameter_coeff F n a j (Nat.lt_succ_iff.mp hj)

private theorem artinUnitToGal_eq_parameter
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateArtinUnitToGal F n a =
      equalCharacteristicLubinTateUnitParameterToGal F n
        (artinUnitParameter F n a⁻¹) := by
  let p := artinUnitParameter F n a⁻¹
  let b := equalCharacteristicLubinTateUnitParameterUnit F n p
  have hab : a * b ∈
      equalCharacteristicLubinTateHigherUnitSubgroup F n := by
    change equalCharacteristicLubinTateUnitReduction F n (a * b) = 1
    rw [map_mul]
    have hb :
        equalCharacteristicLubinTateUnitReduction F n b =
          equalCharacteristicLubinTateUnitReduction F n a⁻¹ := by
      simpa [p, b] using artinUnitParameter_reduction F n a⁻¹
    rw [hb, map_inv, mul_inv_cancel]
  have hprod :
      equalCharacteristicLubinTateArtinUnitToGal F n a *
          equalCharacteristicLubinTateArtinUnitToGal F n b = 1 := by
    rw [← map_mul]
    exact
      (equalCharacteristicLubinTateArtinUnitToGal_eq_one_iff F n
        (a * b)).2 hab
  calc
    equalCharacteristicLubinTateArtinUnitToGal F n a =
        (equalCharacteristicLubinTateArtinUnitToGal F n b)⁻¹ :=
      eq_inv_of_mul_eq_one_left hprod
    _ = equalCharacteristicLubinTateArtinUnitToGal F n b⁻¹ := by
          exact
            (map_inv (equalCharacteristicLubinTateArtinUnitToGal F n) b).symm
    _ = equalCharacteristicLubinTateUnitParameterToGal F n p := by
          simpa [b, equalCharacteristicLubinTateUnitParameterToGal] using
            equalCharacteristicLubinTateArtinUnitToGal_parameterUnit_inv
              F n p
    _ = equalCharacteristicLubinTateUnitParameterToGal F n
          (artinUnitParameter F n a⁻¹) := by rfl

private theorem mem_span_X_pow_iff_coeff_zero
    {k : Type u} [Field k] (f : k⟦X⟧) (m : ℕ) :
    f ∈ Ideal.span ({PowerSeries.X ^ m} : Set k⟦X⟧) ↔
      ∀ j < m, PowerSeries.coeff j f = 0 := by
  rw [Ideal.mem_span_singleton]
  exact PowerSeries.X_pow_dvd_iff

theorem equalCharacteristicLubinTateArtinHigherUnitImage_eq_upper
    {K₀ : Type} [Field K₀]
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    (equalCharacteristicLubinTateHigherUnitSubgroup F (k - 1)).map
        (equalCharacteristicLubinTateArtinUnitToGal F n) =
      equalCharacteristicLubinTateRealUpperRamificationGroup F n (k : ℝ) := by
  ext σ
  constructor
  · rintro ⟨a, ha, rfl⟩
    let p := artinUnitParameter F n a⁻¹
    rw [artinUnitToGal_eq_parameter F n a]
    apply
      (mem_equalCharacteristicLubinTateRealUpperRamificationGroup_nat_iff_coeff_zero
        F n k hkn p).2
    have hainv :
        a⁻¹ ∈ equalCharacteristicLubinTateHigherUnitSubgroup F (k - 1) :=
      (equalCharacteristicLubinTateHigherUnitSubgroup F (k - 1)).inv_mem ha
    have hspan :
        ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧) - 1 ∈
          Ideal.span
            ({PowerSeries.X ^ k} : Set F.residueField⟦X⟧) := by
      simpa [Nat.sub_add_cancel hk] using
        (mem_equalCharacteristicLubinTateHigherUnitSubgroup
          F (k - 1) a⁻¹).1 hainv
    have hzero :
        ∀ j < k,
          PowerSeries.coeff j
              (((a⁻¹ : F.residueField⟦X⟧ˣ) :
                F.residueField⟦X⟧) - 1) = 0 :=
      (mem_span_X_pow_iff_coeff_zero
        (((a⁻¹ : F.residueField⟦X⟧ˣ) :
          F.residueField⟦X⟧) - 1) k).1 hspan
    intro j hj
    change PowerSeries.coeff j
        (equalCharacteristicLubinTateUnitParameterSeries F n
          (artinUnitParameter F n a⁻¹) - 1) = 0
    rw [map_sub, artinUnitParameter_coeff F n a⁻¹ j (by omega)]
    simpa only [map_sub] using hzero j hj
  · intro hσ
    let p :=
      (equalCharacteristicLubinTateUnitParameterEquivGal F n).symm σ
    let a := (equalCharacteristicLubinTateUnitParameterUnit F n p)⁻¹
    have hpσ :
        equalCharacteristicLubinTateUnitParameterToGal F n p = σ := by
      change
        equalCharacteristicLubinTateUnitParameterEquivGal F n
            ((equalCharacteristicLubinTateUnitParameterEquivGal F n).symm σ) =
          σ
      exact
        (equalCharacteristicLubinTateUnitParameterEquivGal F n).apply_symm_apply σ
    have hpupper :
        equalCharacteristicLubinTateUnitParameterToGal F n p ∈
          equalCharacteristicLubinTateRealUpperRamificationGroup
            F n (k : ℝ) := by
      simpa [hpσ] using hσ
    have hpzero :
        ∀ j < k,
          PowerSeries.coeff j
              (equalCharacteristicLubinTateUnitParameterSeries F n p - 1) = 0 :=
      (mem_equalCharacteristicLubinTateRealUpperRamificationGroup_nat_iff_coeff_zero
        F n k hkn p).1 hpupper
    have hpunit :
        equalCharacteristicLubinTateUnitParameterUnit F n p ∈
          equalCharacteristicLubinTateHigherUnitSubgroup F (k - 1) := by
      apply
        (mem_equalCharacteristicLubinTateHigherUnitSubgroup
          F (k - 1)
            (equalCharacteristicLubinTateUnitParameterUnit F n p)).2
      simpa [equalCharacteristicLubinTateUnitParameterUnit_val,
        Nat.sub_add_cancel hk] using
        (mem_span_X_pow_iff_coeff_zero
          (equalCharacteristicLubinTateUnitParameterSeries F n p - 1) k).2
            hpzero
    refine ⟨a, ?_, ?_⟩
    · exact
        (equalCharacteristicLubinTateHigherUnitSubgroup F (k - 1)).inv_mem
          hpunit
    · calc
        equalCharacteristicLubinTateArtinUnitToGal F n a =
            equalCharacteristicLubinTateUnitParameterToGal F n p := by
          simpa [a, equalCharacteristicLubinTateUnitParameterToGal] using
            equalCharacteristicLubinTateArtinUnitToGal_parameterUnit_inv F n p
        _ = σ := hpσ

end LocalClassFieldTheory
