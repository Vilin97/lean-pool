/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.PrimitivePoint
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PolynomialRootProximity
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.ValuationKrasner
/-!
# Valuation of primitive-point displacement

This module computes the normalized additive valuation of the displacement of
the chosen primitive Lubin--Tate point from the first visible coefficient of
the corresponding unit parameter.
-/

@[expose] public section

noncomputable
section

open scoped LaurentSeries Pointwise PowerSeries

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LubinTate.EqualCharacteristic
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v y

variable {K : Type u} [Field K]

section ChosenRamificationTarget

variable {K₀ : Type} [Field K₀]

section PrimitivePointDisplacementValuation

attribute [local instance]
  equalCharacteristicLubinTateLevelField_finiteDimensional_forDisplacementValuation
  equalCharacteristicLubinTateLevelField_isGalois_forDisplacementValuation

private noncomputable def equalCharacteristicLubinTateCoefficientInteger
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) (c : F.residueField) :
    (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring :=
  integerMap
    (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF
    (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF
    (equalCharacteristicPowerSeriesEquivLubinTateBaseValuationSubring F
      (PowerSeries.C c))

@[simp]
private theorem equalCharacteristicLubinTateCoefficientInteger_zero
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateCoefficientInteger F n 0 = 0 := by
  simp [equalCharacteristicLubinTateCoefficientInteger]

@[simp]
private theorem equalCharacteristicLubinTateCoefficientInteger_coe
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) (c : F.residueField) :
    (equalCharacteristicLubinTateCoefficientInteger F n c :
      equalCharacteristicLubinTateLevelField F n) =
        algebraMap F.residueField⸨X⸩
          (equalCharacteristicLubinTateLevelField F n)
          (algebraMap F.residueField F.residueField⸨X⸩ c) := by
  rfl

private noncomputable def equalCharacteristicLubinTatePiEndInteger
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ)
    (x :
      (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring) :
    (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring :=
  x ^ Nat.card F.residueField +
    integerMap
        (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF
        (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF
        (equalCharacteristicLubinTateBaseUniformizerInteger F) * x

@[simp]
private theorem equalCharacteristicLubinTatePiEndInteger_coe
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ)
    (x :
      (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring) :
    (equalCharacteristicLubinTatePiEndInteger F n x :
      equalCharacteristicLubinTateLevelField F n) =
      equalCharacteristicLubinTateAmbientPiEnd F
        (algebraMap F.residueField⸨X⸩
          (equalCharacteristicLubinTateLevelField F n)
          (equalCharacteristicLaurentUniformizer F))
        (x : equalCharacteristicLubinTateLevelField F n) := by
  simp [equalCharacteristicLubinTatePiEndInteger,
    equalCharacteristicLubinTateAmbientPiEnd_apply,
    integerMap_apply,
    equalCharacteristicLubinTateBaseUniformizerInteger_coe]

private noncomputable def equalCharacteristicLubinTatePiIterateInteger
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    ℕ →
      (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring
  | 0 => equalCharacteristicLubinTatePrimitivePointInteger F n
  | i + 1 =>
      equalCharacteristicLubinTatePiEndInteger F n
        (equalCharacteristicLubinTatePiIterateInteger F n i)

private theorem equalCharacteristicLubinTateAmbientPiIterate_succ_left
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n i : ℕ) (x : equalCharacteristicLubinTateLevelField F n) :
    equalCharacteristicLubinTateAmbientPiIterate F
        (algebraMap F.residueField⸨X⸩
          (equalCharacteristicLubinTateLevelField F n)
          (equalCharacteristicLaurentUniformizer F))
        (i + 1) x =
      equalCharacteristicLubinTateAmbientPiEnd F
          (algebraMap F.residueField⸨X⸩
            (equalCharacteristicLubinTateLevelField F n)
            (equalCharacteristicLaurentUniformizer F))
        (equalCharacteristicLubinTateAmbientPiIterate F
          (algebraMap F.residueField⸨X⸩
            (equalCharacteristicLubinTateLevelField F n)
            (equalCharacteristicLaurentUniformizer F))
          i x) := by
  change
    ((equalCharacteristicLubinTateAmbientPiEnd F
      (algebraMap F.residueField⸨X⸩
        (equalCharacteristicLubinTateLevelField F n)
        (equalCharacteristicLaurentUniformizer F))) ^ (i + 1)) x =
      equalCharacteristicLubinTateAmbientPiEnd F
        (algebraMap F.residueField⸨X⸩
          (equalCharacteristicLubinTateLevelField F n)
          (equalCharacteristicLaurentUniformizer F))
        (((equalCharacteristicLubinTateAmbientPiEnd F
          (algebraMap F.residueField⸨X⸩
            (equalCharacteristicLubinTateLevelField F n)
            (equalCharacteristicLaurentUniformizer F))) ^ i) x)
  rw [pow_succ']
  rfl

@[simp]
private theorem equalCharacteristicLubinTatePiIterateInteger_coe
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n i : ℕ) :
    (equalCharacteristicLubinTatePiIterateInteger F n i :
      equalCharacteristicLubinTateLevelField F n) =
      equalCharacteristicLubinTateAmbientPiIterate F
        (algebraMap F.residueField⸨X⸩
          (equalCharacteristicLubinTateLevelField F n)
          (equalCharacteristicLaurentUniformizer F))
        i (equalCharacteristicLubinTateLevelPowerBasis F n).gen := by
  induction i with
  | zero =>
      simp [equalCharacteristicLubinTatePiIterateInteger]
  | succ i ih =>
      rw [equalCharacteristicLubinTatePiIterateInteger,
        equalCharacteristicLubinTatePiEndInteger_coe, ih,
        equalCharacteristicLubinTateAmbientPiIterate_succ_left]

private theorem equalCharacteristicLubinTateCoefficientInteger_isUnit
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) {c : F.residueField} (hc : c ≠ 0) :
    IsUnit (equalCharacteristicLubinTateCoefficientInteger F n c) := by
  rw [equalCharacteristicLubinTateCoefficientInteger,
    integerMap_isUnit_iff]
  have hC : IsUnit (PowerSeries.C c : F.residueField⟦X⟧) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simpa using hc
  exact
    (equalCharacteristicPowerSeriesEquivLubinTateBaseValuationSubring F).toRingHom.isUnit_map
      hC

private theorem equalCharacteristicLubinTateCoefficientInteger_addVal
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) {c : F.residueField} (hc : c ≠ 0) :
    IsDiscreteValuationRing.addVal
        (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring
        (equalCharacteristicLubinTateCoefficientInteger F n c) = 0 :=
  (IsDiscreteValuationRing.addVal_eq_zero_iff).2
    (equalCharacteristicLubinTateCoefficientInteger_isUnit F n hc)

private theorem equalCharacteristicLubinTatePiIterateInteger_addVal
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n i : ℕ) (hi : i ≤ n) :
    IsDiscreteValuationRing.addVal
        (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring
        (equalCharacteristicLubinTatePiIterateInteger F n i) =
      (Nat.card F.residueField ^ i : ℕ) := by
  induction i with
  | zero =>
      simpa [equalCharacteristicLubinTatePiIterateInteger] using
        equalCharacteristicLubinTatePrimitivePointInteger_addVal F n
  | succ i ih =>
      let target := equalCharacteristicLubinTateLevelCompleteDVF F n
      let q := Nat.card F.residueField
      let d := (q - 1) * q ^ n
      let y := equalCharacteristicLubinTatePiIterateInteger F n i
      have hi' : i ≤ n := Nat.le_trans (Nat.le_succ i) hi
      have hiy :
          IsDiscreteValuationRing.addVal target.valuationSubring y =
            (q ^ i : ℕ) := by
        exact ih hi'
      have hT :
          IsDiscreteValuationRing.addVal target.valuationSubring
              (integerMap
                (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF
                target.toDVF
                (equalCharacteristicLubinTateBaseUniformizerInteger F)) =
            (d : ℕ) := by
        exact
          equalCharacteristicLubinTateBaseUniformizerInteger_map_addVal_eq_degree
            F n
      have hpow :
          IsDiscreteValuationRing.addVal target.valuationSubring (y ^ q) =
            (q ^ (i + 1) : ℕ) := by
        rw [IsDiscreteValuationRing.addVal_pow, hiy]
        simp [nsmul_eq_mul, pow_succ, Nat.mul_comm]
      have hmul :
          IsDiscreteValuationRing.addVal target.valuationSubring
              (integerMap
                  (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF
                  target.toDVF
                  (equalCharacteristicLubinTateBaseUniformizerInteger F) *
                y) =
            (d + q ^ i : ℕ) := by
        rw [IsDiscreteValuationRing.addVal_mul, hT, hiy]
        rfl
      have hqone : 1 < q := by
        exact (Finite.one_lt_card : 1 < Nat.card F.residueField)
      have hqpos : 0 < q := Nat.zero_lt_one.trans hqone
      have hpowle : q ^ (i + 1) ≤ q ^ n :=
        Nat.pow_le_pow_right hqpos hi
      have hqsub : 1 ≤ q - 1 := by
        omega
      have hdegreele : q ^ n ≤ d := by
        calc
          q ^ n = 1 * q ^ n := by simp
          _ ≤ (q - 1) * q ^ n := Nat.mul_le_mul_right (q ^ n) hqsub
      have htailpos : 0 < q ^ i := Nat.pow_pos hqpos
      have hnatlt : q ^ (i + 1) < d + q ^ i :=
        hpowle.trans_lt (hdegreele.trans_lt (Nat.lt_add_of_pos_right htailpos))
      have henatlt : (q ^ (i + 1) : ℕ∞) < (d + q ^ i : ℕ) := by
        exact_mod_cast hnatlt
      have hdistinct :
          IsDiscreteValuationRing.addVal target.valuationSubring (y ^ q) ≠
            IsDiscreteValuationRing.addVal target.valuationSubring
              (integerMap
                  (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF
                  target.toDVF
                  (equalCharacteristicLubinTateBaseUniformizerInteger F) *
                y) := by
        rw [hpow, hmul]
        exact ne_of_lt henatlt
      rw [equalCharacteristicLubinTatePiIterateInteger,
        equalCharacteristicLubinTatePiEndInteger]
      rw [(IsDiscreteValuationRing.addVal target.valuationSubring).map_add_of_distinct_val
        hdistinct, hpow, hmul]
      rw [min_eq_left]
      exact henatlt.le

private noncomputable def equalCharacteristicLubinTateBracketInteger
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) (u : F.residueField⟦X⟧) :
    (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring :=
  ∑ i ∈ Finset.range (n + 1),
    equalCharacteristicLubinTateCoefficientInteger F n
        (PowerSeries.coeff i u) *
      equalCharacteristicLubinTatePiIterateInteger F n i

@[simp]
private theorem equalCharacteristicLubinTateBracketInteger_coe
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) (u : F.residueField⟦X⟧) :
    (equalCharacteristicLubinTateBracketInteger F n u :
      equalCharacteristicLubinTateLevelField F n) =
      equalCharacteristicLubinTateAmbientBracket F
        ((algebraMap F.residueField⸨X⸩
          (equalCharacteristicLubinTateLevelField F n)).comp
            (algebraMap F.residueField F.residueField⸨X⸩))
        (algebraMap F.residueField⸨X⸩
          (equalCharacteristicLubinTateLevelField F n)
          (equalCharacteristicLaurentUniformizer F))
        (n + 1) u (equalCharacteristicLubinTateLevelPowerBasis F n).gen := by
  rw [equalCharacteristicLubinTateBracketInteger,
    equalCharacteristicLubinTateAmbientBracket_apply]
  change
    (equalCharacteristicLubinTateLevelCompleteDVF F n).valuation.valuationSubring.subtype
        (∑ i ∈ Finset.range (n + 1),
          equalCharacteristicLubinTateCoefficientInteger F n
              (PowerSeries.coeff i u) *
            equalCharacteristicLubinTatePiIterateInteger F n i) =
      _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul]
  change
    (equalCharacteristicLubinTateCoefficientInteger F n
        (PowerSeries.coeff i u) :
      equalCharacteristicLubinTateLevelField F n) *
        (equalCharacteristicLubinTatePiIterateInteger F n i :
          equalCharacteristicLubinTateLevelField F n) =
      _
  rw [equalCharacteristicLubinTateCoefficientInteger_coe,
    equalCharacteristicLubinTatePiIterateInteger_coe]
  rfl

private theorem natCast_lt_addVal_finsetSum_of_forall_lt
    {R I : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (c : ℕ) (s : Finset I) (f : I → R)
    (h : ∀ i ∈ s,
      (c : ℕ∞) < IsDiscreteValuationRing.addVal R (f i)) :
    (c : ℕ∞) <
      IsDiscreteValuationRing.addVal R (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      have hmin :
          (c : ℕ∞) <
            min
              (IsDiscreteValuationRing.addVal R (f i))
              (IsDiscreteValuationRing.addVal R (∑ j ∈ s, f j)) :=
        lt_min (h i (Finset.mem_insert_self i s))
          (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
      exact hmin.trans_le IsDiscreteValuationRing.addVal_add

private theorem equalCharacteristicLubinTateBracketInteger_addVal_eq_order
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) (u : F.residueField⟦X⟧)
    (hu : u ≠ 0) (hk : u.order.toNat ≤ n) :
    IsDiscreteValuationRing.addVal
        (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring
        (equalCharacteristicLubinTateBracketInteger F n u) =
      (Nat.card F.residueField ^ u.order.toNat : ℕ) := by
  classical
  let target := equalCharacteristicLubinTateLevelCompleteDVF F n
  let q := Nat.card F.residueField
  let k := u.order.toNat
  let term :
      ℕ → target.valuationSubring := fun i =>
    equalCharacteristicLubinTateCoefficientInteger F n
        (PowerSeries.coeff i u) *
      equalCharacteristicLubinTatePiIterateInteger F n i
  let s := Finset.range (n + 1)
  have hk_mem : k ∈ s := by
    simpa [s, k] using hk
  have hkcoeff : PowerSeries.coeff k u ≠ 0 := by
    exact PowerSeries.coeff_order hu
  have hterm :
      IsDiscreteValuationRing.addVal target.valuationSubring (term k) =
        (q ^ k : ℕ) := by
    change
      IsDiscreteValuationRing.addVal target.valuationSubring
          (equalCharacteristicLubinTateCoefficientInteger F n
              (PowerSeries.coeff k u) *
            equalCharacteristicLubinTatePiIterateInteger F n k) =
        _
    rw [IsDiscreteValuationRing.addVal_mul,
      equalCharacteristicLubinTateCoefficientInteger_addVal F n hkcoeff,
      equalCharacteristicLubinTatePiIterateInteger_addVal F n k hk,
      zero_add]
  have hqone : 1 < q := by
    exact (Finite.one_lt_card : 1 < Nat.card F.residueField)
  have htailTerm :
      ∀ i ∈ s.erase k,
        (q ^ k : ℕ∞) <
          IsDiscreteValuationRing.addVal target.valuationSubring (term i) := by
    intro i hi
    have his : i ∈ s := (Finset.mem_erase.mp hi).2
    have hine : i ≠ k := (Finset.mem_erase.mp hi).1
    have hin : i ≤ n := by
      simpa [s, Nat.lt_succ_iff] using his
    rcases lt_or_gt_of_ne hine with hik | hki
    · have hcoeffzero : PowerSeries.coeff i u = 0 := by
        exact PowerSeries.coeff_of_lt_order_toNat i (by simpa [k] using hik)
      simp [term, hcoeffzero]
    · by_cases hcoeffzero : PowerSeries.coeff i u = 0
      · simp [term, hcoeffzero]
      · have hpowlt : q ^ k < q ^ i :=
          Nat.pow_lt_pow_right hqone hki
        change
          (q ^ k : ℕ∞) <
            IsDiscreteValuationRing.addVal target.valuationSubring
              (equalCharacteristicLubinTateCoefficientInteger F n
                  (PowerSeries.coeff i u) *
                equalCharacteristicLubinTatePiIterateInteger F n i)
        rw [IsDiscreteValuationRing.addVal_mul,
          equalCharacteristicLubinTateCoefficientInteger_addVal F n hcoeffzero,
          equalCharacteristicLubinTatePiIterateInteger_addVal F n i hin,
          zero_add]
        exact_mod_cast hpowlt
  have htail :
      (q ^ k : ℕ∞) <
        IsDiscreteValuationRing.addVal target.valuationSubring
          (∑ i ∈ s.erase k, term i) :=
    natCast_lt_addVal_finsetSum_of_forall_lt
      (q ^ k) (s.erase k) term htailTerm
  have hdistinct :
      IsDiscreteValuationRing.addVal target.valuationSubring (term k) ≠
        IsDiscreteValuationRing.addVal target.valuationSubring
          (∑ i ∈ s.erase k, term i) := by
    rw [hterm]
    exact ne_of_lt htail
  rw [equalCharacteristicLubinTateBracketInteger]
  change
    IsDiscreteValuationRing.addVal target.valuationSubring
        (∑ i ∈ s, term i) = _
  rw [← Finset.add_sum_erase s term hk_mem]
  rw [(IsDiscreteValuationRing.addVal target.valuationSubring).map_add_of_distinct_val
    hdistinct, hterm]
  rw [min_eq_left]
  exact htail.le

/-- The first nonzero coefficient of a nontrivial visible parameter occurs
at an index at most `n`. -/
theorem equalCharacteristicLubinTateUnitParameterSeries_sub_one_order_toNat_le
    (F : LocalField.{0, v} K₀)
    (n : ℕ) (a : equalCharacteristicLubinTateUnitParameter F n)
    (hu : equalCharacteristicLubinTateUnitParameterSeries F n a - 1 ≠ 0) :
    (equalCharacteristicLubinTateUnitParameterSeries F n a - 1).order.toNat ≤
      n := by
  let u := equalCharacteristicLubinTateUnitParameterSeries F n a - 1
  let k := u.order.toNat
  have hkcoeff : PowerSeries.coeff k u ≠ 0 :=
    PowerSeries.coeff_order hu
  by_contra hk
  have hnk : n < k := Nat.lt_of_not_ge hk
  have hk0 : k ≠ 0 := by omega
  have hklarge : ¬ k - 1 < n := by omega
  apply hkcoeff
  simp [u, equalCharacteristicLubinTateUnitParameterSeries, hk0, hklarge]

private theorem equalCharacteristicLubinTateBracketInteger_coe_eq_aeval
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) (u : F.residueField⟦X⟧) :
    (equalCharacteristicLubinTateBracketInteger F n u :
      equalCharacteristicLubinTateLevelField F n) =
      Polynomial.aeval (equalCharacteristicLubinTateLevelPowerBasis F n).gen
        (equalCharacteristicLubinTateBracketPolynomial F (n + 1) u) := by
  rw [equalCharacteristicLubinTateBracketInteger_coe]
  symm
  change
    Polynomial.eval₂
        (algebraMap F.residueField⸨X⸩
          (equalCharacteristicLubinTateLevelField F n))
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen
        (equalCharacteristicLubinTateBracketPolynomial F (n + 1) u) =
      _
  exact
    equalCharacteristicLubinTateBracketPolynomial_eval₂ F
      (algebraMap F.residueField⸨X⸩
        (equalCharacteristicLubinTateLevelField F n))
      (n + 1) u (equalCharacteristicLubinTateLevelPowerBasis F n).gen

private theorem
    equalCharacteristicLubinTatePrimitivePointInteger_displacement_eq_bracketInteger
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ)
    (sigma : Gal((equalCharacteristicLubinTateLevelField F n)/F.residueField⸨X⸩))
    (a : equalCharacteristicLubinTateUnitParameter F n)
    (ha :
      sigma (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
        equalCharacteristicLubinTateLevelBracket F n (n + 1)
          (equalCharacteristicLubinTateUnitParameterSeries F n a)
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen) :
    valuationSubringAutOfUniqueExtension
          (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
            F n)
          sigma (equalCharacteristicLubinTatePrimitivePointInteger F n) -
        equalCharacteristicLubinTatePrimitivePointInteger F n =
      equalCharacteristicLubinTateBracketInteger F n
        (equalCharacteristicLubinTateUnitParameterSeries F n a - 1) := by
  apply Subtype.ext
  rw [
    equalCharacteristicLubinTatePrimitivePointInteger_displacement_coe_eq_aeval
      F n sigma a ha,
    equalCharacteristicLubinTateBracketInteger_coe_eq_aeval]

private theorem
    equalCharacteristicLubinTatePrimitivePointInteger_displacement_addVal
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ)
    (sigma : Gal((equalCharacteristicLubinTateLevelField F n)/F.residueField⸨X⸩))
    (a : equalCharacteristicLubinTateUnitParameter F n)
    (ha :
      sigma (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
        equalCharacteristicLubinTateLevelBracket F n (n + 1)
          (equalCharacteristicLubinTateUnitParameterSeries F n a)
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen)
    (hu : equalCharacteristicLubinTateUnitParameterSeries F n a - 1 ≠ 0) :
    IsDiscreteValuationRing.addVal
        (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring
        (valuationSubringAutOfUniqueExtension
            (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
              F n)
            sigma (equalCharacteristicLubinTatePrimitivePointInteger F n) -
          equalCharacteristicLubinTatePrimitivePointInteger F n) =
      (Nat.card F.residueField ^
        (equalCharacteristicLubinTateUnitParameterSeries F n a - 1).order.toNat :
          ℕ) := by
  rw [
    equalCharacteristicLubinTatePrimitivePointInteger_displacement_eq_bracketInteger
      F n sigma a ha]
  exact
    equalCharacteristicLubinTateBracketInteger_addVal_eq_order F n
      (equalCharacteristicLubinTateUnitParameterSeries F n a - 1) hu
      (equalCharacteristicLubinTateUnitParameterSeries_sub_one_order_toNat_le
        F n a hu)

/-- A nonidentity automorphism has a genuinely nonzero visible coefficient
difference from the identity parameter. -/
theorem
    equalCharacteristicLubinTateUnitParameterSeries_sub_one_ne_zero_of_sigma_ne_one
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ)
    (sigma : Gal((equalCharacteristicLubinTateLevelField F n)/F.residueField⸨X⸩))
    (a : equalCharacteristicLubinTateUnitParameter F n)
    (ha :
      sigma (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
        equalCharacteristicLubinTateLevelBracket F n (n + 1)
          (equalCharacteristicLubinTateUnitParameterSeries F n a)
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen)
    (hsigma : sigma ≠ 1) :
    equalCharacteristicLubinTateUnitParameterSeries F n a - 1 ≠ 0 := by
  intro hu
  apply hsigma
  have hseries :
      equalCharacteristicLubinTateUnitParameterSeries F n a = 1 :=
    sub_eq_zero.mp hu
  have hone :
      equalCharacteristicLubinTateLevelBracket F n (n + 1) 1
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen := by
    apply Subtype.ext
    change
      equalCharacteristicLubinTateAmbientBracket F
          (equalCharacteristicSeparableCoefficientHom F)
          (equalCharacteristicSeparableUniformizer F) (n + 1) 1
          (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) =
        chosenEqualCharacteristicLubinTatePrimitiveRoot F n
    exact
      equalCharacteristicLubinTateAmbientBracket_one_apply_of_torsion F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)
        (chosenEqualCharacteristicLubinTatePrimitiveRoot_torsion F n)
  apply AlgEquiv.coe_toAlgHom_injective
  apply (equalCharacteristicLubinTateLevelPowerBasis F n).algHom_ext
  change
    sigma (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
      (equalCharacteristicLubinTateLevelPowerBasis F n).gen
  calc
    sigma (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
        equalCharacteristicLubinTateLevelBracket F n (n + 1)
          (equalCharacteristicLubinTateUnitParameterSeries F n a)
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen := ha
    _ = equalCharacteristicLubinTateLevelBracket F n (n + 1) 1
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen := by
            rw [hseries]
    _ = (equalCharacteristicLubinTateLevelPowerBasis F n).gen := hone

/-- If `k` is the first visible coefficient where a nonidentity Galois
parameter differs from `1`, then its displacement of the primitive
uniformizer has normalized additive valuation exactly `q^k`. -/
theorem
    equalCharacteristicLubinTatePrimitivePointInteger_displacement_addVal_of_ne_one
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ)
    (sigma : Gal((equalCharacteristicLubinTateLevelField F n)/F.residueField⸨X⸩))
    (a : equalCharacteristicLubinTateUnitParameter F n)
    (ha :
      sigma (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
        equalCharacteristicLubinTateLevelBracket F n (n + 1)
          (equalCharacteristicLubinTateUnitParameterSeries F n a)
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen)
    (hsigma : sigma ≠ 1) :
    IsDiscreteValuationRing.addVal
        (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring
        (valuationSubringAutOfUniqueExtension
            (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
              F n)
            sigma (equalCharacteristicLubinTatePrimitivePointInteger F n) -
          equalCharacteristicLubinTatePrimitivePointInteger F n) =
      (Nat.card F.residueField ^
        (equalCharacteristicLubinTateUnitParameterSeries F n a - 1).order.toNat :
          ℕ) := by
  exact
    equalCharacteristicLubinTatePrimitivePointInteger_displacement_addVal
      F n sigma a ha
      (equalCharacteristicLubinTateUnitParameterSeries_sub_one_ne_zero_of_sigma_ne_one
        F n sigma a ha hsigma)

end PrimitivePointDisplacementValuation


end ChosenRamificationTarget

end LubinTate

end
