/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.DisplacementValuation
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.RamificationNumber
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.AddVal
/-!
# Lower ramification groups of equal-characteristic Lubin--Tate levels

This module identifies the actual lower ramification groups attached to the
chosen complete valuation, both by visible unit-parameter coefficients and by
their exact cardinalities.
-/

noncomputable section

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

/-- The actual real lower ramification group of the explicit
equal-characteristic Lubin--Tate level, formed from the chosen
integral-closure valuation. -/
noncomputable def equalCharacteristicLubinTateRealLowerRamificationGroup
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) (s : ℝ) :
    Subgroup Gal((equalCharacteristicLubinTateLevelField F n)/F.residueField⸨X⸩) :=
  RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup
    (base := (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF)
    (target := (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF)
    (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
      F n)
    s

/-- Finite-dimensionality for the explicit level while computing its lower
ramification groups. -/
noncomputable local instance
    equalCharacteristicLubinTateLevelField_finiteDimensional_forLowerGroups
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
  equalCharacteristicLubinTateLevelField_finiteDimensional F n

/-- Galoisness for the explicit level while computing its lower
ramification groups. -/
noncomputable local instance
    equalCharacteristicLubinTateLevelField_isGalois_forLowerGroups
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    IsGalois F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
  equalCharacteristicLubinTateLevelField_isGalois F n

/-- At a natural lower index, membership in the actual Lubin--Tate lower
ramification group is detected by the displacement of its primitive
uniformizer alone. -/
theorem
    mem_equalCharacteristicLubinTateRealLowerRamificationGroup_nat_iff_primitivePoint
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n i : ℕ)
    (sigma : Gal((equalCharacteristicLubinTateLevelField F n)/F.residueField⸨X⸩)) :
    sigma ∈ equalCharacteristicLubinTateRealLowerRamificationGroup
        F n (i : ℝ) ↔
      ((i + 1 : ℕ) : ℕ∞) ≤
        IsDiscreteValuationRing.addVal
          (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring
          (valuationSubringAutOfUniqueExtension
              (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
                F n)
              sigma (equalCharacteristicLubinTatePrimitivePointInteger F n) -
            equalCharacteristicLubinTatePrimitivePointInteger F n) := by
  change
    sigma ∈ lowerRamificationGroup
        (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
          F n) (i : ℝ) ↔ _
  constructor
  · intro hsigma
    have hall :=
      (mem_lowerRamificationGroup_nat_iff
        (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
          F n)
        i sigma).mp hsigma
    exact
      (IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_addVal_ge
        (valuationSubringAutOfUniqueExtension
            (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
              F n)
            sigma (equalCharacteristicLubinTatePrimitivePointInteger F n) -
          equalCharacteristicLubinTatePrimitivePointInteger F n)
        (i + 1)).mp
        (hall (equalCharacteristicLubinTatePrimitivePointInteger F n))
  · intro hdisplacement
    apply
      (mem_lowerRamificationGroup_nat_iff
        (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
          F n)
        i sigma).mpr
    intro z
    apply
      valuationSubringAutOfUniqueExtension_sub_mem_of_mem_adjoin
        (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
          F n)
    · exact
        (IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_addVal_ge
          (valuationSubringAutOfUniqueExtension
              (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
                F n)
              sigma (equalCharacteristicLubinTatePrimitivePointInteger F n) -
            equalCharacteristicLubinTatePrimitivePointInteger F n)
          (i + 1)).mpr hdisplacement
    · exact
        (equalCharacteristicLubinTatePrimitivePointInteger_adjoin_eq_top
          F n).symm.le
          (show z ∈
              (⊤ : Subalgebra
                (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring
                (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring) from
            by simp)

/-- Elementwise lower-ramification form: if a nonidentity
automorphism first differs from the identity unit parameter in degree `k`,
then it belongs to the natural lower group `G_i` exactly when
`i + 1 ≤ q^k`. -/
theorem
    mem_equalCharacteristicLubinTateRealLowerRamificationGroup_nat_iff_parameterPower_of_ne_one
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n i : ℕ)
    (sigma : Gal((equalCharacteristicLubinTateLevelField F n)/F.residueField⸨X⸩))
    (a : equalCharacteristicLubinTateUnitParameter F n)
    (ha :
      sigma (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
        equalCharacteristicLubinTateLevelBracket F n (n + 1)
          (equalCharacteristicLubinTateUnitParameterSeries F n a)
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen)
    (hsigma : sigma ≠ 1) :
    sigma ∈ equalCharacteristicLubinTateRealLowerRamificationGroup
        F n (i : ℝ) ↔
      ((i + 1 : ℕ) : ℕ∞) ≤
        (Nat.card F.residueField ^
          (equalCharacteristicLubinTateUnitParameterSeries F n a - 1).order.toNat :
            ℕ) := by
  rw [
    mem_equalCharacteristicLubinTateRealLowerRamificationGroup_nat_iff_primitivePoint]
  rw [
    equalCharacteristicLubinTatePrimitivePointInteger_displacement_addVal_of_ne_one
      F n sigma a ha hsigma]

/-- The explicit finite unit-parameter bijection with the Galois group of the
chosen equal-characteristic Lubin--Tate level. -/
noncomputable def equalCharacteristicLubinTateUnitParameterEquivGal
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateUnitParameter F n ≃
      Gal((equalCharacteristicLubinTateLevelField F n)/LaurentSeries F.residueField) :=
  Equiv.ofBijective
    (equalCharacteristicLubinTateUnitParameterToGal F n)
    ⟨equalCharacteristicLubinTateUnitParameterToGal_injective F n,
      equalCharacteristicLubinTateUnitParameterToGal_surjective F n⟩

@[simp]
theorem equalCharacteristicLubinTateUnitParameterEquivGal_apply
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : equalCharacteristicLubinTateUnitParameter F n) :
    equalCharacteristicLubinTateUnitParameterEquivGal F n a =
      equalCharacteristicLubinTateUnitParameterToGal F n a :=
  rfl

/-- For the automorphism attached to a finite unit parameter, membership in a
natural lower group is the parameter-power inequality, with the identity case
included explicitly and no side hypotheses. -/
theorem mem_equalCharacteristicLubinTateRealLowerRamificationGroup_nat_iff_parameterPower
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n i : ℕ)
    (a : equalCharacteristicLubinTateUnitParameter F n) :
    equalCharacteristicLubinTateUnitParameterToGal F n a ∈
        equalCharacteristicLubinTateRealLowerRamificationGroup F n (i : ℝ) ↔
      equalCharacteristicLubinTateUnitParameterToGal F n a = 1 ∨
        ((i + 1 : ℕ) : ℕ∞) ≤
          (Nat.card F.residueField ^
            (equalCharacteristicLubinTateUnitParameterSeries F n a - 1).order.toNat :
              ℕ) := by
  let sigma :=
    equalCharacteristicLubinTateUnitParameterToGal F n a
  have ha :
      sigma (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
        equalCharacteristicLubinTateLevelBracket F n (n + 1)
          (equalCharacteristicLubinTateUnitParameterSeries F n a)
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen := by
    calc
      sigma (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
          equalCharacteristicLubinTateUnitParameterLevelRoot F n a := by
            exact equalCharacteristicLubinTateUnitParameterAlgEquiv_apply_gen F n a
      _ = equalCharacteristicLubinTateLevelBracket F n (n + 1)
          (equalCharacteristicLubinTateUnitParameterSeries F n a)
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen :=
        (equalCharacteristicLubinTateLevelBracket_gen F n a).symm
  by_cases hsigma : sigma = 1
  · constructor
    · exact fun _ => Or.inl hsigma
    · intro _
      simp [sigma, hsigma]
  · rw [
      mem_equalCharacteristicLubinTateRealLowerRamificationGroup_nat_iff_parameterPower_of_ne_one
        F n i sigma a ha hsigma]
    change _ ↔ sigma = 1 ∨ _
    exact (or_iff_right hsigma).symm

private def equalCharacteristicLubinTateOneUnitParameter
    (F : LocalField.{u, v} K) (n : ℕ) :
    equalCharacteristicLubinTateUnitParameter F n :=
  equalCharacteristicLubinTateUnitParameterOfCoefficients F n 1 (fun _ => 0)

@[simp]
private theorem equalCharacteristicLubinTateOneUnitParameterSeries
    (F : LocalField.{u, v} K) (n : ℕ) :
    equalCharacteristicLubinTateUnitParameterSeries F n
        (equalCharacteristicLubinTateOneUnitParameter F n) = 1 := by
  ext i
  cases i with
  | zero =>
      simp [equalCharacteristicLubinTateOneUnitParameter,
        equalCharacteristicLubinTateUnitParameterOfCoefficients]
  | succ i =>
      by_cases hi : i < n
      · let j : Fin n := ⟨i, hi⟩
        simpa [j, equalCharacteristicLubinTateOneUnitParameter,
            equalCharacteristicLubinTateUnitParameterOfCoefficients] using
          equalCharacteristicLubinTateUnitParameterSeries_coeff_succ
            F n (equalCharacteristicLubinTateOneUnitParameter F n) j
      · simp [equalCharacteristicLubinTateUnitParameterSeries,
          equalCharacteristicLubinTateOneUnitParameter,
          equalCharacteristicLubinTateUnitParameterOfCoefficients]

@[simp]
private theorem equalCharacteristicLubinTateOneUnitParameterToGal
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateUnitParameterToGal F n
        (equalCharacteristicLubinTateOneUnitParameter F n) = 1 := by
  let a := equalCharacteristicLubinTateOneUnitParameter F n
  let sigma := equalCharacteristicLubinTateUnitParameterToGal F n a
  have ha :
      sigma (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
        equalCharacteristicLubinTateLevelBracket F n (n + 1)
          (equalCharacteristicLubinTateUnitParameterSeries F n a)
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen := by
    calc
      sigma (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
          equalCharacteristicLubinTateUnitParameterLevelRoot F n a := by
            exact equalCharacteristicLubinTateUnitParameterAlgEquiv_apply_gen F n a
      _ = equalCharacteristicLubinTateLevelBracket F n (n + 1)
          (equalCharacteristicLubinTateUnitParameterSeries F n a)
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen :=
        (equalCharacteristicLubinTateLevelBracket_gen F n a).symm
  by_contra hsigma
  have hne :=
    equalCharacteristicLubinTateUnitParameterSeries_sub_one_ne_zero_of_sigma_ne_one
      F n sigma a ha hsigma
  apply hne
  simp [a, equalCharacteristicLubinTateOneUnitParameterSeries]

private theorem equalCharacteristicLubinTateUnitParameterToGal_eq_one_iff
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ)
    (a : equalCharacteristicLubinTateUnitParameter F n) :
    equalCharacteristicLubinTateUnitParameterToGal F n a = 1 ↔
      a = equalCharacteristicLubinTateOneUnitParameter F n := by
  constructor
  · intro ha
    apply equalCharacteristicLubinTateUnitParameterToGal_injective F n
    rw [ha, equalCharacteristicLubinTateOneUnitParameterToGal]
  · rintro rfl
    exact equalCharacteristicLubinTateOneUnitParameterToGal F n

@[simp]
private theorem equalCharacteristicLubinTateUnitParameterSeries_sub_one_eq_zero_iff
    (F : LocalField.{u, v} K)
    (n : ℕ)
    (a : equalCharacteristicLubinTateUnitParameter F n) :
    equalCharacteristicLubinTateUnitParameterSeries F n a - 1 = 0 ↔
      a = equalCharacteristicLubinTateOneUnitParameter F n := by
  constructor
  · intro ha
    have hseries :
        equalCharacteristicLubinTateUnitParameterSeries F n a = 1 :=
      sub_eq_zero.mp ha
    apply equalCharacteristicLubinTateUnitParameter_eq_of_coeff_eq F n
    intro i hi
    rw [hseries, equalCharacteristicLubinTateOneUnitParameterSeries]
  · rintro rfl
    rw [equalCharacteristicLubinTateOneUnitParameterSeries, sub_self]

/-- At the lower endpoint `q^k - 1`, membership is equivalent to vanishing of
the first `k` coefficients of the visible difference from the identity. -/
theorem mem_equalCharacteristicLubinTateRealLowerRamificationGroup_pow_sub_one_iff_coeff_zero
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n k : ℕ)
    (a : equalCharacteristicLubinTateUnitParameter F n) :
    equalCharacteristicLubinTateUnitParameterToGal F n a ∈
        equalCharacteristicLubinTateRealLowerRamificationGroup F n
          ((Nat.card F.residueField ^ k - 1 : ℕ) : ℝ) ↔
      ∀ j < k,
        PowerSeries.coeff j
            (equalCharacteristicLubinTateUnitParameterSeries F n a - 1) = 0 := by
  let q := Nat.card F.residueField
  let u := equalCharacteristicLubinTateUnitParameterSeries F n a - 1
  have hqone : 1 < q :=
    (Finite.one_lt_card : 1 < Nat.card F.residueField)
  have hqpos : 0 < q := Nat.zero_lt_one.trans hqone
  have hqpow : 1 ≤ q ^ k := by
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (Nat.ne_of_gt hqpos))
  rw [
    mem_equalCharacteristicLubinTateRealLowerRamificationGroup_nat_iff_parameterPower,
    Nat.sub_add_cancel hqpow]
  change
    equalCharacteristicLubinTateUnitParameterToGal F n a = 1 ∨
        ((q ^ k : ℕ) : ℕ∞) ≤ ((q ^ u.order.toNat : ℕ) : ℕ∞) ↔
      ∀ j < k, PowerSeries.coeff j u = 0
  constructor
  · rintro (hsigma | hpow)
    · have ha :
          a = equalCharacteristicLubinTateOneUnitParameter F n :=
        (equalCharacteristicLubinTateUnitParameterToGal_eq_one_iff
          F n a).mp hsigma
      subst a
      simp [u, equalCharacteristicLubinTateOneUnitParameterSeries]
    · intro j hj
      have hpowNat : q ^ k ≤ q ^ u.order.toNat := by
        exact_mod_cast hpow
      have hkorder : k ≤ u.order.toNat := by
        by_contra hk
        have horderlt : u.order.toNat < k := Nat.lt_of_not_ge hk
        have hp :=
          Nat.pow_lt_pow_right hqone horderlt
        omega
      exact
        PowerSeries.coeff_of_lt_order_toNat j
          (lt_of_lt_of_le hj hkorder)
  · intro hcoeff
    by_cases ha :
        a = equalCharacteristicLubinTateOneUnitParameter F n
    · left
      exact
        (equalCharacteristicLubinTateUnitParameterToGal_eq_one_iff
          F n a).mpr ha
    · right
      have hu : u ≠ 0 := by
        intro hu
        apply ha
        exact
          (equalCharacteristicLubinTateUnitParameterSeries_sub_one_eq_zero_iff
            F n a).mp hu
      have horder : (k : ℕ∞) ≤ u.order :=
        PowerSeries.nat_le_order u k hcoeff
      have hordertop : u.order ≠ ⊤ := by
        intro htop
        exact hu (PowerSeries.order_eq_top.mp htop)
      have hcoe : ((u.order.toNat : ℕ) : ℕ∞) = u.order :=
        ENat.natCast_toNat hordertop
      have hkorder : k ≤ u.order.toNat := by
        rw [← hcoe] at horder
        exact_mod_cast horder
      have hpowNat : q ^ k ≤ q ^ u.order.toNat :=
        Nat.pow_le_pow_right hqpos hkorder
      exact_mod_cast hpowNat

private def equalCharacteristicLubinTateUnitParameterVanishesBefore
    (F : LocalField.{u, v} K) (n k : ℕ)
    (a : equalCharacteristicLubinTateUnitParameter F n) : Prop :=
  a.constantUnit = 1 ∧
    ∀ i : Fin n, i.val + 1 < k → a.higherCoeff i = 0

private theorem equalCharacteristicLubinTateUnitParameter_coeff_zero_iff_vanishesBefore
    (F : LocalField.{u, v} K)
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1)
    (a : equalCharacteristicLubinTateUnitParameter F n) :
    (∀ j < k,
        PowerSeries.coeff j
            (equalCharacteristicLubinTateUnitParameterSeries F n a - 1) = 0) ↔
      equalCharacteristicLubinTateUnitParameterVanishesBefore
        F n k a := by
  constructor
  · intro hcoeff
    constructor
    · apply Units.ext
      have hzero := hcoeff 0 hk
      rw [map_sub] at hzero
      have hconstant :
          (a.constantUnit : F.residueField) = 1 := by
        simpa only [
          equalCharacteristicLubinTateUnitParameterSeries_coeff_zero,
          PowerSeries.coeff_one, ite_eq_left] using sub_eq_zero.mp hzero
      exact hconstant
    · intro i hi
      have hcoeffi := hcoeff (i.val + 1) hi
      rw [map_sub,
        equalCharacteristicLubinTateUnitParameterSeries_coeff_succ,
        PowerSeries.coeff_one, ite_eq_right (Nat.succ_ne_zero i.val)] at hcoeffi
      simpa using hcoeffi
  · rintro ⟨hconstant, hhigher⟩ j hj
    cases j with
    | zero =>
        rw [map_sub,
          equalCharacteristicLubinTateUnitParameterSeries_coeff_zero,
          PowerSeries.coeff_one, ite_eq_left rfl, hconstant]
        simp
    | succ j =>
        have hjn : j < n := by omega
        let i : Fin n := ⟨j, hjn⟩
        have hi : i.val + 1 < k := by simpa [i] using hj
        have hz := hhigher i hi
        rw [map_sub]
        change
          PowerSeries.coeff (i.val + 1)
              (equalCharacteristicLubinTateUnitParameterSeries F n a) -
            PowerSeries.coeff (i.val + 1) 1 = 0
        rw [equalCharacteristicLubinTateUnitParameterSeries_coeff_succ,
          PowerSeries.coeff_one, ite_eq_right (Nat.succ_ne_zero j)]
        simpa [i] using hz

private def equalCharacteristicLubinTateTailIndex
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1)
    (j : Fin (n + 1 - k)) : Fin n :=
  ⟨k - 1 + j.val, by omega⟩

private def equalCharacteristicLubinTateTailOffset
    (n k : ℕ) (_hk : 1 ≤ k) (hkn : k ≤ n + 1)
    (i : Fin n) (hi : k ≤ i.val + 1) : Fin (n + 1 - k) :=
  ⟨i.val + 1 - k, by omega⟩

private theorem equalCharacteristicLubinTateTailIndex_offset
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1)
    (i : Fin n) (hi : k ≤ i.val + 1) :
    equalCharacteristicLubinTateTailIndex n k hk hkn
        (equalCharacteristicLubinTateTailOffset n k hk hkn i hi) = i := by
  apply Fin.ext
  simp [equalCharacteristicLubinTateTailIndex,
    equalCharacteristicLubinTateTailOffset]
  omega

private theorem equalCharacteristicLubinTateTailOffset_index
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1)
    (j : Fin (n + 1 - k)) :
    equalCharacteristicLubinTateTailOffset n k hk hkn
        (equalCharacteristicLubinTateTailIndex n k hk hkn j)
        (by
          simp [equalCharacteristicLubinTateTailIndex]
          omega) = j := by
  apply Fin.ext
  simp [equalCharacteristicLubinTateTailIndex,
    equalCharacteristicLubinTateTailOffset]
  omega

private def equalCharacteristicLubinTateUnitParameterVanishesBeforeEquiv
    (F : LocalField.{u, v} K)
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    {a : equalCharacteristicLubinTateUnitParameter F n //
      equalCharacteristicLubinTateUnitParameterVanishesBefore
        F n k a} ≃
      (Fin (n + 1 - k) → F.residueField) where
  toFun a j :=
    a.1.higherCoeff
      (equalCharacteristicLubinTateTailIndex n k hk hkn j)
  invFun g :=
    ⟨equalCharacteristicLubinTateUnitParameterOfCoefficients F n 1
        (fun i =>
          if hi : k ≤ i.val + 1 then
            g (equalCharacteristicLubinTateTailOffset
              n k hk hkn i hi)
          else 0),
      by
        constructor
        · rfl
        · intro i hi
          simp [equalCharacteristicLubinTateUnitParameterOfCoefficients,
            not_le.mpr hi]⟩
  left_inv a := by
    apply Subtype.ext
    apply equalCharacteristicLubinTateUnitParameter_ext F n
    · change 1 = a.1.constantUnit
      exact a.2.1.symm
    · funext i
      by_cases hi : k ≤ i.val + 1
      · change
          (if h : k ≤ i.val + 1 then
              a.1.higherCoeff
                (equalCharacteristicLubinTateTailIndex n k hk hkn
                  (equalCharacteristicLubinTateTailOffset
                    n k hk hkn i h))
            else 0) =
            a.1.higherCoeff i
        rw [dite_eq_left hi,
          equalCharacteristicLubinTateTailIndex_offset
            n k hk hkn i]
      · change
          (if h : k ≤ i.val + 1 then
              a.1.higherCoeff
                (equalCharacteristicLubinTateTailIndex n k hk hkn
                  (equalCharacteristicLubinTateTailOffset
                    n k hk hkn i h))
            else 0) =
            a.1.higherCoeff i
        rw [dite_eq_right hi]
        exact (a.2.2 i (Nat.lt_of_not_ge hi)).symm
  right_inv g := by
    funext j
    change
      (if hi :
          k ≤
            (equalCharacteristicLubinTateTailIndex
              n k hk hkn j).val + 1 then
          g (equalCharacteristicLubinTateTailOffset n k hk hkn
            (equalCharacteristicLubinTateTailIndex
              n k hk hkn j) hi)
        else 0) = g j
    have hi :
        k ≤
          (equalCharacteristicLubinTateTailIndex
            n k hk hkn j).val + 1 := by
      simp [equalCharacteristicLubinTateTailIndex]
      omega
    rw [dite_eq_left hi,
      equalCharacteristicLubinTateTailOffset_index n k hk hkn j]

private theorem equalCharacteristicLubinTateUnitParameterVanishesBefore_natCard
    (F : LocalField.{u, v} K)
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    Nat.card
        {a : equalCharacteristicLubinTateUnitParameter F n //
          equalCharacteristicLubinTateUnitParameterVanishesBefore
            F n k a} =
      Nat.card F.residueField ^ (n + 1 - k) := by
  rw [Nat.card_congr
      (equalCharacteristicLubinTateUnitParameterVanishesBeforeEquiv
        F n k hk hkn),
    Nat.card_fun, Nat.card_fin]

private noncomputable def
    equalCharacteristicLubinTateRealLowerRamificationGroupEquivVanishesBefore
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    equalCharacteristicLubinTateRealLowerRamificationGroup F n
        ((Nat.card F.residueField ^ k - 1 : ℕ) : ℝ) ≃
      {a : equalCharacteristicLubinTateUnitParameter F n //
        equalCharacteristicLubinTateUnitParameterVanishesBefore
          F n k a} where
  toFun sigma := by
    let e := equalCharacteristicLubinTateUnitParameterEquivGal F n
    let a := e.symm sigma.1
    refine ⟨a, ?_⟩
    apply
      (equalCharacteristicLubinTateUnitParameter_coeff_zero_iff_vanishesBefore
        F n k hk hkn a).mp
    apply
      (mem_equalCharacteristicLubinTateRealLowerRamificationGroup_pow_sub_one_iff_coeff_zero
        F n k a).mp
    change e (e.symm sigma.1) ∈
      equalCharacteristicLubinTateRealLowerRamificationGroup F n
        ((Nat.card F.residueField ^ k - 1 : ℕ) : ℝ)
    simpa using sigma.2
  invFun a := by
    let e := equalCharacteristicLubinTateUnitParameterEquivGal F n
    refine ⟨e a.1, ?_⟩
    change equalCharacteristicLubinTateUnitParameterToGal F n a.1 ∈
      equalCharacteristicLubinTateRealLowerRamificationGroup F n
        ((Nat.card F.residueField ^ k - 1 : ℕ) : ℝ)
    apply
      (mem_equalCharacteristicLubinTateRealLowerRamificationGroup_pow_sub_one_iff_coeff_zero
        F n k a.1).mpr
    exact
      (equalCharacteristicLubinTateUnitParameter_coeff_zero_iff_vanishesBefore
        F n k hk hkn a.1).mpr a.2
  left_inv sigma := by
    apply Subtype.ext
    exact
      (equalCharacteristicLubinTateUnitParameterEquivGal F n).apply_symm_apply
        sigma.1
  right_inv a := by
    apply Subtype.ext
    exact
      (equalCharacteristicLubinTateUnitParameterEquivGal F n).symm_apply_apply
        a.1

/-- For `1 ≤ k ≤ n + 1`, the lower group at `q^k - 1` has order
`q^(n + 1 - k)`. -/
theorem equalCharacteristicLubinTateRealLowerRamificationGroup_natCard_pow_sub_one
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    Nat.card
        (equalCharacteristicLubinTateRealLowerRamificationGroup F n
          ((Nat.card F.residueField ^ k - 1 : ℕ) : ℝ)) =
      Nat.card F.residueField ^ (n + 1 - k) := by
  rw [Nat.card_congr
      (equalCharacteristicLubinTateRealLowerRamificationGroupEquivVanishesBefore
        F n k hk hkn),
    equalCharacteristicLubinTateUnitParameterVanishesBefore_natCard
      F n k hk hkn]

/-- On the whole interval `q^(k-1) ≤ r < q^k`, lower-group membership is
controlled by the same first-`k` coefficient condition. -/
theorem
  mem_equalCharacteristicLubinTateRealLowerRamificationGroup_nat_iff_coeff_zero_of_pow_interval
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n k r : ℕ) (hk : 1 ≤ k)
    (hlow : Nat.card F.residueField ^ (k - 1) ≤ r)
    (hhigh : r < Nat.card F.residueField ^ k)
    (a : equalCharacteristicLubinTateUnitParameter F n) :
    equalCharacteristicLubinTateUnitParameterToGal F n a ∈
        equalCharacteristicLubinTateRealLowerRamificationGroup F n (r : ℝ) ↔
      ∀ j < k,
        PowerSeries.coeff j
            (equalCharacteristicLubinTateUnitParameterSeries F n a - 1) = 0 := by
  let q := Nat.card F.residueField
  let u := equalCharacteristicLubinTateUnitParameterSeries F n a - 1
  have hqone : 1 < q :=
    (Finite.one_lt_card : 1 < Nat.card F.residueField)
  have hqpos : 0 < q := Nat.zero_lt_one.trans hqone
  change q ^ (k - 1) ≤ r at hlow
  change r < q ^ k at hhigh
  rw [
    mem_equalCharacteristicLubinTateRealLowerRamificationGroup_nat_iff_parameterPower]
  change
    equalCharacteristicLubinTateUnitParameterToGal F n a = 1 ∨
        (((r + 1 : ℕ) : ℕ∞) ≤ ((q ^ u.order.toNat : ℕ) : ℕ∞)) ↔
      ∀ j < k, PowerSeries.coeff j u = 0
  constructor
  · rintro (hsigma | hpow)
    · have ha :
          a = equalCharacteristicLubinTateOneUnitParameter F n :=
        (equalCharacteristicLubinTateUnitParameterToGal_eq_one_iff
          F n a).mp hsigma
      subst a
      simp [u, equalCharacteristicLubinTateOneUnitParameterSeries]
    · intro j hj
      have hpowNat : r + 1 ≤ q ^ u.order.toNat := by
        exact_mod_cast hpow
      have hlower : q ^ (k - 1) < q ^ u.order.toNat :=
        lt_of_le_of_lt hlow (lt_of_lt_of_le (Nat.lt_succ_self r) hpowNat)
      have hkorder : k ≤ u.order.toNat := by
        have hpred : k - 1 < u.order.toNat := by
          by_contra hnot
          have horder : u.order.toNat ≤ k - 1 :=
            Nat.le_of_not_gt hnot
          have hp :=
            Nat.pow_le_pow_right hqpos horder
          omega
        omega
      exact
        PowerSeries.coeff_of_lt_order_toNat j
          (lt_of_lt_of_le hj hkorder)
  · intro hcoeff
    by_cases ha :
        a = equalCharacteristicLubinTateOneUnitParameter F n
    · left
      exact
        (equalCharacteristicLubinTateUnitParameterToGal_eq_one_iff
          F n a).mpr ha
    · right
      have hu : u ≠ 0 := by
        intro hu
        apply ha
        exact
          (equalCharacteristicLubinTateUnitParameterSeries_sub_one_eq_zero_iff
            F n a).mp hu
      have horder : (k : ℕ∞) ≤ u.order :=
        PowerSeries.nat_le_order u k hcoeff
      have hordertop : u.order ≠ ⊤ := by
        intro htop
        exact hu (PowerSeries.order_eq_top.mp htop)
      have hcoe : ((u.order.toNat : ℕ) : ℕ∞) = u.order :=
        ENat.natCast_toNat hordertop
      have hkorder : k ≤ u.order.toNat := by
        rw [← hcoe] at horder
        exact_mod_cast horder
      have hpowNat : r + 1 ≤ q ^ u.order.toNat :=
        (by omega : r + 1 ≤ q ^ k).trans
          (Nat.pow_le_pow_right hqpos hkorder)
      exact_mod_cast hpowNat

/-- The lower-group order is constant on `q^(k-1) ≤ r < q^k`. -/
theorem equalCharacteristicLubinTateRealLowerRamificationGroup_natCard_of_pow_interval
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n k r : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1)
    (hlow : Nat.card F.residueField ^ (k - 1) ≤ r)
    (hhigh : r < Nat.card F.residueField ^ k) :
    Nat.card
        (equalCharacteristicLubinTateRealLowerRamificationGroup F n (r : ℝ)) =
      Nat.card F.residueField ^ (n + 1 - k) := by
  have hgroup :
      equalCharacteristicLubinTateRealLowerRamificationGroup F n (r : ℝ) =
        equalCharacteristicLubinTateRealLowerRamificationGroup F n
          ((Nat.card F.residueField ^ k - 1 : ℕ) : ℝ) := by
    ext sigma
    let e := equalCharacteristicLubinTateUnitParameterEquivGal F n
    let a := e.symm sigma
    have hsigma : e a = sigma := e.apply_symm_apply sigma
    rw [← hsigma]
    change
      equalCharacteristicLubinTateUnitParameterToGal F n a ∈
          equalCharacteristicLubinTateRealLowerRamificationGroup F n (r : ℝ) ↔
        equalCharacteristicLubinTateUnitParameterToGal F n a ∈
          equalCharacteristicLubinTateRealLowerRamificationGroup F n
            ((Nat.card F.residueField ^ k - 1 : ℕ) : ℝ)
    rw [
      mem_equalCharacteristicLubinTateRealLowerRamificationGroup_nat_iff_coeff_zero_of_pow_interval
        F n k r hk hlow hhigh a,
      mem_equalCharacteristicLubinTateRealLowerRamificationGroup_pow_sub_one_iff_coeff_zero]
  rw [hgroup,
    equalCharacteristicLubinTateRealLowerRamificationGroup_natCard_pow_sub_one
      F n k hk hkn]


end ChosenRamificationTarget

end LubinTate

end
