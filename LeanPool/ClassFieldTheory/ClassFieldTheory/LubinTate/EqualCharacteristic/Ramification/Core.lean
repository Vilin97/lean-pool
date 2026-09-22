/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.LowerGroups
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.GaloisAction
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.PrimitivePoint
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.DisplacementValuation
/-!
# Herbrand function and upper ramification groups of Lubin--Tate levels

The lower-group calculation is integrated here to compute the actual Herbrand
function and the resulting upper ramification groups of the chosen
equal-characteristic Lubin--Tate level.
-/

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  herbrandSlope →
    herbrandSlope


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

attribute [local instance]
  equalCharacteristicLubinTateLevelField_finiteDimensional_forLowerGroups
  equalCharacteristicLubinTateLevelField_isGalois_forLowerGroups

private theorem
    equalCharacteristicLubinTateUnitParameterToGal_mem_lowerRamificationGroup_zero
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) (a : equalCharacteristicLubinTateUnitParameter F n) :
    equalCharacteristicLubinTateUnitParameterToGal F n a ∈
      equalCharacteristicLubinTateRealLowerRamificationGroup F n 0 := by
  have hqpos :
      0 < Nat.card F.residueField :=
    Nat.zero_lt_one.trans
      (Finite.one_lt_card : 1 < Nat.card F.residueField)
  have hpow :
      1 ≤
        Nat.card F.residueField ^
          (equalCharacteristicLubinTateUnitParameterSeries F n a - 1).order.toNat :=
    Nat.one_le_iff_ne_zero.mpr
      (pow_ne_zero _ (Nat.ne_of_gt hqpos))
  have hm :
      equalCharacteristicLubinTateUnitParameterToGal F n a ∈
        equalCharacteristicLubinTateRealLowerRamificationGroup F n
          ((0 : ℕ) : ℝ) :=
    (mem_equalCharacteristicLubinTateRealLowerRamificationGroup_nat_iff_parameterPower
      F n 0 a).mpr (Or.inr (by exact_mod_cast hpow))
  simpa only [Nat.cast_zero] using hm

private noncomputable def
    equalCharacteristicLubinTateUnitParameterEquivLowerRamificationGroupZero
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateUnitParameter F n ≃
      equalCharacteristicLubinTateRealLowerRamificationGroup F n 0 where
  toFun a :=
    ⟨equalCharacteristicLubinTateUnitParameterToGal F n a,
      equalCharacteristicLubinTateUnitParameterToGal_mem_lowerRamificationGroup_zero
        F n a⟩
  invFun sigma :=
    (equalCharacteristicLubinTateUnitParameterEquivGal F n).symm sigma.1
  left_inv a :=
    (equalCharacteristicLubinTateUnitParameterEquivGal F n).symm_apply_apply a
  right_inv sigma := by
    apply Subtype.ext
    exact
      (equalCharacteristicLubinTateUnitParameterEquivGal F n).apply_symm_apply
        sigma.1

private theorem equalCharacteristicLubinTateRealLowerRamificationGroup_zero_natCard
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    Nat.card (equalCharacteristicLubinTateRealLowerRamificationGroup F n 0) =
      (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n := by
  calc
    Nat.card (equalCharacteristicLubinTateRealLowerRamificationGroup F n 0) =
        Nat.card (equalCharacteristicLubinTateUnitParameter F n) :=
      (Nat.card_congr
        (equalCharacteristicLubinTateUnitParameterEquivLowerRamificationGroupZero
          F n)).symm
    _ = (Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n :=
      equalCharacteristicLubinTateUnitParameter_natCard F n

private noncomputable def
    equalCharacteristicLubinTateLowerRamificationFiltration
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration
      Gal((equalCharacteristicLubinTateLevelField F n)/LaurentSeries F.residueField) :=
  lowerRamificationFiltrationOfUniqueExtension
    (base := (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF)
    (target := (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF)
    (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
      F n)

private theorem equalCharacteristicLubinTateHerbrandSlope_eq_of_pow_interval
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n k i : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1)
    (hlow : Nat.card F.residueField ^ (k - 1) ≤ i + 1)
    (hhigh : i + 1 < Nat.card F.residueField ^ k) :
    herbrandSlope
        (equalCharacteristicLubinTateLowerRamificationFiltration F n) i =
      (Nat.card F.residueField ^ (n + 1 - k) : ℕ) /
        ((Nat.card F.residueField - 1) *
          Nat.card F.residueField ^ n : ℕ) := by
  rw [
    herbrandSlope]
  change
    (Nat.card
        (equalCharacteristicLubinTateRealLowerRamificationGroup F n
          ((i + 1 : ℕ) : ℝ)) : ℝ) /
        Nat.card
          (equalCharacteristicLubinTateRealLowerRamificationGroup F n
            ((0 : ℕ) : ℝ)) =
      _
  rw [
    equalCharacteristicLubinTateRealLowerRamificationGroup_natCard_of_pow_interval
      F n k (i + 1) hk hkn hlow hhigh,
    show
      Nat.card
          (equalCharacteristicLubinTateRealLowerRamificationGroup F n
            ((0 : ℕ) : ℝ)) =
        (Nat.card F.residueField - 1) *
          Nat.card F.residueField ^ n by
      simpa only [Nat.cast_zero] using
        equalCharacteristicLubinTateRealLowerRamificationGroup_zero_natCard
          F n]

private theorem equalCharacteristicLubinTateHerbrandValueNat_pow_sub_one
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n k : ℕ) (hkn : k ≤ n + 1) :
    RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandValueNat
        (equalCharacteristicLubinTateLowerRamificationFiltration F n)
        (Nat.card F.residueField ^ k - 1) =
      (k : ℝ) := by
  let q := Nat.card F.residueField
  let filtration :=
    equalCharacteristicLubinTateLowerRamificationFiltration F n
  have hqone : 1 < q :=
    (Finite.one_lt_card : 1 < Nat.card F.residueField)
  have hqpos : 0 < q := Nat.zero_lt_one.trans hqone
  revert hkn
  induction k with
  | zero =>
      intro _
      simp
  | succ k ih =>
      intro hsucc
      have hkn : k ≤ n := by omega
      have ihval := ih (by omega : k ≤ n + 1)
      let a := q ^ k - 1
      let b := q ^ (k + 1) - q ^ k
      have hqpowpos : 1 ≤ q ^ k :=
        Nat.one_le_iff_ne_zero.mpr
          (pow_ne_zero _ (Nat.ne_of_gt hqpos))
      have hqpowle : q ^ k ≤ q ^ (k + 1) :=
        Nat.pow_le_pow_right hqpos (Nat.le_succ k)
      have hdecomp : q ^ (k + 1) - 1 = a + b := by
        dsimp [a, b]
        omega
      have hslope :
          ∀ x ∈ Finset.range b,
            herbrandSlope
                filtration (a + x) =
              (q ^ (n + 1 - (k + 1)) : ℕ) /
                ((q - 1) * q ^ n : ℕ) := by
        intro x hx
        apply
          equalCharacteristicLubinTateHerbrandSlope_eq_of_pow_interval
            F n (k + 1) (a + x) (by omega) hsucc
        · change q ^ k ≤ a + x + 1
          dsimp [a]
          omega
        · change a + x + 1 < q ^ (k + 1)
          have hxlt : x < b := Finset.mem_range.mp hx
          dsimp [a, b] at *
          omega
      have hb : b = (q - 1) * q ^ k := by
        dsimp [b]
        calc
          q ^ (k + 1) - q ^ k = q * q ^ k - q ^ k := by
            rw [pow_succ, Nat.mul_comm]
          _ = (q - 1) * q ^ k := by
            rw [Nat.mul_sub_right_distrib]
            simp
      have hexponent : n + 1 - (k + 1) = n - k := by omega
      have hpowSplit : q ^ n = q ^ k * q ^ (n - k) := by
        rw [← pow_add]
        congr
        omega
      have hproduct :
          b * q ^ (n + 1 - (k + 1)) = (q - 1) * q ^ n := by
        rw [hb, hexponent, hpowSplit]
        simp [Nat.mul_assoc]
      have hdenpos : 0 < (q - 1) * q ^ n :=
        Nat.mul_pos (Nat.sub_pos_of_lt hqone) (Nat.pow_pos hqpos)
      have htail :
          (∑ x ∈ Finset.range b,
              herbrandSlope
                filtration (a + x)) = 1 := by
        calc
          _ = ∑ _x ∈ Finset.range b,
                ((q ^ (n + 1 - (k + 1)) : ℕ) /
                  ((q - 1) * q ^ n : ℕ) : ℝ) := by
              apply Finset.sum_congr rfl
              intro x hx
              exact hslope x hx
          _ = (b : ℝ) *
                ((q ^ (n + 1 - (k + 1)) : ℕ) /
                  ((q - 1) * q ^ n : ℕ) : ℝ) := by
              simp
          _ = 1 := by
              rw [← mul_div_assoc, ← Nat.cast_mul, hproduct, div_self]
              exact_mod_cast (Nat.ne_of_gt hdenpos)
      change
        (∑ i ∈ Finset.range (q ^ (k + 1) - 1),
          herbrandSlope
            filtration i) = ((k + 1 : ℕ) : ℝ)
      rw [hdecomp, Finset.sum_range_add]
      change
        RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandValueNat
            filtration a +
          (∑ x ∈ Finset.range b,
            herbrandSlope
              filtration (a + x)) =
          ((k + 1 : ℕ) : ℝ)
      rw [show a = q ^ k - 1 by rfl, ihval, htail]
      norm_num

/-- The Herbrand function of the chosen equal-characteristic Lubin--Tate
level and its chosen complete discrete valuation. -/
noncomputable def equalCharacteristicLubinTateHerbrandFunction
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) (s : ℝ) : ℝ :=
  herbrandFunctionOfUniqueExtension
    (base := (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF)
    (target := (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF)
    (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
      F n)
    s

/-- The lower endpoints `q^k - 1` map to the integral upper endpoints `k`.
This also includes the harmless endpoint `k = 0`. -/
theorem equalCharacteristicLubinTateHerbrandFunction_pow_sub_one
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n k : ℕ) (hkn : k ≤ n + 1) :
    equalCharacteristicLubinTateHerbrandFunction F n
        ((Nat.card F.residueField ^ k - 1 : ℕ) : ℝ) =
      (k : ℝ) := by
  change
    RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction
        (equalCharacteristicLubinTateLowerRamificationFiltration F n)
        ((Nat.card F.residueField ^ k - 1 : ℕ) : ℝ) =
      (k : ℝ)
  rw [
    RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_nat]
  exact
    equalCharacteristicLubinTateHerbrandValueNat_pow_sub_one
      F n k hkn

/-- The actual real upper ramification group of the chosen
equal-characteristic Lubin--Tate level valuation. -/
noncomputable def equalCharacteristicLubinTateRealUpperRamificationGroup
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) (s : ℝ) :
    Subgroup Gal((equalCharacteristicLubinTateLevelField F n)/LaurentSeries F.residueField) :=
  upperRamificationGroupOfUniqueExtension
    (base := (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF)
    (target := (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF)
    (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
      F n)
    s

/-- At an integral upper index `k ≤ n + 1`, the actual upper group is the
actual lower group at `q^k - 1`. -/
theorem
    equalCharacteristicLubinTateRealUpperRamificationGroup_nat_eq_lower_pow_sub_one
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n k : ℕ) (hkn : k ≤ n + 1) :
    equalCharacteristicLubinTateRealUpperRamificationGroup F n (k : ℝ) =
      equalCharacteristicLubinTateRealLowerRamificationGroup F n
        ((Nat.card F.residueField ^ k - 1 : ℕ) : ℝ) := by
  let : FiniteDimensional (LaurentSeries F.residueField)
      (equalCharacteristicLubinTateLevelField F n) :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  change
    upperRamificationGroupOfUniqueExtension
        (base := (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF)
        (target := (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF)
        (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
          F n)
        (k : ℝ) =
      lowerRamificationGroup
        (base := (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF)
        (target := (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF)
        (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
          F n)
        ((Nat.card F.residueField ^ k - 1 : ℕ) : ℝ)
  rw [← equalCharacteristicLubinTateHerbrandFunction_pow_sub_one F n k hkn]
  exact
    upperRamificationGroupOfUniqueExtension_herbrandFunction
      (base := (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF)
      (target := (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF)
      (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
        F n)
      ((Nat.card F.residueField ^ k - 1 : ℕ) : ℝ)

/-- For `1 ≤ k ≤ n + 1`, the integral upper group has order
`q^(n + 1 - k)`. -/
theorem equalCharacteristicLubinTateRealUpperRamificationGroup_natCard
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    Nat.card
        (equalCharacteristicLubinTateRealUpperRamificationGroup
          F n (k : ℝ)) =
      Nat.card F.residueField ^ (n + 1 - k) := by
  rw [
    equalCharacteristicLubinTateRealUpperRamificationGroup_nat_eq_lower_pow_sub_one
      F n k hkn,
    equalCharacteristicLubinTateRealLowerRamificationGroup_natCard_pow_sub_one
      F n k hk hkn]

/-- Parameter membership in the integral upper group is equivalent to
vanishing of the first `k` visible coefficients. -/
theorem
    mem_equalCharacteristicLubinTateRealUpperRamificationGroup_nat_iff_coeff_zero
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n k : ℕ) (hkn : k ≤ n + 1)
    (a : equalCharacteristicLubinTateUnitParameter F n) :
    equalCharacteristicLubinTateUnitParameterToGal F n a ∈
        equalCharacteristicLubinTateRealUpperRamificationGroup
          F n (k : ℝ) ↔
      ∀ j < k,
        PowerSeries.coeff j
            (equalCharacteristicLubinTateUnitParameterSeries F n a - 1) = 0 := by
  rw [
    equalCharacteristicLubinTateRealUpperRamificationGroup_nat_eq_lower_pow_sub_one
      F n k hkn,
    mem_equalCharacteristicLubinTateRealLowerRamificationGroup_pow_sub_one_iff_coeff_zero]


end ChosenRamificationTarget

end LubinTate

end
