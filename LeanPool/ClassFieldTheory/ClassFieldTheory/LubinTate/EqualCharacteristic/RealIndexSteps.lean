/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.Core
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic
/-!
# Real-index steps for equal-characteristic Lubin--Tate levels

This file packages the ceiling behavior of the chosen real lower filtration
and the integral values of its inverse Herbrand function.  Together they show
that, on the positive range covered by an explicit finite Lubin--Tate level,
the real upper filtration is constant on the natural-ceiling steps.
-/

@[expose] public section

noncomputable section

open scoped LaurentSeries

namespace LubinTate

open LubinTate.EqualCharacteristic
open LocalFieldTheory.DiscreteValuationField
open RamificationTheory.HilbertRamification.Higher

universe v

variable {K₀ : Type} [Field K₀]

/-- Finite-dimensionality for explicit levels while forming the real-index
Herbrand functions in this module. -/
noncomputable local instance
    equalCharacteristicLubinTateLevelField_finiteDimensional_forRealIndexSteps
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
  equalCharacteristicLubinTateLevelField_finiteDimensional F n

/-- Galoisness for explicit levels while forming the real-index Herbrand
functions in this module. -/
noncomputable local instance
    equalCharacteristicLubinTateLevelField_isGalois_forRealIndexSteps
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    IsGalois F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
  equalCharacteristicLubinTateLevelField_isGalois F n

/-- At a nonnegative real lower index, the chosen equal-characteristic
Lubin--Tate lower group is the group at the natural-number ceiling. -/
theorem
    equalCharacteristicLubinTateRealLowerRamificationGroup_eq_natCeil
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    equalCharacteristicLubinTateRealLowerRamificationGroup F n s =
      equalCharacteristicLubinTateRealLowerRamificationGroup
        F n (⌈s⌉₊ : ℝ) := by
  have hexponent :
      realRamificationExponent s =
        realRamificationExponent (⌈s⌉₊ : ℝ) := by
    rw [realRamificationExponent_nat]
    unfold realRamificationExponent
    rw [Int.ceil_toNat, Nat.ceil_add_one hs]
  have hideal :
      realRamificationIdeal
          (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF s =
        realRamificationIdeal
          (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF
          (⌈s⌉₊ : ℝ) := by
    unfold realRamificationIdeal
    rw [hexponent]
  unfold equalCharacteristicLubinTateRealLowerRamificationGroup
  ext sigma
  change
    (∀ a, _ ∈
      realRamificationIdeal
        (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF s) ↔
      ∀ a, _ ∈
        realRamificationIdeal
          (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF
          (⌈s⌉₊ : ℝ)
  rw [hideal]

/-- The inverse Herbrand function attached to the chosen complete-DVF
structure on an equal-characteristic Lubin--Tate level. -/
noncomputable def equalCharacteristicLubinTateInverseHerbrandFunction
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) (t : ℝ) : ℝ :=
  inverseHerbrandFunctionOfUniqueExtension
    (base := (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF)
    (target := (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF)
    (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
      F n)
    t

/-- At every integral upper endpoint visible at level `n + 1`, the chosen
inverse Herbrand function returns the lower endpoint `q^k - 1`. -/
theorem
    equalCharacteristicLubinTateInverseHerbrandFunction_nat_eq_pow_sub_one
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n k : ℕ) (hkn : k ≤ n + 1) :
    equalCharacteristicLubinTateInverseHerbrandFunction F n (k : ℝ) =
      ((Nat.card F.residueField ^ k - 1 : ℕ) : ℝ) := by
  change
    inverseHerbrandFunctionOfUniqueExtension
        (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
          F n)
        (k : ℝ) =
      ((Nat.card F.residueField ^ k - 1 : ℕ) : ℝ)
  rw [← equalCharacteristicLubinTateHerbrandFunction_pow_sub_one F n k hkn]
  exact
    inverseHerbrandFunctionOfUniqueExtension_eta
      (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
        F n)
      ((Nat.card F.residueField ^ k - 1 : ℕ) : ℝ)

/-- On a lower-numbering power interval, the chosen lower group is the group
at the right endpoint `q^k - 1`. -/
theorem
    equalCharacteristicLubinTateRealLowerRamificationGroup_nat_eq_pow_sub_one_of_pow_interval
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n k r : ℕ) (hk : 1 ≤ k)
    (hlow : Nat.card F.residueField ^ (k - 1) ≤ r)
    (hhigh : r < Nat.card F.residueField ^ k) :
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

/-- On the positive range visible at level `n + 1`, the chosen real upper
filtration is the natural-ceiling step extension of its integral values. -/
theorem
    equalCharacteristicLubinTateRealUpperRamificationGroup_eq_natCeil
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) (t : ℝ)
    (hk : 1 ≤ ⌈t⌉₊) (hkn : ⌈t⌉₊ ≤ n + 1) :
    equalCharacteristicLubinTateRealUpperRamificationGroup F n t =
      equalCharacteristicLubinTateRealUpperRamificationGroup
        F n (⌈t⌉₊ : ℝ) := by
  let k : ℕ := ⌈t⌉₊
  let q : ℕ := Nat.card F.residueField
  let ψ : ℝ → ℝ :=
    equalCharacteristicLubinTateInverseHerbrandFunction F n
  have hk' : 1 ≤ k := by
    simpa only [k] using hk
  have hkn' : k ≤ n + 1 := by
    simpa only [k] using hkn
  have ht_interval : ((k - 1 : ℕ) : ℝ) < t ∧ t ≤ (k : ℝ) := by
    apply (Nat.ceil_eq_iff (by omega : k ≠ 0)).mp
    rfl
  have hψ_strict : StrictMono ψ := by
    dsimp only [ψ, equalCharacteristicLubinTateInverseHerbrandFunction]
    exact
      inverseHerbrandFunctionOfUniqueExtension_strictMono
        (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
          F n)
  have hψ_endpoint :
      ∀ j : ℕ, j ≤ n + 1 →
        ψ (j : ℝ) = ((q ^ j - 1 : ℕ) : ℝ) := by
    intro j hj
    simpa only [ψ, q] using
      equalCharacteristicLubinTateInverseHerbrandFunction_nat_eq_pow_sub_one
        F n j hj
  have hψ_zero : ψ 0 = 0 := by
    simpa using hψ_endpoint 0 (by omega)
  have hψ_nonneg : 0 ≤ ψ t := by
    calc
      0 = ψ 0 := hψ_zero.symm
      _ ≤ ψ t := hψ_strict.monotone (by
        exact (Nat.one_le_ceil_iff.mp hk).le)
  have hψ_lower :
      (((q ^ (k - 1) - 1 : ℕ) : ℝ)) < ψ t := by
    calc
      (((q ^ (k - 1) - 1 : ℕ) : ℝ)) =
          ψ ((k - 1 : ℕ) : ℝ) :=
        (hψ_endpoint (k - 1) (by omega)).symm
      _ < ψ t := hψ_strict ht_interval.1
  have hψ_upper :
      ψ t ≤ ((q ^ k - 1 : ℕ) : ℝ) := by
    calc
      ψ t ≤ ψ (k : ℝ) := hψ_strict.monotone ht_interval.2
      _ = ((q ^ k - 1 : ℕ) : ℝ) := hψ_endpoint k hkn'
  have hqone : 1 < q := by
    simpa only [q] using
      (Finite.one_lt_card : 1 < Nat.card F.residueField)
  have hqpos : 0 < q := Nat.zero_lt_one.trans hqone
  have hqpow_previous : 1 ≤ q ^ (k - 1) := by
    exact
      Nat.one_le_iff_ne_zero.mpr
        (pow_ne_zero _ (Nat.ne_of_gt hqpos))
  have hqpow_current : 1 ≤ q ^ k := by
    exact
      Nat.one_le_iff_ne_zero.mpr
        (pow_ne_zero _ (Nat.ne_of_gt hqpos))
  have hlow : q ^ (k - 1) ≤ ⌈ψ t⌉₊ := by
    rw [← Nat.sub_add_cancel hqpow_previous]
    exact Nat.add_one_le_ceil_iff.mpr hψ_lower
  have hceil_upper : ⌈ψ t⌉₊ ≤ q ^ k - 1 :=
    Nat.ceil_le.mpr hψ_upper
  have hhigh : ⌈ψ t⌉₊ < q ^ k := by
    omega
  change
    equalCharacteristicLubinTateRealUpperRamificationGroup F n t =
      equalCharacteristicLubinTateRealUpperRamificationGroup F n (k : ℝ)
  rw [
    equalCharacteristicLubinTateRealUpperRamificationGroup_nat_eq_lower_pow_sub_one
      F n k hkn']
  change
    equalCharacteristicLubinTateRealLowerRamificationGroup F n (ψ t) =
      equalCharacteristicLubinTateRealLowerRamificationGroup F n
        ((q ^ k - 1 : ℕ) : ℝ)
  calc
    equalCharacteristicLubinTateRealLowerRamificationGroup F n (ψ t) =
        equalCharacteristicLubinTateRealLowerRamificationGroup
          F n (⌈ψ t⌉₊ : ℝ) :=
      equalCharacteristicLubinTateRealLowerRamificationGroup_eq_natCeil
        F n (ψ t) hψ_nonneg
    _ =
        equalCharacteristicLubinTateRealLowerRamificationGroup F n
          ((q ^ k - 1 : ℕ) : ℝ) :=
      equalCharacteristicLubinTateRealLowerRamificationGroup_nat_eq_pow_sub_one_of_pow_interval
        F n k ⌈ψ t⌉₊ hk' hlow hhigh

end LubinTate
