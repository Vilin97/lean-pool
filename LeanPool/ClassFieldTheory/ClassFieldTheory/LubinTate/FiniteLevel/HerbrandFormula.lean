/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LowerRamificationFormula
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.UpperRamification
/-!
# Herbrand formula for finite Lubin--Tate levels

The explicit lower ramification groups determine the slopes of the Herbrand
function.  Summing those slopes sends the lower breaks `q ^ k - 1` to the
integral upper breaks `k`.  Consequently the upper ramification group at `k`
is the Galois image of the `k`-th principal-unit subgroup and has order
`q ^ (n + 1 - k)`.
-/

@[expose] public section

noncomputable
section

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open RamificationTheory.DiscreteValuationField
open RamificationTheory.HilbertRamification.Higher

variable {K : Type u} [Field K]

noncomputable local instance
    standardLubinTateLevelField_finiteDimensional_forHerbrandFormula
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    FiniteDimensional K (standardLubinTateLevelField hπ n) :=
  standardLubinTateLevelField_finiteDimensional hπ n

noncomputable local instance
    standardLubinTateLevelField_isGalois_forHerbrandFormula
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    IsGalois K (standardLubinTateLevelField hπ n) :=
  standardLubinTateLevelField_isGalois hπ n

private theorem standardLubinTateUnitParameterSubgroup_zero_eq_top
    (F : LocalField.{u, v} K) (n : ℕ) :
    standardLubinTateUnitParameterSubgroup F n 0 = ⊤ := by
  apply top_unique
  intro a _ha
  rw [← standardLubinTateUnitParameterChosenRepresentative_spec F n a]
  exact
    (standardLubinTateUnitParameterClass_mem_subgroup_iff
      F n 0 (Nat.zero_le (n + 1))
      (standardLubinTateUnitParameterChosenRepresentative F n a)).2 (by
        simp)

private theorem standardLubinTateRealLowerRamificationGroup_zero_eq_top
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    standardLubinTateRealLowerRamificationGroup hπ n 0 = ⊤ := by
  ext σ
  obtain ⟨a, rfl⟩ :=
    standardLubinTateUnitParameterToGal_surjective F hπ n σ
  rw [show (0 : ℝ) = ((0 : ℕ) : ℝ) by norm_num]
  rw [mem_standardLubinTateRealLowerRamificationGroup_nat_iff_primitivePoint]
  simpa [standardLubinTateUnitParameterSubgroup_zero_eq_top] using
    (standardLubinTateUnitParameterToGal_displacement_addVal_ge_iff_mem_parameterSubgroup
      F hπ n a 0 (Nat.zero_le (n + 1)))

private theorem standardLubinTateRealLowerRamificationGroup_zero_natCard
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    Nat.card (standardLubinTateRealLowerRamificationGroup hπ n 0) =
      (Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n := by
  rw [standardLubinTateRealLowerRamificationGroup_zero_eq_top F hπ n,
    Subgroup.card_top,
    standardLubinTateLevelField_natCard_gal (F := F) hπ n,
    standardLubinTateLevelField_finrank (F := F) hπ n]

/-- On a lower-numbering power interval, the Herbrand slope is the ratio of
the corresponding lower-group order to the inertia-group order. -/
theorem standardLubinTateHerbrandSlope_eq_of_pow_interval
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n k i : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1)
    (hlow : Nat.card F.residueField ^ (k - 1) ≤ i + 1)
    (hhigh : i + 1 < Nat.card F.residueField ^ k) :
    AntitoneNormalSubgroupFiltration.herbrandSlope
        (standardLubinTateLowerRamificationFiltration hπ n) i =
      (Nat.card F.residueField ^ (n + 1 - k) : ℕ) /
        ((Nat.card F.residueField - 1) *
          Nat.card F.residueField ^ n : ℕ) := by
  rw [AntitoneNormalSubgroupFiltration.herbrandSlope]
  change
    (Nat.card
        (standardLubinTateRealLowerRamificationGroup hπ n
          ((i + 1 : ℕ) : ℝ)) : ℝ) /
        Nat.card
          (standardLubinTateRealLowerRamificationGroup hπ n
            ((0 : ℕ) : ℝ)) =
      _
  rw [standardLubinTateRealLowerRamificationGroup_natCard_of_pow_interval
      F hπ n k (i + 1) hk hkn hlow hhigh,
    show
      Nat.card
          (standardLubinTateRealLowerRamificationGroup hπ n
            ((0 : ℕ) : ℝ)) =
        (Nat.card F.residueField - 1) *
          Nat.card F.residueField ^ n by
      simpa only [Nat.cast_zero] using
        standardLubinTateRealLowerRamificationGroup_zero_natCard F hπ n]

private theorem standardLubinTateHerbrandValueNat_pow_sub_one
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n k : ℕ) (hkn : k ≤ n + 1) :
    AntitoneNormalSubgroupFiltration.herbrandValueNat
        (standardLubinTateLowerRamificationFiltration hπ n)
        (Nat.card F.residueField ^ k - 1) =
      (k : ℝ) := by
  let q := Nat.card F.residueField
  let filtration :=
    standardLubinTateLowerRamificationFiltration hπ n
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
            AntitoneNormalSubgroupFiltration.herbrandSlope
                filtration (a + x) =
              (q ^ (n + 1 - (k + 1)) : ℕ) /
                ((q - 1) * q ^ n : ℕ) := by
        intro x hx
        apply
          standardLubinTateHerbrandSlope_eq_of_pow_interval
            F hπ n (k + 1) (a + x) (by omega) hsucc
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
              AntitoneNormalSubgroupFiltration.herbrandSlope
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
          AntitoneNormalSubgroupFiltration.herbrandSlope filtration i) =
            ((k + 1 : ℕ) : ℝ)
      rw [hdecomp, Finset.sum_range_add]
      change
        AntitoneNormalSubgroupFiltration.herbrandValueNat filtration a +
            (∑ x ∈ Finset.range b,
              AntitoneNormalSubgroupFiltration.herbrandSlope
                filtration (a + x)) =
          ((k + 1 : ℕ) : ℝ)
      rw [show a = q ^ k - 1 by rfl, ihval, htail]
      norm_num

/-- The lower endpoints `q ^ k - 1` map to the integral upper endpoints
`k`, including the endpoint `k = 0`. -/
theorem standardLubinTateHerbrandFunction_pow_sub_one
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n k : ℕ) (hkn : k ≤ n + 1) :
    standardLubinTateHerbrandFunction hπ n
        ((Nat.card F.residueField ^ k - 1 : ℕ) : ℝ) =
      (k : ℝ) := by
  change
    AntitoneNormalSubgroupFiltration.herbrandFunction
        (standardLubinTateLowerRamificationFiltration hπ n)
        ((Nat.card F.residueField ^ k - 1 : ℕ) : ℝ) =
      (k : ℝ)
  rw [AntitoneNormalSubgroupFiltration.herbrandFunction_nat]
  exact standardLubinTateHerbrandValueNat_pow_sub_one
    F hπ n k hkn

/-- At an integral upper endpoint, the inverse Herbrand function returns the
lower endpoint `q ^ k - 1`. -/
theorem standardLubinTateInverseHerbrandFunction_nat_eq_pow_sub_one
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n k : ℕ) (hkn : k ≤ n + 1) :
    standardLubinTateInverseHerbrandFunction hπ n (k : ℝ) =
      ((Nat.card F.residueField ^ k - 1 : ℕ) : ℝ) := by
  change
    inverseHerbrandFunctionOfUniqueExtension
        (standardLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
          hπ n)
        (k : ℝ) =
      ((Nat.card F.residueField ^ k - 1 : ℕ) : ℝ)
  rw [← standardLubinTateHerbrandFunction_pow_sub_one F hπ n k hkn]
  exact
    inverseHerbrandFunctionOfUniqueExtension_eta
      (standardLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
        hπ n)
      ((Nat.card F.residueField ^ k - 1 : ℕ) : ℝ)

/-- At an integral upper index, the upper group is the lower group at the
corresponding power break. -/
theorem
    standardLubinTateRealUpperRamificationGroup_nat_eq_lower_pow_sub_one
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n k : ℕ) (hkn : k ≤ n + 1) :
    standardLubinTateRealUpperRamificationGroup hπ n (k : ℝ) =
      standardLubinTateRealLowerRamificationGroup hπ n
        ((Nat.card F.residueField ^ k - 1 : ℕ) : ℝ) := by
  rw [← standardLubinTateHerbrandFunction_pow_sub_one F hπ n k hkn]
  exact
    standardLubinTateRealUpperRamificationGroup_herbrandFunction
      hπ n ((Nat.card F.residueField ^ k - 1 : ℕ) : ℝ)

/-- For `1 ≤ k ≤ n + 1`, the integral upper group is the Galois image of
the `k`-th finite principal-unit subgroup. -/
theorem
    standardLubinTateRealUpperRamificationGroup_nat_eq_galoisParameterSubgroup
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    standardLubinTateRealUpperRamificationGroup hπ n (k : ℝ) =
      standardLubinTateGaloisParameterSubgroup F hπ n k := by
  rw [
    standardLubinTateRealUpperRamificationGroup_nat_eq_lower_pow_sub_one
      F hπ n k hkn,
    standardLubinTateRealLowerRamificationGroup_pow_sub_one_eq_galoisParameterSubgroup
      F hπ n k hk hkn]

/-- For `1 ≤ k ≤ n + 1`, the integral upper group has order
`q ^ (n + 1 - k)`. -/
theorem standardLubinTateRealUpperRamificationGroup_natCard
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    Nat.card
        (standardLubinTateRealUpperRamificationGroup hπ n (k : ℝ)) =
      Nat.card F.residueField ^ (n + 1 - k) := by
  rw [
    standardLubinTateRealUpperRamificationGroup_nat_eq_galoisParameterSubgroup
      F hπ n k hk hkn,
    standardLubinTateGaloisParameterSubgroup_natCard F hπ n k hk hkn]

/-- On a lower-numbering power interval, the lower group is the group at the
right endpoint `q ^ k - 1`. -/
theorem standardLubinTateRealLowerRamificationGroup_eq_break_of_pow_interval
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n k r : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1)
    (hlow : Nat.card F.residueField ^ (k - 1) ≤ r)
    (hhigh : r < Nat.card F.residueField ^ k) :
    standardLubinTateRealLowerRamificationGroup hπ n (r : ℝ) =
      standardLubinTateRealLowerRamificationGroup hπ n
        ((Nat.card F.residueField ^ k - 1 : ℕ) : ℝ) := by
  rw [
    standardLubinTateRealLowerRamificationGroup_eq_galoisParameterSubgroup_of_pow_interval
      F hπ n k r hk hkn hlow hhigh,
    standardLubinTateRealLowerRamificationGroup_pow_sub_one_eq_galoisParameterSubgroup
      F hπ n k hk hkn]

/-- On the positive range visible at level `n + 1`, the real upper
filtration is the natural-ceiling extension of its integral values. -/
theorem standardLubinTateRealUpperRamificationGroup_eq_natCeil
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (t : ℝ)
    (hk : 1 ≤ ⌈t⌉₊) (hkn : ⌈t⌉₊ ≤ n + 1) :
    standardLubinTateRealUpperRamificationGroup hπ n t =
      standardLubinTateRealUpperRamificationGroup
        hπ n (⌈t⌉₊ : ℝ) := by
  let k : ℕ := ⌈t⌉₊
  let q : ℕ := Nat.card F.residueField
  let ψ : ℝ → ℝ :=
    standardLubinTateInverseHerbrandFunction hπ n
  have hk' : 1 ≤ k := by
    simpa only [k] using hk
  have hkn' : k ≤ n + 1 := by
    simpa only [k] using hkn
  have ht_interval : ((k - 1 : ℕ) : ℝ) < t ∧ t ≤ (k : ℝ) := by
    apply (Nat.ceil_eq_iff (by omega : k ≠ 0)).mp
    rfl
  have hψ_strict : StrictMono ψ := by
    dsimp only [ψ, standardLubinTateInverseHerbrandFunction]
    exact
      inverseHerbrandFunctionOfUniqueExtension_strictMono
        (standardLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
          hπ n)
  have hψ_endpoint :
      ∀ j : ℕ, j ≤ n + 1 →
        ψ (j : ℝ) = ((q ^ j - 1 : ℕ) : ℝ) := by
    intro j hj
    simpa only [ψ, q] using
      standardLubinTateInverseHerbrandFunction_nat_eq_pow_sub_one
        F hπ n j hj
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
    standardLubinTateRealUpperRamificationGroup hπ n t =
      standardLubinTateRealUpperRamificationGroup hπ n (k : ℝ)
  rw [
    standardLubinTateRealUpperRamificationGroup_nat_eq_lower_pow_sub_one
      F hπ n k hkn']
  change
    standardLubinTateRealLowerRamificationGroup hπ n (ψ t) =
      standardLubinTateRealLowerRamificationGroup hπ n
        ((q ^ k - 1 : ℕ) : ℝ)
  calc
    standardLubinTateRealLowerRamificationGroup hπ n (ψ t) =
        standardLubinTateRealLowerRamificationGroup
          hπ n (⌈ψ t⌉₊ : ℝ) :=
      standardLubinTateRealLowerRamificationGroup_eq_natCeil
        hπ n (ψ t) hψ_nonneg
    _ =
        standardLubinTateRealLowerRamificationGroup hπ n
          ((q ^ k - 1 : ℕ) : ℝ) :=
      standardLubinTateRealLowerRamificationGroup_eq_break_of_pow_interval
        F hπ n k ⌈ψ t⌉₊ hk' hkn' hlow hhigh

/-- On the positive visible range, the real upper group is the Galois image
at its natural-ceiling principal-unit level. -/
theorem
    standardLubinTateRealUpperRamificationGroup_eq_galoisParameterSubgroup_of_ceil
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (t : ℝ)
    (hk : 1 ≤ ⌈t⌉₊) (hkn : ⌈t⌉₊ ≤ n + 1) :
    standardLubinTateRealUpperRamificationGroup hπ n t =
      standardLubinTateGaloisParameterSubgroup F hπ n ⌈t⌉₊ := by
  rw [standardLubinTateRealUpperRamificationGroup_eq_natCeil
      F hπ n t hk hkn,
    standardLubinTateRealUpperRamificationGroup_nat_eq_galoisParameterSubgroup
      F hπ n ⌈t⌉₊ hk hkn]

/-- On the positive visible range, the real upper group has the order
prescribed by its natural-ceiling principal-unit level. -/
theorem standardLubinTateRealUpperRamificationGroup_natCard_of_ceil
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (t : ℝ)
    (hk : 1 ≤ ⌈t⌉₊) (hkn : ⌈t⌉₊ ≤ n + 1) :
    Nat.card (standardLubinTateRealUpperRamificationGroup hπ n t) =
      Nat.card F.residueField ^ (n + 1 - ⌈t⌉₊) := by
  rw [
    standardLubinTateRealUpperRamificationGroup_eq_galoisParameterSubgroup_of_ceil
      F hπ n t hk hkn,
    standardLubinTateGaloisParameterSubgroup_natCard
      F hπ n ⌈t⌉₊ hk hkn]

end LubinTate

end
