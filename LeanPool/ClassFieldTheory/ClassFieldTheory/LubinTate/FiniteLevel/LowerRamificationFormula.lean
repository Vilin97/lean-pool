/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveDisplacement
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.GaloisParameterFiltration
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LowerRamification
/-!
# Explicit lower ramification groups of finite Lubin--Tate levels

The displacement formula for a primitive Lubin--Tate point identifies the
lower ramification filtration with the principal-unit filtration transported
to the finite-level Galois group.  At the break `q ^ k - 1`, and throughout
the interval `q ^ (k - 1) ≤ r < q ^ k`, the group is the image of `U_F^k`.
Its cardinality is therefore `q ^ (n + 1 - k)`.
-/

@[expose] public section

noncomputable
section

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The primitive-point displacement threshold for a finite parameter is
equivalent to membership in the corresponding finite principal-unit
subgroup. -/
theorem
    standardLubinTateUnitParameterToGal_displacement_addVal_ge_iff_mem_parameterSubgroup
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : standardLubinTateUnitParameter F n) (k : ℕ)
    (hkn : k ≤ n + 1) :
    ((Nat.card F.residueField ^ k : ℕ) : ℕ∞) ≤
        IsDiscreteValuationRing.addVal
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
          (valuationSubringAutOfUniqueExtension
              (standardLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
                hπ n)
              (standardLubinTateUnitParameterToGal F hπ n a)
              (standardLubinTatePrimitivePointInteger hπ n) -
            standardLubinTatePrimitivePointInteger hπ n) ↔
      a ∈ standardLubinTateUnitParameterSubgroup F n k := by
  rw [
    standardLubinTateUnitParameterToGal_displacement_addVal_ge_iff_chosenRepresentative_mem
      F hπ n a k hkn]
  simpa only [standardLubinTateUnitParameterChosenRepresentative_spec] using
    (standardLubinTateUnitParameterClass_mem_subgroup_iff
      F n k hkn
      (standardLubinTateUnitParameterChosenRepresentative F n a)).symm

/-- At the lower break `q ^ k - 1`, the real lower ramification group is the
Galois image of the `k`-th finite principal-unit subgroup. -/
theorem
    standardLubinTateRealLowerRamificationGroup_pow_sub_one_eq_galoisParameterSubgroup
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    standardLubinTateRealLowerRamificationGroup hπ n
        ((Nat.card F.residueField ^ k - 1 : ℕ) : ℝ) =
      standardLubinTateGaloisParameterSubgroup F hπ n k := by
  ext σ
  obtain ⟨a, rfl⟩ :=
    standardLubinTateUnitParameterToGal_surjective F hπ n σ
  have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hqpow : 1 ≤ Nat.card F.residueField ^ k :=
    (Nat.one_lt_pow hkpos.ne'
      (Finite.one_lt_card : 1 < Nat.card F.residueField)).le
  rw [mem_standardLubinTateRealLowerRamificationGroup_nat_iff_primitivePoint,
    Nat.sub_add_cancel hqpow,
    standardLubinTateUnitParameterToGal_displacement_addVal_ge_iff_mem_parameterSubgroup
      F hπ n a k hkn,
    standardLubinTateUnitParameterToGal_mem_galoisParameterSubgroup_iff]

/-- The lower ramification group at `q ^ k - 1` has order
`q ^ (n + 1 - k)`. -/
theorem standardLubinTateRealLowerRamificationGroup_pow_sub_one_natCard
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    Nat.card
        (standardLubinTateRealLowerRamificationGroup hπ n
          ((Nat.card F.residueField ^ k - 1 : ℕ) : ℝ)) =
      Nat.card F.residueField ^ (n + 1 - k) := by
  rw [
    standardLubinTateRealLowerRamificationGroup_pow_sub_one_eq_galoisParameterSubgroup
      F hπ n k hk hkn,
    standardLubinTateGaloisParameterSubgroup_natCard F hπ n k hk hkn]

/-- On a full power interval, the primitive-point displacement threshold for
a finite parameter is equivalent to membership in the `k`-th finite
principal-unit subgroup. -/
theorem
    standardLubinTateUnitParameterToGal_interval_displacement_iff_mem_parameterSubgroup
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : standardLubinTateUnitParameter F n) (k r : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ n + 1)
    (hlower : Nat.card F.residueField ^ (k - 1) ≤ r)
    (hupper : r < Nat.card F.residueField ^ k) :
    (((r + 1 : ℕ) : ℕ∞) ≤
        IsDiscreteValuationRing.addVal
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
          (valuationSubringAutOfUniqueExtension
              (standardLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
                hπ n)
              (standardLubinTateUnitParameterToGal F hπ n a)
              (standardLubinTatePrimitivePointInteger hπ n) -
            standardLubinTatePrimitivePointInteger hπ n)) ↔
      a ∈ standardLubinTateUnitParameterSubgroup F n k := by
  rw [standardLubinTateUnitParameterToGal_apply_primitivePointInteger]
  rw [
    standardLubinTatePrimitivePointIntegerAction_sub_self_addVal_ge_iff_mem_of_pow_interval
      hπ n (standardLubinTateUnitParameterChosenRepresentative F n a)
      k r hk hkn hlower hupper]
  simpa only [standardLubinTateUnitParameterChosenRepresentative_spec] using
    (standardLubinTateUnitParameterClass_mem_subgroup_iff
      F n k hkn
      (standardLubinTateUnitParameterChosenRepresentative F n a)).symm

/-- Throughout `q ^ (k - 1) ≤ r < q ^ k`, the real lower ramification group
is the Galois image of the `k`-th finite principal-unit subgroup. -/
theorem
    standardLubinTateRealLowerRamificationGroup_eq_galoisParameterSubgroup_of_pow_interval
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n k r : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1)
    (hlower : Nat.card F.residueField ^ (k - 1) ≤ r)
    (hupper : r < Nat.card F.residueField ^ k) :
    standardLubinTateRealLowerRamificationGroup hπ n (r : ℝ) =
      standardLubinTateGaloisParameterSubgroup F hπ n k := by
  ext σ
  obtain ⟨a, rfl⟩ :=
    standardLubinTateUnitParameterToGal_surjective F hπ n σ
  rw [mem_standardLubinTateRealLowerRamificationGroup_nat_iff_primitivePoint,
    standardLubinTateUnitParameterToGal_interval_displacement_iff_mem_parameterSubgroup
      F hπ n a k r hk hkn hlower hupper,
    standardLubinTateUnitParameterToGal_mem_galoisParameterSubgroup_iff]

/-- Throughout a full power interval, the real lower ramification group has
order `q ^ (n + 1 - k)`. -/
theorem
    standardLubinTateRealLowerRamificationGroup_natCard_of_pow_interval
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n k r : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1)
    (hlower : Nat.card F.residueField ^ (k - 1) ≤ r)
    (hupper : r < Nat.card F.residueField ^ k) :
    Nat.card
        (standardLubinTateRealLowerRamificationGroup hπ n (r : ℝ)) =
      Nat.card F.residueField ^ (n + 1 - k) := by
  rw [
    standardLubinTateRealLowerRamificationGroup_eq_galoisParameterSubgroup_of_pow_interval
      F hπ n k r hk hkn hlower hupper,
    standardLubinTateGaloisParameterSubgroup_natCard F hπ n k hk hkn]

end LubinTate

end
