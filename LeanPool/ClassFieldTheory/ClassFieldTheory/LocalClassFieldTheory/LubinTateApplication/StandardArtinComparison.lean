/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.Core
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.Core
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.BaseChange
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.Unramified
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidueNaturality
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.NormSubgroup
import LeanPool.ClassFieldTheory.GaloisCohomology.GroupTheory.RestrictionKernel
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelFieldTower
/-!
# Standard local Artin map on equal-characteristic Lubin--Tate levels

This file compares the principal-unit filtration transported by the standard
finite local Artin map with the actual upper ramification filtration of an
explicit equal-characteristic Lubin--Tate level.

The proof uses restriction to the lower Lubin--Tate level rather than a
pointwise comparison between the standard Artin map and the explicit
power-series action.
-/

noncomputable section

open scoped LaurentSeries ValuativeRel

universe v

namespace LocalClassFieldTheory

open RamificationTheory.LocalField
open RamificationTheory
open LubinTate

open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LubinTate.EqualCharacteristic
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

private theorem natCard_ker_eq_pow_sub_of_surjective
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (ψ : G →* H) (hψ : Function.Surjective ψ)
    (q m n : ℕ) (hmn : m ≤ n) (hq : 1 < q)
    (hcardG : Nat.card G = (q - 1) * q ^ n)
    (hcardH : Nat.card H = (q - 1) * q ^ m) :
    Nat.card ψ.ker = q ^ (n - m) := by
  have hindex : ψ.ker.index = Nat.card H := by
    rw [Subgroup.index_ker,
      ψ.range_eq_top_of_surjective hψ,
      Subgroup.card_top]
  have hcardKerMul :
      Nat.card ψ.ker * Nat.card H = Nat.card G := by
    rw [← hindex]
    exact Subgroup.card_mul_index ψ.ker
  rw [hcardH, hcardG] at hcardKerMul
  have hfactor_pos : 0 < (q - 1) * q ^ m := by
    exact Nat.mul_pos (Nat.sub_pos_of_lt hq) (Nat.pow_pos (by omega))
  have hpow : q ^ n = q ^ m * q ^ (n - m) := by
    rw [← pow_add, Nat.add_sub_of_le hmn]
  apply Nat.eq_of_mul_eq_mul_left hfactor_pos
  calc
    ((q - 1) * q ^ m) * Nat.card ψ.ker =
        Nat.card ψ.ker * ((q - 1) * q ^ m) := Nat.mul_comm _ _
    _ = (q - 1) * q ^ n := hcardKerMul
    _ = ((q - 1) * q ^ m) * q ^ (n - m) := by
      rw [hpow, Nat.mul_assoc]

variable {K₀ : Type} [Field K₀]

/-- On a tower of explicit levels `m + 1 ≤ n + 1`, the standard local Artin
image of `U^(m + 1)` is the kernel of restriction to level `m + 1`. -/
theorem
    equalCharacteristicLubinTateArtinPrincipalUnitsImage_eq_restrictKer
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    {m n : ℕ} (hmn : m ≤ n) :
    let B := F.residueField⸨X⸩
    let E := equalCharacteristicLubinTateLevelField F m
    let L := equalCharacteristicLubinTateLevelField F n
    letI : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    letI : FiniteDimensional B E :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F m
    letI : FiniteDimensional B L :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    (LocalFieldTheory.fieldPrincipalUnits B (m + 1)).map
        (abelianLocalArtinMonoidHom B L) =
      (intermediateFieldRestrictNormalHom E L
        (equalCharacteristicLubinTateLevelField_mono F hmn)).ker := by
  let B := F.residueField⸨X⸩
  let E := equalCharacteristicLubinTateLevelField F m
  let L := equalCharacteristicLubinTateLevelField F n
  let pi : Bˣ := (equalCharacteristicLaurentUniformizerUnit F)⁻¹
  let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField B :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  let : FiniteDimensional B E :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F m
  let : FiniteDimensional B L :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  let hEL : E ≤ L := equalCharacteristicLubinTateLevelField_mono F hmn
  let φ := abelianLocalArtinMonoidHom B L
  let ψ := intermediateFieldRestrictNormalHom E L hEL
  have hker :
      (ψ.comp φ).ker =
        Subgroup.zpowers pi ⊔ LocalFieldTheory.fieldPrincipalUnits B (m + 1) := by
    rw [show ψ.comp φ = abelianLocalArtinMonoidHom B E by
      exact abelianLocalArtinMonoidHom_restrict B E L hEL]
    rw [abelianLocalArtinMonoidHom_ker]
    change equalCharacteristicLubinTateNormSubgroup F m =
      Subgroup.zpowers pi ⊔ LocalFieldTheory.fieldPrincipalUnits B (m + 1)
    simpa [B, pi, LocalFieldTheory.uniformizerPrincipalSubgroup] using
      equalCharacteristicLubinTateNormSubgroup_eq_uniformizerPrincipalSubgroup
        F m
  have hZ : Subgroup.zpowers pi ≤ φ.ker := by
    rw [abelianLocalArtinMonoidHom_ker]
    change Subgroup.zpowers pi ≤
      equalCharacteristicLubinTateNormSubgroup F n
    rw [
      equalCharacteristicLubinTateNormSubgroup_eq_uniformizerPrincipalSubgroup]
    simp [B, pi, LocalFieldTheory.uniformizerPrincipalSubgroup]
  exact Subgroup.map_eq_ker_of_comp_ker_eq_sup_of_left_le_ker
    φ ψ (Subgroup.zpowers pi) (LocalFieldTheory.fieldPrincipalUnits B (m + 1))
    (abelianLocalArtinMonoidHom_surjective B L) hker hZ

/-- The explicitly chosen complete-DVF upper group agrees with the canonical
local upper ramification group on the same Lubin--Tate level field. -/
theorem
    equalCharacteristicLubinTateRealUpperRamificationGroup_eq_localUpperRamificationGroup
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) (t : ℝ) :
    let B := F.residueField⸨X⸩
    let L := equalCharacteristicLubinTateLevelField F n
    letI : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    letI : FiniteDimensional B L :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    equalCharacteristicLubinTateRealUpperRamificationGroup F n t =
      localUpperRamificationGroup B L t := by
  let B := F.residueField⸨X⸩
  let L := equalCharacteristicLubinTateLevelField F n
  let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField B :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  let : FiniteDimensional B L :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  let base := localCompleteDVF B
  let targetLocal := chosenLocalExtensionCompleteDVF B L
  let targetLT := equalCharacteristicLubinTateLevelCompleteDVF F n
  let : base.valuation.HasExtension targetLT.valuation := by
    change
      (equalCharacteristicLubinTateBaseCompleteDVF F).valuation.HasExtension
        (equalCharacteristicLubinTateLevelCompleteDVF F n).valuation
    exact equalCharacteristicLubinTateLevelCompleteDVF_hasExtension F n
  let huniqLocal :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base.toDVF targetLocal.toDVF :=
    chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension B L
  let huniqLT :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base.toDVF targetLT.toDVF := by
    change
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF
        (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF
    exact
      equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
        F n
  have hvaluationSubring :
      targetLocal.valuation.valuationSubring =
        targetLT.valuation.valuationSubring := by
    exact
      (_root_.Valuation.isEquiv_iff_valuationSubring
        targetLocal.valuation targetLT.valuation).1
        (chosenLocalExtensionCompleteDVF_hasUniqueValuationExtension B L
          targetLT.valuation)
  change
    upperRamificationGroupOfUniqueExtension
        (base := base.toDVF) (target := targetLT.toDVF)
        huniqLT t =
      upperRamificationGroupOfUniqueExtension
        (base := base.toDVF) (target := targetLocal.toDVF)
        huniqLocal t
  exact
    (upperRamificationGroup_eq_of_valuationSubring_eq
      huniqLocal huniqLT hvaluationSubring t).symm

/-- For `1 ≤ k ≤ n + 1`, the `k`-th upper ramification group of level
`n + 1` is the kernel of restriction to level `k`. -/
theorem
    equalCharacteristicLubinTateRealUpperRamificationGroup_eq_restrictKer
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    let B := F.residueField⸨X⸩
    let m := k - 1
    let E := equalCharacteristicLubinTateLevelField F m
    let L := equalCharacteristicLubinTateLevelField F n
    letI : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    letI : FiniteDimensional B E :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F m
    letI : FiniteDimensional B L :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    equalCharacteristicLubinTateRealUpperRamificationGroup F n (k : ℝ) =
      (intermediateFieldRestrictNormalHom E L
        (equalCharacteristicLubinTateLevelField_mono F
          (Nat.sub_le_iff_le_add.2 hkn))).ker := by
  let B := F.residueField⸨X⸩
  let m := k - 1
  let E := equalCharacteristicLubinTateLevelField F m
  let L := equalCharacteristicLubinTateLevelField F n
  let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField B :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  let : FiniteDimensional B E :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F m
  let : FiniteDimensional B L :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  let : IsAbelianGalois B E :=
    equalCharacteristicLubinTateLevelField_isAbelianGalois F m
  let : IsAbelianGalois B L :=
    equalCharacteristicLubinTateLevelField_isAbelianGalois F n
  let hmn : m ≤ n := by
    simpa only [m] using Nat.sub_le_iff_le_add.2 hkn
  let hEL : E ≤ L := equalCharacteristicLubinTateLevelField_mono F hmn
  let ψ := intermediateFieldRestrictNormalHom E L hEL
  have hmap :
      Subgroup.map ψ
          (equalCharacteristicLubinTateRealUpperRamificationGroup
            F n (k : ℝ)) =
        equalCharacteristicLubinTateRealUpperRamificationGroup
          F m (k : ℝ) := by
    rw [
      equalCharacteristicLubinTateRealUpperRamificationGroup_eq_localUpperRamificationGroup,
      equalCharacteristicLubinTateRealUpperRamificationGroup_eq_localUpperRamificationGroup]
    exact localUpperRamificationGroup_map_restrict B E L hEL (k : ℝ)
  have hkm : k ≤ m + 1 := by
    dsimp only [m]
    omega
  have hcardLower :
      Nat.card
          (equalCharacteristicLubinTateRealUpperRamificationGroup
            F m (k : ℝ)) = 1 := by
    rw [
      equalCharacteristicLubinTateRealUpperRamificationGroup_natCard
        F m k hk hkm]
    have hmkeq : m + 1 = k := by
      dsimp only [m]
      omega
    rw [hmkeq, Nat.sub_self, pow_zero]
  have hLowerBot :
      equalCharacteristicLubinTateRealUpperRamificationGroup
          F m (k : ℝ) = ⊥ := by
    exact Subgroup.eq_bot_of_card_le _ (by omega)
  have hUpperLeKer :
      equalCharacteristicLubinTateRealUpperRamificationGroup
          F n (k : ℝ) ≤ ψ.ker := by
    apply (Subgroup.map_eq_bot_iff
      (equalCharacteristicLubinTateRealUpperRamificationGroup
        F n (k : ℝ))).1
    exact hmap.trans hLowerBot
  have hψ_surjective : Function.Surjective ψ := by
    intro σ
    obtain ⟨a, ha⟩ :=
      abelianLocalArtinMonoidHom_surjective B E σ
    refine ⟨abelianLocalArtinMonoidHom B L a, ?_⟩
    exact
      (DFunLike.congr_fun
        (abelianLocalArtinMonoidHom_restrict B E L hEL) a).trans ha
  let q := Nat.card F.residueField
  have hcardGalE :
      Nat.card (Gal(E / B)) = (q - 1) * q ^ m := by
    calc
      Nat.card (Gal(E / B)) =
          Module.finrank B E := by
            simpa [B, E] using
              equalCharacteristicLubinTateLevelField_natCard_gal F m
      _ = (q - 1) * q ^ m := by
            simpa [B, E, q] using
              equalCharacteristicLubinTateLevelField_finrank F m
  have hcardGalL :
      Nat.card (Gal(L / B)) = (q - 1) * q ^ n := by
    calc
      Nat.card (Gal(L / B)) =
          Module.finrank B L := by
            simpa [B, L] using
              equalCharacteristicLubinTateLevelField_natCard_gal F n
      _ = (q - 1) * q ^ n := by
            simpa [B, L, q] using
              equalCharacteristicLubinTateLevelField_finrank F n
  have hcardKer :
      Nat.card ψ.ker = q ^ (n - m) := by
    exact
      natCard_ker_eq_pow_sub_of_surjective
        ψ hψ_surjective q m n hmn
        (Finite.one_lt_card : 1 < Nat.card F.residueField)
        hcardGalL hcardGalE
  have hexponent : n - m = n + 1 - k := by
    dsimp only [m]
    omega
  have hcardUpper :
      Nat.card
          (equalCharacteristicLubinTateRealUpperRamificationGroup
            F n (k : ℝ)) =
        q ^ (n + 1 - k) := by
    simpa [q] using
      equalCharacteristicLubinTateRealUpperRamificationGroup_natCard
        F n k hk hkn
  apply Subgroup.eq_of_le_of_card_ge hUpperLeKer
  rw [hcardKer, hexponent, hcardUpper]

/-- Filtered local reciprocity for an explicit equal-characteristic
Lubin--Tate level: the standard local Artin image of `U^k` is the actual
canonical upper ramification group `G^k`. -/
theorem
    equalCharacteristicLubinTateArtinPrincipalUnitsImage_eq_localUpperRamificationGroup
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    let B := F.residueField⸨X⸩
    let L := equalCharacteristicLubinTateLevelField F n
    letI : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    letI : FiniteDimensional B L :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    (LocalFieldTheory.fieldPrincipalUnits B k).map (abelianLocalArtinMonoidHom B L) =
      localUpperRamificationGroup B L (k : ℝ) := by
  let m := k - 1
  have hmn : m ≤ n := by
    dsimp only [m]
    omega
  have hArtin :=
    equalCharacteristicLubinTateArtinPrincipalUnitsImage_eq_restrictKer
      F hmn
  have hUpper :=
    equalCharacteristicLubinTateRealUpperRamificationGroup_eq_restrictKer
      F n k hk hkn
  have hChoice :=
    equalCharacteristicLubinTateRealUpperRamificationGroup_eq_localUpperRamificationGroup
      F n (k : ℝ)
  simpa [m, Nat.sub_add_cancel hk] using
    hArtin.trans (hUpper.symm.trans hChoice)

end LocalClassFieldTheory
