/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.Core
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.RealIndexSteps
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.StandardArtinComparison
/-!
# Real filtered reciprocity on equal-characteristic Lubin--Tate levels

This file extends the integral comparison between standard local Artin images
and upper ramification groups to every nonnegative real index.  It separately
packages the zeroth and terminal cases, then combines them with the positive
ceiling-step comparison.
-/

@[expose] public section

noncomputable
section

open scoped LaurentSeries ValuativeRel

namespace LocalClassFieldTheory

open RamificationTheory.LocalField
open LubinTate

open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.IsNonarchimedeanLocalField
open LubinTate.EqualCharacteristic
open RamificationTheory.HilbertRamification.Higher

universe v

variable {K₀ : Type} [Field K₀]

/-- The chosen lower ramification group at index zero is the full Galois
group for an equal-characteristic Lubin--Tate level. -/
theorem
    equalCharacteristicLubinTateRealLowerRamificationGroup_zero_eq_top
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateRealLowerRamificationGroup F n 0 = ⊤ := by
  apply top_unique
  intro sigma _
  let e := equalCharacteristicLubinTateUnitParameterEquivGal F n
  let a := e.symm sigma
  have hsigma : e a = sigma := e.apply_symm_apply sigma
  rw [← hsigma]
  change
    equalCharacteristicLubinTateUnitParameterToGal F n a ∈
      equalCharacteristicLubinTateRealLowerRamificationGroup F n 0
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

/-- The chosen upper ramification group at index zero is the full Galois
group for an equal-characteristic Lubin--Tate level. -/
theorem
    equalCharacteristicLubinTateRealUpperRamificationGroup_zero_eq_top
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateRealUpperRamificationGroup F n 0 = ⊤ := by
  calc
    equalCharacteristicLubinTateRealUpperRamificationGroup F n 0 =
        equalCharacteristicLubinTateRealLowerRamificationGroup F n 0 := by
      simpa using
        equalCharacteristicLubinTateRealUpperRamificationGroup_nat_eq_lower_pow_sub_one
          F n 0 (by omega)
    _ = ⊤ :=
      equalCharacteristicLubinTateRealLowerRamificationGroup_zero_eq_top F n

/-- The canonical local upper ramification group at index zero is full on an
equal-characteristic Lubin--Tate level. -/
theorem
    equalCharacteristicLubinTateLocalUpperRamificationGroup_zero_eq_top
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    let B := F.residueField⸨X⸩
    let L := equalCharacteristicLubinTateLevelField F n
    letI : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    letI : FiniteDimensional B L :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    localUpperRamificationGroup B L 0 = ⊤ := by
  let B := F.residueField⸨X⸩
  let L := equalCharacteristicLubinTateLevelField F n
  let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField B :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  let : FiniteDimensional B L :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  calc
    localUpperRamificationGroup B L 0 =
        equalCharacteristicLubinTateRealUpperRamificationGroup F n 0 :=
      (equalCharacteristicLubinTateRealUpperRamificationGroup_eq_localUpperRamificationGroup
        F n 0).symm
    _ = ⊤ :=
      equalCharacteristicLubinTateRealUpperRamificationGroup_zero_eq_top F n

/-- The standard local Artin image of the full valuation-ring unit group
`U^0` is the full Galois group of an equal-characteristic Lubin--Tate level. -/
theorem
    equalCharacteristicLubinTateArtinPrincipalUnitsImage_zero_eq_top
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    let B := F.residueField⸨X⸩
    let L := equalCharacteristicLubinTateLevelField F n
    letI : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    letI : FiniteDimensional B L :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    (LocalFieldTheory.fieldPrincipalUnits B 0).map (abelianLocalArtinMonoidHom B L) = ⊤ := by
  let B := F.residueField⸨X⸩
  let L := equalCharacteristicLubinTateLevelField F n
  let pi : Bˣ := (equalCharacteristicLaurentUniformizerUnit F)⁻¹
  let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField B :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  let : FiniteDimensional B L :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  have hpi :
      valuationMap B (Additive.ofMul pi) = 1 := by
    simpa only [B, pi] using
      equalCharacteristicLaurentUniformizerUnit_inv_valuationMap F
  have hpiKer :
      Subgroup.zpowers pi ≤ (abelianLocalArtinMonoidHom B L).ker := by
    rw [abelianLocalArtinMonoidHom_ker]
    change Subgroup.zpowers pi ≤
      equalCharacteristicLubinTateNormSubgroup F n
    rw [
      equalCharacteristicLubinTateNormSubgroup_eq_uniformizerPrincipalSubgroup]
    simp [B, pi, LocalFieldTheory.uniformizerPrincipalSubgroup]
  apply top_unique
  intro sigma _
  obtain ⟨x, hx⟩ :=
    abelianLocalArtinMonoidHom_surjective B L sigma
  obtain ⟨u, hdecomp⟩ :=
    exists_integerUnit_mul_uniformizer_zpow B pi hpi x
  have hpowKer :
      pi ^ valuationMap B (Additive.ofMul x) ∈
        (abelianLocalArtinMonoidHom B L).ker :=
    hpiKer (Subgroup.zpow_mem_zpowers pi _)
  have hpow :
      abelianLocalArtinMonoidHom B L
          (pi ^ valuationMap B (Additive.ofMul x)) = 1 :=
    MonoidHom.mem_ker.mp hpowKer
  refine ⟨integerUnitsToFieldUnits B u, ?_, ?_⟩
  · unfold LocalFieldTheory.fieldPrincipalUnits
    exact ⟨u, by simp, rfl⟩
  · rw [← hx, ← hdecomp, map_mul, hpow, mul_one]

/-- The zeroth Artin principal-unit group is full on an explicit
equal-characteristic Lubin--Tate level. -/
theorem
    equalCharacteristicLubinTateArtinPrincipalUnitGroup_zero_eq_top
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    let B := F.residueField⸨X⸩
    let L := equalCharacteristicLubinTateLevelField F n
    letI : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    letI : FiniteDimensional B L :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    artinPrincipalUnitGroup B L 0 = ⊤ := by
  simpa only [artinPrincipalUnitGroup] using
    equalCharacteristicLubinTateArtinPrincipalUnitsImage_zero_eq_top F n

/-- At the last visible integral upper index `n + 1`, the chosen upper group
is trivial. -/
theorem
    equalCharacteristicLubinTateRealUpperRamificationGroup_succ_eq_bot
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateRealUpperRamificationGroup
      F n ((n + 1 : ℕ) : ℝ) = ⊥ := by
  have hcard :
      Nat.card
          (equalCharacteristicLubinTateRealUpperRamificationGroup
            F n ((n + 1 : ℕ) : ℝ)) = 1 := by
    simpa using
      equalCharacteristicLubinTateRealUpperRamificationGroup_natCard
        F n (n + 1) (by omega) (by omega)
  exact Subgroup.eq_bot_of_card_le _ (by omega)

/-- At the last visible integral upper index `n + 1`, the canonical local
upper group is trivial. -/
theorem
    equalCharacteristicLubinTateLocalUpperRamificationGroup_succ_eq_bot
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    let B := F.residueField⸨X⸩
    let L := equalCharacteristicLubinTateLevelField F n
    letI : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    letI : FiniteDimensional B L :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    localUpperRamificationGroup B L ((n + 1 : ℕ) : ℝ) = ⊥ := by
  let B := F.residueField⸨X⸩
  let L := equalCharacteristicLubinTateLevelField F n
  let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField B :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  let : FiniteDimensional B L :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  calc
    localUpperRamificationGroup B L ((n + 1 : ℕ) : ℝ) =
        equalCharacteristicLubinTateRealUpperRamificationGroup
          F n ((n + 1 : ℕ) : ℝ) :=
      (equalCharacteristicLubinTateRealUpperRamificationGroup_eq_localUpperRamificationGroup
        F n ((n + 1 : ℕ) : ℝ)).symm
    _ = ⊥ :=
      equalCharacteristicLubinTateRealUpperRamificationGroup_succ_eq_bot F n

/-- The standard Artin image of `U^(n+1)` is trivial on the level `n + 1`
extension. -/
theorem
    equalCharacteristicLubinTateArtinPrincipalUnitGroup_succ_eq_bot
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    let B := F.residueField⸨X⸩
    let L := equalCharacteristicLubinTateLevelField F n
    letI : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    letI : FiniteDimensional B L :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    artinPrincipalUnitGroup B L (n + 1) = ⊥ := by
  let B := F.residueField⸨X⸩
  let L := equalCharacteristicLubinTateLevelField F n
  let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField B :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  let : FiniteDimensional B L :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  change
    (LocalFieldTheory.fieldPrincipalUnits B (n + 1)).map
        (abelianLocalArtinMonoidHom B L) = ⊥
  exact
    (equalCharacteristicLubinTateArtinPrincipalUnitsImage_eq_localUpperRamificationGroup
      F n (n + 1) (by omega) (by omega)).trans
      (equalCharacteristicLubinTateLocalUpperRamificationGroup_succ_eq_bot
        F n)

/-- Beyond the last visible level, the real Artin principal-unit step group is
trivial. -/
theorem
    equalCharacteristicLubinTateArtinPrincipalUnitStepGroup_eq_bot_of_level_lt_ceil
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) (t : ℝ) (hlevel : n + 1 < ⌈t⌉₊) :
    let B := F.residueField⸨X⸩
    let L := equalCharacteristicLubinTateLevelField F n
    letI : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    letI : FiniteDimensional B L :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    artinPrincipalUnitStepGroup B L t = ⊥ := by
  let B := F.residueField⸨X⸩
  let L := equalCharacteristicLubinTateLevelField F n
  let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField B :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  let : FiniteDimensional B L :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  unfold artinPrincipalUnitStepGroup RamificationTheory.natCeilStepFiltration
  apply le_antisymm
  · have hle :=
      artinPrincipalUnitGroup_antitone B L (Nat.le_of_lt hlevel)
    rw [
      equalCharacteristicLubinTateArtinPrincipalUnitGroup_succ_eq_bot
        F n] at hle
    exact hle
  · exact bot_le

/-- Beyond the last visible level, the canonical local upper ramification
group is trivial. -/
theorem
    equalCharacteristicLubinTateLocalUpperRamificationGroup_eq_bot_of_level_lt_ceil
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) (t : ℝ) (hlevel : n + 1 < ⌈t⌉₊) :
    let B := F.residueField⸨X⸩
    let L := equalCharacteristicLubinTateLevelField F n
    letI : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    letI : FiniteDimensional B L :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    localUpperRamificationGroup B L t = ⊥ := by
  let B := F.residueField⸨X⸩
  let L := equalCharacteristicLubinTateLevelField F n
  let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField B :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  let : FiniteDimensional B L :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  have ht :
      (((n + 1 : ℕ) : ℝ)) ≤ t := by
    have hsucc : n + 1 + 1 ≤ ⌈t⌉₊ := by
      omega
    exact (Nat.add_one_le_ceil_iff.mp hsucc).le
  apply le_antisymm
  · have hle := localUpperRamificationGroup_antitone B L ht
    rw [
      equalCharacteristicLubinTateLocalUpperRamificationGroup_succ_eq_bot
        F n] at hle
    exact hle
  · exact bot_le

/-- Real filtered local reciprocity for an explicit equal-characteristic
Lubin--Tate level: at every nonnegative real index, the standard Artin image
of the natural-ceiling principal-unit step is the canonical upper
ramification group. -/
theorem
    equalCharacteristicLubinTateArtinPrincipalUnitStepGroup_eq_localUpperRamificationGroup
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    let B := F.residueField⸨X⸩
    let L := equalCharacteristicLubinTateLevelField F n
    letI : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    letI : FiniteDimensional B L :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    artinPrincipalUnitStepGroup B L t =
      localUpperRamificationGroup B L t := by
  let B := F.residueField⸨X⸩
  let L := equalCharacteristicLubinTateLevelField F n
  let k : ℕ := ⌈t⌉₊
  let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField B :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  let : FiniteDimensional B L :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  by_cases hkzero : k = 0
  · have hceilzero : ⌈t⌉₊ = 0 := by
      simpa only [k] using hkzero
    have htzero : t = 0 :=
      le_antisymm (Nat.ceil_eq_zero.mp hceilzero) ht
    subst t
    calc
      artinPrincipalUnitStepGroup B L (0 : ℝ) = ⊤ := by
        simpa [artinPrincipalUnitStepGroup,
          RamificationTheory.natCeilStepFiltration] using
          equalCharacteristicLubinTateArtinPrincipalUnitGroup_zero_eq_top
            F n
      _ = localUpperRamificationGroup B L 0 :=
        (equalCharacteristicLubinTateLocalUpperRamificationGroup_zero_eq_top
          F n).symm
  · have hk : 1 ≤ k := by
      omega
    by_cases hkn : k ≤ n + 1
    · have hLocalStep :
          localUpperRamificationGroup B L t =
            localUpperRamificationGroup B L (k : ℝ) := by
        calc
          localUpperRamificationGroup B L t =
              equalCharacteristicLubinTateRealUpperRamificationGroup F n t :=
            (equalCharacteristicLubinTateRealUpperRamificationGroup_eq_localUpperRamificationGroup
              F n t).symm
          _ =
              equalCharacteristicLubinTateRealUpperRamificationGroup
                F n (k : ℝ) := by
            have hstep :=
              equalCharacteristicLubinTateRealUpperRamificationGroup_eq_natCeil
                F n t
                  (by simpa only [k] using hk)
                  (by simpa only [k] using hkn)
            simpa only [k] using hstep
          _ = localUpperRamificationGroup B L (k : ℝ) :=
            equalCharacteristicLubinTateRealUpperRamificationGroup_eq_localUpperRamificationGroup
              F n (k : ℝ)
      change
        (LocalFieldTheory.fieldPrincipalUnits B k).map
            (abelianLocalArtinMonoidHom B L) =
          localUpperRamificationGroup B L t
      exact
        (equalCharacteristicLubinTateArtinPrincipalUnitsImage_eq_localUpperRamificationGroup
          F n k hk hkn).trans hLocalStep.symm
    · have hlevel : n + 1 < ⌈t⌉₊ := by
        dsimp only [k] at hkn
        omega
      exact
        (equalCharacteristicLubinTateArtinPrincipalUnitStepGroup_eq_bot_of_level_lt_ceil
          F n t hlevel).trans
          (equalCharacteristicLubinTateLocalUpperRamificationGroup_eq_bot_of_level_lt_ceil
            F n t hlevel).symm

end LocalClassFieldTheory
