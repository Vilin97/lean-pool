/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.Core
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.BaseChange
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.Unramified
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.HerbrandFormula
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LevelFieldTower
/-!
# Upper ramification groups of standard Lubin--Tate levels

For the canonical `LocalField` package attached to a nonarchimedean local
field, the explicit complete-DVF valuation chosen in the standard
Lubin--Tate construction is equivalent to the valuation chosen by the local
upper-ramification API.  This identifies their upper filtrations.

The explicit Herbrand formula and the finite-level tower then identify the
integral upper group at `k` with the kernel of restriction to level `k - 1`.
-/

@[expose] public section

noncomputable section

open scoped ValuativeRel

namespace LubinTate

open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LubinTate
open RamificationTheory.HilbertRamification.Higher
open RamificationTheory.LocalField
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The explicit complete-DVF upper group on a standard Lubin--Tate level
agrees with the canonical local upper ramification group. -/
theorem
    standardLubinTateRealUpperRamificationGroup_eq_localUpperRamificationGroup
    {π : (standardLocalField K).valuationSubring}
    (hπ :
      (standardLocalField K).toCompleteDVF.valuation.IsUniformizer
        (π : K))
    (n : ℕ) (t : ℝ) :
    let F := standardLocalField K
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional K L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsGalois K L :=
      standardLubinTateLevelField_isGalois (F := F) hπ n
    standardLubinTateRealUpperRamificationGroup hπ n t =
      localUpperRamificationGroup K L t := by
  let F := standardLocalField K
  let L := standardLubinTateLevelField hπ n
  let : FiniteDimensional K L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsGalois K L :=
    standardLubinTateLevelField_isGalois (F := F) hπ n
  let base := localCompleteDVF K
  let targetLocal := chosenLocalExtensionCompleteDVF K L
  let targetLT := standardLubinTateLevelCompleteDVF hπ n
  let : base.valuation.HasExtension targetLT.valuation := by
    change F.toCompleteDVF.valuation.HasExtension targetLT.valuation
    exact standardLubinTateLevelCompleteDVF_hasExtension hπ n
  let huniqLocal :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base.toDVF targetLocal.toDVF :=
    chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K L
  let huniqLT :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base.toDVF targetLT.toDVF := by
    change
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        F.toCompleteDVF.toDVF targetLT.toDVF
    exact
      standardLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
        hπ n
  have hvaluationSubring :
      targetLocal.valuation.valuationSubring =
        targetLT.valuation.valuationSubring := by
    exact
      (_root_.Valuation.isEquiv_iff_valuationSubring
        targetLocal.valuation targetLT.valuation).1
        (chosenLocalExtensionCompleteDVF_hasUniqueValuationExtension
          K L targetLT.valuation)
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

/-- For `1 ≤ k ≤ n + 1`, the `k`-th upper ramification group of the
standard level `n + 1` is the kernel of restriction to level `k`. -/
theorem standardLubinTateRealUpperRamificationGroup_eq_restrictKer
    {π : (standardLocalField K).valuationSubring}
    (hπ :
      (standardLocalField K).toCompleteDVF.valuation.IsUniformizer
        (π : K))
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    let F := standardLocalField K
    let m := k - 1
    let E := standardLubinTateLevelField hπ m
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional K E :=
      standardLubinTateLevelField_finiteDimensional hπ m
    letI : FiniteDimensional K L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsGalois K E :=
      standardLubinTateLevelField_isGalois (F := F) hπ m
    letI : IsGalois K L :=
      standardLubinTateLevelField_isGalois (F := F) hπ n
    let hEL : E ≤ L :=
      standardLubinTateLevelField_mono hπ (by omega)
    standardLubinTateRealUpperRamificationGroup hπ n (k : ℝ) =
      (RamificationTheory.intermediateFieldRestrictNormalHom E L hEL).ker := by
  let F := standardLocalField K
  let m := k - 1
  let E := standardLubinTateLevelField hπ m
  let L := standardLubinTateLevelField hπ n
  let : FiniteDimensional K E :=
    standardLubinTateLevelField_finiteDimensional hπ m
  let : FiniteDimensional K L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsGalois K E :=
    standardLubinTateLevelField_isGalois (F := F) hπ m
  let : IsGalois K L :=
    standardLubinTateLevelField_isGalois (F := F) hπ n
  let hmn : m ≤ n := by
    dsimp only [m]
    omega
  let hEL : E ≤ L := standardLubinTateLevelField_mono hπ hmn
  let ψ := RamificationTheory.intermediateFieldRestrictNormalHom E L hEL
  have hmap :
      Subgroup.map ψ
          (standardLubinTateRealUpperRamificationGroup
            hπ n (k : ℝ)) =
        standardLubinTateRealUpperRamificationGroup
          hπ m (k : ℝ) := by
    rw [
      standardLubinTateRealUpperRamificationGroup_eq_localUpperRamificationGroup
        K hπ n (k : ℝ),
      standardLubinTateRealUpperRamificationGroup_eq_localUpperRamificationGroup
        K hπ m (k : ℝ)]
    exact localUpperRamificationGroup_map_restrict K E L hEL (k : ℝ)
  have hkm : k ≤ m + 1 := by
    dsimp only [m]
    omega
  have hcardLower :
      Nat.card
          (standardLubinTateRealUpperRamificationGroup
            hπ m (k : ℝ)) = 1 := by
    rw [
      standardLubinTateRealUpperRamificationGroup_natCard
        F hπ m k hk hkm]
    have hmkeq : m + 1 = k := by
      dsimp only [m]
      omega
    rw [hmkeq, Nat.sub_self, pow_zero]
  have hLowerBot :
      standardLubinTateRealUpperRamificationGroup
          hπ m (k : ℝ) = ⊥ := by
    exact Subgroup.eq_bot_of_card_le _ (by omega)
  have hUpperLeKer :
      standardLubinTateRealUpperRamificationGroup
          hπ n (k : ℝ) ≤ ψ.ker := by
    apply (Subgroup.map_eq_bot_iff
      (standardLubinTateRealUpperRamificationGroup
        hπ n (k : ℝ))).1
    exact hmap.trans hLowerBot
  have hψ_surjective : Function.Surjective ψ := by
    let : Algebra E L :=
      RingHom.toAlgebra (IntermediateField.inclusion hEL).toRingHom
    let : IsScalarTower K E L :=
      IsScalarTower.of_algebraMap_eq' rfl
    change Function.Surjective
      (AlgEquiv.restrictNormalHom E :
        Gal(L/K) →* Gal(E/K))
    exact
      AlgEquiv.restrictNormalHom_surjective
        (F := K) (K₁ := E) (E := L)
  let q := Nat.card F.residueField
  have hcardGalE :
      Nat.card (Gal(E/K)) = (q - 1) * q ^ m := by
    calc
      Nat.card (Gal(E/K)) =
          Module.finrank K E := by
            simpa [E] using
              standardLubinTateLevelField_natCard_gal
                (F := F) hπ m
      _ = (q - 1) * q ^ m := by
            simpa [E, q] using
              standardLubinTateLevelField_finrank
                (F := F) hπ m
  have hcardGalL :
      Nat.card (Gal(L/K)) = (q - 1) * q ^ n := by
    calc
      Nat.card (Gal(L/K)) =
          Module.finrank K L := by
            simpa [L] using
              standardLubinTateLevelField_natCard_gal
                (F := F) hπ n
      _ = (q - 1) * q ^ n := by
            simpa [L, q] using
              standardLubinTateLevelField_finrank
                (F := F) hπ n
  have hindex :
      ψ.ker.index = Nat.card (Gal(E/K)) := by
    rw [Subgroup.index_ker,
      ψ.range_eq_top_of_surjective hψ_surjective,
      Subgroup.card_top]
  have hcardKerMul :
      Nat.card ψ.ker * Nat.card (Gal(E/K)) =
        Nat.card (Gal(L/K)) := by
    rw [← hindex]
    exact Subgroup.card_mul_index ψ.ker
  rw [hcardGalE, hcardGalL] at hcardKerMul
  have hfactor_pos : 0 < (q - 1) * q ^ m := by
    exact Nat.mul_pos
      (Nat.sub_pos_of_lt
        (Finite.one_lt_card : 1 < Nat.card F.residueField))
      (Nat.pow_pos Nat.card_pos)
  have hcardKer :
      Nat.card ψ.ker = q ^ (n - m) := by
    have hpow : q ^ n = q ^ m * q ^ (n - m) := by
      rw [← pow_add, Nat.add_sub_of_le hmn]
    apply Nat.eq_of_mul_eq_mul_left hfactor_pos
    calc
      ((q - 1) * q ^ m) * Nat.card ψ.ker =
          Nat.card ψ.ker * ((q - 1) * q ^ m) := by
            exact Nat.mul_comm _ _
      _ = (q - 1) * q ^ n := hcardKerMul
      _ = ((q - 1) * q ^ m) * q ^ (n - m) := by
        rw [hpow, Nat.mul_assoc]
  have hexponent : n - m = n + 1 - k := by
    dsimp only [m]
    omega
  have hcardUpper :
      Nat.card
          (standardLubinTateRealUpperRamificationGroup
            hπ n (k : ℝ)) =
        q ^ (n + 1 - k) := by
    simpa [q] using
      standardLubinTateRealUpperRamificationGroup_natCard
        F hπ n k hk hkn
  apply Subgroup.eq_of_le_of_card_ge hUpperLeKer
  rw [hcardKer, hexponent, hcardUpper]

end LubinTate

end
