/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.Core
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing
/-!
# Ramification groups of unramified local extensions

This file connects the concrete unramified-valued-extension predicate with
the actual upper ramification groups of a finite local extension.
-/

@[expose] public section

noncomputable section

namespace RamificationTheory.LocalField

open LocalFieldTheory
open RamificationTheory
open RamificationTheory.HilbertRamification
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension
open scoped ValuativeRel

/-- The complete-DVF package used by local reciprocity contains the canonical
valuation of the local field. -/
private theorem localCompleteDVF_valuation_eq_valuativeRel
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    (localCompleteDVF K).valuation = ValuativeRel.valuation K := by
  unfold localCompleteDVF
  unfold ValuationTheory.Valuations.completeDVFOfCompleteValuedField
  rfl

/-- The inertia group, equivalently the lower ramification group at zero, is
trivial for an actual finite unramified Galois extension of local fields. -/
private theorem localLowerRamificationGroup_zero_eq_bot_of_unramifiedValuation
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    localLowerRamificationGroup K L 0 = ⊥ := by
  let base := localCompleteDVF K
  let target := localCompleteDVF L
  let chosenTarget := chosenLocalExtensionCompleteDVF K L
  let hExtTarget : base.valuation.HasExtension target.valuation := by
    apply Valuation.HasExtension.ofComapInteger
    ext x
    change
      target.valuation (algebraMap K L x) ≤ 1 ↔
        base.valuation x ≤ 1
    dsimp only [base, target]
    rw [localCompleteDVF_valuation_eq_valuativeRel K,
      localCompleteDVF_valuation_eq_valuativeRel L]
    exact
      Valuation.HasExtension.val_map_le_one_iff
        (ValuativeRel.valuation K) (ValuativeRel.valuation L) x
  let huniqChosen :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base.toDVF chosenTarget.toDVF :=
    chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K L
  let huniqTarget :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base.toDVF target.toDVF :=
    hasUniqueValuationExtension_of_finite_separable base target
  have hvaluationSubring :
      chosenTarget.valuation.valuationSubring =
        target.valuation.valuationSubring := by
    rw [← _root_.Valuation.isEquiv_iff_valuationSubring]
    exact
      chosenLocalExtensionCompleteDVF_hasUniqueValuationExtension K L
        target.valuation
  rw [show localLowerRamificationGroup K L 0 =
      lowerRamificationGroup
        (base := base.toDVF) (target := chosenTarget.toDVF)
        huniqChosen 0 by rfl]
  rw [lowerRamificationGroup_eq_of_valuationSubring_eq
    huniqChosen huniqTarget hvaluationSubring 0]
  ext σ
  constructor
  · intro hσ
    have hker :
        σ ∈
          (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker := by
      rw [
        galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal
          K L σ]
      intro x
      have hInteger :
          target.valuation.valuationSubring.toSubring =
            (ValuativeRel.valuation L).integer := by
        dsimp only [target]
        unfold localCompleteDVF
        unfold ValuationTheory.Valuations.completeDVFOfCompleteValuedField
        rfl
      let eInteger : target.valuationSubring ≃+* 𝒪[L] :=
        RingEquiv.subringCongr hInteger
      let y := eInteger.symm x
      have hσ' :
          σ ∈
            lowerRamificationGroup
              (base := base.toDVF) (target := target.toDVF)
              huniqTarget ((0 : ℕ) : ℝ) := by
        simpa using hσ
      have hx :=
        (mem_lowerRamificationGroup_nat_iff
          (base := base.toDVF) (target := target.toDVF)
          huniqTarget 0 σ).1 hσ' y
      have hxMaximal :
          valuationSubringAutOfUniqueExtension
                (base := base.toDVF) (target := target.toDVF)
                huniqTarget σ y - y ∈
            target.maximalIdeal := by
        simpa only [Nat.zero_add, pow_one] using hx
      have hxMapped :
          eInteger
                (valuationSubringAutOfUniqueExtension
                    (base := base.toDVF) (target := target.toDVF)
                    huniqTarget σ y - y) ∈
            (𝓂[L] : Ideal 𝒪[L]) := by
        rw [IsLocalRing.mem_maximalIdeal,
          map_mem_nonunits_iff eInteger,
          ← IsLocalRing.mem_maximalIdeal]
        exact hxMaximal
      have hunderlying :
          eInteger
                (valuationSubringAutOfUniqueExtension
                    (base := base.toDVF) (target := target.toDVF)
                    huniqTarget σ y - y) =
            galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x - x := by
        apply Subtype.ext
        rfl
      rw [← hunderlying]
      exact hxMapped
    have hinjective :=
      galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation
        K L
    have hσone : σ = 1 := by
      apply hinjective
      rw [MonoidHom.mem_ker.mp hker, map_one]
    change σ = 1
    exact hσone
  · intro hσ
    change σ = 1 at hσ
    subst σ
    exact Subgroup.one_mem _

/-- Every nonnegative upper ramification group of an actual finite
unramified Galois extension of local fields is trivial. -/
theorem localUpperRamificationGroup_eq_bot_of_unramifiedValuation
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (t : ℝ) (ht : 0 ≤ t) :
    localUpperRamificationGroup K L t = ⊥ := by
  apply le_antisymm
  · calc
      localUpperRamificationGroup K L t ≤
          localUpperRamificationGroup K L 0 :=
        localUpperRamificationGroup_antitone K L ht
      _ = localLowerRamificationGroup K L 0 :=
        localUpperRamificationGroup_eq_localLowerRamificationGroup_of_nonpos
          K L 0 (by norm_num)
      _ = ⊥ :=
        localLowerRamificationGroup_zero_eq_bot_of_unramifiedValuation K L
  · exact bot_le

end RamificationTheory.LocalField
