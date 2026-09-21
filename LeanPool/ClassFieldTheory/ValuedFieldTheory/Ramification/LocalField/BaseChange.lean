/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.Core
/-!
# Transport of upper ramification groups under an equivalent base field

The target field can carry two algebra structures whose base fields are
identified by a valuation-preserving field equivalence.  This file proves
that the resulting Galois groups have the same upper filtration, after
identifying their automorphisms by their common action on the target.
-/

noncomputable section

namespace RamificationTheory.LocalField

open LocalFieldTheory
open RamificationTheory.HilbertRamification
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension
open scoped ValuativeRel

/-- If two base fields have the same image in a common extension, their
Galois groups are identified by leaving the underlying target automorphism
unchanged. -/
noncomputable def galoisGroupEquivOfBaseRingEquiv
    (B K E : Type)
    [Field B] [Field K] [Field E]
    [Algebra B E] [Algebra K E]
    (e : B ≃+* K)
    (he : ∀ b, algebraMap K E (e b) = algebraMap B E b) :
    Gal(E / B) ≃* Gal(E / K) where
  toFun σ :=
    { σ.toRingEquiv with
      commutes' := by
        intro k
        rw [← e.apply_symm_apply k, he]
        exact σ.commutes (e.symm k) }
  invFun τ :=
    { τ.toRingEquiv with
      commutes' := by
        intro b
        rw [← he b]
        exact τ.commutes (e b) }
  left_inv σ := by
    ext x
    rfl
  right_inv τ := by
    ext x
    rfl
  map_mul' σ τ := by
    ext x
    rfl

@[simp]
theorem galoisGroupEquivOfBaseRingEquiv_apply
    (B K E : Type)
    [Field B] [Field K] [Field E]
    [Algebra B E] [Algebra K E]
    (e : B ≃+* K)
    (he : ∀ b, algebraMap K E (e b) = algebraMap B E b)
    (σ : Gal(E / B)) (x : E) :
    galoisGroupEquivOfBaseRingEquiv B K E e he σ x = σ x :=
  rfl

private theorem upperRamificationGroup_map_baseChange
    (B K E : Type)
    [Field B] [Field K] [Field E]
    [Algebra B E] [Algebra K E]
    [FiniteDimensional B E] [FiniteDimensional K E]
    (baseB : DVF.{0, 0} B)
    (baseK : DVF.{0, 0} K)
    (target : DVF.{0, 0} E)
    [baseB.valuation.HasExtension target.valuation]
    [baseK.valuation.HasExtension target.valuation]
    (huniqB :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        (base := baseB) (target := target))
    (huniqK :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        (base := baseK) (target := target))
    (q : Gal(E / B) ≃* Gal(E / K))
    (hq : ∀ σ x, q σ x = σ x)
    (t : ℝ) :
    Subgroup.map q.toMonoidHom
        (upperRamificationGroupOfUniqueExtension
          (base := baseB) (target := target) huniqB t) =
      upperRamificationGroupOfUniqueExtension
        (base := baseK) (target := target) huniqK t := by
  have hdisplacement
      (σ : Gal(E / B)) (a : target.valuationSubring) :
      valuationSubringAutOfUniqueExtension
            (base := baseK) (target := target)
            huniqK (q σ) a - a =
        valuationSubringAutOfUniqueExtension
            (base := baseB) (target := target)
            huniqB σ a - a := by
    apply Subtype.ext
    change q σ (a : E) - (a : E) = σ (a : E) - (a : E)
    rw [hq σ (a : E)]
  have hmem (s : ℝ) (σ : Gal(E / B)) :
      σ ∈ lowerRamificationGroup
            (base := baseB) (target := target) huniqB s ↔
        q σ ∈ lowerRamificationGroup
            (base := baseK) (target := target) huniqK s := by
    constructor
    · intro hσ a
      rw [hdisplacement]
      exact hσ a
    · intro hσ a
      rw [← hdisplacement]
      exact hσ a
  have hlower (s : ℝ) :
      Subgroup.map q.toMonoidHom
          (lowerRamificationGroup
            (base := baseB) (target := target) huniqB s) =
        lowerRamificationGroup
          (base := baseK) (target := target) huniqK s := by
    ext τ
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact (hmem s σ).1 hσ
    · intro hτ
      refine ⟨q.symm τ, (hmem s (q.symm τ)).2 ?_, by simp⟩
      simpa using hτ
  have hcard (n : ℕ) :
      Nat.card
          ((lowerRamificationFiltrationOfUniqueExtension
            (base := baseB) (target := target) huniqB).lower n) =
        Nat.card
          ((lowerRamificationFiltrationOfUniqueExtension
            (base := baseK) (target := target) huniqK).lower n) := by
    let H :=
      lowerRamificationGroup
        (base := baseB) (target := target) huniqB (n : ℝ)
    let qH :=
      (q.subgroupMap H).trans
        (MulEquiv.subgroupCongr (hlower (n : ℝ)))
    exact Nat.card_congr qH.toEquiv
  have hherbrand (s : ℝ) :
      herbrandFunctionOfUniqueExtension
          (base := baseB) (target := target) huniqB s =
        herbrandFunctionOfUniqueExtension
          (base := baseK) (target := target) huniqK s := by
    exact
      RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_eq_of_card_lower_eq
        _ _ hcard s
  have hinverse (u : ℝ) :
      inverseHerbrandFunctionOfUniqueExtension
          (base := baseB) (target := target) huniqB u =
        inverseHerbrandFunctionOfUniqueExtension
          (base := baseK) (target := target) huniqK u := by
    apply
      (herbrandFunctionOfUniqueExtension_strictMono
        (base := baseK) (target := target) huniqK).injective
    rw [herbrandFunctionOfUniqueExtension_psi]
    rw [← hherbrand]
    rw [herbrandFunctionOfUniqueExtension_psi]
  change
    Subgroup.map q.toMonoidHom
        (lowerRamificationGroup
          (base := baseB) (target := target) huniqB
          (inverseHerbrandFunctionOfUniqueExtension
            (base := baseB) (target := target) huniqB t)) =
      lowerRamificationGroup
        (base := baseK) (target := target) huniqK
        (inverseHerbrandFunctionOfUniqueExtension
          (base := baseK) (target := target) huniqK t)
  rw [hinverse]
  exact hlower _

/-- A valuation-preserving base-field equivalence transports every actual
local upper ramification group to the group for the transported algebra
structure on the same target field. -/
theorem localUpperRamificationGroup_map_baseRingEquiv
    (B K E : Type)
    [Field B] [Field K] [Field E]
    [Algebra B E] [Algebra K E]
    [FiniteDimensional B E] [FiniteDimensional K E]
    [IsGalois B E] [IsGalois K E]
    [ValuativeRel B] [TopologicalSpace B]
    [IsNonarchimedeanLocalField B]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (e : B ≃+* K)
    (he : ∀ b, algebraMap K E (e b) = algebraMap B E b)
    (hvaluation : ∀ b,
      ValuativeRel.valuation B b ≤ 1 ↔
        ValuativeRel.valuation K (e b) ≤ 1)
    (t : ℝ) :
    Subgroup.map
        (galoisGroupEquivOfBaseRingEquiv B K E e he).toMonoidHom
        (localUpperRamificationGroup B E t) =
      localUpperRamificationGroup K E t := by
  let baseB := localCompleteDVF B
  let baseK := localCompleteDVF K
  let targetB := chosenLocalExtensionCompleteDVF B E
  let targetK := chosenLocalExtensionCompleteDVF K E
  let q := galoisGroupEquivOfBaseRingEquiv B K E e he
  let hExtB : baseB.valuation.HasExtension targetB.valuation :=
    chosenLocalExtensionCompleteDVF_hasExtension B E
  let hExtK : baseK.valuation.HasExtension targetK.valuation :=
    chosenLocalExtensionCompleteDVF_hasExtension K E
  let hExtBK : baseB.valuation.HasExtension targetK.valuation := by
    refine { val_isEquiv_comap := ?_ }
    rw [_root_.Valuation.isEquiv_iff_val_le_one]
    intro b
    change
      baseB.valuation b ≤ 1 ↔
        targetK.valuation (algebraMap B E b) ≤ 1
    rw [← he b]
    exact
      (hvaluation b).trans
        ((_root_.Valuation.HasExtension.val_map_le_one_iff
          (vR := baseK.valuation) (vA := targetK.valuation) (e b)).symm)
  let huniqB :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        (base := baseB.toDVF) (target := targetB.toDVF) :=
    chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension B E
  let huniqK :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        (base := baseK.toDVF) (target := targetK.toDVF) :=
    chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K E
  let huniqBK :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        (base := baseB.toDVF) (target := targetK.toDVF) :=
    hasUniqueValuationExtension_of_finite_separable baseB targetK
  have hvaluationSubring :
      targetB.valuation.valuationSubring =
        targetK.valuation.valuationSubring := by
    exact
      (_root_.Valuation.isEquiv_iff_valuationSubring
        targetB.valuation targetK.valuation).1
        (huniqB targetK.valuation)
  have hchosen :
      upperRamificationGroupOfUniqueExtension
          (base := baseB.toDVF) (target := targetB.toDVF)
          huniqB t =
        upperRamificationGroupOfUniqueExtension
          (base := baseB.toDVF) (target := targetK.toDVF)
          huniqBK t :=
    upperRamificationGroup_eq_of_valuationSubring_eq
      huniqB huniqBK hvaluationSubring t
  change
    Subgroup.map q.toMonoidHom
        (upperRamificationGroupOfUniqueExtension
          (base := baseB.toDVF) (target := targetB.toDVF)
          huniqB t) =
      upperRamificationGroupOfUniqueExtension
        (base := baseK.toDVF) (target := targetK.toDVF)
        huniqK t
  rw [hchosen]
  exact
    upperRamificationGroup_map_baseChange
      B K E baseB.toDVF baseK.toDVF targetK.toDVF
      huniqBK huniqK q
      (fun σ x => galoisGroupEquivOfBaseRingEquiv_apply
        B K E e he σ x) t

end RamificationTheory.LocalField
