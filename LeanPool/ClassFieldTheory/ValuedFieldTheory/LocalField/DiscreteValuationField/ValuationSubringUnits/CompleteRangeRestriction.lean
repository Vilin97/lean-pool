/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestriction
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CyclicValueGroup
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationIdeal
public import Mathlib.RingTheory.AdicCompletion.Topology
/-!
# Range restriction for complete discretely valued fields

This file specializes multiplicative-range restriction to `CompleteDVF` and
transports residue finiteness, adic completeness, cyclicity, and discreteness.
-/

@[expose] public section

noncomputable section

universe u v

open WithZero
open scoped NNReal Valued WithZero

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace CompleteDVF

variable {K : Type u} [Field K]

/-- Restrict the chosen valuation of a complete DVF to its actual
multiplicative range.  This keeps the valuation ring, maximal ideal, and
residue field unchanged while eliminating irrelevant ambient value-group
elements. -/
def mrangeRestrict (F : CompleteDVF.{u, v} K) :
    _root_.Valuation K (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
  WithZeroValuation.mrangeRestrict F.valuation

/--
The defining evaluation formula for `mrangeRestrict` is `((CompleteDVF.mrangeRestrict F) x :
F.ValueGroup) = F.valuation x`.
-/
@[simp]
theorem mrangeRestrict_apply (F : CompleteDVF.{u, v} K) (x : K) :
    ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F) x : F.ValueGroup) =
      F.valuation x :=
  rfl

/-- The residue field remains finite after restricting the value group to the
actual multiplicative range. -/
theorem mrangeRestrict_residueField_finite
    (F : CompleteDVF.{u, v} K) [Finite F.residueField] :
    Finite (IsLocalRing.ResidueField
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring) :=
  Finite.of_equiv F.residueField
    (WithZeroValuation.residueFieldEquivMrangeRestrict
      F.valuation).toEquiv

/-- The range-restricted valuation ring is adically complete because it is
identified with the original complete-DVF valuation ring and the maximal ideal
is preserved by that identification. -/
theorem mrangeRestrict_isAdicComplete
    (F : CompleteDVF.{u, v} K) :
    IsAdicComplete
      (IsLocalRing.maximalIdeal
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring)
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring := by
  let e : F.valuationSubring ≃+*
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring :=
    WithZeroValuation.valuationSubringEquivMrangeRestrict
      F.valuation
  let : Algebra F.valuationSubring
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring :=
    e.toRingHom.toAlgebra
  let eLin :
      F.valuationSubring ≃ₗ[F.valuationSubring]
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro a x
        change e (a * x) =
          (algebraMap F.valuationSubring
            (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict
              F).valuationSubring a) * e x
        simp [RingHom.algebraMap_toAlgebra] }
  have hcompleteBase : IsAdicComplete F.maximalIdeal F.valuationSubring :=
    F.isAdicComplete
  let : IsAdicComplete F.maximalIdeal F.valuationSubring := hcompleteBase
  have hcompleteAsBase :
      IsAdicComplete F.maximalIdeal
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring :=
    isAdicComplete_of_linearEquiv
      (M := F.valuationSubring)
      (N := (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring)
      F.maximalIdeal eLin
  have hcompleteMap :
      IsAdicComplete
        (F.maximalIdeal.map
          (algebraMap F.valuationSubring
            (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict
            F).valuationSubring))
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring :=
    (isAdicComplete_map_algebraMap_iff
      (I := F.maximalIdeal)
      (S := (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict
        F).valuationSubring)).2 hcompleteAsBase
  have hmap :
      F.maximalIdeal.map
          (algebraMap F.valuationSubring
            (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict
            F).valuationSubring) =
        IsLocalRing.maximalIdeal
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict
          F).valuationSubring := by
    change
      F.maximalIdeal.map
          (e : F.valuationSubring →+*
            (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict
              F).valuationSubring) =
        IsLocalRing.maximalIdeal
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring
    exact IsLocalRing.map_ringEquiv_maximalIdeal e
  simpa [hmap] using hcompleteMap

/-- The actual multiplicative range of a complete-DVF valuation is generated
by the image of a discrete valuation generator. -/
theorem mrangeRestrict_units_isCyclic
    (F : CompleteDVF.{u, v} K) :
    IsCyclic (MonoidHom.mrange F.valuation.toMonoidWithZeroHom)ˣ := by
  let γ : F.ValueGroupˣ :=
    _root_.Valuation.IsRankOneDiscrete.generator F.valuation
  have hγrange : (γ : F.ValueGroup) ∈ Set.range F.valuation :=
    _root_.Valuation.IsRankOneDiscrete.generator_mem_range K F.valuation
  let γm : MonoidHom.mrange F.valuation.toMonoidWithZeroHom :=
    ⟨(γ : F.ValueGroup), hγrange⟩
  have hγm_ne : γm ≠ 0 := by
    intro hzero
    have hγzero : (γ : F.ValueGroup) = 0 := by
      simpa [γm] using
        congrArg
          (fun z : MonoidHom.mrange
            F.valuation.toMonoidWithZeroHom => (z : F.ValueGroup))
          hzero
    exact Units.ne_zero γ hγzero
  let δ : (MonoidHom.mrange F.valuation.toMonoidWithZeroHom)ˣ :=
    Units.mk0 γm hγm_ne
  have htop : Subgroup.zpowers δ = ⊤ := by
    rw [eq_top_iff]
    intro η _
    have hη_ne : ((η : MonoidHom.mrange
        F.valuation.toMonoidWithZeroHom) : F.ValueGroup) ≠ 0 := by
      intro hzero
      have hηzero :
          (η : MonoidHom.mrange
            F.valuation.toMonoidWithZeroHom) = 0 := by
        ext
        exact hzero
      exact Units.ne_zero η hηzero
    obtain ⟨x, hx⟩ :=
      MonoidHom.mem_mrange.mp
        ((η : MonoidHom.mrange
          F.valuation.toMonoidWithZeroHom).2)
    let ηΓ : F.ValueGroupˣ :=
      Units.mk0
        (((η : MonoidHom.mrange
          F.valuation.toMonoidWithZeroHom) : F.ValueGroup))
        hη_ne
    have hηΓ_mem :
        ηΓ ∈ MonoidWithZeroHom.valueGroup
          (MonoidWithZeroHom.ofClass F.valuation) :=
      MonoidWithZeroHom.mem_valueGroup
        (MonoidWithZeroHom.ofClass F.valuation) ⟨x, hx⟩
    rw [← _root_.Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup
      F.valuation, Subgroup.mem_zpowers_iff] at hηΓ_mem
    rcases hηΓ_mem with ⟨z, hz⟩
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨z, ?_⟩
    let φ :
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom)ˣ →*
          F.ValueGroupˣ :=
      Units.map (MonoidHom.mrange F.valuation.toMonoidWithZeroHom).subtype
    have hsub_inj :
        Function.Injective
          ((MonoidHom.mrange F.valuation.toMonoidWithZeroHom).subtype) := by
      intro a b h
      exact Subtype.ext h
    have hφinj : Function.Injective φ :=
      Units.map_injective hsub_inj
    have hφδ : φ δ = γ := by
      apply Units.ext
      rfl
    have hφη : φ η = ηΓ := by
      apply Units.ext
      rfl
    apply hφinj
    calc
      φ (δ ^ z) = φ δ ^ z := map_zpow φ δ z
      _ = γ ^ z := by rw [hφδ]
      _ = ηΓ := hz
      _ = φ η := hφη.symm
  exact (isCyclic_iff_exists_zpowers_eq_top).2 ⟨δ, htop⟩

/-- The range-restricted valuation is nontrivial whenever the original
complete-DVF valuation is nontrivial. -/
theorem mrangeRestrict_isNontrivial
    (F : CompleteDVF.{u, v} K) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).IsNontrivial := by
  rcases _root_.Valuation.IsNontrivial.exists_val_nontrivial
      (v := F.valuation) with ⟨x, hx0, hx1⟩
  refine ⟨⟨x, ?_, ?_⟩⟩
  · intro hx
    exact hx0 (by
      have h :=
        congrArg
          (fun z : MonoidHom.mrange
            F.valuation.toMonoidWithZeroHom => (z : F.ValueGroup)) hx
      simpa [CompleteDVF.mrangeRestrict, WithZeroValuation.mrangeRestrict] using h)
  · intro hx
    exact hx1 (by
      have h :=
        congrArg
          (fun z : MonoidHom.mrange
            F.valuation.toMonoidWithZeroHom => (z : F.ValueGroup)) hx
      simpa [CompleteDVF.mrangeRestrict, WithZeroValuation.mrangeRestrict] using h)

/-- Restricting a complete-DVF valuation to its actual multiplicative range
preserves rank-one discreteness. -/
theorem mrangeRestrict_isRankOneDiscrete
    (F : CompleteDVF.{u, v} K) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).IsRankOneDiscrete := by
  have :
      IsCyclic
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom)ˣ :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_units_isCyclic F)
  have : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).IsNontrivial :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_isNontrivial F)
  have :
      IsCyclic (MonoidWithZeroHom.valueGroup
        (MonoidWithZeroHom.ofClass
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F))) :=
    Subgroup.isCyclic_of_le (show
      MonoidWithZeroHom.valueGroup
        (MonoidWithZeroHom.ofClass
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F)) ≤
          ⊤ from le_top)
  infer_instance

/-- The range-restricted valuation is rank one as a valuation into its actual
value group. -/
@[implicit_reducible]
noncomputable def mrangeRestrictRankOne
    (F : CompleteDVF.{u, v} K) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).RankOne := by
  haveI : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).IsNontrivial :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_isNontrivial F)
  haveI :
      IsCyclic
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom)ˣ :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_units_isCyclic F)
  exact WithZeroValuation.rankOneOfUnitsIsCyclic
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F)

end CompleteDVF
end LocalFieldTheory.DiscreteValuationField

end
