/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.UniformizerGradedHom
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.CharacterMap
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.CompleteDVF
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.RamificationCharacterization
/-!
# Comparing first principal units in the two ramification conventions

The DVF filtration uses units of the valuation ring, whereas Hilbert's
ramification group uses the principal-unit subgroup of the field units.
This file identifies their first levels before comparing group actions.
-/

noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification

open ValuationTheory.DiscreteValuationField

variable {L : Type u} [Field L]

/-- A valuation-ring unit belongs to the first DVF principal-unit group
exactly when its image among field units is principal in Hilbert's sense. -/
theorem mem_dvfHigherPrincipalUnitGroup_one_iff_principalUnitGroup
    (target : DVF.{u, v} L) (a : target.valuationSubringˣ) :
    a ∈ Higher.dvfHigherPrincipalUnitGroup target 1 ↔
      ((target.valuation.valuationSubring.unitGroupMulEquiv.symm a :
        target.valuation.valuationSubring.unitGroup) : Lˣ) ∈
          target.valuation.valuationSubring.principalUnitGroup := by
  rw [Higher.mem_dvfHigherPrincipalUnitGroup_iff, pow_one,
    target.mem_maximalIdeal_iff,
    target.valuation.valuationSubring.mem_principalUnitGroup_iff]
  simpa using
    (_root_.Valuation.isEquiv_valuation_valuationSubring
      target.valuation).lt_one_iff_lt_one
        (x := (((a : target.valuationSubring) : L) - 1))

/-- The DVF unit `σ(π)/π` and Hilbert's field-unit quotient are the same
after the canonical embedding of valuation-ring units into field units. -/
theorem coe_dvfUniformizerQuotientUnit_eq_automorphismUnitQuotient
    {K : Type w} [Field K] [Algebra K L]
    {base : DVF.{w, x} K} {target : DVF.{u, v} L}
    [base.valuation.HasExtension target.valuation]
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{w, x, u, v, v}
        base target)
    (pi : target.valuationSubring)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (sigma : ValuationSubring.decompositionGroup K
      target.valuation.valuationSubring) :
    ((target.valuation.valuationSubring.unitGroupMulEquiv.symm
        (Higher.dvfUniformizerQuotientUnit
          (base := base) (target := target) huniq pi hpi
          (sigma : Gal(L/K))) :
        target.valuation.valuationSubring.unitGroup) : Lˣ) =
      ValuationSubring.automorphismUnitQuotient K
        target.valuation.valuationSubring sigma
        (Units.mk0 (pi : L) hpi.ne_zero) := by
  let q := Higher.dvfUniformizerQuotientUnit
    (base := base) (target := target) huniq pi hpi (sigma : Gal(L/K))
  have hq : (sigma : L ≃ₐ[K] L) (pi : L) =
      ((q : target.valuationSubring) : L) * (pi : L) := by
    have h := Higher.dvfUniformizerQuotientUnit_mul_uniformizer
      (base := base) (target := target) huniq pi hpi (sigma : Gal(L/K))
    have h' := congrArg (fun z : target.valuationSubring => (z : L)) h
    simpa [q] using h'
  apply Units.ext
  rw [_root_.ValuationSubring.coe_unitGroupMulEquiv_symm_apply]
  simp only [ValuationSubring.automorphismUnitQuotient,
    Units.val_div_eq_div_val, Units.val_mk0]
  change ((q : target.valuationSubring) : L) =
    (sigma : L ≃ₐ[K] L) (pi : L) / (pi : L)
  exact (eq_div_iff hpi.ne_zero).2 hq.symm

/-- For an inertia element of a discretely valued field, Hilbert's
principal-unit condition on every field unit is determined by one
uniformizer. -/
theorem inertia_forall_automorphismUnitQuotient_mem_principal_iff_uniformizer
    {K : Type w} [Field K] [Algebra K L]
    (target : DVF.{u, v} L)
    (pi : target.valuationSubring)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (sigma : ValuationSubring.inertiaGroup K
      target.valuation.valuationSubring) :
    (∀ y : Lˣ,
      ValuationSubring.automorphismUnitQuotient K
        target.valuation.valuationSubring
        (sigma : ValuationSubring.decompositionGroup K
          target.valuation.valuationSubring) y ∈
        target.valuation.valuationSubring.principalUnitGroup) ↔
      ValuationSubring.automorphismUnitQuotient K
        target.valuation.valuationSubring
        (sigma : ValuationSubring.decompositionGroup K
          target.valuation.valuationSubring)
        (Units.mk0 (pi : L) hpi.ne_zero) ∈
          target.valuation.valuationSubring.principalUnitGroup := by
  let A := target.valuation.valuationSubring
  let piUnit : Lˣ := Units.mk0 (pi : L) hpi.ne_zero
  let qHom : Lˣ →* Lˣ :=
    { toFun := ValuationSubring.automorphismUnitQuotient K A
        (sigma : ValuationSubring.decompositionGroup K A)
      map_one' := ValuationSubring.automorphismUnitQuotient_one_arg
        (K := K) A (sigma : ValuationSubring.decompositionGroup K A)
      map_mul' := ValuationSubring.automorphismUnitQuotient_mul_arg
        (K := K) A (sigma : ValuationSubring.decompositionGroup K A) }
  let S : Subgroup Lˣ := A.principalUnitGroup.comap qHom
  constructor
  · intro h
    exact h piUnit
  · intro hpiPrincipal y
    have hpiS : piUnit ∈ S := hpiPrincipal
    have hunit (z : A.unitGroup) : (z : Lˣ) ∈ S :=
      ValuationSubring.inertia_automorphismUnitQuotient_mem_principalUnitGroup_of_mem_unitGroup
        (K := K) A sigma z.property
    have hintegral (z : Lˣ) (hz : (z : L) ∈ A) : z ∈ S := by
      let r : A := ⟨(z : L), hz⟩
      have hr : r ≠ 0 := by
        intro hr0
        apply z.ne_zero
        exact congrArg (fun a : A => (a : L)) hr0
      rcases _root_.Valuation.exists_pow_Uniformizer
          (v := target.valuation) hr ⟨pi, hpi⟩ with ⟨n, unit, hfactor⟩
      let unitField : A.unitGroup := A.unitGroupMulEquiv.symm unit
      have hzfactor : z = piUnit ^ n * (unitField : Lˣ) := by
        apply Units.ext
        simpa [r, piUnit, unitField] using hfactor
      rw [hzfactor]
      exact S.mul_mem (S.pow_mem hpiS n) (hunit unitField)
    rcases A.mem_or_inv_mem (y : L) with hy | hy
    · exact hintegral y hy
    · have hyinv : y⁻¹ ∈ S := hintegral y⁻¹ (by simpa using hy)
      have hyS : y ∈ S := by simpa only [inv_inv] using S.inv_mem hyinv
      exact hyS

/-- The zeroth lower group is the inertia group for a finite separable
extension of complete DVFs, under the canonical identification of the
Galois and decomposition groups. -/
theorem mem_lowerRamificationGroup_zero_iff_completeDVF_inertiaGroup
    {K : Type w} [Field K] [Algebra K L]
    (base : CompleteDVF.{w, x} K) (target : CompleteDVF.{u, v} L)
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [base.valuation.HasExtension target.valuation]
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{w, x, u, v, v}
        base.toDVF target.toDVF)
    (sigma : Gal(L/K)) :
    sigma ∈ Higher.lowerRamificationGroup
        (base := base.toDVF) (target := target.toDVF) huniq (0 : ℝ) ↔
      sigma ∈ CompleteDVF.inertiaGroup (base := base) (target := target) := by
  have hact (a : target.valuationSubring) :
      Higher.valuationSubringAutOfUniqueExtension
          (base := base.toDVF) (target := target.toDVF) huniq sigma a =
        (CompleteDVF.galEquivDecompositionGroup
          (base := base) (target := target) sigma) • a := by
    apply Subtype.ext
    rfl
  have hG0 :
      sigma ∈ Higher.lowerRamificationGroup
          (base := base.toDVF) (target := target.toDVF) huniq (0 : ℝ) ↔
        ∀ a : target.valuationSubring,
          Higher.valuationSubringAutOfUniqueExtension
              (base := base.toDVF) (target := target.toDVF) huniq sigma a - a ∈
            target.maximalIdeal := by
    simpa only [Nat.cast_zero, zero_add, pow_one] using
      (Higher.mem_lowerRamificationGroup_nat_iff
        (base := base.toDVF) (target := target.toDVF) huniq 0 sigma)
  rw [hG0, CompleteDVF.mem_inertiaGroup_iff
      (base := base) (target := target) sigma,
    ← CompleteDVF.maximalIdealInertia_eq_decompositionInertia
      (K := K) (target := target),
    AddSubgroup.mem_inertia]
  simp only [hact, Submodule.mem_toAddSubgroup]

/-- Under separable residue extension, the uniformizer quotient detects the
first lower ramification subgroup inside the zeroth one. -/
theorem mem_lowerRamificationGroup_one_of_uniformizerQuotient_mem
    {K : Type w} [Field K] [Algebra K L]
    {base : DVF.{w, x} K} {target : DVF.{u, v} L}
    [FiniteDimensional K L] [IsGalois K L]
    [base.valuation.HasExtension target.valuation]
    [Algebra.IsSeparable base.residueField target.residueField]
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{w, x, u, v, v}
        base target)
    (pi : target.valuationSubring)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (sigma : Gal(L/K))
    (hzero : sigma ∈ Higher.lowerRamificationGroup
      (base := base) (target := target) huniq (0 : ℝ))
    (hpiUnit : Higher.dvfUniformizerQuotientUnit
        (base := base) (target := target) huniq pi hpi sigma ∈
      Higher.dvfHigherPrincipalUnitGroup target 1) :
    sigma ∈ Higher.lowerRamificationGroup
      (base := base) (target := target) huniq (1 : ℝ) := by
  let sigmaZero : Higher.lowerRamificationGroup
      (base := base) (target := target) huniq ((0 : ℕ) : ℝ) :=
    ⟨sigma, by simpa only [Nat.cast_zero] using hzero⟩
  have hgraded :
      Higher.uniformizerGradedHom
          (base := base) (target := target) huniq pi hpi 0
          (QuotientGroup.mk' _ sigmaZero) = 1 :=
    (Higher.uniformizerGradedHom_mk_eq_one_iff
      (base := base) (target := target) huniq pi hpi 0 sigmaZero).2
        (by simpa only [zero_add] using hpiUnit)
  have hinj := Higher.uniformizerGradedHom_injective_of_residue_isSeparable
    (base := base) (target := target) huniq pi hpi 0
  have hone :
      (QuotientGroup.mk' _ sigmaZero :
        Higher.lowerRamificationGradedPiece
          (base := base) (target := target) huniq 0) = 1 := by
    apply hinj
    simpa using hgraded
  have hnext :=
    (QuotientGroup.eq_one_iff
      (N := (Higher.lowerRamificationGroup
          (base := base) (target := target) huniq ((0 + 1 : ℕ) : ℝ)).subgroupOf
        (Higher.lowerRamificationGroup
          (base := base) (target := target) huniq ((0 : ℕ) : ℝ)))
      sigmaZero).1 hone
  change sigma ∈ Higher.lowerRamificationGroup
    (base := base) (target := target) huniq ((0 + 1 : ℕ) : ℝ) at hnext
  simpa only [zero_add, Nat.cast_one] using hnext

/-- For a finite Galois extension of complete DVFs with separable residue
extension, the first lower ramification group is Hilbert's ramification
group, transported from the decomposition group to the full Galois group. -/
theorem lowerRamificationGroup_one_eq_hilbertRamificationGroup
    {K : Type w} [Field K] [Algebra K L]
    (base : CompleteDVF.{w, x} K) (target : CompleteDVF.{u, v} L)
    [FiniteDimensional K L] [IsGalois K L] [Algebra.IsSeparable K L]
    [base.valuation.HasExtension target.valuation]
    [Algebra.IsSeparable base.residueField target.residueField]
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{w, x, u, v, v}
        base.toDVF target.toDVF) :
    Higher.lowerRamificationGroup
        (base := base.toDVF) (target := target.toDVF) huniq (1 : ℝ) =
      Subgroup.comap
        (CompleteDVF.galEquivDecompositionGroup
          (base := base) (target := target)).toMonoidHom
        (ValuationSubring.ramificationGroupInDecomposition K
          target.valuation.valuationSubring) := by
  let A := target.valuation.valuationSubring
  obtain ⟨pi, hpi⟩ := target.exists_uniformizer
  ext sigma
  let dSigma : ValuationSubring.decompositionGroup K A :=
    CompleteDVF.galEquivDecompositionGroup
      (base := base) (target := target) sigma
  change sigma ∈ Higher.lowerRamificationGroup
      (base := base.toDVF) (target := target.toDVF) huniq (1 : ℝ) ↔
    dSigma ∈ ValuationSubring.ramificationGroupInDecomposition K A
  rw [ValuationSubring.mem_ramificationGroupInDecomposition_iff]
  constructor
  · intro hOne
    have hZero : sigma ∈ Higher.lowerRamificationGroup
        (base := base.toDVF) (target := target.toDVF) huniq (0 : ℝ) :=
      (Higher.lowerRamificationGroup_antitone
        (base := base.toDVF) (target := target.toDVF) huniq
        (show (0 : ℝ) ≤ 1 by norm_num)) hOne
    have hInertia : dSigma ∈ ValuationSubring.inertiaGroup K A :=
      (CompleteDVF.mem_inertiaGroup_iff
        (base := base) (target := target) sigma).mp
        ((mem_lowerRamificationGroup_zero_iff_completeDVF_inertiaGroup
          (base := base) (target := target) huniq sigma).mp hZero)
    let iSigma : ValuationSubring.inertiaGroup K A := ⟨dSigma, hInertia⟩
    have hUone : Higher.dvfUniformizerQuotientUnit
        (base := base.toDVF) (target := target.toDVF) huniq pi hpi sigma ∈
        Higher.dvfHigherPrincipalUnitGroup target.toDVF 1 :=
      Higher.dvfUniformizerQuotientUnit_mem_of_mem_lowerRamificationGroup
        (base := base.toDVF) (target := target.toDVF) huniq hpi
        (by simpa only [Nat.cast_one] using hOne)
    have hPiPrincipal :
        ValuationSubring.automorphismUnitQuotient K A dSigma
          (Units.mk0 (pi : L) hpi.ne_zero) ∈ A.principalUnitGroup := by
      rw [← coe_dvfUniformizerQuotientUnit_eq_automorphismUnitQuotient
        (base := base.toDVF) (target := target.toDVF) huniq pi hpi dSigma]
      exact (mem_dvfHigherPrincipalUnitGroup_one_iff_principalUnitGroup
        target.toDVF _).mp (by simpa [dSigma] using hUone)
    exact (inertia_forall_automorphismUnitQuotient_mem_principal_iff_uniformizer
      (K := K) target.toDVF pi hpi iSigma).mpr hPiPrincipal
  · intro hAll
    have hInertia : dSigma ∈ ValuationSubring.inertiaGroup K A :=
      ValuationSubring.ramificationCondition_mem_inertiaGroup
        (K := K) A dSigma hAll
    have hZero : sigma ∈ Higher.lowerRamificationGroup
        (base := base.toDVF) (target := target.toDVF) huniq (0 : ℝ) :=
      (mem_lowerRamificationGroup_zero_iff_completeDVF_inertiaGroup
        (base := base) (target := target) huniq sigma).mpr
        ((CompleteDVF.mem_inertiaGroup_iff
          (base := base) (target := target) sigma).mpr hInertia)
    have hPiPrincipal :
        ((A.unitGroupMulEquiv.symm
          (Higher.dvfUniformizerQuotientUnit
            (base := base.toDVF) (target := target.toDVF)
            huniq pi hpi (dSigma : Gal(L/K))) : A.unitGroup) : Lˣ) ∈
          A.principalUnitGroup := by
      rw [coe_dvfUniformizerQuotientUnit_eq_automorphismUnitQuotient
        (base := base.toDVF) (target := target.toDVF) huniq pi hpi dSigma]
      exact hAll (Units.mk0 (pi : L) hpi.ne_zero)
    have hUone : Higher.dvfUniformizerQuotientUnit
        (base := base.toDVF) (target := target.toDVF) huniq pi hpi sigma ∈
        Higher.dvfHigherPrincipalUnitGroup target.toDVF 1 := by
      have h := (mem_dvfHigherPrincipalUnitGroup_one_iff_principalUnitGroup
        target.toDVF _).mpr hPiPrincipal
      simpa [dSigma] using h
    exact mem_lowerRamificationGroup_one_of_uniformizerQuotient_mem
      (base := base.toDVF) (target := target.toDVF)
      huniq pi hpi sigma hZero hUone

end RamificationTheory.HilbertRamification
