/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Completion
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.Core
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.FiniteNormExtension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormula
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaAbsoluteValue
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaCoefficients
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaExtension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaIntegralClosure
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.RamificationInvariants
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueExtensionCoefficients
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueValuationSubring
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicLocalization
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Completeness
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.ExponentialValuation
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Extension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Nonarchimedean
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Ostrowski
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.PrincipalAdicCompleteness
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.SpectralExtension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Theory.Core
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.ValuationSubring
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.DegreeNormTrace
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Complete
/-!
# Local degree, ramification, and residue invariants

For a finite separable extension `L / K` and a discrete nonarchimedean
absolute value `v` on `K`, this file proves the exact degree formula
`∑_{w ∣ v} e_w f_w = [L : K]`.

The proof makes explicit the two facts used implicitly in the construction: metric
completion preserves the value group and residue field, and every completed
local extension `L_w / K_v` is finite separable.  The fundamental inequality then gives
`[L_w : K_v] = e_w f_w`; summing and applying the local degree, norm, and trace formulas gives the result.
-/

noncomputable section

open scoped BigOperators

namespace AlgebraicNumberTheory.Valuations

universe u v

private theorem completionNonarchimedean
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK) :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue
      (AbsoluteValue.completionAbsoluteValue vK) :=
  (AbsoluteValue.isNonarchimedean_iff_bounded_nat
    (AbsoluteValue.completionAbsoluteValue vK)).1
    (AbsoluteValue.completionAbsoluteValue_isNonarchimedean vK
      ((AbsoluteValue.isNonarchimedean_iff_bounded_nat vK).2 hv))

theorem mem_absoluteValueExponentialSubring_iff
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a) (x : K) :
    x ∈ LubinTate.Valuations.exponentialValuationSubring
        (absoluteValueExponentialValuation a ha) ↔ a x ≤ 1 := by
  rw [LubinTate.Valuations.mem_exponentialValuationSubring_iff]
  by_cases hx : x = 0
  · subst x
    simp [absoluteValueExponentialValuation]
  · rw [absoluteValueExponentialValuation_apply_ne_zero a ha hx]
    rw [WithTop.coe_nonneg]
    constructor
    · intro h
      by_contra hnot
      have hone : 1 < a x := lt_of_not_ge hnot
      linarith [Real.log_pos hone]
    · intro h
      exact neg_nonneg.mpr (Real.log_nonpos (a.nonneg x) h)

theorem completionExponentialValueSubgroup_eq
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a) :
    exponentialValueSubgroup
        (absoluteValueExponentialValuation
          (AbsoluteValue.completionAbsoluteValue a)
          (completionNonarchimedean a ha)) =
      exponentialValueSubgroup
        (absoluteValueExponentialValuation a ha) := by
  let aC := AbsoluteValue.completionAbsoluteValue a
  let haC := completionNonarchimedean a ha
  let v := absoluteValueExponentialValuation a ha
  let vC := absoluteValueExponentialValuation aC haC
  ext r
  constructor
  · rintro ⟨x, hx, hxr⟩
    have hrange : aC x ∈ Set.range aC := ⟨x, rfl⟩
    have hrange' : aC x ∈ Set.range a := by
      rw [← AbsoluteValue.completionAbsoluteValue_range_eq a
        ((AbsoluteValue.isNonarchimedean_iff_bounded_nat a).2 ha)]
      exact hrange
    obtain ⟨y, hy⟩ := hrange'
    have hy0 : y ≠ 0 := by
      intro hyzero
      subst y
      have : aC x = 0 := by simpa using hy.symm
      exact hx (aC.eq_zero.mp this)
    refine ⟨y, hy0, ?_⟩
    rw [absoluteValueExponentialValuation_apply_ne_zero a ha hy0]
    rw [absoluteValueExponentialValuation_apply_ne_zero aC haC hx] at hxr
    simpa [hy] using hxr
  · rintro ⟨x, hx, hxr⟩
    let xC : a.Completion := algebraMap K a.Completion x
    have hxC : xC ≠ 0 := (algebraMap K a.Completion).injective.ne hx
    refine ⟨xC, hxC, ?_⟩
    rw [absoluteValueExponentialValuation_apply_ne_zero aC haC hxC]
    rw [absoluteValueExponentialValuation_apply_ne_zero a ha hx] at hxr
    rw [show aC xC = a x by
      exact AbsoluteValue.completionAbsoluteValue_coe a x]
    exact hxr

theorem completionRamificationIndex_eq
    {K : Type u} {L : Type v} [Field K] [Field L]
    (a : AbsoluteValue K ℝ) (b : AbsoluteValue L ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a)
    (hb : LubinTate.Valuations.NonarchimedeanAbsoluteValue b) :
    exponentialRamificationIndex
        (absoluteValueExponentialValuation
          (AbsoluteValue.completionAbsoluteValue a)
          (completionNonarchimedean a ha))
        (absoluteValueExponentialValuation
          (AbsoluteValue.completionAbsoluteValue b)
          (completionNonarchimedean b hb)) =
      exponentialRamificationIndex
        (absoluteValueExponentialValuation a ha)
        (absoluteValueExponentialValuation b hb) := by
  unfold exponentialRamificationIndex ExponentialValueGroupQuotient
  rw [completionExponentialValueSubgroup_eq a ha,
    completionExponentialValueSubgroup_eq b hb]

theorem mem_absoluteValueExponentialSubring_maximalIdeal_iff
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a)
    (x : LubinTate.Valuations.exponentialValuationSubring
      (absoluteValueExponentialValuation a ha)) :
    x ∈ IsLocalRing.maximalIdeal
        (LubinTate.Valuations.exponentialValuationSubring
          (absoluteValueExponentialValuation a ha)) ↔
      a (x : K) < 1 := by
  rw [← LubinTate.Valuations.exponentialMaxIdeal_eq_maximalIdeal]
  change (0 : WithTop ℝ) <
      absoluteValueExponentialValuation a ha (x : K) ↔ _
  by_cases hx : (x : K) = 0
  · simp [hx, absoluteValueExponentialValuation]
  · exact (LubinTate.Valuations.associatedAbsoluteValue_lt_one_iff
      (absoluteValueExponentialValuation_associated a ha) hx).symm

/-- The homomorphism from the exponential valuation subring of a field to that
of its completion, induced by the canonical map into the completion. -/
def completionExponentialSubringMap
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a) :
    LubinTate.Valuations.exponentialValuationSubring
        (absoluteValueExponentialValuation a ha) →+*
      LubinTate.Valuations.exponentialValuationSubring
        (absoluteValueExponentialValuation
          (AbsoluteValue.completionAbsoluteValue a)
          (completionNonarchimedean a ha)) :=
  (algebraMap K a.Completion).restrict _ _ fun x hx => by
    rw [mem_absoluteValueExponentialSubring_iff] at hx ⊢
    change AbsoluteValue.completionAbsoluteValue a (x : a.Completion) ≤ 1
    rw [AbsoluteValue.completionAbsoluteValue_coe]
    exact hx

@[simp] theorem completionExponentialSubringMap_apply
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a)
    (x : LubinTate.Valuations.exponentialValuationSubring
      (absoluteValueExponentialValuation a ha)) :
    ((completionExponentialSubringMap a ha x :
      LubinTate.Valuations.exponentialValuationSubring
        (absoluteValueExponentialValuation
          (AbsoluteValue.completionAbsoluteValue a)
          (completionNonarchimedean a ha))) : a.Completion) =
      algebraMap K a.Completion (x : K) := rfl

theorem completionExponentialSubringMap_isLocalHom
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a) :
    IsLocalHom (completionExponentialSubringMap a ha) := by
  constructor
  intro x hx
  rw [LubinTate.Valuations.associatedAbsoluteValue_isUnit_iff_eq_one
    (absoluteValueExponentialValuation_associated a ha)]
  rw [LubinTate.Valuations.associatedAbsoluteValue_isUnit_iff_eq_one
    (absoluteValueExponentialValuation_associated
      (AbsoluteValue.completionAbsoluteValue a)
      (completionNonarchimedean a ha))] at hx
  change AbsoluteValue.completionAbsoluteValue a
      ((x : K) : a.Completion) = 1 at hx
  rw [AbsoluteValue.completionAbsoluteValue_coe] at hx
  exact hx

theorem completionResidueMap_surjective
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a) :
    letI : IsLocalHom (completionExponentialSubringMap a ha) :=
      completionExponentialSubringMap_isLocalHom a ha
    Function.Surjective
      (IsLocalRing.ResidueField.map (completionExponentialSubringMap a ha)) := by
  let v := absoluteValueExponentialValuation a ha
  let aC := AbsoluteValue.completionAbsoluteValue a
  let haC := completionNonarchimedean a ha
  let vC := absoluteValueExponentialValuation aC haC
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let VC := LubinTate.Valuations.exponentialValuationSubring vC
  let f : V →+* VC := completionExponentialSubringMap a ha
  let : IsLocalHom f := completionExponentialSubringMap_isLocalHom a ha
  intro z
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
  let vId : AbsoluteValueExtension a K := ⟨a, fun _ => rfl⟩
  obtain ⟨x, hx⟩ :=
    (AbsoluteValue.denseRange_toCompletion vId.1).exists_dist_lt
      (y : a.Completion) zero_lt_one
  have hclose : aC (algebraMap K a.Completion x - (y : a.Completion)) < 1 := by
    change ‖algebraMap K a.Completion x - (y : a.Completion)‖ < 1
    rw [dist_eq_norm] at hx
    change ‖(y : a.Completion) - algebraMap K a.Completion x‖ < 1 at hx
    simpa only [norm_sub_rev] using hx
  have hy_le : aC (y : a.Completion) ≤ 1 := by
    exact (mem_absoluteValueExponentialSubring_iff aC haC (y : a.Completion)).1 y.property
  have hx_leC : aC (algebraMap K a.Completion x) ≤ 1 := by
    calc
      aC (algebraMap K a.Completion x) =
          aC ((algebraMap K a.Completion x - (y : a.Completion)) + y) := by
            congr 1
            ring
      _ ≤ max (aC (algebraMap K a.Completion x - (y : a.Completion)))
          (aC (y : a.Completion)) :=
        LubinTate.Valuations.strong_triangle_of_nonarchimedean aC haC _ _
      _ ≤ 1 := max_le hclose.le hy_le
  have hx_le : a x ≤ 1 := by
    change aC (x : a.Completion) ≤ 1 at hx_leC
    rwa [AbsoluteValue.completionAbsoluteValue_coe] at hx_leC
  let xV : V := ⟨x, (mem_absoluteValueExponentialSubring_iff a ha x).2 hx_le⟩
  refine ⟨IsLocalRing.residue V xV, ?_⟩
  rw [IsLocalRing.ResidueField.map_residue]
  rw [ValuationTheory.DiscreteValuationField.ResidueField.residue_eq_residue_iff_sub_mem_maximalIdeal]
  rw [mem_absoluteValueExponentialSubring_maximalIdeal_iff aC haC]
  exact hclose

/-- The residue-field equivalence induced by the canonical map from a
nonarchimedean valued field to its completion. -/
noncomputable def completionResidueEquiv
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a) :
    IsLocalRing.ResidueField
        (LubinTate.Valuations.exponentialValuationSubring
          (absoluteValueExponentialValuation a ha)) ≃+*
      IsLocalRing.ResidueField
        (LubinTate.Valuations.exponentialValuationSubring
          (absoluteValueExponentialValuation
            (AbsoluteValue.completionAbsoluteValue a)
            (completionNonarchimedean a ha))) := by
  letI : IsLocalHom (completionExponentialSubringMap a ha) :=
    completionExponentialSubringMap_isLocalHom a ha
  exact ValuationTheory.DiscreteValuationField.ResidueField.ringEquivOfSurjective
    (completionExponentialSubringMap a ha)
    (completionResidueMap_surjective a ha)

@[simp] theorem completionResidueEquiv_residue
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a)
    (x : LubinTate.Valuations.exponentialValuationSubring
      (absoluteValueExponentialValuation a ha)) :
    completionResidueEquiv a ha
        (IsLocalRing.residue _ x) =
      IsLocalRing.residue _ (completionExponentialSubringMap a ha x) := by
  let : IsLocalHom (completionExponentialSubringMap a ha) :=
    completionExponentialSubringMap_isLocalHom a ha
  exact IsLocalRing.ResidueField.map_residue _ _

theorem absoluteValueExtension_nonarchimedean
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (a : AbsoluteValue K ℝ) (b : AbsoluteValue L ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a)
    (hExt : AbsoluteValue.Extends a b) :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue b := by
  rcases ha with ⟨C, hC⟩
  refine ⟨C, fun n => ?_⟩
  simpa only [map_natCast] using (hExt (n : K)).trans_le (hC n)

theorem completionAbsoluteValue_extends_base
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (a : AbsoluteValue K ℝ) (w : AbsoluteValueExtension a L) :
    letI := AbsoluteValue.completionAlgebra a w.1 w.2
    AbsoluteValue.Extends
      (AbsoluteValue.completionAbsoluteValue a)
      (AbsoluteValue.completionAbsoluteValue w.1) := by
  let := AbsoluteValue.completionAlgebra a w.1 w.2
  intro x
  change ‖algebraMap a.Completion w.1.Completion x‖ = ‖x‖
  exact (AbsoluteValue.completionMap_isometry a w.1 w.2).norm_map_of_map_zero
    (map_zero _) x

theorem completionExponentialValuation_discrete
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a)
    (hdisc : LubinTate.Valuations.DiscreteExponentialValuation
      (absoluteValueExponentialValuation a ha)) :
    LubinTate.Valuations.DiscreteExponentialValuation
      (absoluteValueExponentialValuation
        (AbsoluteValue.completionAbsoluteValue a)
        (completionNonarchimedean a ha)) := by
  let aC := AbsoluteValue.completionAbsoluteValue a
  let haC := completionNonarchimedean a ha
  let v := absoluteValueExponentialValuation a ha
  let vC := absoluteValueExponentialValuation aC haC
  rcases hdisc with ⟨s, hs, hvalues, pi, hpival⟩
  have hpi0 : pi ≠ 0 := LubinTate.Valuations.discretePrimeElement_ne_zero_of_value v hpival
  refine ⟨s, hs, ?_, algebraMap K a.Completion pi, ?_⟩
  · intro x hx
    obtain ⟨r, hxr⟩ := LubinTate.Valuations.exponentialValuation_exists_real_of_ne_zero vC hx
    have hrC : r ∈ exponentialValueSubgroup vC := ⟨x, hx, hxr⟩
    have hr : r ∈ exponentialValueSubgroup v := by
      rw [← completionExponentialValueSubgroup_eq a ha]
      exact hrC
    obtain ⟨y, hy, hyr⟩ := hr
    obtain ⟨m, hym⟩ := hvalues y hy
    refine ⟨m, ?_⟩
    exact hxr.trans (hyr.symm.trans hym)
  · have hpiC : (algebraMap K a.Completion pi) ≠ 0 :=
      (algebraMap K a.Completion).injective.ne hpi0
    rw [absoluteValueExponentialValuation_apply_ne_zero aC haC hpiC]
    rw [absoluteValueExponentialValuation_apply_ne_zero a ha hpi0] at hpival
    rw [show aC (algebraMap K a.Completion pi) = a pi by
      change aC (pi : a.Completion) = a pi
      exact AbsoluteValue.completionAbsoluteValue_coe a pi]
    exact hpival

theorem completionExponentialSubringMap_square
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (a : AbsoluteValue K ℝ) (b : AbsoluteValue L ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a)
    (hb : LubinTate.Valuations.NonarchimedeanAbsoluteValue b)
    (hExt : AbsoluteValue.Extends a b) :
    letI := AbsoluteValue.completionAlgebra a b hExt
    let v := absoluteValueExponentialValuation a ha
    let w := absoluteValueExponentialValuation b hb
    let aC := AbsoluteValue.completionAbsoluteValue a
    let bC := AbsoluteValue.completionAbsoluteValue b
    let haC := completionNonarchimedean a ha
    let hbC := completionNonarchimedean b hb
    let vC := absoluteValueExponentialValuation aC haC
    let wC := absoluteValueExponentialValuation bC hbC
    let hvw := absoluteValueExponentialValuation_extends a b ha hb hExt
    let hvwC := absoluteValueExponentialValuation_extends aC bC haC hbC
      (completionAbsoluteValue_extends_base a ⟨b, hExt⟩)
    (completionExponentialSubringMap b hb).comp (exponentialValuationRingMap v w hvw) =
      (exponentialValuationRingMap vC wC hvwC).comp
        (completionExponentialSubringMap a ha) := by
  let := AbsoluteValue.completionAlgebra a b hExt
  apply RingHom.ext
  intro x
  apply Subtype.ext
  change (algebraMap L b.Completion) (algebraMap K L (x : K)) =
    algebraMap a.Completion b.Completion (algebraMap K a.Completion (x : K))
  exact (AbsoluteValue.completionMap_coe a b hExt (x : K)).symm

theorem completionResidueDegree_eq
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (a : AbsoluteValue K ℝ) (b : AbsoluteValue L ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a)
    (hb : LubinTate.Valuations.NonarchimedeanAbsoluteValue b)
    (hExt : AbsoluteValue.Extends a b) :
    letI := AbsoluteValue.completionAlgebra a b hExt
    let v := absoluteValueExponentialValuation a ha
    let w := absoluteValueExponentialValuation b hb
    let aC := AbsoluteValue.completionAbsoluteValue a
    let bC := AbsoluteValue.completionAbsoluteValue b
    let haC := completionNonarchimedean a ha
    let hbC := completionNonarchimedean b hb
    let vC := absoluteValueExponentialValuation aC haC
    let wC := absoluteValueExponentialValuation bC hbC
    let hvw := absoluteValueExponentialValuation_extends a b ha hb hExt
    let hvwC := absoluteValueExponentialValuation_extends aC bC haC hbC
      (completionAbsoluteValue_extends_base a ⟨b, hExt⟩)
    exponentialResidueDegree v w hvw = exponentialResidueDegree vC wC hvwC := by
  let := AbsoluteValue.completionAlgebra a b hExt
  let v := absoluteValueExponentialValuation a ha
  let w := absoluteValueExponentialValuation b hb
  let aC := AbsoluteValue.completionAbsoluteValue a
  let bC := AbsoluteValue.completionAbsoluteValue b
  let haC := completionNonarchimedean a ha
  let hbC := completionNonarchimedean b hb
  let vC := absoluteValueExponentialValuation aC haC
  let wC := absoluteValueExponentialValuation bC hbC
  let hvw := absoluteValueExponentialValuation_extends a b ha hb hExt
  let hvwC := absoluteValueExponentialValuation_extends aC bC haC hbC
    (completionAbsoluteValue_extends_base a ⟨b, hExt⟩)
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let VC := LubinTate.Valuations.exponentialValuationSubring vC
  let WC := LubinTate.Valuations.exponentialValuationSubring wC
  let i := exponentialValuationRingMap v w hvw
  let iC := exponentialValuationRingMap vC wC hvwC
  let cv := completionExponentialSubringMap a ha
  let cw := completionExponentialSubringMap b hb
  let : IsLocalHom i := exponentialValuationRingMap_isLocalHom v w hvw
  let : IsLocalHom iC := exponentialValuationRingMap_isLocalHom vC wC hvwC
  let : IsLocalHom cv := completionExponentialSubringMap_isLocalHom a ha
  let : IsLocalHom cw := completionExponentialSubringMap_isLocalHom b hb
  let : Algebra V W := i.toAlgebra
  let : Algebra VC WC := iC.toAlgebra
  let ev := completionResidueEquiv a ha
  let ew := completionResidueEquiv b hb
  change Module.finrank (IsLocalRing.ResidueField V)
      (IsLocalRing.ResidueField W) =
    Module.finrank (IsLocalRing.ResidueField VC)
      (IsLocalRing.ResidueField WC)
  apply Algebra.finrank_eq_of_equiv_equiv ev ew
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
  change IsLocalRing.residue WC (iC (cv x)) =
    IsLocalRing.residue WC (cw (i x))
  have hsquare := DFunLike.congr_fun
    (completionExponentialSubringMap_square a b ha hb hExt) x
  exact congrArg (IsLocalRing.residue WC) hsquare.symm

theorem completionExtension_isSeparable
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (a : AbsoluteValue K ℝ) (ha : a.IsNontrivial)
    (w : AbsoluteValueExtension a L) :
    letI := AbsoluteValue.completionAlgebra a w.1 w.2
    Algebra.IsSeparable a.Completion w.1.Completion := by
  let pb := completionTensorDecomposition_powerBasis K L
  let α : L := pb.gen
  let hα : IsIntegral K α := pb.isIntegral_gen
  let hgen : Algebra.adjoin K ({α} : Set L) = ⊤ := pb.adjoin_gen_eq_top
  let τ := absoluteValueExtension_embeddingOfExtension a w
  let hτ := absoluteValueExtension_extension_eq_pullback_embeddingOfExtension a ha w
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra a w.1 w.2
  let : IsScalarTower K a.Completion w.1.Completion :=
    AbsoluteValue.completion_isScalarTower a w.1 w.2
  have hsepMapped :
      ((minpoly K α).map (algebraMap K a.Completion)).Separable :=
    Polynomial.Separable.map
      (Algebra.IsSeparable.isSeparable K α)
  have hdvd : minpoly a.Completion (τ α) ∣
      (minpoly K α).map (algebraMap K a.Completion) := by
    let g := completionExtensionFactor_extensionToFactor a
      (minpoly.irreducible hα) (minpoly.aeval K α) w
    have hgdvd := (completionExtensionFactor_factor_irreducible_monic_dvd_minpoly a
      (minpoly.irreducible hα) (minpoly.aeval K α) g).2.2
    rw [completionExtensionFactor_embeddingOfExtension_minpoly a α w]
    simpa [g, completionExtensionFactor_extensionToFactor] using hgdvd
  have hτα : IsSeparable a.Completion (τ α) :=
    hsepMapped.of_dvd hdvd
  let E := IntermediateField.adjoin a.Completion
    ({τ α} : Set (absoluteValueExtension_algebraicCompletionClosure a))
  have hEsep : Algebra.IsSeparable a.Completion E :=
    Iff.mpr (IntermediateField.isSeparable_adjoin_iff_isSeparable
      a.Completion (absoluteValueExtension_algebraicCompletionClosure a)) (by
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      exact hτα)
  let : Algebra.IsSeparable a.Completion E := hEsep
  exact AlgEquiv.Algebra.isSeparable
    (completionExtensionFactor_completionEquivSimpleRoot
      a ha α hα hgen w τ hτ).symm

theorem completionExtensionInvariants_local_identity
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (a : AbsoluteValue K ℝ) (ha0 : a.IsNontrivial)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a)
    (hdisc : LubinTate.Valuations.DiscreteExponentialValuation
      (absoluteValueExponentialValuation a ha))
    (w : AbsoluteValueExtension a L) :
    let hb := absoluteValueExtension_nonarchimedean a w.1 ha w.2
    let v := absoluteValueExponentialValuation a ha
    let wv := absoluteValueExponentialValuation w.1 hb
    let hvw := absoluteValueExponentialValuation_extends
      a w.1 ha hb w.2
    letI := AbsoluteValue.completionAlgebra a w.1 w.2
    Module.finrank a.Completion w.1.Completion =
      exponentialRamificationIndex v wv * exponentialResidueDegree v wv hvw := by
  let hb := absoluteValueExtension_nonarchimedean a w.1 ha w.2
  let v := absoluteValueExponentialValuation a ha
  let wv := absoluteValueExponentialValuation w.1 hb
  let hvw := absoluteValueExponentialValuation_extends
    a w.1 ha hb w.2
  let aC := AbsoluteValue.completionAbsoluteValue a
  let bC := AbsoluteValue.completionAbsoluteValue w.1
  let haC := completionNonarchimedean a ha
  let hbC := completionNonarchimedean w.1 hb
  let vC := absoluteValueExponentialValuation aC haC
  let wC := absoluteValueExponentialValuation bC hbC
  let := AbsoluteValue.completionAlgebra a w.1 w.2
  let hvwC := absoluteValueExponentialValuation_extends
    aC bC haC hbC (completionAbsoluteValue_extends_base a w)
  let : Module.Finite a.Completion w.1.Completion :=
    completionModuleFinite a ha0 w
  let : Algebra.IsSeparable a.Completion w.1.Completion :=
    completionExtension_isSeparable a ha0 w
  have hhensC : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vC).valuation := by
    rw [associatedAbsoluteValue_valuationSubring_eq
      vC (Real.exp 1) aC haC
        (absoluteValueExponentialValuation_associated aC haC)]
    exact henselianValuation_of_complete aC
      ((absoluteValueCompleteness_completeSpace_withAbs_iff_complete _).1
        (AbsoluteValue.completionAbsoluteValue_complete a))
      haC
  have hlocal :=
    ramificationInvariants_fundamental_identity_of_discrete_of_separable
      vC wC hvwC (completionExponentialValuation_discrete a ha hdisc) hhensC
  calc
    Module.finrank a.Completion w.1.Completion =
        exponentialRamificationIndex vC wC * exponentialResidueDegree vC wC hvwC := hlocal
    _ = exponentialRamificationIndex v wv * exponentialResidueDegree v wv hvw := by
      rw [completionRamificationIndex_eq a w.1 ha hb,
        ← completionResidueDegree_eq a w.1 ha hb w.2]

theorem absoluteValue_isNontrivial_of_discrete
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a)
    (hdisc : LubinTate.Valuations.DiscreteExponentialValuation
      (absoluteValueExponentialValuation a ha)) :
    a.IsNontrivial := by
  let v := absoluteValueExponentialValuation a ha
  rcases hdisc with ⟨s, hs, _hvalues, pi, hpival⟩
  have hpi0 : pi ≠ 0 := LubinTate.Valuations.discretePrimeElement_ne_zero_of_value v hpival
  refine ⟨pi, hpi0, ?_⟩
  intro hpi
  have hvpi0 : v pi = 0 := by
    rw [absoluteValueExponentialValuation_apply_ne_zero a ha hpi0,
      hpi, Real.log_one]
    norm_num
  rw [hvpi0] at hpival
  have hs0 : s = 0 := by
    apply WithTop.coe_eq_coe.mp
    simpa using hpival.symm
  exact (ne_of_gt hs) hs0

/-- **the local ramification identity.**  For a discrete valuation and a finite separable
extension, the sum of the ramification indices times residue degrees over all
extensions of the valuation is the global degree. -/
theorem completionExtensionInvariants
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a)
    (hdisc : LubinTate.Valuations.DiscreteExponentialValuation
      (absoluteValueExponentialValuation a ha)) :
    let ha0 := absoluteValue_isNontrivial_of_discrete a ha hdisc
    letI := completionTensorDecomposition_extensionFintype (K := K) (L := L) a ha0
    (∑ w : AbsoluteValueExtension a L,
      let hw := absoluteValueExtension_nonarchimedean a w.1 ha w.2
      let va := absoluteValueExponentialValuation a ha
      let vw := absoluteValueExponentialValuation w.1 hw
      let hvw := absoluteValueExponentialValuation_extends
        a w.1 ha hw w.2
      exponentialRamificationIndex va vw * exponentialResidueDegree va vw hvw) =
        Module.finrank K L := by
  let ha0 := absoluteValue_isNontrivial_of_discrete a ha hdisc
  let := completionTensorDecomposition_extensionFintype (K := K) (L := L) a ha0
  rw [completionDegreeNormTrace_degree (K := K) (L := L) a ha0]
  apply Finset.sum_congr rfl
  intro w _hw
  exact (completionExtensionInvariants_local_identity a ha0 ha hdisc w).symm


end AlgebraicNumberTheory.Valuations
