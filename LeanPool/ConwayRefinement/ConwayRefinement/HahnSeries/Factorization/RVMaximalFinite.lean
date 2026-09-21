/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Divisibility.MaximalDivisor
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringTensor

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.MaximalFinite

/-!
# Maximal finite-support divisors in RV

This module works with the actual multiplicative RV quotient attached to Hahn-series degree. It
defines the finite-support embedding into RV and proves that divisibility in RV agrees with the
fixed-component divisibility used by the tensor-content construction.

Consequently every RV class has a unique intrinsic maximal finite-support divisor in
`Associates K(ℝ^{≤ 0})`, assuming only pairwise gcd existence in the finite-support ring. This
is the associate-class form of LM24, Proposition 5.4.3. In particular, the source statement is
not silently replaced by divisibility in the full associated graded ring.
-/

open scoped DirectSum HahnSeries NatOrdinal

universe v

namespace Berarducci

public noncomputable section

open HahnSeries.Nonpositive

variable {K : Type v} [Field K] [CharZero K]

private theorem directSum_index_eq_of_of_eq {ι : Type*} [DecidableEq ι]
    {A : ι → Type*} [∀ i, AddCommMonoid (A i)]
    {i j : ι} {x : A i} {y : A j}
    (hx : x ≠ 0) (h : DirectSum.of A i x = DirectSum.of A j y) : i = j := by
  by_contra hij
  have hvalue := congrArg (fun z : DirectSum ι A ↦ z i) h
  rw [DirectSum.of_eq_same,
    DirectSum.of_eq_of_ne j i y hij] at hvalue
  exact hx hvalue

variable (K) in
/-- The RV monoid attached to the multiplicative Hahn-series degree valuation. -/
abbrev HahnDegreeRV :=
  (HahnSeries.Nonpositive.degreeValuation K).RV

variable (K) in
/-- The finite-support ring embeds multiplicatively into degree RV. -/
def finiteSupportRVEmbedding :
    FiniteSupportRing (K := K) →*₀ HahnDegreeRV K where
  toFun p :=
    (HahnSeries.Nonpositive.degreeValuation K).rv (p : Series K)
  map_one' := map_one _
  map_mul' p q := by
    change (HahnSeries.Nonpositive.degreeValuation K).rv
        ((p : Series K) * (q : Series K)) = _
    rw [map_mul]
  map_zero' :=
    (HahnSeries.Nonpositive.degreeValuation K).rv_zero

/-- The finite-support RV embedding is the RV quotient map on the underlying Hahn series. -/
@[simp]
theorem finiteSupportRVEmbedding_apply (p : FiniteSupportRing (K := K)) :
    finiteSupportRVEmbedding K p =
      (HahnSeries.Nonpositive.degreeValuation K).rv (p : Series K) :=
  (rfl)

/-- Under the RV/homogeneous equivalence, the finite-support RV embedding agrees with the
grade-zero embedding into the associated graded ring. -/
theorem coe_rvEquivHomogeneous_finiteSupportRVEmbedding (p : FiniteSupportRing (K := K)) :
    (((HahnSeries.Nonpositive.degreeValuation K).rvEquivHomogeneous
        (finiteSupportRVEmbedding K p) :
          (HahnSeries.Nonpositive.degreeValuation K).HomogeneousClasses) :
      DegreeGraded K) =
        finiteSupportGradedEmbedding K p := by
  rw [finiteSupportRVEmbedding_apply]
  rw [coe_rvEquivHomogeneous_rv_eq_residueRingHom_finiteSupportResidueEquiv
      (w := HahnSeries.Nonpositive.degreeValuation K)
      (HahnSeries.Nonpositive.degreeValuation_apply) p]
  rw [(HahnSeries.Nonpositive.degreeValuation K).residueRingHom_apply,
    finiteSupportGradedEmbedding_apply,
    degreeFiniteSupportResidueEquiv_apply,
    finiteSupportResidueEquiv_apply]

variable (K) in
/-- The finite-support embedding into degree RV is injective. -/
theorem finiteSupportRVEmbedding_injective :
    Function.Injective (finiteSupportRVEmbedding K) := by
  intro p q hpq
  apply finiteSupportGradedEmbedding_injective K
  rw [← coe_rvEquivHomogeneous_finiteSupportRVEmbedding p,
    ← coe_rvEquivHomogeneous_finiteSupportRVEmbedding q,
    hpq]

/-- The homogeneous graded class corresponding to the RV class of a finite-support series. -/
def finiteSupportHomogeneousClass (p : FiniteSupportRing (K := K)) :
    (HahnSeries.Nonpositive.degreeValuation K).HomogeneousClasses :=
  (HahnSeries.Nonpositive.degreeValuation K).rvHomogeneous
    (finiteSupportRVEmbedding K p)

/-- Evaluation of the finite-support homogeneous class. -/
@[simp]
theorem finiteSupportHomogeneousClass_apply (p : FiniteSupportRing (K := K)) :
    finiteSupportHomogeneousClass p =
      (HahnSeries.Nonpositive.degreeValuation K).rvHomogeneous
        (finiteSupportRVEmbedding K p) :=
  (rfl)

/-- The finite-support homogeneous class has the expected grade-zero image. -/
theorem coe_finiteSupportHomogeneousClass (p : FiniteSupportRing (K := K)) :
    (finiteSupportHomogeneousClass p :
      DegreeGraded K) =
        finiteSupportGradedEmbedding K p :=
  by
    rw [finiteSupportHomogeneousClass_apply,
      ← (HahnSeries.Nonpositive.degreeValuation K).rvEquivHomogeneous_apply]
    exact coe_rvEquivHomogeneous_finiteSupportRVEmbedding p

/-- A fixed component, regarded as an element of the monoid of homogeneous graded classes. -/
def degreeHomogeneousClass (α : NatOrdinal)
    (B : (HahnSeries.Nonpositive.degreeValuation K).Component α) :
    (HahnSeries.Nonpositive.degreeValuation K).HomogeneousClasses :=
  ⟨DirectSum.of
      (HahnSeries.Nonpositive.degreeValuation K).Component α B,
    (MaxAddDegree.mem_homogeneousClasses_iff
      (HahnSeries.Nonpositive.degreeValuation K) _).mpr
        (Or.inr ⟨α, B, rfl⟩)⟩

omit [CharZero K] in
/-- The underlying graded element of a fixed homogeneous class. -/
@[simp]
theorem coe_degreeHomogeneousClass (α : NatOrdinal)
    (B : (HahnSeries.Nonpositive.degreeValuation K).Component α) :
    (degreeHomogeneousClass α B : DegreeGraded K) =
      DirectSum.of
        (HahnSeries.Nonpositive.degreeValuation K).Component α B :=
  (rfl)

/-- Multiplication of a finite-support homogeneous class with a fixed homogeneous class is the
degree-zero residue action on that component. -/
theorem finiteSupportHomogeneousClass_mul_degreeHomogeneousClass
    (q : FiniteSupportRing (K := K)) (α : NatOrdinal)
    (C : (HahnSeries.Nonpositive.degreeValuation K).Component α) :
    finiteSupportHomogeneousClass q * degreeHomogeneousClass α C =
      degreeHomogeneousClass α
        (HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv K q • C) := by
  apply Subtype.ext
  rw [Submonoid.coe_mul,
    coe_finiteSupportHomogeneousClass,
    coe_degreeHomogeneousClass,
    coe_degreeHomogeneousClass]
  exact finiteSupportGradedEmbedding_mul_of q α C

/-- The RV class of a series of exact degree `α` corresponds to its class in the degree-`α`
homogeneous component. -/
theorem rvEquivHomogeneous_rv_eq_degreeHomogeneousClass (α : NatOrdinal) (p : Series K)
    (hpDegree : (p : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal)) :
    (HahnSeries.Nonpositive.degreeValuation K).rvEquivHomogeneous
        ((HahnSeries.Nonpositive.degreeValuation K).rv p) =
      degreeHomogeneousClass α
        (degreeLayerMk α p hpDegree.le) := by
  let w := HahnSeries.Nonpositive.degreeValuation K
  let pLE : w.filtrationLE α :=
    ⟨p, (w.mem_filtrationLE_iff α p).mpr (by
      rw [HahnSeries.Nonpositive.degreeValuation_apply, hpDegree])⟩
  have hpComponent : w.componentMk α pLE ≠ 0 := by
    intro hzero
    have hlt := (w.componentMk_eq_zero_iff α pLE).mp hzero
    rw [HahnSeries.Nonpositive.degreeValuation_apply, hpDegree] at hlt
    exact lt_irrefl _ hlt
  apply Subtype.ext
  rw [w.rvEquivHomogeneous_apply, w.coe_rvHomogeneous, w.rvInitialFormHom_rv]
  calc
    w.initialForm p = w.homogeneousMk α pLE :=
      w.initialForm_eq_homogeneousMk_of_componentMk_ne_zero α pLE hpComponent
    _ = DirectSum.of w.Component α (w.componentMk α pLE) :=
      w.homogeneousMk_apply α pLE
    _ = DirectSum.of w.Component α (degreeLayerMk α p hpDegree.le) := by
      apply congrArg (DirectSum.of w.Component α)
      exact (degreeLayerMk_eq_componentMk α p hpDegree.le).symm

/-- LM24, Definition 5.2.1: an RV class is principal when it has a principal Hahn-series
representative. Zero is deliberately excluded because principal series are nonzero. -/
def IsPrincipalRV (B : HahnDegreeRV K) : Prop :=
  ∃ p : Series K, HahnSeries.Nonpositive.IsPrincipal p ∧
    B = (HahnSeries.Nonpositive.degreeValuation K).rv p

/-- Characterization of a principal RV class by a principal representative. -/
theorem isPrincipalRV_iff (B : HahnDegreeRV K) :
    IsPrincipalRV B ↔
      ∃ p : Series K, HahnSeries.Nonpositive.IsPrincipal p ∧
        B = (HahnSeries.Nonpositive.degreeValuation K).rv p :=
  Iff.rfl

/-- An RV class is principal in the sense of LM24, Definition 5.2.1 exactly when its homogeneous
image is a nonzero principal vector in one degree component. -/
theorem isPrincipalRV_iff_exists_degreeHomogeneousClass (B : HahnDegreeRV K) :
    IsPrincipalRV B ↔
      ∃ (α : NatOrdinal)
        (C : (HahnSeries.Nonpositive.degreeValuation K).Component α),
        C ≠ 0 ∧ IsPrincipalDegreeClass α C ∧
          (HahnSeries.Nonpositive.degreeValuation K).rvEquivHomogeneous B =
            degreeHomogeneousClass α C := by
  let w := HahnSeries.Nonpositive.degreeValuation K
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hpDegreeNe : (p : K⟦ℝ⟧).degree ≠ ⊥ := by
      intro hbot
      exact hp.ne_zero (Subtype.ext (HahnSeries.degree_eq_bot.mp hbot))
    let α := (p : K⟦ℝ⟧).degree.unbot hpDegreeNe
    have hpDegree : (p : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal) :=
      (WithBot.coe_unbot _ hpDegreeNe).symm
    let C := degreeLayerMk α p hpDegree.le
    have hC : C ≠ 0 := by
      intro hzero
      have hlt := (degreeLayerMk_eq_zero_iff α p hpDegree.le).mp hzero
      rw [hpDegree] at hlt
      exact lt_irrefl _ hlt
    refine ⟨α, C, hC,
      (isPrincipalDegreeClass_iff α C).mpr
        (Or.inr ⟨p, hp, hpDegree, rfl⟩), ?_⟩
    exact rvEquivHomogeneous_rv_eq_degreeHomogeneousClass α p hpDegree
  · rintro ⟨α, C, hC, hCPrincipal, hB⟩
    rcases (isPrincipalDegreeClass_iff α C).mp hCPrincipal with
      hCzero | ⟨p, hp, hpDegree, hCp⟩
    · exact (hC hCzero).elim
    · refine ⟨p, hp, ?_⟩
      apply w.rvEquivHomogeneous.injective
      calc
        w.rvEquivHomogeneous B = degreeHomogeneousClass α C := hB
        _ = degreeHomogeneousClass α
              (degreeLayerMk α p hpDegree.le) :=
          congrArg (degreeHomogeneousClass α) hCp
        _ = w.rvEquivHomogeneous (w.rv p) :=
          (rvEquivHomogeneous_rv_eq_degreeHomogeneousClass α p hpDegree).symm

/-- Divisibility of a fixed homogeneous class by a finite-support class is exactly scalar
divisibility in that fixed component. -/
theorem finiteSupportHomogeneousClass_dvd_degreeHomogeneousClass_iff
    (q : FiniteSupportRing (K := K)) (α : NatOrdinal)
    (B : (HahnSeries.Nonpositive.degreeValuation K).Component α) :
    finiteSupportHomogeneousClass q ∣
        degreeHomogeneousClass α B ↔
      ∃ C :
          (HahnSeries.Nonpositive.degreeValuation K).Component α,
        HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv K q • C = B := by
  by_cases hB : B = 0
  · subst B
    constructor
    · intro _
      refine ⟨0, ?_⟩
      let w := HahnSeries.Nonpositive.degreeValuation K
      apply DirectSum.of_injective (β := w.Component) α
      rw [DirectSum.of_zero_smul, map_zero, mul_zero]
    · rintro ⟨C, hC⟩
      refine ⟨degreeHomogeneousClass α C, ?_⟩
      apply Subtype.ext
      change DirectSum.of
          (HahnSeries.Nonpositive.degreeValuation K).Component
          α 0 =
        (finiteSupportHomogeneousClass q :
            DegreeGraded K) *
          (degreeHomogeneousClass α C : DegreeGraded K)
      rw [coe_finiteSupportHomogeneousClass,
        finiteSupportGradedEmbedding_apply,
        coe_degreeHomogeneousClass,
        ← DirectSum.of_zero_smul, hC, map_zero]
  · constructor
    · rintro ⟨H, hH⟩
      have hHCoe := congrArg Subtype.val hH
      have hHmem :=
        (MaxAddDegree.mem_homogeneousClasses_iff
          (HahnSeries.Nonpositive.degreeValuation K)
          (H : DegreeGraded K)).mp H.2
      rcases hHmem with hzero | ⟨β, C, hC⟩
      · have hOfZero : DirectSum.of
            (HahnSeries.Nonpositive.degreeValuation K).Component
            α B = 0 := by
          change DirectSum.of
              (HahnSeries.Nonpositive.degreeValuation K).Component
              α B =
            (finiteSupportHomogeneousClass q :
                DegreeGraded K) *
              (H : DegreeGraded K) at hHCoe
          simpa [hzero] using hHCoe
        apply (hB ?_).elim
        apply DirectSum.of_injective α
        simpa using hOfZero
      · have hHrepr : H = degreeHomogeneousClass β C :=
          Subtype.ext hC
        subst H
        change DirectSum.of
            (HahnSeries.Nonpositive.degreeValuation K).Component
            α B =
          (finiteSupportHomogeneousClass q :
              DegreeGraded K) *
            (degreeHomogeneousClass β C : DegreeGraded K)
          at hHCoe
        rw [coe_finiteSupportHomogeneousClass,
          coe_degreeHomogeneousClass,
          finiteSupportGradedEmbedding_mul_of] at hHCoe
        have hαβ : α = β := directSum_index_eq_of_of_eq hB hHCoe
        subst β
        exact ⟨C, ((DirectSum.of_injective α) hHCoe).symm⟩
    · rintro ⟨C, hC⟩
      refine ⟨degreeHomogeneousClass α C, ?_⟩
      rw [finiteSupportHomogeneousClass_mul_degreeHomogeneousClass, hC]

/-- Divisibility is preserved and reflected by the multiplicative equivalence from RV to
homogeneous graded classes. -/
theorem finiteSupportRVEmbedding_dvd_iff_homogeneous
    (q : FiniteSupportRing (K := K)) (B : HahnDegreeRV K) :
    finiteSupportRVEmbedding K q ∣ B ↔
      finiteSupportHomogeneousClass q ∣
        (HahnSeries.Nonpositive.degreeValuation K).rvEquivHomogeneous B := by
  let e :=
    (HahnSeries.Nonpositive.degreeValuation K).rvEquivHomogeneous
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨(HahnSeries.Nonpositive.degreeValuation K).rvHomogeneous C,
      ?_⟩
    apply Subtype.ext
    rw [(HahnSeries.Nonpositive.degreeValuation K).rvEquivHomogeneous_apply,
      (HahnSeries.Nonpositive.degreeValuation K).coe_rvHomogeneous]
    change
      (HahnSeries.Nonpositive.degreeValuation K).rvInitialFormHom B =
        (finiteSupportHomogeneousClass q : DegreeGraded K) *
          ((HahnSeries.Nonpositive.degreeValuation K).rvHomogeneous C :
            DegreeGraded K)
    rw [finiteSupportHomogeneousClass_apply,
      (HahnSeries.Nonpositive.degreeValuation K).coe_rvHomogeneous
          (finiteSupportRVEmbedding K q),
      (HahnSeries.Nonpositive.degreeValuation K).coe_rvHomogeneous C]
    rw [← (HahnSeries.Nonpositive.degreeValuation K).rvInitialFormHom.map_mul, hC]
  · rintro ⟨H, hH⟩
    refine ⟨e.symm H, ?_⟩
    apply (HahnSeries.Nonpositive.degreeValuation K).rvHomogeneous_injective
    have hsymm :
        (HahnSeries.Nonpositive.degreeValuation K).rvHomogeneous
            (e.symm H) = H := by
      rw [← (HahnSeries.Nonpositive.degreeValuation K).rvEquivHomogeneous_apply, e.apply_symm_apply]
    apply Subtype.ext
    have hHCoe := congrArg Subtype.val hH
    rw [(HahnSeries.Nonpositive.degreeValuation K).rvEquivHomogeneous_apply,
      (HahnSeries.Nonpositive.degreeValuation K).coe_rvHomogeneous] at hHCoe
    change
      (HahnSeries.Nonpositive.degreeValuation K).rvInitialFormHom B =
        (finiteSupportHomogeneousClass q : DegreeGraded K) *
          (H : DegreeGraded K) at hHCoe
    rw [finiteSupportHomogeneousClass_apply,
      (HahnSeries.Nonpositive.degreeValuation K).coe_rvHomogeneous
          (finiteSupportRVEmbedding K q)] at hHCoe
    rw [(HahnSeries.Nonpositive.degreeValuation K).coe_rvHomogeneous B,
      (HahnSeries.Nonpositive.degreeValuation K).coe_rvHomogeneous
          (finiteSupportRVEmbedding K q * e.symm H)]
    change
      (HahnSeries.Nonpositive.degreeValuation K).rvInitialFormHom B =
        (HahnSeries.Nonpositive.degreeValuation K).rvInitialFormHom
          (finiteSupportRVEmbedding K q * e.symm H)
    rw [(HahnSeries.Nonpositive.degreeValuation K).rvInitialFormHom.map_mul]
    have hsymmCoe := congrArg Subtype.val hsymm
    rw [(HahnSeries.Nonpositive.degreeValuation K).coe_rvHomogeneous (e.symm H)] at hsymmCoe
    change
      (HahnSeries.Nonpositive.degreeValuation K).rvInitialFormHom
          (e.symm H) = (H : DegreeGraded K) at hsymmCoe
    rw [hsymmCoe]
    exact hHCoe

/-- An associate class records exactly the finite-support divisors of an RV class. This is the
intrinsic predicate underlying LM24, Proposition 5.4.3. -/
def IsRVMaximalFiniteSupportDivisor (B : HahnDegreeRV K)
    (a : Associates (FiniteSupportRing (K := K))) : Prop :=
  IsMaximalDivisorAlong
    (finiteSupportRVEmbedding K).toMonoidHom B a

/-- The defining divisibility characterization for a maximal finite-support divisor in RV. -/
theorem isRVMaximalFiniteSupportDivisor_iff (B : HahnDegreeRV K)
    (a : Associates (FiniteSupportRing (K := K))) :
    IsRVMaximalFiniteSupportDivisor B a ↔
      ∀ q : FiniteSupportRing (K := K), Associates.mk q ≤ a ↔
        (finiteSupportRVEmbedding K).toMonoidHom q ∣ B := by
  rw [IsRVMaximalFiniteSupportDivisor,
    isMaximalDivisorAlong_iff]

/-- Representative form of the maximal-divisor characterization used in LM24,
Proposition 5.4.3. -/
theorem isRVMaximalFiniteSupportDivisor_mk_iff
    (B : HahnDegreeRV K) (p : FiniteSupportRing (K := K)) :
    IsRVMaximalFiniteSupportDivisor B (Associates.mk p) ↔
      ∀ q : FiniteSupportRing (K := K),
        finiteSupportRVEmbedding K q ∣ B ↔ q ∣ p := by
  rw [isRVMaximalFiniteSupportDivisor_iff]
  constructor
  · intro h q
    constructor
    · intro hqB
      exact Associates.mk_le_mk_iff_dvd.mp ((h q).mpr hqB)
    · intro hqp
      exact (h q).mp (Associates.mk_le_mk_iff_dvd.mpr hqp)
  · intro h q
    constructor
    · intro hqp
      exact (h q).mpr (Associates.mk_le_mk_iff_dvd.mp hqp)
    · intro hqB
      exact Associates.mk_le_mk_iff_dvd.mpr ((h q).mp hqB)

/-- An RV class has at most one maximal finite-support divisor class. -/
theorem IsRVMaximalFiniteSupportDivisor.eq {B : HahnDegreeRV K}
    {a b : Associates (FiniteSupportRing (K := K))}
    (ha : IsRVMaximalFiniteSupportDivisor B a)
    (hb : IsRVMaximalFiniteSupportDivisor B b) : a = b := by
  exact IsMaximalDivisorAlong.eq ha hb

/-- Pairwise gcd existence gives a unique maximal finite-support divisor class for every RV
class. -/
theorem existsUnique_isRVMaximalFiniteSupportDivisor_of_exists_gcd
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (B : HahnDegreeRV K) :
    ∃! a : Associates (FiniteSupportRing (K := K)),
      IsRVMaximalFiniteSupportDivisor B a := by
  let w := HahnSeries.Nonpositive.degreeValuation K
  let e := w.rvEquivHomogeneous
  by_cases hB : B = 0
  · subst B
    refine ⟨0, ?_, ?_⟩
    · exact IsMaximalDivisorAlong.zero
        (finiteSupportRVEmbedding K).toMonoidHom
    · intro a ha
      exact IsRVMaximalFiniteSupportDivisor.eq ha
        (IsMaximalDivisorAlong.zero
          (finiteSupportRVEmbedding K).toMonoidHom)
  · have hEB : e B ≠ 0 := by
      intro hzero
      apply hB
      apply e.injective
      rw [w.rvEquivHomogeneous_zero]
      exact hzero
    have hEBmem := (w.mem_homogeneousClasses_iff (e B : w.AssociatedGraded)).mp (e B).2
    rcases hEBmem with hzero | ⟨α, C, hC⟩
    · exact (hEB (Subtype.ext hzero)).elim
    · obtain ⟨a, ha, hunique⟩ :=
        existsUnique_isLayerMaximalFiniteSupportDivisor_of_exists_gcd hgcd α C
      have hEBrepr : e B = degreeHomogeneousClass α C :=
        Subtype.ext hC
      refine ⟨a, ?_, ?_⟩
      · apply (isRVMaximalFiniteSupportDivisor_iff B a).mpr
        intro q
        change Associates.mk q ≤ a ↔ finiteSupportRVEmbedding K q ∣ B
        rw [finiteSupportRVEmbedding_dvd_iff_homogeneous,
          hEBrepr,
          finiteSupportHomogeneousClass_dvd_degreeHomogeneousClass_iff]
        exact (isLayerMaximalFiniteSupportDivisor_iff α C a).mp ha q
      · intro b hb
        apply hunique b
        apply (isLayerMaximalFiniteSupportDivisor_iff α C b).mpr
        intro q
        rw [← finiteSupportHomogeneousClass_dvd_degreeHomogeneousClass_iff,
          ← hEBrepr,
          ← finiteSupportRVEmbedding_dvd_iff_homogeneous]
        exact (isRVMaximalFiniteSupportDivisor_iff B b).mp hb q

/-- If `a` is principal of degree `α` and `p` is a nonzero finite-support series, then the
RV class of `p * a` has maximal finite-support divisor class represented by `p`. -/
theorem isRVMaximalFiniteSupportDivisor_finiteSupport_mul_principal
    (α : NatOrdinal) (p : FiniteSupportRing (K := K)) (hp : p ≠ 0)
    (a : Series K) (ha : HahnSeries.Nonpositive.IsPrincipal a)
    (haDegree : (a : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal)) :
    IsRVMaximalFiniteSupportDivisor
      ((HahnSeries.Nonpositive.degreeValuation K).rv
        ((p : Series K) * a))
      (Associates.mk p) := by
  have hpHahn : (p : K⟦ℝ⟧) ≠ 0 := by
    intro hzero
    apply hp
    exact Subtype.ext (Subtype.ext hzero)
  have hpDegree : (p : K⟦ℝ⟧).degree = 0 := by
    rw [HahnSeries.degree_eq_zero]
    exact ⟨hpHahn,
      (HahnSeries.Nonpositive.mem_finiteSupportSubring_iff
        (p : Series K)).mp p.2⟩
  have hprodDegree : (((p : Series K) * a : Series K) : K⟦ℝ⟧).degree =
      (α : WithBot NatOrdinal) := by
    rw [HahnSeries.Nonpositive.degree_mul, hpDegree, haDegree, zero_add]
  have hLayer :=
    isLayerMaximalFiniteSupportDivisor_finiteSupport_mul_principal α p a ha haDegree
  apply (isRVMaximalFiniteSupportDivisor_iff _ (Associates.mk p)).mpr
  intro q
  change Associates.mk q ≤ Associates.mk p ↔
    finiteSupportRVEmbedding K q ∣
      (HahnSeries.Nonpositive.degreeValuation K).rv
        ((p : Series K) * a)
  rw [finiteSupportRVEmbedding_dvd_iff_homogeneous,
    rvEquivHomogeneous_rv_eq_degreeHomogeneousClass α _ hprodDegree,
    finiteSupportHomogeneousClass_dvd_degreeHomogeneousClass_iff]
  exact (isLayerMaximalFiniteSupportDivisor_iff α _ _).mp hLayer q

/-- A principal RV class has a maximal finite-support divisor represented by a constant series,
as in the final clause of LM24, Proposition 5.4.3. -/
theorem exists_scalar_isRVMaximalFiniteSupportDivisor_of_isPrincipal
    (B : HahnDegreeRV K) (hB : IsPrincipalRV B) :
    ∃ k : K, IsRVMaximalFiniteSupportDivisor B
      (Associates.mk
        (HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k)) := by
  obtain ⟨α, C, _, hCPrincipal, hBCoe⟩ :=
    (isPrincipalRV_iff_exists_degreeHomogeneousClass B).mp hB
  obtain ⟨k, hk⟩ :=
    exists_scalar_isLayerMaximalFiniteSupportDivisor_of_isPrincipal α C hCPrincipal
  refine ⟨k, (isRVMaximalFiniteSupportDivisor_iff B _).mpr ?_⟩
  intro q
  change Associates.mk q ≤ Associates.mk
      (HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k) ↔
    finiteSupportRVEmbedding K q ∣ B
  rw [finiteSupportRVEmbedding_dvd_iff_homogeneous,
    hBCoe,
    finiteSupportHomogeneousClass_dvd_degreeHomogeneousClass_iff]
  exact (isLayerMaximalFiniteSupportDivisor_iff α C _).mp hk q

/-- The canonical maximal finite-support divisor class of an RV element.

The fallback branch is unreachable whenever maximal-divisor existence has been established. -/
noncomputable def rvMaximalFiniteSupportDivisor (B : HahnDegreeRV K) :
    Associates (FiniteSupportRing (K := K)) := by
  classical
  exact if h : ∃ a : Associates (FiniteSupportRing (K := K)),
        IsRVMaximalFiniteSupportDivisor B a then
      Classical.choose h
    else
      0

/-- Any class satisfying the RV characterization is the canonical class. -/
theorem rvMaximalFiniteSupportDivisor_eq_of_is {B : HahnDegreeRV K}
    {a : Associates (FiniteSupportRing (K := K))}
    (ha : IsRVMaximalFiniteSupportDivisor B a) :
    rvMaximalFiniteSupportDivisor B = a := by
  classical
  let hex : ∃ b : Associates (FiniteSupportRing (K := K)),
      IsRVMaximalFiniteSupportDivisor B b := ⟨a, ha⟩
  rw [rvMaximalFiniteSupportDivisor, dif_pos hex]
  exact (Classical.choose_spec hex).eq ha

/-- Under pairwise gcd existence, the canonical RV class satisfies its defining
characterization. -/
theorem rvMaximalFiniteSupportDivisor_is_of_exists_gcd (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (B : HahnDegreeRV K) :
    IsRVMaximalFiniteSupportDivisor B
      (rvMaximalFiniteSupportDivisor B) := by
  obtain ⟨a, ha, _⟩ :=
    existsUnique_isRVMaximalFiniteSupportDivisor_of_exists_gcd hgcd B
  rw [rvMaximalFiniteSupportDivisor_eq_of_is ha]
  exact ha

/-- For a principal RV class, the canonical maximal finite-support divisor is represented by a
constant series. -/
theorem exists_scalar_rvMaximalFiniteSupportDivisor_of_isPrincipal
    (B : HahnDegreeRV K) (hB : IsPrincipalRV B) :
    ∃ k : K, rvMaximalFiniteSupportDivisor B =
      Associates.mk
        (HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k) := by
  obtain ⟨k, hk⟩ :=
    exists_scalar_isRVMaximalFiniteSupportDivisor_of_isPrincipal B hB
  exact ⟨k, rvMaximalFiniteSupportDivisor_eq_of_is hk⟩

end

end Berarducci
