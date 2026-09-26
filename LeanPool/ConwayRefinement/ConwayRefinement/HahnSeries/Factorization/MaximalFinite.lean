/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Divisibility.MaximalDivisor
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringTensor
public import LeanPool.ConwayRefinement.ConwayRefinement.LinearAlgebra.TensorProduct.Content

/-!
# Maximal finite-support divisors in the degree-graded ring

This module constructs the intrinsic associate classes underlying LM24, Proposition 5.4.3,
Corollary 5.4.4, and Proposition 5.4.8. For a homogeneous component or for the full
degree-graded ring, a class is characterized by the equivalence

`q divides the class ↔ Associates.mk q divides the maximal associate class`.

The construction transports the basis-independent content of a tensor through the componentwise
and global tensor equivalences. A basis is therefore used only inside the generic existence proof;
it does not occur in any definition in this module. Pairwise gcd existence is an explicit theorem
hypothesis. It is neither installed as a typeclass nor incorporated into the primitive
definitions.

The paper's representative-valued normalization and its exact statements in the RV monoid are
kept separate from this associate-class core.
-/

open scoped DirectSum HahnSeries NatOrdinal TensorProduct

universe v

namespace Berarducci

public noncomputable section

variable {K : Type v} [Field K]

/-- Multiplication on the finite-support tensor factor agrees with the residue-ring action on a
fixed component of `RV̂`. -/
theorem principalComponentTensorEquiv_mulRightFactor
    (α : NatOrdinal) (q : FiniteSupportRing (K := K))
    (z : PrincipalComponent K α ⊗[K] FiniteSupportRing (K := K)) :
    principalComponentTensorEquiv K α
        (TensorProduct.mulRightFactor q z) =
      HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv K q •
        principalComponentTensorEquiv K α z := by
  induction z using TensorProduct.inductionOn with
  | tmul x p =>
      rw [TensorProduct.mulRightFactor_tmul,
        principalComponentTensorEquiv_tmul,
        principalComponentTensorEquiv_tmul, map_mul]
      exact degreeResidue_smul_smul α _ _ _
  | add x y hx hy =>
      rw [(TensorProduct.mulRightFactor (K := K) q).map_add,
        (principalComponentTensorEquiv K α).map_add,
        (principalComponentTensorEquiv K α).map_add, hx, hy]
      exact (smul_add
        (HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv K q)
        (principalComponentTensorEquiv K α x)
        (principalComponentTensorEquiv K α y)).symm

/-- Multiplication on the finite-support tensor factor agrees with multiplication by the
grade-zero finite-support embedding in the associated graded ring. -/
theorem principalSubringTensorEquiv_mulRightFactor [CharZero K] (q : FiniteSupportRing (K := K))
    (z : PrincipalSubring K ⊗[K] FiniteSupportRing (K := K)) :
    principalSubringTensorEquiv K
        (TensorProduct.mulRightFactor q z) =
      finiteSupportGradedEmbedding K q *
        principalSubringTensorEquiv K z := by
  induction z using TensorProduct.inductionOn with
  | tmul x p =>
      rw [TensorProduct.mulRightFactor_tmul,
        principalSubringTensorEquiv_tmul,
        principalSubringTensorEquiv_tmul, map_mul]
      ac_rfl
  | add x y hx hy =>
      calc
        principalSubringTensorEquiv K
              (TensorProduct.mulRightFactor q (x + y)) =
            principalSubringTensorEquiv K
              (TensorProduct.mulRightFactor q x +
                TensorProduct.mulRightFactor q y) :=
          congrArg (principalSubringTensorEquiv K)
            ((TensorProduct.mulRightFactor (K := K) q).map_add x y)
        _ = principalSubringTensorEquiv K
              (TensorProduct.mulRightFactor q x) +
            principalSubringTensorEquiv K
              (TensorProduct.mulRightFactor q y) :=
          map_add (principalSubringTensorEquiv K) _ _
        _ = finiteSupportGradedEmbedding K q *
              principalSubringTensorEquiv K x +
            finiteSupportGradedEmbedding K q *
              principalSubringTensorEquiv K y :=
          congrArg₂ (· + ·) hx hy
        _ = finiteSupportGradedEmbedding K q *
              (principalSubringTensorEquiv K x +
                principalSubringTensorEquiv K y) :=
          (mul_add _ _ _).symm
        _ = finiteSupportGradedEmbedding K q *
              principalSubringTensorEquiv K (x + y) :=
          congrArg (finiteSupportGradedEmbedding K q * ·)
            (map_add (principalSubringTensorEquiv K) x y).symm

/-- An associate class records exactly the finite-support divisors of a fixed homogeneous
component of `RV̂`. -/
def IsLayerMaximalFiniteSupportDivisor (α : NatOrdinal)
    (B : (HahnSeries.Nonpositive.degreeValuation K).Component α)
    (a : Associates (FiniteSupportRing (K := K))) : Prop :=
  ∀ q : FiniteSupportRing (K := K), Associates.mk q ≤ a ↔
    ∃ C : (HahnSeries.Nonpositive.degreeValuation K).Component α,
      HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv K q • C = B

/-- The defining divisibility characterization for a fixed homogeneous component. -/
theorem isLayerMaximalFiniteSupportDivisor_iff (α : NatOrdinal)
    (B : (HahnSeries.Nonpositive.degreeValuation K).Component α)
    (a : Associates (FiniteSupportRing (K := K))) :
    IsLayerMaximalFiniteSupportDivisor α B a ↔
      ∀ q : FiniteSupportRing (K := K), Associates.mk q ≤ a ↔
        ∃ C :
            (HahnSeries.Nonpositive.degreeValuation K).Component α,
          HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv K q • C = B :=
  Iff.rfl

/-- An associate class records exactly the divisors of a graded element that arise from the
finite-support subring in grade zero. -/
def IsGradedMaximalFiniteSupportDivisor (B : DegreeGraded K)
    (a : Associates (FiniteSupportRing (K := K))) : Prop :=
  IsMaximalDivisorAlong
    (finiteSupportGradedEmbedding K).toMonoidHom B a

/-- The defining divisibility characterization for an element of the associated graded ring. -/
theorem isGradedMaximalFiniteSupportDivisor_iff (B : DegreeGraded K)
    (a : Associates (FiniteSupportRing (K := K))) :
    IsGradedMaximalFiniteSupportDivisor B a ↔
      ∀ q : FiniteSupportRing (K := K), Associates.mk q ≤ a ↔
        (finiteSupportGradedEmbedding K).toMonoidHom q ∣ B := by
  rw [IsGradedMaximalFiniteSupportDivisor,
    isMaximalDivisorAlong_iff]

/-- Representative form of the maximal-divisor characterization used in LM24,
Corollary 5.4.4. -/
theorem isGradedMaximalFiniteSupportDivisor_mk_iff (B : DegreeGraded K)
    (p : FiniteSupportRing (K := K)) :
    IsGradedMaximalFiniteSupportDivisor B (Associates.mk p) ↔
      ∀ q : FiniteSupportRing (K := K),
        finiteSupportGradedEmbedding K q ∣ B ↔ q ∣ p := by
  rw [isGradedMaximalFiniteSupportDivisor_iff]
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

/-- The maximal-divisor predicate on a homogeneous component is the intrinsic tensor-content
predicate transported through the homogeneous-component equivalence. -/
theorem isContent_principalComponentTensorEquiv_symm_iff (α : NatOrdinal)
    (B : (HahnSeries.Nonpositive.degreeValuation K).Component α)
    (a : Associates (FiniteSupportRing (K := K))) :
    TensorProduct.IsContent
        ((principalComponentTensorEquiv K α).symm B) a ↔
      IsLayerMaximalFiniteSupportDivisor α B a := by
  rw [TensorProduct.isContent_iff,
    isLayerMaximalFiniteSupportDivisor_iff]
  constructor
  · intro h q
    rw [h q]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨principalComponentTensorEquiv K α z, ?_⟩
      rw [← principalComponentTensorEquiv_mulRightFactor,
        hz, LinearEquiv.apply_symm_apply]
    · rintro ⟨C, hC⟩
      refine ⟨(principalComponentTensorEquiv K α).symm C, ?_⟩
      apply (principalComponentTensorEquiv K α).injective
      rw [principalComponentTensorEquiv_mulRightFactor,
        LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hC]
  · intro h q
    rw [h q]
    constructor
    · rintro ⟨C, hC⟩
      refine ⟨(principalComponentTensorEquiv K α).symm C, ?_⟩
      apply (principalComponentTensorEquiv K α).injective
      rw [principalComponentTensorEquiv_mulRightFactor,
        LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hC]
    · rintro ⟨z, hz⟩
      refine ⟨principalComponentTensorEquiv K α z, ?_⟩
      rw [← principalComponentTensorEquiv_mulRightFactor,
        hz, LinearEquiv.apply_symm_apply]

/-- Multiplying a nonzero principal fixed-degree class by a finite-support series gives a class
whose maximal finite-support divisor is represented by that finite-support series. -/
theorem isLayerMaximalFiniteSupportDivisor_finiteSupport_mul_principal [CharZero K]
    (α : NatOrdinal) (p : FiniteSupportRing (K := K)) (a : Series K)
    (ha : HahnSeries.Nonpositive.IsPrincipal a)
    (haDegree : (a : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal)) :
    IsLayerMaximalFiniteSupportDivisor α
      (degreeLayerMk α ((p : Series K) * a) (by
        rw [HahnSeries.Nonpositive.degree_mul, haDegree]
        exact add_le_of_nonpos_left (HahnSeries.degree_le_zero_iff.mpr
          ((HahnSeries.Nonpositive.mem_finiteSupportSubring_iff
            (p : Series K)).mp p.2))))
      (Associates.mk p) := by
  let C := degreeLayerMk α a haDegree.le
  have hCPrincipal : IsPrincipalDegreeClass α C := by
    rw [isPrincipalDegreeClass_iff]
    exact Or.inr ⟨a, ha, haDegree, rfl⟩
  let x := degreeLayerToPrincipalComponent K α C
  have hxImage : principalComponentToHahnDegreeLayer K α x = C :=
    principalComponentToHahnDegreeLayer_degreeLayerToPrincipalComponent_of_isPrincipal
      α C hCPrincipal
  have hC : C ≠ 0 := by
    intro hzero
    have hlt := (degreeLayerMk_eq_zero_iff α a haDegree.le).mp hzero
    rw [haDegree] at hlt
    exact lt_irrefl _ hlt
  have hx : x ≠ 0 := by
    intro hzero
    apply hC
    rw [← hxImage, hzero, map_zero]
  have heq :
      principalComponentTensorEquiv K α (x ⊗ₜ[K] p) =
        degreeLayerMk α ((p : Series K) * a) (by
          rw [HahnSeries.Nonpositive.degree_mul, haDegree]
          exact add_le_of_nonpos_left (HahnSeries.degree_le_zero_iff.mpr
            ((HahnSeries.Nonpositive.mem_finiteSupportSubring_iff
              (p : Series K)).mp p.2))) := by
    rw [principalComponentTensorEquiv_tmul, hxImage]
    exact degreeFiniteSupportResidueEquiv_smul_degreeLayerMk α p a haDegree.le
  apply (isContent_principalComponentTensorEquiv_symm_iff α _ (Associates.mk p)).mp
  rw [← heq, LinearEquiv.symm_apply_apply]
  exact TensorProduct.isContent_tmul_of_ne_zero x hx p

/-- The graded maximal-divisor predicate is intrinsic tensor content transported through the
global tensor equivalence. -/
theorem isContent_principalGradedTensorEquiv_symm_iff [CharZero K] (B : DegreeGraded K)
    (a : Associates (FiniteSupportRing (K := K))) :
    TensorProduct.IsContent
        ((principalSubringTensorEquiv K).symm B) a ↔
      IsGradedMaximalFiniteSupportDivisor B a := by
  rw [TensorProduct.isContent_iff,
    isGradedMaximalFiniteSupportDivisor_iff]
  constructor
  · intro h q
    rw [h q]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨principalSubringTensorEquiv K z, ?_⟩
      change B = finiteSupportGradedEmbedding K q *
        principalSubringTensorEquiv K z
      rw [← principalSubringTensorEquiv_mulRightFactor,
        hz, AlgEquiv.apply_symm_apply]
    · rintro ⟨C, hC⟩
      change B = finiteSupportGradedEmbedding K q * C at hC
      refine ⟨(principalSubringTensorEquiv K).symm C, ?_⟩
      apply (principalSubringTensorEquiv K).injective
      rw [principalSubringTensorEquiv_mulRightFactor,
        AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
      exact hC.symm
  · intro h q
    rw [h q]
    constructor
    · rintro ⟨C, hC⟩
      change B = finiteSupportGradedEmbedding K q * C at hC
      refine ⟨(principalSubringTensorEquiv K).symm C, ?_⟩
      apply (principalSubringTensorEquiv K).injective
      rw [principalSubringTensorEquiv_mulRightFactor,
        AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
      exact hC.symm
    · rintro ⟨z, hz⟩
      refine ⟨principalSubringTensorEquiv K z, ?_⟩
      change B = finiteSupportGradedEmbedding K q *
        principalSubringTensorEquiv K z
      rw [← principalSubringTensorEquiv_mulRightFactor,
        hz, AlgEquiv.apply_symm_apply]

/-- A finite-support series, embedded in grade zero, is its own maximal finite-support
divisor. -/
theorem isGradedMaximalFiniteSupportDivisor_finiteSupport [CharZero K] (p : FiniteSupportRing (K
  := K)) :
    IsGradedMaximalFiniteSupportDivisor
      (finiteSupportGradedEmbedding K p) (Associates.mk p) := by
  apply (isContent_principalGradedTensorEquiv_symm_iff _ (Associates.mk p)).mp
  rw [← principalSubringTensorEquiv_one_tmul p,
    AlgEquiv.symm_apply_apply]
  have hOne : (1 : PrincipalSubring K) ≠ 0 := by
    intro hzero
    have htarget : (1 : DegreeGraded K) = 0 := by
      rw [← map_one (principalSubringEmbedding K),
        ← map_zero (principalSubringEmbedding K), hzero]
    have hfinite :
        finiteSupportGradedEmbedding K
            (1 : FiniteSupportRing (K := K)) =
          finiteSupportGradedEmbedding K 0 := by
      calc
        finiteSupportGradedEmbedding K
              (1 : FiniteSupportRing (K := K)) = 1 :=
          map_one (finiteSupportGradedEmbedding K)
        _ = 0 := htarget
        _ = finiteSupportGradedEmbedding K 0 :=
          (map_zero (finiteSupportGradedEmbedding K)).symm
    exact one_ne_zero (finiteSupportGradedEmbedding_injective K hfinite)
  exact TensorProduct.isContent_tmul_of_ne_zero
    (1 : PrincipalSubring K) hOne p

/-- Multiplying a nonzero principal fixed-degree class by a finite-support series gives a
homogeneous graded class whose maximal finite-support divisor is represented by that series. -/
theorem isGradedMaximalFiniteSupportDivisor_finiteSupport_mul_principal [CharZero K]
    (α : NatOrdinal) (p : FiniteSupportRing (K := K)) (a : Series K)
    (ha : HahnSeries.Nonpositive.IsPrincipal a)
    (haDegree : (a : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal)) :
    IsGradedMaximalFiniteSupportDivisor
      (DirectSum.of
        (HahnSeries.Nonpositive.degreeValuation K).Component
        α
        (degreeLayerMk α ((p : Series K) * a) (by
          rw [HahnSeries.Nonpositive.degree_mul, haDegree]
          exact add_le_of_nonpos_left (HahnSeries.degree_le_zero_iff.mpr
            ((HahnSeries.Nonpositive.mem_finiteSupportSubring_iff
              (p : Series K)).mp p.2)))))
      (Associates.mk p) := by
  let C := degreeLayerMk α a haDegree.le
  have hCPrincipal : IsPrincipalDegreeClass α C := by
    rw [isPrincipalDegreeClass_iff]
    exact Or.inr ⟨a, ha, haDegree, rfl⟩
  let x := degreeLayerToPrincipalComponent K α C
  have hxImage : principalComponentToHahnDegreeLayer K α x = C :=
    principalComponentToHahnDegreeLayer_degreeLayerToPrincipalComponent_of_isPrincipal
      α C hCPrincipal
  have hC : C ≠ 0 := by
    intro hzero
    have hlt := (degreeLayerMk_eq_zero_iff α a haDegree.le).mp hzero
    rw [haDegree] at hlt
    exact lt_irrefl _ hlt
  have hx : x ≠ 0 := by
    intro hzero
    apply hC
    rw [← hxImage, hzero, map_zero]
  let X : PrincipalSubring K :=
    DirectSum.of (PrincipalComponent K) α x
  have hX : X ≠ 0 := by
    intro hzero
    apply hx
    exact DirectSum.of_injective α (by simpa [X] using hzero)
  have heq :
      principalSubringTensorEquiv K (X ⊗ₜ[K] p) =
        DirectSum.of
          (HahnSeries.Nonpositive.degreeValuation K).Component
          α
          (degreeLayerMk α ((p : Series K) * a) (by
            rw [HahnSeries.Nonpositive.degree_mul, haDegree]
            exact add_le_of_nonpos_left (HahnSeries.degree_le_zero_iff.mpr
              ((HahnSeries.Nonpositive.mem_finiteSupportSubring_iff
                (p : Series K)).mp p.2)))) := by
    rw [principalSubringTensorEquiv_tmul, show X =
      DirectSum.of (PrincipalComponent K) α x by rfl,
      principalSubringEmbedding_of, hxImage, mul_comm,
      finiteSupportGradedEmbedding_mul_of]
    exact congrArg
      (DirectSum.of
        (HahnSeries.Nonpositive.degreeValuation K).Component
        α)
      (degreeFiniteSupportResidueEquiv_smul_degreeLayerMk α p a haDegree.le)
  apply (isContent_principalGradedTensorEquiv_symm_iff _ (Associates.mk p)).mp
  rw [← heq, AlgEquiv.symm_apply_apply]
  exact TensorProduct.isContent_tmul_of_ne_zero X hX p

/-- A fixed homogeneous component has at most one maximal finite-support divisor class. -/
theorem IsLayerMaximalFiniteSupportDivisor.eq {α : NatOrdinal}
    {B : (HahnSeries.Nonpositive.degreeValuation K).Component α}
    {a b : Associates (FiniteSupportRing (K := K))}
    (ha : IsLayerMaximalFiniteSupportDivisor α B a)
    (hb : IsLayerMaximalFiniteSupportDivisor α B b) : a = b := by
  induction a using Quotient.inductionOn with
  | _ p =>
      induction b using Quotient.inductionOn with
      | _ q =>
          apply le_antisymm
          · exact (hb p).2 ((ha p).1 le_rfl)
          · exact (ha q).2 ((hb q).1 le_rfl)

/-- A graded element has at most one maximal finite-support divisor class. -/
theorem IsGradedMaximalFiniteSupportDivisor.eq {B : DegreeGraded K}
    {a b : Associates (FiniteSupportRing (K := K))}
    (ha : IsGradedMaximalFiniteSupportDivisor B a)
    (hb : IsGradedMaximalFiniteSupportDivisor B b) : a = b := by
  exact IsMaximalDivisorAlong.eq ha hb

/-- Pairwise gcd existence gives a unique maximal finite-support divisor of every fixed
homogeneous component. -/
theorem existsUnique_isLayerMaximalFiniteSupportDivisor_of_exists_gcd
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K),
          e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (α : NatOrdinal)
    (B : (HahnSeries.Nonpositive.degreeValuation K).Component α) :
    ∃! a : Associates (FiniteSupportRing (K := K)),
      IsLayerMaximalFiniteSupportDivisor α B a := by
  obtain ⟨a, ha, hunique⟩ :=
    TensorProduct.existsUnique_isContent_of_exists_gcd hgcd
      ((principalComponentTensorEquiv K α).symm B)
  refine ⟨a,
    (isContent_principalComponentTensorEquiv_symm_iff α B a).mp ha,
    ?_⟩
  intro b hb
  exact hunique b
    ((isContent_principalComponentTensorEquiv_symm_iff α B b).mpr hb)

/-- A principal fixed-degree class has a maximal finite-support divisor represented by a
constant series. -/
theorem exists_scalar_isLayerMaximalFiniteSupportDivisor_of_isPrincipal (α : NatOrdinal)
    (B : (HahnSeries.Nonpositive.degreeValuation K).Component α)
    (hB : IsPrincipalDegreeClass α B) :
    ∃ k : K, IsLayerMaximalFiniteSupportDivisor α B
      (Associates.mk
        (HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k)) := by
  by_cases hB0 : B = 0
  · subst B
    refine ⟨0, ?_⟩
    simpa using
      (isContent_principalComponentTensorEquiv_symm_iff α 0 0).mp
        (by
          simpa using
            (TensorProduct.isContent_zero (K := K)
              (D := FiniteSupportRing (K := K))
              (V := PrincipalComponent K α)))
  · let x := degreeLayerToPrincipalComponent K α B
    have hxImage : principalComponentToHahnDegreeLayer K α x = B :=
      principalComponentToHahnDegreeLayer_degreeLayerToPrincipalComponent_of_isPrincipal α B hB
    have hx : x ≠ 0 := by
      intro hx0
      apply hB0
      rw [← hxImage, hx0, map_zero]
    have hinv : (principalComponentTensorEquiv K α).symm B =
        x ⊗ₜ[K] (1 : FiniteSupportRing (K := K)) := by
      apply (principalComponentTensorEquiv K α).injective
      rw [LinearEquiv.apply_symm_apply, principalComponentTensorEquiv_tmul,
        map_one, degreeResidue_one_smul, hxImage]
    refine ⟨1, ?_⟩
    have hcontent := TensorProduct.isContent_tmul_one_of_ne_zero
      (K := K) (D := FiniteSupportRing (K := K)) x hx
    rw [← hinv] at hcontent
    simpa using
      (isContent_principalComponentTensorEquiv_symm_iff α B 1).mp hcontent

/-- Pairwise gcd existence gives a unique maximal finite-support divisor of every element of the
degree-graded ring. -/
theorem existsUnique_isGradedMaximalFiniteSupportDivisor_of_exists_gcd [CharZero K]
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K),
          e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (B : DegreeGraded K) :
    ∃! a : Associates (FiniteSupportRing (K := K)),
      IsGradedMaximalFiniteSupportDivisor B a := by
  obtain ⟨a, ha, hunique⟩ :=
    TensorProduct.existsUnique_isContent_of_exists_gcd hgcd
      ((principalSubringTensorEquiv K).symm B)
  refine ⟨a,
    (isContent_principalGradedTensorEquiv_symm_iff B a).mp ha,
    ?_⟩
  intro b hb
  exact hunique b
    ((isContent_principalGradedTensorEquiv_symm_iff B b).mpr hb)

/-- The canonical maximal finite-support divisor class of a homogeneous component.

The fallback branch is unreachable whenever maximal-divisor existence has been established. -/
noncomputable def layerMaximalFiniteSupportDivisor (α : NatOrdinal)
    (B : (HahnSeries.Nonpositive.degreeValuation K).Component α) :
    Associates (FiniteSupportRing (K := K)) := by
  classical
  exact if h : ∃ a : Associates (FiniteSupportRing (K := K)),
        IsLayerMaximalFiniteSupportDivisor α B a then
      Classical.choose h
    else
      0

/-- Any class satisfying the homogeneous-component characterization is the canonical class. -/
theorem layerMaximalFiniteSupportDivisor_eq_of_is {α : NatOrdinal}
    {B : (HahnSeries.Nonpositive.degreeValuation K).Component α}
    {a : Associates (FiniteSupportRing (K := K))}
    (ha : IsLayerMaximalFiniteSupportDivisor α B a) :
    layerMaximalFiniteSupportDivisor α B = a := by
  classical
  let hex : ∃ b : Associates (FiniteSupportRing (K := K)),
      IsLayerMaximalFiniteSupportDivisor α B b := ⟨a, ha⟩
  rw [layerMaximalFiniteSupportDivisor, dite_eq_left hex]
  exact (Classical.choose_spec hex).eq ha

/-- Under pairwise gcd existence, the canonical homogeneous class satisfies its defining
characterization. -/
theorem layerMaximalFiniteSupportDivisor_is_of_exists_gcd
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K),
          e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (α : NatOrdinal)
    (B : (HahnSeries.Nonpositive.degreeValuation K).Component α) :
    IsLayerMaximalFiniteSupportDivisor α B
      (layerMaximalFiniteSupportDivisor α B) := by
  obtain ⟨a, ha, _⟩ :=
    existsUnique_isLayerMaximalFiniteSupportDivisor_of_exists_gcd hgcd α B
  rw [layerMaximalFiniteSupportDivisor_eq_of_is ha]
  exact ha

/-- The canonical maximal finite-support divisor class of a graded element.

The fallback branch is unreachable whenever maximal-divisor existence has been established. -/
noncomputable def gradedMaximalFiniteSupportDivisor (B : DegreeGraded K) :
    Associates (FiniteSupportRing (K := K)) := by
  classical
  exact if h : ∃ a : Associates (FiniteSupportRing (K := K)),
        IsGradedMaximalFiniteSupportDivisor B a then
      Classical.choose h
    else
      0

/-- Any class satisfying the graded characterization is the canonical class. -/
theorem gradedMaximalFiniteSupportDivisor_eq_of_is {B : DegreeGraded K}
    {a : Associates (FiniteSupportRing (K := K))}
    (ha : IsGradedMaximalFiniteSupportDivisor B a) :
    gradedMaximalFiniteSupportDivisor B = a := by
  classical
  let hex : ∃ b : Associates (FiniteSupportRing (K := K)),
      IsGradedMaximalFiniteSupportDivisor B b := ⟨a, ha⟩
  rw [gradedMaximalFiniteSupportDivisor, dite_eq_left hex]
  exact (Classical.choose_spec hex).eq ha

/-- Under pairwise gcd existence, the canonical graded class satisfies its defining
characterization. -/
theorem gradedMaximalFiniteSupportDivisor_is_of_exists_gcd [CharZero K]
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K),
          e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (B : DegreeGraded K) :
    IsGradedMaximalFiniteSupportDivisor B
      (gradedMaximalFiniteSupportDivisor B) := by
  obtain ⟨a, ha, _⟩ :=
    existsUnique_isGradedMaximalFiniteSupportDivisor_of_exists_gcd hgcd B
  rw [gradedMaximalFiniteSupportDivisor_eq_of_is ha]
  exact ha

/-- Associate-class form of LM24, Proposition 5.4.8: maximal finite-support divisor classes are
supermultiplicative. -/
theorem gradedMaximalFiniteSupportDivisor_mul_le_of_exists_gcd [CharZero K]
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K),
          e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (B C : DegreeGraded K) :
    gradedMaximalFiniteSupportDivisor B *
        gradedMaximalFiniteSupportDivisor C ≤
      gradedMaximalFiniteSupportDivisor (B * C) := by
  exact IsMaximalDivisorAlong.mul_le
    (gradedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd B)
    (gradedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd C)
    (gradedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd (B * C))

end

end Berarducci
