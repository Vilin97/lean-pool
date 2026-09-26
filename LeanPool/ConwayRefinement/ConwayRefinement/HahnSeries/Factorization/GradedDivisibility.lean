/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.RVMaximalFinite

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.AssociatedGradedDivisibility
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringMonoidAlgebra

/-!
# Divisibility in the degree-graded ring

This module formalizes LM24, Proposition 6.2.1, Corollaries 6.2.2--6.2.3, and Proposition
6.2.4. Degree RV is represented by the homogeneous classes in the associated graded ring. The
paper's set `P` of principal RV classes is represented intrinsically as the image of
`IsPrincipalRV` under the canonical RV embedding; `isPrincipalRVImage_iff` relates this exact
image predicate to homogeneous, componentwise-principal graded elements.

The published results retain the characteristic-zero hypothesis. Their divisibility arguments use
field-generic results about trailing grades, homogeneous divisibility, and the monoid-algebra
presentation of the principal graded subring.
-/

open scoped DirectSum HahnSeries NatOrdinal

universe v

namespace Berarducci

public noncomputable section

open HahnSeries.Nonpositive

variable {K : Type v} [Field K] [CharZero K]

/-- Membership in the image of the paper's principal RV classes inside the degree-graded
graded ring. -/
def IsPrincipalRVImage (x : DegreeGraded K) : Prop :=
  ∃ B : HahnDegreeRV K, IsPrincipalRV B ∧
    (degreeValuation K).rvInitialFormHom B = x

/-- Introduction and elimination rule for the image of the principal RV classes. -/
theorem isPrincipalRVImage_iff_exists (x : DegreeGraded K) :
    IsPrincipalRVImage x ↔
      ∃ B : HahnDegreeRV K, IsPrincipalRV B ∧
        (degreeValuation K).rvInitialFormHom B = x :=
  Iff.rfl

/-- The canonical graded image of a principal RV class belongs to `P`. -/
theorem isPrincipalRVImage_initialForm (B : HahnDegreeRV K) (hB : IsPrincipalRV B) :
    IsPrincipalRVImage
      ((degreeValuation K).rvInitialFormHom B) :=
  (isPrincipalRVImage_iff_exists _).mpr ⟨B, hB, rfl⟩

/-- The image of `P` consists exactly of the nonzero homogeneous graded elements whose sole
component is principal. -/
theorem isPrincipalRVImage_iff (x : DegreeGraded K) :
    IsPrincipalRVImage x ↔
      x ≠ 0 ∧
        x ∈ (degreeValuation K).homogeneousClasses ∧
        IsPrincipalGraded x := by
  let w := degreeValuation K
  constructor
  · rintro ⟨B, hBPrincipal, rfl⟩
    obtain ⟨α, C, hC, hCPrincipal, hBC⟩ :=
      (isPrincipalRV_iff_exists_degreeHomogeneousClass B).mp hBPrincipal
    have hBInitial : w.rvInitialFormHom B = DirectSum.of w.Component α C := by
      calc
        w.rvInitialFormHom B =
            ((w.rvEquivHomogeneous B : w.HomogeneousClasses) : w.AssociatedGraded) := by
          rw [w.rvEquivHomogeneous_apply, w.coe_rvHomogeneous]
        _ = (degreeHomogeneousClass α C : w.AssociatedGraded) :=
          congrArg Subtype.val hBC
        _ = DirectSum.of w.Component α C :=
          coe_degreeHomogeneousClass α C
    have hBHomogeneous :
        w.rvInitialFormHom B ∈ w.homogeneousClasses := by
      rw [← w.coe_rvHomogeneous]
      exact (w.rvHomogeneous B).2
    refine ⟨?_, hBHomogeneous, ?_⟩
    · rw [hBInitial]
      intro hzero
      apply hC
      apply DirectSum.of_injective α
      simpa using hzero
    · rw [isPrincipalGraded_iff]
      intro β
      rw [hBInitial]
      by_cases hβ : α = β
      · subst β
        simpa using hCPrincipal
      · rw [DirectSum.of_eq_of_ne α β C (Ne.symm hβ)]
        exact (isPrincipalDegreeClass_iff β 0).mpr (Or.inl rfl)
  · rintro ⟨hx, hxHomogeneous, hxPrincipal⟩
    rw [w.mem_homogeneousClasses_iff] at hxHomogeneous
    rcases hxHomogeneous with hzero | ⟨α, C, hCeq⟩
    · exact (hx hzero).elim
    have hC : C ≠ 0 := by
      intro hC
      subst C
      exact hx (hCeq.trans (map_zero _))
    let xHomogeneous : w.HomogeneousClasses :=
      ⟨x, (w.mem_homogeneousClasses_iff x).mpr (Or.inr ⟨α, C, hCeq⟩)⟩
    let B := w.rvEquivHomogeneous.symm xHomogeneous
    refine ⟨B, ?_, ?_⟩
    · apply (isPrincipalRV_iff_exists_degreeHomogeneousClass B).mpr
      refine ⟨α, C, hC, ?_, ?_⟩
      · rw [isPrincipalGraded_iff] at hxPrincipal
        have hα := hxPrincipal α
        rw [hCeq, DirectSum.of_eq_same] at hα
        exact hα
      · change w.rvEquivHomogeneous B = degreeHomogeneousClass α C
        apply Subtype.ext
        calc
          ((w.rvEquivHomogeneous B : w.HomogeneousClasses) : w.AssociatedGraded) = x := by
            exact congrArg Subtype.val (w.rvEquivHomogeneous.apply_symm_apply xHomogeneous)
          _ = DirectSum.of w.Component α C := hCeq
          _ = (degreeHomogeneousClass α C : w.AssociatedGraded) :=
            (coe_degreeHomogeneousClass α C).symm
    · change w.rvInitialFormHom B = x
      calc
        w.rvInitialFormHom B =
            ((w.rvEquivHomogeneous B : w.HomogeneousClasses) : w.AssociatedGraded) := by
          rw [w.rvEquivHomogeneous_apply, w.coe_rvHomogeneous]
        _ = x := congrArg Subtype.val (w.rvEquivHomogeneous.apply_symm_apply xHomogeneous)

/-- LM24, Proposition 6.2.1: nonzero factors of a product lying in degree RV also lie in
degree RV. -/
theorem hahnDegreeRV_factors_of_mul_mem {B C : DegreeGraded K}
    (hB : B ≠ 0) (hC : C ≠ 0)
    (hBC : B * C ∈ (degreeValuation K).homogeneousClasses) :
    B ∈ (degreeValuation K).homogeneousClasses ∧
      C ∈ (degreeValuation K).homogeneousClasses := by
  exact (degreeValuation K).mem_homogeneousClasses_of_mul_mem
    hB hC hBC

/-- The `P̂` clause of LM24, Corollary 6.2.2: nonzero factors of a componentwise-principal
product are componentwise principal. -/
theorem hahnDegreePrincipalGraded_factors_of_mul_mem {B C : DegreeGraded K}
    (hB : B ≠ 0) (hC : C ≠ 0)
    (hBC : IsPrincipalGraded (B * C)) :
    IsPrincipalGraded B ∧ IsPrincipalGraded C := by
  have hFactors := factors_mem_principalGradedSubalgebra_of_mul_mem hB hC
    ((mem_principalGradedSubalgebra_iff (B * C)).mpr hBC)
  exact ⟨(mem_principalGradedSubalgebra_iff B).mp hFactors.1,
    (mem_principalGradedSubalgebra_iff C).mp hFactors.2⟩

/-- The `P` clause of LM24, Corollary 6.2.2: nonzero factors of a product in the image of the
principal RV classes also lie in that image. -/
theorem hahnDegreePrincipalRVImage_factors_of_mul_mem {B C : DegreeGraded K}
    (hB : B ≠ 0) (hC : C ≠ 0)
    (hBC : IsPrincipalRVImage (B * C)) :
    IsPrincipalRVImage B ∧ IsPrincipalRVImage C := by
  have hBC' := (isPrincipalRVImage_iff (B * C)).mp hBC
  have hHomogeneous := hahnDegreeRV_factors_of_mul_mem hB hC hBC'.2.1
  have hPrincipal := hahnDegreePrincipalGraded_factors_of_mul_mem hB hC hBC'.2.2
  exact ⟨(isPrincipalRVImage_iff B).mpr
      ⟨hB, hHomogeneous.1, hPrincipal.1⟩,
    (isPrincipalRVImage_iff C).mpr
      ⟨hC, hHomogeneous.2, hPrincipal.2⟩⟩

/-- The first clause of LM24, Corollary 6.2.3: divisibility in degree RV agrees with
divisibility after the canonical embedding into the degree-graded ring. -/
theorem hahnDegreeRV_dvd_iff_associatedGraded_dvd (B C : HahnDegreeRV K) :
    B ∣ C ↔
      (degreeValuation K).rvInitialFormHom B ∣
        (degreeValuation K).rvInitialFormHom C := by
  exact (degreeValuation K).rv_dvd_iff_associatedGraded_dvd B C

/-- The finite-support clause of LM24, Corollary 6.2.3: ambient graded divisibility between
finite-support classes is exactly divisibility in the finite-support Hahn-series ring. -/
theorem finiteSupportGradedEmbedding_dvd_iff (p q : FiniteSupportRing (K := K)) :
    finiteSupportGradedEmbedding K p ∣ finiteSupportGradedEmbedding K q ↔
      p ∣ q := by
  let w := degreeValuation K
  constructor
  · intro hpq
    have hpqHomogeneous :
        finiteSupportHomogeneousClass p ∣
          finiteSupportHomogeneousClass q :=
      (w.homogeneous_dvd_iff_associatedGraded_dvd
        (finiteSupportHomogeneousClass p)
        (finiteSupportHomogeneousClass q)).mpr (by
          simpa only [coe_finiteSupportHomogeneousClass] using hpq)
    have hqHomogeneous :
        finiteSupportHomogeneousClass q =
          degreeHomogeneousClass 0
            (degreeFiniteSupportResidueEquiv K q) := by
      apply Subtype.ext
      rw [coe_finiteSupportHomogeneousClass, coe_degreeHomogeneousClass,
        finiteSupportGradedEmbedding_apply]
    have hScalar : ∃ C : w.Component 0,
        degreeFiniteSupportResidueEquiv K p • C =
          degreeFiniteSupportResidueEquiv K q :=
      (finiteSupportHomogeneousClass_dvd_degreeHomogeneousClass_iff p 0
        (degreeFiniteSupportResidueEquiv K q)).mp (by
          rw [← hqHomogeneous]
          exact hpqHomogeneous)
    obtain ⟨C, hC⟩ := hScalar
    let e := degreeFiniteSupportResidueEquiv K
    refine ⟨e.symm C, ?_⟩
    apply e.injective
    rw [map_mul, e.apply_symm_apply]
    simpa only [smul_eq_mul] using hC.symm
  · exact map_dvd (finiteSupportGradedEmbedding K)

/-- LM24, Proposition 6.2.4: an RV class divides a graded element if and only if it divides
every homogeneous component. -/
theorem hahnDegreeRV_dvd_iff_dvd_components
    (B : HahnDegreeRV K) (C : DegreeGraded K) :
    (degreeValuation K).rvInitialFormHom B ∣ C ↔
      ∀ α,
        (degreeValuation K).rvInitialFormHom B ∣
          DirectSum.of (degreeValuation K).Component α (C α) := by
  exact (degreeValuation K).rv_dvd_iff_dvd_components B C

end

end Berarducci
