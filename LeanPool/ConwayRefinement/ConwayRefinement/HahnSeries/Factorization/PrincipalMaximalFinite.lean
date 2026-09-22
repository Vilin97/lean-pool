/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.NormalizedMaximalFinite
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.RVMaximalFinite

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.AssociatedGradedDivisibility
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.GradedDivisibility

/-!
# Maximal finite-support divisors and principal factors

This module proves the field-generic cores of LM24, Lemmas 6.3.1--6.3.2. Multiplication by a
nonzero element of `P̂` is injective. Under the intrinsic tensor
decomposition, it acts only on the principal tensor factor, so it preserves tensor content and
hence the maximal finite-support divisor.

The RV result is obtained from the full graded result through the canonical RV embedding.
Finite-support greatest-common-divisor existence remains an explicit hypothesis; the coefficient
field has characteristic zero.
-/

open scoped DirectSum HahnSeries NatOrdinal TensorProduct

universe v

namespace Berarducci

public noncomputable section

open HahnSeries.Nonpositive

variable {K : Type v} [Field K] [CharZero K]

private theorem principalSubringMulLeft_injective {c : PrincipalSubring K} (hc : c ≠ 0) :
    Function.Injective (LinearMap.mulLeft K c) := by
  intro x y hxy
  change c * x = c * y at hxy
  apply principalSubringEmbedding_injective K
  have hcImage : principalSubringEmbedding K c ≠ 0 := by
    intro hzero
    apply hc
    exact principalSubringEmbedding_injective K
      (hzero.trans (map_zero (principalSubringEmbedding K)).symm)
  apply mul_left_cancel₀ hcImage
  simpa only [map_mul] using
    congrArg (principalSubringEmbedding K) hxy

private theorem principalSubringTensorEquiv_mulLeft_rTensor (c : PrincipalSubring K)
    (z : PrincipalSubring K ⊗[K] FiniteSupportRing (K := K)) :
    principalSubringTensorEquiv K
        ((LinearMap.mulLeft K c).rTensor (FiniteSupportRing (K := K)) z) =
      principalSubringEmbedding K c *
        principalSubringTensorEquiv K z := by
  induction z using TensorProduct.inductionOn with
  | tmul x p =>
      rw [LinearMap.rTensor_tmul,
        principalSubringTensorEquiv_tmul,
        principalSubringTensorEquiv_tmul]
      change principalSubringEmbedding K (c * x) *
          finiteSupportGradedEmbedding K p = _
      rw [map_mul]
      exact mul_assoc _ _ _
  | add x y hx hy => simp [map_add, hx, hy, mul_add]

/-- Multiplication by a nonzero componentwise-principal graded element preserves the intrinsic
maximal finite-support divisor predicate. -/
theorem isGradedMaximalFiniteSupportDivisor_mul_principal_iff (B : DegreeGraded K)
    {C : DegreeGraded K}
    (hC : IsPrincipalGraded C) (hC0 : C ≠ 0)
    (a : Associates (FiniteSupportRing (K := K))) :
    IsGradedMaximalFiniteSupportDivisor (B * C) a ↔
      IsGradedMaximalFiniteSupportDivisor B a := by
  rw [isPrincipalGraded_iff] at hC
  let c := rvProjection K C
  have hc : principalSubringEmbedding K c = C := by
    apply DirectSum.ext
    intro α
    rw [principalSubringEmbedding_apply, rvProjection_apply]
    exact
      principalComponentToHahnDegreeLayer_degreeLayerToPrincipalComponent_of_isPrincipal
        α (C α) (hC α)
  have hc0 : c ≠ 0 := by
    intro hzero
    apply hC0
    rw [← hc, hzero, map_zero]
  let e := principalSubringTensorEquiv K
  let z := e.symm B
  let f := LinearMap.mulLeft K c
  have hef : e (f.rTensor (FiniteSupportRing (K := K)) z) = B * C := by
    calc
      e (f.rTensor (FiniteSupportRing (K := K)) z) =
          principalSubringEmbedding K c * e z := by
        exact principalSubringTensorEquiv_mulLeft_rTensor c z
      _ = C * B := by rw [hc, e.apply_symm_apply]
      _ = B * C := mul_comm _ _
  have hpreimage :
      e.symm (B * C) = f.rTensor (FiniteSupportRing (K := K)) z := by
    apply e.injective
    rw [e.apply_symm_apply, hef]
  rw [← isContent_principalGradedTensorEquiv_symm_iff (B * C) a,
    ← isContent_principalGradedTensorEquiv_symm_iff B a,
    hpreimage]
  exact TensorProduct.isContent_rTensor_iff_of_injective
    f (principalSubringMulLeft_injective hc0) z a

/-- Multiplication by a nonzero componentwise-principal graded element preserves the canonical
maximal finite-support divisor class, assuming pairwise greatest-common-divisor existence. -/
theorem gradedMaximalFiniteSupportDivisor_mul_principal_eq_of_exists_gcd
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (B : DegreeGraded K)
    {C : DegreeGraded K}
    (hC : IsPrincipalGraded C) (hC0 : C ≠ 0) :
    gradedMaximalFiniteSupportDivisor (B * C) =
      gradedMaximalFiniteSupportDivisor B := by
  exact IsGradedMaximalFiniteSupportDivisor.eq
    (gradedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd (B * C))
    ((isGradedMaximalFiniteSupportDivisor_mul_principal_iff B hC hC0 _).mpr
        (gradedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd B))

/-- Multiplication by a nonzero componentwise-principal graded element preserves the normalized
maximal finite-support divisor, assuming pairwise greatest-common-divisor existence. This is the
field-generic core of LM24, Lemma 6.3.2. -/
theorem gradedNormalizedMaximalFiniteSupportDivisor_mul_principal_eq_of_exists_gcd
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (B : DegreeGraded K)
    {C : DegreeGraded K}
    (hC : IsPrincipalGraded C) (hC0 : C ≠ 0) :
    gradedNormalizedMaximalFiniteSupportDivisor (B * C) =
      gradedNormalizedMaximalFiniteSupportDivisor B := by
  rw [gradedNormalizedMaximalFiniteSupportDivisor_eq_normalizedRepresentative,
    gradedNormalizedMaximalFiniteSupportDivisor_eq_normalizedRepresentative,
    gradedMaximalFiniteSupportDivisor_mul_principal_eq_of_exists_gcd hgcd B hC hC0]

/-- Multiplication by a nonzero componentwise-principal graded element neither creates nor
destroys divisibility by an embedded finite-support series. -/
theorem finiteSupportGradedEmbedding_dvd_mul_principal_iff_of_exists_gcd
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (p : FiniteSupportRing (K := K))
    (B : DegreeGraded K)
    {C : DegreeGraded K}
    (hC : IsPrincipalGraded C) (hC0 : C ≠ 0) :
    finiteSupportGradedEmbedding K p ∣ B * C ↔
      finiteSupportGradedEmbedding K p ∣ B := by
  have hmaxBC :=
    gradedNormalizedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd (B * C)
  have hmaxB :=
    gradedNormalizedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd B
  have hmaxBC' :=
    (isNormalizedGradedMaximalFiniteSupportDivisor_iff _ _).mp hmaxBC
  have hmaxB' :=
    (isNormalizedGradedMaximalFiniteSupportDivisor_iff _ _).mp hmaxB
  rw [hmaxBC'.1 p, hmaxB'.1 p,
    gradedNormalizedMaximalFiniteSupportDivisor_mul_principal_eq_of_exists_gcd hgcd B hC hC0]

/-- Multiplication by a nonzero principal RV class preserves the normalized maximal
finite-support divisor of its canonical graded image. This is the field-generic core of LM24,
Lemma 6.3.1. -/
theorem gradedNormalizedMaximalFiniteSupportDivisor_rv_mul_principal_eq_of_exists_gcd
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (B : HahnDegreeRV K) {C : HahnDegreeRV K}
    (hC : IsPrincipalRV C) (hC0 : C ≠ 0) :
    gradedNormalizedMaximalFiniteSupportDivisor
        ((degreeValuation K).rvInitialFormHom (B * C)) =
      gradedNormalizedMaximalFiniteSupportDivisor
        ((degreeValuation K).rvInitialFormHom B) := by
  let w := degreeValuation K
  have hCImage := isPrincipalRVImage_initialForm C hC
  have hCPrincipal := (isPrincipalRVImage_iff (w.rvInitialFormHom C)).mp
    hCImage |>.2.2
  have hCImage0 : w.rvInitialFormHom C ≠ 0 := by
    intro hzero
    apply hC0
    apply w.rvInitialFormHom_injective
    simpa using hzero
  rw [map_mul]
  exact gradedNormalizedMaximalFiniteSupportDivisor_mul_principal_eq_of_exists_gcd hgcd
    (w.rvInitialFormHom B) hCPrincipal hCImage0

end

end Berarducci
