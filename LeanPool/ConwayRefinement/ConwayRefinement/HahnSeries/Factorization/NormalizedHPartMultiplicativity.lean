/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.NormalizedHPart

/-!
# Multiplication of normalized exponent-subgroup parts

LM24, Corollary 6.5.4 states that the normalized `H`-part of a product is the product of
the normalized `H`-parts. Its proof uses a specific Ritt-factorisation consequence: a normalized
`H`-divisor of a product of finite-support real series can be split into normalized `H`-divisors
of the two factors.

This module names that prerequisite explicitly and proves the complete reduction from it. The
prerequisite is neither installed as an instance nor folded into the definition of a normalized
`H`-part. Thus the intrinsic definition and uniqueness theorem remain independent of the later
Ritt and greatest-common-divisor proof.
-/

open scoped HahnSeries

universe v

public noncomputable section

namespace HahnSeries.Nonpositive

variable (H : AddSubgroup ℝ) {K : Type v} [Field K]

/-- Every normalized finite-support `H`-divisor of a product of finite-support real series splits
as a product of normalized `H`-divisors of the two factors. This is the exact factor-splitting
input used in LM24's proof of Corollary 6.5.4. -/
def HasNormalizedHDivisorRefinement : Prop :=
  ∀ (p q : FiniteSupportRing (G := ℝ) (K := K))
    (r : ConstantTermOneFiniteSupport (G := H) (K := K)),
      finiteSupportToReal H
          (r : FiniteSupportRing (G := H) (K := K)) ∣ p * q →
        ∃ r₁ r₂ : ConstantTermOneFiniteSupport (G := H) (K := K),
          r = r₁ * r₂ ∧
            finiteSupportToReal H
                (r₁ : FiniteSupportRing (G := H) (K := K)) ∣ p ∧
              finiteSupportToReal H
                  (r₂ : FiniteSupportRing (G := H) (K := K)) ∣ q

/-- Characterization of normalized `H`-divisor refinement by factor witnesses. -/
theorem hasNormalizedHDivisorRefinement_iff :
    HasNormalizedHDivisorRefinement H (K := K) ↔
      ∀ (p q : FiniteSupportRing (G := ℝ) (K := K))
        (r : ConstantTermOneFiniteSupport (G := H) (K := K)),
          finiteSupportToReal H
              (r : FiniteSupportRing (G := H) (K := K)) ∣ p * q →
            ∃ r₁ r₂ : ConstantTermOneFiniteSupport (G := H) (K := K),
              r = r₁ * r₂ ∧
                finiteSupportToReal H
                    (r₁ : FiniteSupportRing (G := H) (K := K)) ∣ p ∧
                  finiteSupportToReal H
                      (r₂ : FiniteSupportRing (G := H) (K := K)) ∣ q :=
  Iff.rfl

/-- The product of two normalized `H`-parts satisfies the normalized-part divisibility
characterization for the product. -/
theorem isNormalizedHPart_mul
    (hrefine : HasNormalizedHDivisorRefinement H (K := K))
    {p q : FiniteSupportRing (G := ℝ) (K := K)}
    {pH qH : ConstantTermOneFiniteSupport (G := H) (K := K)}
    (hpH : IsNormalizedHPart H p pH)
    (hqH : IsNormalizedHPart H q qH) :
    IsNormalizedHPart H (p * q) (pH * qH) := by
  rw [isNormalizedHPart_iff]
  have hpH' := (isNormalizedHPart_iff H p pH).mp hpH
  have hqH' := (isNormalizedHPart_iff H q qH).mp hqH
  intro r
  constructor
  · intro hr
    obtain ⟨r₁, r₂, rfl, hr₁, hr₂⟩ := hrefine p q r hr
    exact mul_dvd_mul (Iff.mp (hpH' r₁) hr₁) (Iff.mp (hqH' r₂) hr₂)
  · intro hr
    have hpDvd : finiteSupportToReal H
        (pH : FiniteSupportRing (G := H) (K := K)) ∣ p :=
      (hpH' pH).mpr dvd_rfl
    have hqDvd : finiteSupportToReal H
        (qH : FiniteSupportRing (G := H) (K := K)) ∣ q :=
      (hqH' qH).mpr dvd_rfl
    have hrMapped := (finiteSupportToReal H).map_dvd hr
    have hpartsDvd : finiteSupportToReal H
        ((pH * qH : ConstantTermOneFiniteSupport (G := H) (K := K)) :
          FiniteSupportRing (G := H) (K := K)) ∣ p * q := by
      change finiteSupportToReal H
        ((pH : FiniteSupportRing (G := H) (K := K)) *
          (qH : FiniteSupportRing (G := H) (K := K))) ∣ p * q
      rw [map_mul]
      exact mul_dvd_mul hpDvd hqDvd
    exact hrMapped.trans hpartsDvd

/-- Relational form of LM24, Corollary 6.5.4: any normalized `H`-part of a product equals the
product of normalized `H`-parts of its factors. -/
theorem normalizedHPart_mul_eq
    (hrefine : HasNormalizedHDivisorRefinement H (K := K))
    {p q : FiniteSupportRing (G := ℝ) (K := K)}
    {pH qH pqH : ConstantTermOneFiniteSupport (G := H) (K := K)}
    (hpH : IsNormalizedHPart H p pH)
    (hqH : IsNormalizedHPart H q qH)
    (hpqH : IsNormalizedHPart H (p * q) pqH) :
    pqH = pH * qH :=
  hpqH.eq H (isNormalizedHPart_mul H hrefine hpH hqH)

end HahnSeries.Nonpositive
