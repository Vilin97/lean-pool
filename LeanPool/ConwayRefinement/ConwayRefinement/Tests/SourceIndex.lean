/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Divisibility.PrimalPreimage
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.AssociatedGradedValuation
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.ResidueMathlib
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Tests.AlmostIrreducible
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Tests.AlmostIrreducibleFactorization
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Tests.GermLikeFactorization
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Tests.FiniteSupportGCD
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Tests.InfiniteSupportFactorization
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Tests.Multiplicativity
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Tests.NormalizedHPart
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Tests.NormalizedHPartMultiplicativity
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Tests.CardinalProposition922
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Tests.FiniteClassReduction
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Tests.Reduced
import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.Tests.ArchimedeanAssumptions
import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.Tests.CardinalIntegerPart
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Tests.OrdinalValueSubmultiplicative
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Tests.CriticalPoint
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Irreducibility
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OneRow
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Tests.DegreeTwo.TranslatedTruncationSpan
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.DegreeTwo.Factorization
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Tests.DegreeTwo.FactorizationClassification
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Tests.DegreeTwo.TranslatedSpanFactorization
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.DegreeTwo.DegreeTwoExample
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Tests.SectionSixFour
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Tests.SeriesMaximalFiniteSupportDivisor
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Degree.Tests.SupportSupremumMultiplicativity
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrderTypeMultiplicativity
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringTensor
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.GradedDivisibility
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.NormalizedHPartSeries
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportGCDProof
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportUnit
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.PrincipalAddition
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Degree.PrincipalMultiplicativity
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.IrreducibilityTransfer
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Degree.SupportSupremumMultiplicativity
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.SourceStatements
import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.RefinementConjecture
import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.DegreeTransfer
import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.NormalForm
import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ZFC.Identification
import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ZFC.Properness
import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ZFC.Refinement

/-!
# Compiled signatures of the source results

Exact type ascriptions for the published results used in the proof and for the structures on which
they rest. A change in hypotheses, quantifier order, endpoints, or ordinal operations fails
elaboration here. Semantic boundary examples distinguish the intended definitions from nearby
incorrect ones.

The refinement theorem has two isolated statements. `ConwayRefinement/Standalone/Mathlib/` fixes
its Hahn-series form against Mathlib alone, while
`ConwayRefinement/Standalone/CombinatorialGames/` fixes its concrete omnific-integer form against
Mathlib and CombinatorialGames alone.

The hash-command linter is disabled because checked signatures are this module's purpose.
-/
universe u v

open scoped DirectSum HahnSeries NatOrdinal Topology

public section

section ExactSignatures

/- LM24's unsigned normal-form criterion on the class presentation of Conway cuts. -/
  ∀ x : ZFSet.Surreal.{u}, x.IsOmnificInteger ↔
    ZFSet.Surreal.support x ⊆ Set.Ici 0 ∧
      ∃ z : ℤ, ZFSet.Surreal.coeff x 0 = (z : ℝ))

/- Every possible omnific factor or divisibility witness has a code. -/
  Function.Surjective (ZFSet.OmnificCode.value.{u}))

/- Properness of the code class and of its distinct numerical values. -/
  ∀ s : ZFSet.{u}, ZFSet.omnificGameCodes ≠ Class.ofSet s)
  ¬Small.{u} ZFSet.Surreal.OmnificInteger.{u})

/- The class comparison preserves the complete refinement conjecture, not a restricted case. -/
  ZFSet.Surreal.OmnificInteger.RefinementConjecture.{u} ↔ ConwayRefinementConjecture.{u})

/- LM17, Definition 4.1: the two support-order alternatives in the germ-like predicate. -/
  ∀ {K : Type u} [Field K] {a : Berarducci.Series K}, LM17.IsGermLike a →
    (a : K⟦ℝ⟧).supportOrderType = (Berarducci.ordinalValue a).val ∨
      (1 < Berarducci.ordinalValue a ∧
        (a : K⟦ℝ⟧).supportOrderType = (Berarducci.ordinalValue a).val + 1))

/- LM17, Theorem 4.8: every nonzero germ-like series factors into irreducibles. -/
  ∀ {K : Type u} [Field K] [CharZero K] {a : Berarducci.Series K},
    LM17.IsGermLike a → a ≠ 0 →
      ∃ f : Multiset (Berarducci.Series K),
        (∀ b ∈ f, Irreducible b) ∧ Associated f.prod a)

/- The degree-two-plus-one example exercises the second, nondegenerate germ-like branch. -/
  LM17.IsGermLike (PommersheimShahriari.DegreeTwoExample.degreeTwoWithConstant (K := ℚ)))

section ResidueStructures

variable {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M]
  [LinearOrder M] [IsOrderedCancelAddMonoid M]
  (ν : MaxAddDegree R M) (m : M)

#synth CommRing ν.ResidueRing

#synth Module ν.ResidueRing (ν.Component m)

end ResidueStructures

/- LM24, Fact 2.5.2: units and pairwise gcds in the nonpositive finite-support ring. -/
  ∀ {G : Type u} {K : Type v} [LinearOrder G] [AddCommGroup G]
    [IsOrderedAddMonoid G] [Field K]
    (p : (HahnSeries.Nonpositive.finiteSupportSubring :
      Subring (HahnSeries.Nonpositive G K))),
      IsUnit p ↔
        ∃ k : K, k ≠ 0 ∧
          p = HahnSeries.Nonpositive.finiteSupportScalarHom (G := G) k)
  ∀ {G : Type u} {K : Type v} [LinearOrder G] [AddCommGroup G]
    [IsOrderedAddMonoid G] [Field K]
    (p q : (HahnSeries.Nonpositive.finiteSupportSubring :
      Subring (HahnSeries.Nonpositive G K))),
      ∃ d : (HahnSeries.Nonpositive.finiteSupportSubring :
        Subring (HahnSeries.Nonpositive G K)),
        ∀ e : (HahnSeries.Nonpositive.finiteSupportSubring :
          Subring (HahnSeries.Nonpositive G K)),
          e ∣ p ∧ e ∣ q ↔ e ∣ d)

/- The same underlying `t⁻¹` distinguishes the nonpositive ring from the full group ring. -/
  ¬ IsUnit Tests.nonpositiveNegativeMonomial)
  IsUnit Tests.fullNegativeMonomial)

/- The zero-boundary gcd certificate retains both association and the defining orientation. -/
  ∃ d : Tests.IntegerNonpositiveFiniteSupportRing,
    (d ∣ Tests.nonpositiveNegativeMonomial ∧
        Tests.nonpositiveNegativeMonomial ∣ d) ∧
      ∀ e : Tests.IntegerNonpositiveFiniteSupportRing,
        e ∣ 0 ∧ e ∣ Tests.nonpositiveNegativeMonomial ↔ e ∣ d)
  ∀ {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M] [LinearOrder M]
    (ν : MaxAddDegree R M) (x y : R),
      ν.RVRel x y ↔
        (ν x = ⊥ ∧ ν y = ⊥) ∨
          (ν x ≠ ⊥ ∧ ν (x - y) < ν x))
  ∀ {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M]
    [LinearOrder M] [IsOrderedCancelAddMonoid M]
    (ν : MaxAddDegree R M) [ν.IsMultiplicative], ν.RV ≃* ν.HomogeneousClasses)
  ∀ {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M]
    [LinearOrder M] [IsOrderedCancelAddMonoid M]
    (ν : MaxAddDegree R M), MaxAddDegree ν.AssociatedGraded M)
  ∀ {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M] [LinearOrder M]
    (ν : MaxAddDegree R M) (x : ν.AssociatedGraded) (m : M),
      ν.associatedGradedValue x = (m : WithBot M) ↔
        x m ≠ 0 ∧ ∀ i, x i ≠ 0 → i ≤ m)
  ∀ {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M]
    [LinearOrder M] [IsOrderedCancelAddMonoid M]
    (ν : MaxAddDegree R M), ν.associatedGradedValuation.IsSeparated)
  ∀ {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M]
    [LinearOrder M] [IsOrderedCancelAddMonoid M]
    (ν : MaxAddDegree R M) (x : R),
      ν.associatedGradedValuation (ν.initialForm x) = ν x)
  ∀ {K : Type v} [Field K] (b c : Berarducci.Series K),
    Berarducci.ordinalValue (b + c) ≤
      max (Berarducci.ordinalValue b) (Berarducci.ordinalValue c))

/- Berarducci, Theorem 9.7 and Corollary 9.8. -/
  ∀ {K : Type v} [Field K] [CharZero K] (b c : Berarducci.Series K),
    Berarducci.ordinalValue (b * c) =
      Berarducci.ordinalValue b * Berarducci.ordinalValue c)

/- Berarducci, Lemma 10.1 and Definition 10.2. -/
  ∀ {K : Type v} [Field K] [CharZero K] {b : Berarducci.Series K}, b ≠ 0 →
    ∃ x : ℝ, Berarducci.IsCriticalPoint b x)

/- Berarducci, Lemma 10.4. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    {b c : Berarducci.Series K} {x y : ℝ},
      Berarducci.IsCriticalPoint b x → Berarducci.IsCriticalPoint c y →
        Berarducci.ordinalValue
            (Berarducci.translatedTruncation
              (((b * c : Berarducci.Series K) : K⟦ℝ⟧)) (x + y)) =
          Berarducci.ordinalValue
              (Berarducci.translatedTruncation (b : K⟦ℝ⟧) x) *
            Berarducci.ordinalValue
              (Berarducci.translatedTruncation (c : K⟦ℝ⟧) y))

/- Berarducci, Theorem 10.5: both alternatives for the support order type, the prohibition on
strictly negative monomial divisors, and both irreducibility conclusions. -/
  ∀ {K : Type v} [Field K] [CharZero K] {a : Berarducci.Series K},
    (∀ (gamma : ℝ) (hgamma : gamma < 0),
      ¬ HahnSeries.Nonpositive.single gamma (1 : K) hgamma.le ∣ a) →
    ((a : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ∨
      ∃ beta : Ordinal, (a : K⟦ℝ⟧).supportOrderType =
        Ordinal.omega0 ^ Ordinal.omega0 ^ beta) →
    Irreducible a ∧ Irreducible (a + 1))

/- Berarducci, Theorem 10.5, specialized to the coefficient-one row underlying LM24,
Example 9.2.8. -/
  ∀ {K : Type v} [Field K],
    (Berarducci.OneRow.withConstant (K := K) : K⟦ℝ⟧).supportOrderType =
      Ordinal.omega0 + 1)
  ∀ {K : Type v} [Field K] [CharZero K],
    Irreducible (Berarducci.OneRow.withoutConstant (K := K)) ∧
      Irreducible (Berarducci.OneRow.withConstant (K := K)))

/- PS06's quotient is by `J + K`, not Berarducci's ideal `J`. -/
  ∀ {K : Type v} [Field K] {b : Berarducci.Series K},
    b ∈ PommersheimShahriari.nearConstantSubmodule K ↔
      b ∈ Berarducci.nearConstantSubgroup K)
  PommersheimShahriari.toSeriesQuotientByJAddConstants
    (HahnSeries.Nonpositive.C (1 : ℚ)) = 0)
  Berarducci.toGerm (HahnSeries.Nonpositive.C (1 : ℚ)) ≠ 0)

/- PS06, Lemma 3.1: ordinal factorisation and the critical-point obstruction. -/
  ∀ {K : Type v} [Field K] {b c : Berarducci.Series K},
    Berarducci.ordinalValue b * Berarducci.ordinalValue c =
        ω^ (2 : NatOrdinal) →
      Berarducci.ordinalValue b ≤ Berarducci.ordinalValue c →
        (Berarducci.ordinalValue b = 1 ∧
          Berarducci.ordinalValue c = ω^ (2 : NatOrdinal)) ∨
        (Berarducci.ordinalValue b = ω^ (1 : NatOrdinal) ∧
          Berarducci.ordinalValue c = ω^ (1 : NatOrdinal)))
  ∀ {K : Type v} [Field K] [CharZero K]
    {a b c : Berarducci.Series K} {x y : ℝ},
      a = b * c → Berarducci.ordinalValue a = ω^ (2 : NatOrdinal) →
        (∀ u : ℝ, u < 0 →
          Berarducci.ordinalValue (Berarducci.translatedTruncation (a : K⟦ℝ⟧) u) <
            ω^ (2 : NatOrdinal)) →
          Berarducci.IsCriticalPoint b x → Berarducci.IsCriticalPoint c y →
            x = 0 ∧ y = 0)

/- PS06, Lemma 3.1, complete support-order classification. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    {a b c : Berarducci.Series K},
      a ∉ Berarducci.nearConstantSubgroup K →
      ((a : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ^ (2 : Ordinal) ∨
        (a : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ^ (2 : Ordinal) + 1) →
      a = b * c → Berarducci.ordinalValue b ≤ Berarducci.ordinalValue c →
      (∃ k : K, k ≠ 0 ∧ b = HahnSeries.Nonpositive.C k ∧
        c = HahnSeries.Nonpositive.C k⁻¹ * a ∧
        (c : K⟦ℝ⟧).supportOrderType = (a : K⟦ℝ⟧).supportOrderType) ∨
        (((b : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ∨
            (b : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 + 1) ∧
          ((c : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ∨
            (c : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 + 1) ∧
          Berarducci.ordinalValue b = ω^ (1 : NatOrdinal) ∧
          Berarducci.ordinalValue c = ω^ (1 : NatOrdinal)))
  ∀ {K : Type v} [Field K] [CharZero K]
    {a b c : Berarducci.Series K},
      a ∉ Berarducci.nearConstantSubgroup K →
      ((a : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ^ (2 : Ordinal) ∨
        (a : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ^ (2 : Ordinal) + 1) →
      a = b * c → Berarducci.ordinalValue b ≤ Berarducci.ordinalValue c →
      (∃ k : K, k ≠ 0 ∧ b = HahnSeries.Nonpositive.C k ∧
        c = HahnSeries.Nonpositive.C k⁻¹ * a ∧
        (c : K⟦ℝ⟧).supportOrderType = (a : K⟦ℝ⟧).supportOrderType) ∨
        (((b : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ∨
            (b : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 + 1) ∧
          ((c : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ∨
            (c : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 + 1) ∧
          Berarducci.ordinalValue b = ω^ (1 : NatOrdinal) ∧
          Berarducci.ordinalValue c = ω^ (1 : NatOrdinal)))

/- PS06, Proposition 3.2(2) and (5), upper-bound direction. -/
  ∀ {K : Type v} [Field K] {b c : Berarducci.Series K},
    Berarducci.ordinalValue b = ω^ (1 : NatOrdinal) →
      Berarducci.ordinalValue c = ω^ (1 : NatOrdinal) →
      Berarducci.IsCriticalPoint b 0 → Berarducci.IsCriticalPoint c 0 →
        Module.finrank K (PommersheimShahriari.translatedTruncationSpan (b * c)) ≤ 2)

/- PS06, Proposition 3.2(5), without a finite-dimensionality assumption. -/
  ∀ {K : Type v} [Field K] {b c : Berarducci.Series K},
    Berarducci.ordinalValue b = ω^ (1 : NatOrdinal) →
      Berarducci.ordinalValue c = ω^ (1 : NatOrdinal) →
      Berarducci.IsCriticalPoint b 0 → Berarducci.IsCriticalPoint c 0 →
        Module.rank K (PommersheimShahriari.translatedTruncationSpan (b * c)) ≤ 2)

/- PS06, Corollary 3.3. -/
  ∀ {K : Type v} [Field K] [CharZero K] {a : Berarducci.Series K},
    a ∉ Berarducci.nearConstantSubgroup K →
      ((a : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ^ (2 : Ordinal) ∨
        (a : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ^ (2 : Ordinal) + 1) →
      2 < Module.finrank K (PommersheimShahriari.translatedTruncationSpan a) → Irreducible a)

/- PS06, Corollary 3.3, in cardinal-rank form. -/
  ∀ {K : Type v} [Field K] [CharZero K] {a : Berarducci.Series K},
    a ∉ Berarducci.nearConstantSubgroup K →
      ((a : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ^ (2 : Ordinal) ∨
        (a : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ^ (2 : Ordinal) + 1) →
      (2 : Cardinal) <
        Module.rank K (PommersheimShahriari.translatedTruncationSpan a) → Irreducible a)

/- The explicit coefficient-one `ω² + 1` series supplied by the PS06 criterion. -/
  ∀ {K : Type v} [Field K],
    ((PommersheimShahriari.DegreeTwoExample.degreeTwoWithConstant (K := K) :
      Berarducci.Series K) : K⟦ℝ⟧).supportOrderType =
        Ordinal.omega0 ^ (2 : Ordinal) + 1)
  ∀ {K : Type v} [Field K] [CharZero K],
    Irreducible
      (PommersheimShahriari.DegreeTwoExample.degreeTwoWithConstant (K := K)))
  ∀ {K : Type v} [Field K] [CharZero K] {a : Berarducci.Series K},
    a ∉ Berarducci.nearConstantSubgroup K →
      ((a : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ^ (2 : Ordinal) ∨
        (a : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ^ (2 : Ordinal) + 1) →
      2 < Module.finrank K (PommersheimShahriari.translatedTruncationSpan a) → Irreducible a)
  ∀ {K : Type v} [Field K] [CharZero K],
    (HahnSeries.Nonpositive.negativeMonomialIdeal K).IsPrime)

/- Berarducci, Corollary 9.9, imported by LM24 as Fact 3.4.1. -/
  ∀ {K : Type v} [Field K] [CharZero K],
    HahnSeries.Nonpositive.OrderTypeMultiplicativeOnWeaklyPrincipal K)

/- LM24, Propositions 3.5.1(2) and 3.6.1. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    (b c : HahnSeries.Nonpositive ℝ K),
      HahnSeries.Nonpositive.supportSup (b * c) =
        HahnSeries.Nonpositive.supportSup b + HahnSeries.Nonpositive.supportSup c)
  ∀ {K : Type v} [Field K] [CharZero K]
    {b c : HahnSeries.Nonpositive ℝ K},
      HahnSeries.Nonpositive.IsPrincipal b →
        HahnSeries.Nonpositive.IsPrincipal c →
          HahnSeries.Nonpositive.IsPrincipal (b * c))

/- Boundary certificates exercise the proved characteristic-zero theorems on nonconstant
inputs. -/
  Berarducci.ordinalValue
      (Tests.approachZeroNonpositive *
        Tests.approachZeroNonpositive) =
    Berarducci.ordinalValue Tests.approachZeroNonpositive *
      Berarducci.ordinalValue Tests.approachZeroNonpositive)
  ((Tests.twoTermNonprincipal * Tests.twoTermNonprincipal :
    HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧).degree =
    (Tests.twoTermNonprincipal : ℚ⟦ℝ⟧).degree +
      (Tests.twoTermNonprincipal : ℚ⟦ℝ⟧).degree)
  ∃ b : HahnSeries.Nonpositive ℝ ℚ,
    HahnSeries.Nonpositive.supportSup b = 0 ∧
      0 ∉ (b : ℚ⟦ℝ⟧).support ∧
      HahnSeries.Nonpositive.supportSup (b * b) = 0)
  ∀ {K : Type v} [Field K] {b : Berarducci.Series K},
    Berarducci.ordinalValueDegree b = ⊥ ↔
      b ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K)
  ∀ {K : Type v} [Field K] (b : Berarducci.Series K),
      Berarducci.ordinalValueDegreeValuation K b = ⊥ ↔
        b ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K)
  ∀ {K : Type v} [Field K]
    (α : NatOrdinal) (b c : Berarducci.Series K)
    (hb : Berarducci.ordinalValue b < ω^ (α + 1))
    (hc : Berarducci.ordinalValue c < ω^ (α + 1)),
      Berarducci.principalComponentMk α b hb =
          Berarducci.principalComponentMk α c hc ↔
        Berarducci.ordinalValue (b - c) < ω^ α)
  ∀ {K : Type v} [Field K] (α : NatOrdinal)
    (x : Berarducci.PrincipalComponent K α), x ≠ 0 →
      ∃ (p : Berarducci.Series K)
        (hpBound : Berarducci.ordinalValue p < ω^ (α + 1)),
          HahnSeries.Nonpositive.IsPrincipal p ∧
            (p : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal) ∧
            Berarducci.principalComponentMk α p hpBound = x)

/- The equal-degree specialization of LM24, Proposition 3.6.2 used in Lemma 7.2.3. The
unrestricted printed proposition is false. -/
  ∀ {K : Type v} [Field K] {b c : HahnSeries.Nonpositive ℝ K},
    HahnSeries.Nonpositive.IsPrincipal b →
      HahnSeries.Nonpositive.IsPrincipal c →
        (c : K⟦ℝ⟧).degree = (b : K⟦ℝ⟧).degree →
          ((b + c : HahnSeries.Nonpositive ℝ K) : K⟦ℝ⟧).degree =
              (b : K⟦ℝ⟧).degree →
            HahnSeries.Nonpositive.IsPrincipal (b + c))
  ∀ {K : Type v} [Field K] {p : Berarducci.Series K}
    (_hp : HahnSeries.Nonpositive.IsPrincipal p) {α : NatOrdinal},
      (p : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal) →
        Berarducci.ordinalValue p = ω^ α)
  ∀ {K : Type v} [Field K]
    (α : NatOrdinal) {b c : Berarducci.Series K}
    (_hb : HahnSeries.Nonpositive.IsPrincipal b)
    (_hc : HahnSeries.Nonpositive.IsPrincipal c)
    (hbDegree : (b : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal))
    (hcDegree : (c : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal)),
      Berarducci.degreeLayerMk α b hbDegree.le =
          Berarducci.degreeLayerMk α c hcDegree.le ↔
        Berarducci.ordinalValue (b - c) < ω^ α)
  ∀ (K : Type v) [Field K]
    (α : NatOrdinal),
      Berarducci.principalDegreeClasses K α ≃ₗ[K]
        Berarducci.PrincipalComponent K α)

/- LM24, Proposition 5.3.1. -/
  ∀ (K : Type v) [Field K] [CharZero K]
    (α : NatOrdinal),
      TensorProduct K (Berarducci.PrincipalComponent K α)
          Berarducci.FiniteSupportRing ≃ₗ[K]
        (HahnSeries.Nonpositive.degreeValuation K).Component α)

/- LM24, Proposition 6.1.2, under the paper's blanket characteristic-zero hypothesis. -/
      (Berarducci.principalSubringTensorEquiv K :
        TensorProduct K (Berarducci.PrincipalSubring K)
            Berarducci.FiniteSupportRing ≃ₐ[K]
          Berarducci.DegreeGraded K))
  ∀ {K : Type v} [Field K] [CharZero K]
    (x : Berarducci.PrincipalSubring K)
    (p : Berarducci.FiniteSupportRing) (α : NatOrdinal),
      Berarducci.principalSubringTensorEquiv K (x ⊗ₜ p) α =
        Berarducci.principalComponentTensorEquiv K α (x α ⊗ₜ p))
  ∀ {K : Type v} [Field K] [CharZero K]
    (z : TensorProduct K (Berarducci.PrincipalSubring K)
      Berarducci.FiniteSupportRing) (α : NatOrdinal),
      Berarducci.principalSubringTensorEquiv K z α =
        Berarducci.principalComponentTensorEquiv K α
          (Berarducci.principalSubringTensorComponent K α z))

/- LM24, Proposition 5.4.3. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    (B : Berarducci.HahnDegreeRV K),
      ∃ p : Berarducci.FiniteSupportRing,
        (∀ q : Berarducci.FiniteSupportRing,
          Berarducci.finiteSupportRVEmbedding K q ∣ B ↔ q ∣ p) ∧
        (∀ p' : Berarducci.FiniteSupportRing,
          (∀ q : Berarducci.FiniteSupportRing,
            Berarducci.finiteSupportRVEmbedding K q ∣ B ↔ q ∣ p') →
          ∃ k : K, k ≠ 0 ∧
            p' = HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k * p) ∧
        (Berarducci.IsPrincipalRV B →
          ∃ k : K,
            p = HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k))

/- LM24, Corollary 5.4.4. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    (B : Berarducci.DegreeGraded K),
      ∃ p : Berarducci.FiniteSupportRing,
        (∀ q : Berarducci.FiniteSupportRing,
          Berarducci.finiteSupportGradedEmbedding K q ∣ B ↔ q ∣ p) ∧
        ∀ p' : Berarducci.FiniteSupportRing,
          (∀ q : Berarducci.FiniteSupportRing,
            Berarducci.finiteSupportGradedEmbedding K q ∣ B ↔ q ∣ p') →
          ∃ k : K, k ≠ 0 ∧
            p' = HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k * p)

/- LM24, Notation 5.4.5. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    (B : Berarducci.DegreeGraded K),
      ∃! p : Berarducci.FiniteSupportRing,
        Berarducci.IsNormalizedGradedMaximalFiniteSupportDivisor B p)

/- LM24, Remark 5.4.6. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    (B : Berarducci.DegreeGraded K),
      Berarducci.finiteSupportGradedEmbedding K
          (Berarducci.gradedNormalizedMaximalFiniteSupportDivisor B) ∣ B)

/- LM24, Proposition 5.4.8. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    (B C : Berarducci.DegreeGraded K),
      Berarducci.gradedNormalizedMaximalFiniteSupportDivisor B *
          Berarducci.gradedNormalizedMaximalFiniteSupportDivisor C ∣
        Berarducci.gradedNormalizedMaximalFiniteSupportDivisor (B * C))

/- LM24, Proposition 5.5.1. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    (b : Berarducci.Series K),
      ∃ p : Berarducci.FiniteSupportRing,
        (∀ q : Berarducci.FiniteSupportRing,
          (q : Berarducci.Series K) ∣ b ↔ q ∣ p) ∧
        ∀ p' : Berarducci.FiniteSupportRing,
          (∀ q : Berarducci.FiniteSupportRing,
            (q : Berarducci.Series K) ∣ b ↔ q ∣ p') →
          ∃ k : K, k ≠ 0 ∧
            p' = HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k * p)

/- LM24, Notation 5.5.2. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    (b : Berarducci.Series K),
      ∃! p : Berarducci.FiniteSupportRing,
        Berarducci.IsNormalizedSeriesMaximalFiniteSupportDivisor b p)
  ∀ {K : Type v} [Field K] [CharZero K]
    (b : Berarducci.Series K),
      Berarducci.IsNormalizedSeriesMaximalFiniteSupportDivisor b
        (Berarducci.seriesNormalizedMaximalFiniteSupportDivisor b))

/- LM24, Remark 5.5.3. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    (b : Berarducci.Series K),
      (Berarducci.seriesNormalizedMaximalFiniteSupportDivisor b :
        Berarducci.Series K) ∣ b)
  ∀ (K : Type v) [Field K] [CharZero K],
      Berarducci.seriesNormalizedMaximalFiniteSupportDivisor
        (0 : Berarducci.Series K) = 0)
  ∀ {K : Type v} [Field K] [CharZero K]
    (p : Berarducci.FiniteSupportRing),
      ∃ k : K, k ≠ 0 ∧
        Berarducci.seriesNormalizedMaximalFiniteSupportDivisor
            (p : Berarducci.Series K) =
          HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k * p)
  ∀ {K : Type v} [Field K] [CharZero K]
    (p : Berarducci.FiniteSupportRing),
      Berarducci.seriesNormalizedMaximalFiniteSupportDivisor
          (p : Berarducci.Series K) =
        Berarducci.gradedNormalizedMaximalFiniteSupportDivisor
          (Berarducci.finiteSupportGradedEmbedding K p))
  ∀ {K : Type v} [Field K] [CharZero K]
    {b : Berarducci.Series K},
      HahnSeries.Nonpositive.IsPrincipal b →
        Berarducci.seriesNormalizedMaximalFiniteSupportDivisor b = 1)

/- LM24, Proposition 5.5.5. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    (b c : Berarducci.Series K),
      Berarducci.seriesNormalizedMaximalFiniteSupportDivisor b *
          Berarducci.seriesNormalizedMaximalFiniteSupportDivisor c ∣
        Berarducci.seriesNormalizedMaximalFiniteSupportDivisor (b * c))

/- LM24, Example 5.5.4. -/
  Berarducci.IsRVMaximalFiniteSupportDivisor
    ((HahnSeries.Nonpositive.degreeValuation ℚ).rv Tests.seriesMaximalExample)
    (Associates.mk Tests.seriesMaximalExampleRVDivisor))
  ∀ (_hgcd : ∀ p q : Berarducci.FiniteSupportRing,
      ∃ d : Berarducci.FiniteSupportRing,
        ∀ e : Berarducci.FiniteSupportRing, e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (_hunits : ∀ u : Berarducci.FiniteSupportRing,
      IsUnit u ↔ ∃ k : ℚ, k ≠ 0 ∧
        u = HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k),
      Berarducci.seriesNormalizedMaximalFiniteSupportDivisor
          Tests.seriesMaximalExample =
        Tests.seriesMaximalExampleDivisor)
  ∀ (_hgcd : ∀ p q : Berarducci.FiniteSupportRing,
      ∃ d : Berarducci.FiniteSupportRing,
        ∀ e : Berarducci.FiniteSupportRing, e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (_hunits : ∀ u : Berarducci.FiniteSupportRing,
      IsUnit u ↔ ∃ k : ℚ, k ≠ 0 ∧
        u = HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k),
      Berarducci.gradedNormalizedMaximalFiniteSupportDivisor
          Tests.seriesMaximalExampleLeadingGraded =
        Tests.seriesMaximalExampleRVDivisor)
  Tests.seriesMaximalExampleRVDivisor ≠
    Tests.seriesMaximalExampleDivisor)

/- LM24, Proposition 5.6.1. The list is the finite sequence `c₁, …, cₙ`, and its length
is `n`. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    {b : Berarducci.Series K}, b ≠ 0 →
      ∃ (factors : List (Berarducci.Series K)) (k : K),
        b = HahnSeries.Nonpositive.C k *
          (Berarducci.seriesNormalizedMaximalFiniteSupportDivisor b :
            Berarducci.Series K) * factors.prod ∧
          (∀ c ∈ factors,
            Irreducible c ∧ (c : K⟦ℝ⟧).support.Infinite) ∧
          factors.length ≤
            HahnSeries.degreeCantorTermCount (b : K⟦ℝ⟧))
  ∀ {K : Type v} [Field K] [CharZero K]
    {b : Berarducci.Series K}, b ≠ 0 →
      ∃ (factors : List (Berarducci.Series K)) (k : K),
        k ≠ 0 ∧
          b = HahnSeries.Nonpositive.C k *
            (Berarducci.seriesNormalizedMaximalFiniteSupportDivisor b :
              Berarducci.Series K) * factors.prod ∧
          (∀ c ∈ factors,
            Irreducible c ∧ (c : K⟦ℝ⟧).support.Infinite) ∧
          factors.length ≤
            HahnSeries.degreeCantorTermCount (b : K⟦ℝ⟧))
  ¬Berarducci.HasOnlyUnitFiniteSupportDivisors
    (0 : Berarducci.Series ℚ))

/- LM24, Proposition 6.2.1. -/
  ∀ {K : Type v} [Field K]
    [CharZero K]
    {B C : Berarducci.DegreeGraded K},
      B ≠ 0 → C ≠ 0 →
        B * C ∈
          (HahnSeries.Nonpositive.degreeValuation K).homogeneousClasses →
        B ∈
            (HahnSeries.Nonpositive.degreeValuation K).homogeneousClasses ∧
          C ∈
            (HahnSeries.Nonpositive.degreeValuation K).homogeneousClasses)

/- The exact graded-image model of `P` used in LM24, Corollary 6.2.2. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    (x : Berarducci.DegreeGraded K),
      Berarducci.IsPrincipalRVImage x ↔
        ∃ B : Berarducci.HahnDegreeRV K,
          Berarducci.IsPrincipalRV B ∧
            (HahnSeries.Nonpositive.degreeValuation K).rvInitialFormHom B = x)

/- The intrinsic characterization of the exact graded-image model of `P`. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    (x : Berarducci.DegreeGraded K),
      Berarducci.IsPrincipalRVImage x ↔
        x ≠ 0 ∧
          x ∈
              (HahnSeries.Nonpositive.degreeValuation K).homogeneousClasses ∧
            Berarducci.IsPrincipalGraded x)

/- LM24, Corollary 6.2.2, `P̂` clause. -/
  ∀ {K : Type v} [Field K]
    [CharZero K]
    {B C : Berarducci.DegreeGraded K},
      B ≠ 0 → C ≠ 0 → Berarducci.IsPrincipalGraded (B * C) →
        Berarducci.IsPrincipalGraded B ∧
          Berarducci.IsPrincipalGraded C)

/- LM24, Corollary 6.2.2, `P` clause. -/
  ∀ {K : Type v} [Field K]
    [CharZero K]
    {B C : Berarducci.DegreeGraded K},
      B ≠ 0 → C ≠ 0 → Berarducci.IsPrincipalRVImage (B * C) →
        Berarducci.IsPrincipalRVImage B ∧
          Berarducci.IsPrincipalRVImage C)

/- LM24, Corollary 6.2.3, RV clause. -/
  ∀ {K : Type v} [Field K]
    [CharZero K]
    (B C : Berarducci.HahnDegreeRV K),
      B ∣ C ↔
        (HahnSeries.Nonpositive.degreeValuation K).rvInitialFormHom B ∣
          (HahnSeries.Nonpositive.degreeValuation K).rvInitialFormHom C)

/- LM24, Corollary 6.2.3, finite-support clause. -/
  ∀ {K : Type v} [Field K]
    [CharZero K]
    (p q : Berarducci.FiniteSupportRing),
      Berarducci.finiteSupportGradedEmbedding K p ∣
          Berarducci.finiteSupportGradedEmbedding K q ↔
        p ∣ q)

/- LM24, Proposition 6.2.4. -/
  ∀ {K : Type v} [Field K]
    [CharZero K]
    (B : Berarducci.HahnDegreeRV K)
    (C : Berarducci.DegreeGraded K),
      (HahnSeries.Nonpositive.degreeValuation K).rvInitialFormHom B ∣ C ↔
        ∀ α,
          (HahnSeries.Nonpositive.degreeValuation K).rvInitialFormHom B ∣
            DirectSum.of
              (HahnSeries.Nonpositive.degreeValuation K).Component
              α (C α))

/- LM24, Lemma 6.3.1. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    (B C : Berarducci.HahnDegreeRV K),
      Berarducci.IsPrincipalRV C → C ≠ 0 →
        Berarducci.gradedNormalizedMaximalFiniteSupportDivisor
            ((HahnSeries.Nonpositive.degreeValuation K).rvInitialFormHom (B * C)) =
          Berarducci.gradedNormalizedMaximalFiniteSupportDivisor
            ((HahnSeries.Nonpositive.degreeValuation K).rvInitialFormHom B))

/- LM24, Lemma 6.3.2. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    (B C : Berarducci.DegreeGraded K),
      Berarducci.IsPrincipalGraded C → C ≠ 0 →
        Berarducci.gradedNormalizedMaximalFiniteSupportDivisor (B * C) =
          Berarducci.gradedNormalizedMaximalFiniteSupportDivisor B)

/- LM24, Lemma 6.3.3. -/
  ∀ (K : Type v) [Field K] [CharZero K],
    @Algebra.IsRelativelyAlgebraicallyClosed K
      (Berarducci.PrincipalSubringFractionField K) _ _
      (Berarducci.principalSubringFractionAlgebra K))

/- LM24, Lemma 6.3.4. The nonzeroness of the inverted coefficient is made explicit because
Lean's inverse is total. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    {p₁ p₂ : Berarducci.PrincipalSubringFractionFiniteSupportRing K},
      p₁ ≠ 0 → p₂ ≠ 0 →
        p₁ * p₂ ∈ Berarducci.principalSubringFractionCoefficientSubring K →
          ∃ B : Berarducci.PrincipalSubringFractionField K,
            B ≠ 0 ∧
              p₁ * HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) B ∈
                Berarducci.principalSubringFractionCoefficientSubring K ∧
              p₂ * HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) B⁻¹ ∈
                Berarducci.principalSubringFractionCoefficientSubring K)

/- Guardrail: omitting the preceding `B ≠ 0` lets `B = 0` satisfy both membership clauses for
arbitrary factors under Lean's total inverse. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    (p₁ p₂ : Berarducci.PrincipalSubringFractionFiniteSupportRing K),
      ∃ B : Berarducci.PrincipalSubringFractionField K,
        p₁ * HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) B ∈
            Berarducci.principalSubringFractionCoefficientSubring K ∧
          p₂ * HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) B⁻¹ ∈
            Berarducci.principalSubringFractionCoefficientSubring K)

/- LM24, Remark 6.3.5. Under the identification of Remark 6.1.3, coefficient extension
reflects divisibility. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    (p q : HahnSeries.Nonpositive.FiniteSupportRing (G := ℝ) (K := K)),
      Berarducci.principalSubringFractionScalarExtension K p ∣
          Berarducci.principalSubringFractionScalarExtension K q ↔
        p ∣ q)

/- LM24, Corollary 6.3.6, in the stronger factor-witness form used in its proof. The
finite-support factors remain elements of `K(ℝ^{≤ 0})`. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    (p : Berarducci.FiniteSupportRing)
    (B C : Berarducci.DegreeGraded K),
      Berarducci.finiteSupportGradedEmbedding K p ∣ B * C →
        ∃ p₁ p₂ : Berarducci.FiniteSupportRing,
          p = p₁ * p₂ ∧
            Berarducci.finiteSupportGradedEmbedding K p₁ ∣ B ∧
            Berarducci.finiteSupportGradedEmbedding K p₂ ∣ C)

/- LM24, Corollary 6.3.6. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    (p : Berarducci.FiniteSupportRing),
      IsPrimal (Berarducci.finiteSupportGradedEmbedding K p))

/- LM24, Corollary 6.3.7. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    (B C : Berarducci.DegreeGraded K),
      Berarducci.gradedNormalizedMaximalFiniteSupportDivisor (B * C) =
        Berarducci.gradedNormalizedMaximalFiniteSupportDivisor B *
          Berarducci.gradedNormalizedMaximalFiniteSupportDivisor C)

/- LM24, Proposition 6.3.8. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    (b c : Berarducci.Series K),
      Berarducci.seriesNormalizedMaximalFiniteSupportDivisor (b * c) =
        Berarducci.seriesNormalizedMaximalFiniteSupportDivisor b *
          Berarducci.seriesNormalizedMaximalFiniteSupportDivisor c)

/- LM24, Corollary 6.3.9, in the stronger factor-witness form used in its proof. The factors
remain in the finite-support subring, and their equality is asserted in the ambient series ring. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    (p : Berarducci.FiniteSupportRing (K := K)) (b c : Berarducci.Series K),
      (p : Berarducci.Series K) ∣ b * c →
        ∃ p₁ p₂ : Berarducci.FiniteSupportRing (K := K),
          (p : Berarducci.Series K) =
              (p₁ : Berarducci.Series K) * (p₂ : Berarducci.Series K) ∧
            (p₁ : Berarducci.Series K) ∣ b ∧
            (p₂ : Berarducci.Series K) ∣ c)

/- LM24, Theorem 6.4.1. The list is the sequence `c₁, …, cₙ`, its length is `n`, and
only the finite-support factor is asserted to be unique. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    {b : Berarducci.Series K}, b ≠ 0 →
      ∃ (p : Berarducci.FiniteSupportRing (K := K))
        (factors : List (Berarducci.Series K)),
        Berarducci.IsInfiniteSupportIrreducibleFactorization b p factors ∧
          factors.length ≤
            HahnSeries.degreeCantorTermCount (b : K⟦ℝ⟧) ∧
          Berarducci.IsUniqueFiniteSupportFactorUpToScalar b p)

/- Pending exact target for LM24, Corollary 6.4.2. `DecompositionMonoid` is the
pre-Schreier condition, while `GCDMonoid` contains data and is therefore asserted through
`Nonempty`. This anonymous fixture freezes the proposition without introducing a theorem stub. -/
  ((DecompositionMonoid (Berarducci.Series K) ↔
      Nonempty (GCDMonoid (Berarducci.Series K))) ∧
    (Nonempty (GCDMonoid (Berarducci.Series K)) ↔
      ∀ c : Berarducci.Series K,
        Irreducible c → (c : K⟦ℝ⟧).support.Infinite → Prime c)))

/- Boundary guardrail for Theorem 6.4.1: the source permits `n = 0`. -/
  Berarducci.IsInfiniteSupportIrreducibleFactorization
    (1 : Berarducci.Series ℚ)
      (1 : Berarducci.FiniteSupportRing (K := ℚ)) [])

/- Scalar-uniqueness guardrail: literal equality of finite-support factors is false. -/
  (-1 : Berarducci.FiniteSupportRing (K := ℚ)) ≠ 1)

/- LM24, Section 6.5, definition of almost irreducibility. The factorisation form makes the
quotient in the printed wording explicit without choosing a division operation. -/
  ∀ {H : AddSubgroup ℝ} {K : Type v} [Field K]
    {b : HahnSeries.Nonpositive H K},
      HahnSeries.Nonpositive.IsAlmostIrreducible b ↔
        ∀ c d : HahnSeries.Nonpositive H K, b = c * d →
          ¬HahnSeries.Nonpositive.IsMonomial c →
            HahnSeries.Nonpositive.IsMonomial d)

/- LM24, Remark 6.5.1, first assertion. -/
  ∀ {H : AddSubgroup ℝ} {K : Type v} [Field K]
    {b : HahnSeries.Nonpositive H K}, Irreducible b →
      HahnSeries.Nonpositive.IsAlmostIrreducible b)

/- Corrected second assertion of LM24, Remark 6.5.1. The printed statement omits the
necessary hypothesis that `b` is not a unit. -/
open HahnSeries.Nonpositive in
  ∀ {H : AddSubgroup ℝ} {K : Type v} [Field K]
    {b : HahnSeries.Nonpositive H K},
      HahnSeries.Nonpositive.IsAlmostIrreducible b → ¬IsUnit b →
        HahnSeries.Nonpositive.realSupportSup H b = 0 → Irreducible b)

/- Counterexample to the printed second assertion of LM24, Remark 6.5.1. -/
  HahnSeries.Nonpositive.IsAlmostIrreducible
      (1 : Tests.RealExponentSeries) ∧
    HahnSeries.Nonpositive.realSupportSup Tests.RealExponentSubgroup
        (1 : Tests.RealExponentSeries) = 0 ∧
      ¬Irreducible (1 : Tests.RealExponentSeries))

/- LM24, Remark 6.5.1, final assertion. -/
  ∀ {H : AddSubgroup ℝ} {K : Type v} [Field K] [DivisibleBy H ℤ]
    {b : HahnSeries.Nonpositive H K},
      HahnSeries.Nonpositive.realSupportSup H b < 0 → ¬Irreducible b)

/- Corrected exact target for LM24, Lemma 6.5.2. The printed universal quantifier includes
`p = 0`, although the proof and the notation `p_H` require `p ≠ 0`. This proposition remains
uninhabited until the Ritt-factorisation prerequisites are available. -/
    [DivisibleBy H ℤ]
    (p : HahnSeries.Nonpositive.FiniteSupportRing (G := ℝ) (K := K)) ↦
  p ≠ 0 →
    ∃! q : HahnSeries.Nonpositive.ConstantTermOneFiniteSupport
        (G := H) (K := K),
      HahnSeries.Nonpositive.IsNormalizedHPart H p q)

/- Semantic boundary for the normalized `H`-part predicate: the identity has the identity as
its unique normalized part. -/
  ∀ (H : AddSubgroup ℝ) {K : Type v} [Field K],
    ∃! q : HahnSeries.Nonpositive.ConstantTermOneFiniteSupport
        (G := H) (K := K),
      HahnSeries.Nonpositive.IsNormalizedHPart H
        (1 : HahnSeries.Nonpositive.FiniteSupportRing (G := ℝ) (K := K)) q)

/- The uniqueness part of LM24, Lemma 6.5.2 is proved without the Ritt existence input. -/
  ∀ {H : AddSubgroup ℝ} {K : Type v} [Field K]
    {p : HahnSeries.Nonpositive.FiniteSupportRing (G := ℝ) (K := K)}
    {q q' : HahnSeries.Nonpositive.ConstantTermOneFiniteSupport
      (G := H) (K := K)},
      HahnSeries.Nonpositive.IsNormalizedHPart H p q →
        HahnSeries.Nonpositive.IsNormalizedHPart H p q' → q = q')

/- Corrected exact target for LM24, Corollary 6.5.3. The nonzero hypothesis ensures that the
normalized `H`-part of `p(b)` is defined. This relational statement avoids choosing it before
Lemma 6.5.2 is proved. -/
    [DivisibleBy H ℤ] (b : HahnSeries.Nonpositive ℝ K) ↦
  b ≠ 0 →
    ∀ pH : HahnSeries.Nonpositive.ConstantTermOneFiniteSupport (G := H) (K := K),
      HahnSeries.Nonpositive.IsNormalizedHPart H
          (Berarducci.seriesNormalizedMaximalFiniteSupportDivisor b) pH →
        ∀ q : HahnSeries.Nonpositive.ConstantTermOneFiniteSupport (G := H) (K := K),
          HahnSeries.Nonpositive.mapDomainToReal H
              ((q : HahnSeries.Nonpositive.FiniteSupportRing (G := H) (K := K)) :
                HahnSeries.Nonpositive H K) ∣ b ↔
            (q : HahnSeries.Nonpositive.FiniteSupportRing (G := H) (K := K)) ∣
              (pH : HahnSeries.Nonpositive.FiniteSupportRing (G := H) (K := K)))

/- The proved, prerequisite-explicit reduction underlying Corollary 6.5.3. -/
  ∀ (H : AddSubgroup ℝ) {K : Type v} [Field K]
    {b : HahnSeries.Nonpositive ℝ K}
    {p : HahnSeries.Nonpositive.FiniteSupportRing (G := ℝ) (K := K)}
    {pH : HahnSeries.Nonpositive.ConstantTermOneFiniteSupport (G := H) (K := K)},
      Berarducci.IsNormalizedSeriesMaximalFiniteSupportDivisor b p →
        HahnSeries.Nonpositive.IsNormalizedHPart H p pH →
          ∀ q : HahnSeries.Nonpositive.ConstantTermOneFiniteSupport (G := H) (K := K),
            HahnSeries.Nonpositive.mapDomainToReal H
                ((q : HahnSeries.Nonpositive.FiniteSupportRing (G := H) (K := K)) :
                  HahnSeries.Nonpositive H K) ∣ b ↔
              (q : HahnSeries.Nonpositive.FiniteSupportRing (G := H) (K := K)) ∣
                (pH : HahnSeries.Nonpositive.FiniteSupportRing (G := H) (K := K)))

/- Corrected relational target for LM24, Corollary 6.5.4. Both inputs are nonzero because the
normalized `H`-part is a partial operation with codomain `1 + K(H^{<0})`. -/
    [DivisibleBy H ℤ]
    (p q : HahnSeries.Nonpositive.FiniteSupportRing (G := ℝ) (K := K)) ↦
  p ≠ 0 → q ≠ 0 →
    ∀ pH qH pqH : HahnSeries.Nonpositive.ConstantTermOneFiniteSupport
        (G := H) (K := K),
      HahnSeries.Nonpositive.IsNormalizedHPart H p pH →
        HahnSeries.Nonpositive.IsNormalizedHPart H q qH →
          HahnSeries.Nonpositive.IsNormalizedHPart H (p * q) pqH →
            pqH = pH * qH)

/- The proved reduction underlying Corollary 6.5.4 isolates exactly the factor-refinement input
used in the printed proof. -/
  ∀ (H : AddSubgroup ℝ) {K : Type v} [Field K],
    HahnSeries.Nonpositive.HasNormalizedHDivisorRefinement H (K := K) →
      ∀ {p q : HahnSeries.Nonpositive.FiniteSupportRing (G := ℝ) (K := K)}
        {pH qH pqH : HahnSeries.Nonpositive.ConstantTermOneFiniteSupport
          (G := H) (K := K)},
          HahnSeries.Nonpositive.IsNormalizedHPart H p pH →
            HahnSeries.Nonpositive.IsNormalizedHPart H q qH →
              HahnSeries.Nonpositive.IsNormalizedHPart H (p * q) pqH →
                pqH = pH * qH)

/- Nonconstant semantic certificate for the multiplication reduction: for the trivial exponent
subgroup, the normalized part of `(1 + t⁻¹)²` is `1`, although `1 + t⁻¹` is not its embedded
normalized part. -/
  Tests.normalizedPartNonconstantSeries ≠
    HahnSeries.Nonpositive.finiteSupportToReal Tests.TrivialExponentSubgroup
      (1 : HahnSeries.Nonpositive.FiniteSupportRing
        (G := Tests.TrivialExponentSubgroup) (K := ℚ)))
  HahnSeries.Nonpositive.IsNormalizedHPart Tests.TrivialExponentSubgroup
    (Tests.normalizedPartNonconstantSeries *
      Tests.normalizedPartNonconstantSeries) 1)

/- Corrected relational target for LM24, Corollary 6.5.5. -/
    [DivisibleBy H ℤ] (b c : HahnSeries.Nonpositive ℝ K) ↦
  b ≠ 0 → c ≠ 0 →
    ∀ bH cH bcH : HahnSeries.Nonpositive.ConstantTermOneFiniteSupport
        (G := H) (K := K),
      HahnSeries.Nonpositive.IsNormalizedHPart H
          (Berarducci.seriesNormalizedMaximalFiniteSupportDivisor b) bH →
        HahnSeries.Nonpositive.IsNormalizedHPart H
            (Berarducci.seriesNormalizedMaximalFiniteSupportDivisor c) cH →
          HahnSeries.Nonpositive.IsNormalizedHPart H
              (Berarducci.seriesNormalizedMaximalFiniteSupportDivisor (b * c)) bcH →
            bcH = bH * cH)

/- The proved reduction underlying Corollary 6.5.5 keeps both mathematical prerequisites
explicit: normalized-divisor refinement and multiplicativity of the real maximal finite-support
divisor. -/
  ∀ (H : AddSubgroup ℝ) {K : Type v} [Field K],
    HahnSeries.Nonpositive.HasNormalizedHDivisorRefinement H (K := K) →
      ∀ {b c : HahnSeries.Nonpositive ℝ K}
        {bH cH bcH : HahnSeries.Nonpositive.ConstantTermOneFiniteSupport
          (G := H) (K := K)},
          HahnSeries.Nonpositive.IsNormalizedHPart H
              (Berarducci.seriesNormalizedMaximalFiniteSupportDivisor b) bH →
            HahnSeries.Nonpositive.IsNormalizedHPart H
                (Berarducci.seriesNormalizedMaximalFiniteSupportDivisor c) cH →
              HahnSeries.Nonpositive.IsNormalizedHPart H
                  (Berarducci.seriesNormalizedMaximalFiniteSupportDivisor (b * c)) bcH →
                Berarducci.seriesNormalizedMaximalFiniteSupportDivisor (b * c) =
                    Berarducci.seriesNormalizedMaximalFiniteSupportDivisor b *
                      Berarducci.seriesNormalizedMaximalFiniteSupportDivisor c →
                  bcH = bH * cH)

/- Exact target for LM24, Corollary 6.5.6. -/
    [DivisibleBy H ℤ] ↦
  ∀ p : HahnSeries.Nonpositive.ConstantTermOneFiniteSupport (G := H) (K := K),
    IsPrimal
      (((p : HahnSeries.Nonpositive.FiniteSupportRing (G := H) (K := K)) :
        HahnSeries.Nonpositive H K)))

/- Corrected exact target for LM24, Theorem 6.5.7. The coefficient unit is indispensable. The
first clause gives existence and global uniqueness of the normalized finite-support factor. When
the real support supremum lies in `H`, the second clause gives an irreducible factorisation whose
monomial exponent equals that supremum and is globally unique among such factorisations. -/
    [DivisibleBy H ℤ] (b : HahnSeries.Nonpositive H K) ↦
  b ≠ 0 →
    ∃ (k : Kˣ)
      (p : HahnSeries.Nonpositive.ConstantTermOneFiniteSupport (G := H) (K := K))
      (x : HahnSeries.Nonpositive.exponentMonoid H)
      (factors : List (HahnSeries.Nonpositive H K)),
        HahnSeries.Nonpositive.IsAlmostIrreducibleFactorization b k p x factors ∧
          HahnSeries.Nonpositive.IsUniqueNormalizedHFactor b p ∧
          ((∃ s : H, HahnSeries.Nonpositive.realSupportSup H b = ((s : ℝ) : WithBot ℝ)) →
            ∃ (k' : Kˣ) (x' : HahnSeries.Nonpositive.exponentMonoid H)
              (factors' : List (HahnSeries.Nonpositive H K)),
                HahnSeries.Nonpositive.IsIrreducibleSubgroupFactorization
                    b k' p x' factors' ∧
                  HahnSeries.Nonpositive.realSupportSup H b =
                    ((((x' : H) : ℝ) : WithBot ℝ)) ∧
                  HahnSeries.Nonpositive.IsUniqueIrreducibleFactorizationExponent b x'))

/- Scalar boundary for Theorem 6.5.7: the corrected factorisation represents `2`, whereas the
same normalized factor, zero exponent, and empty residual list without a scalar do not. -/
  HahnSeries.Nonpositive.IsAlmostIrreducibleFactorization
    (HahnSeries.Nonpositive.C 2 : Tests.FactorizationSeries)
      (Units.mk0 2 (by norm_num))
      (1 : HahnSeries.Nonpositive.ConstantTermOneFiniteSupport
        (G := Tests.FactorizationExponentSubgroup) (K := ℚ))
      Tests.factorizationZeroExponent [])
  (HahnSeries.Nonpositive.C 2 : Tests.FactorizationSeries) ≠
    (((1 : HahnSeries.Nonpositive.ConstantTermOneFiniteSupport
        (G := Tests.FactorizationExponentSubgroup) (K := ℚ)) :
          HahnSeries.Nonpositive.FiniteSupportRing
            (G := Tests.FactorizationExponentSubgroup) (K := ℚ)) :
        Tests.FactorizationSeries) *
      (HahnSeries.Nonpositive.finiteSupportMonomial (K := ℚ)
        Tests.factorizationZeroExponent :
          Tests.FactorizationSeries) *
      ([] : List Tests.FactorizationSeries).prod)
  ∀ {K : Type v} [Field K]
    (α : NatOrdinal) (k : K)
    (x : Berarducci.principalDegreeClasses K α),
      Berarducci.principalDegreeClassesToPrincipalComponent K α (k • x) =
        k • Berarducci.principalDegreeClassesToPrincipalComponent K α x)
  ∀ {K : Type v} [Field K] [CharZero K]
    {α β : NatOrdinal}
    (x : Berarducci.principalDegreeClasses K α)
    (y : Berarducci.principalDegreeClasses K β),
      Berarducci.principalDegreeClassesEquivPrincipalComponent K (α + β)
          (Berarducci.principalDegreeClassesMul x y) =
        Berarducci.principalComponentMul
          (Berarducci.principalDegreeClassesEquivPrincipalComponent K α x)
          (Berarducci.principalDegreeClassesEquivPrincipalComponent K β y))
  ∀ (K : Type v) [Field K],
    Type (max v 1))
  ∀ (K : Type v) [Field K] [CharZero K],
      Berarducci.PrincipalSubring K →ₐ[K]
        Berarducci.DegreeGraded K)
  ∀ {K : Type v} [Field K] [CharZero K]
    (x : Berarducci.PrincipalSubring K) (α : NatOrdinal),
      Berarducci.principalSubringEmbedding K x α =
        Berarducci.principalComponentToHahnDegreeLayer K α (x α))
  ∀ {K : Type v} [Field K] [CharZero K]
    (x : Berarducci.DegreeGraded K),
      x ∈ Berarducci.principalSubringSubalgebra K ↔
        Berarducci.IsPrincipalGraded x)
  ∀ {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M]
    [LinearOrder M] [IsOrderedCancelAddMonoid M]
    (ν : MaxAddDegree R M), ν.nonpositiveSubring →+* ν.ResidueRing)
  ∀ {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M]
    [LinearOrder M] [IsOrderedCancelAddMonoid M]
    (ν : MaxAddDegree R M), Function.Surjective ν.residueMap)
  ∀ {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M]
    [LinearOrder M] [IsOrderedCancelAddMonoid M]
    (ν : MaxAddDegree R M),
      RingHom.ker ν.residueMap = ν.negativeIdeal)
  ∀ {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M]
    [LinearOrder M] [IsOrderedCancelAddMonoid M]
    (ν : MaxAddDegree R M),
      ν.nonpositiveSubring ⧸ ν.negativeIdeal ≃+* ν.ResidueRing)
  ∀ {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M]
    [LinearOrder M] [IsOrderedAddMonoid M]
    (w : Valuation R (WithZero (Multiplicative M))),
      (MaxAddDegree.ofValuation w).nonpositiveSubring = w.integer)
  ∀ {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M]
    [LinearOrder M] [IsOrderedAddMonoid M]
    (w : Valuation R (WithZero (Multiplicative M))),
      (MaxAddDegree.ofValuation w).negativeIdeal =
        (w.ltIdeal 1).comap (MaxAddDegree.nonpositiveEquivInteger w).toRingHom)
  ∀ {K : Type v} [Field K] [CharZero K],
    ∃ w : MaxAddDegree (HahnSeries.Nonpositive ℝ K) NatOrdinal, w.IsMultiplicative ∧
      (∀ b, w b = (b : K⟦ℝ⟧).degree) ∧
        w.nonpositiveSubring = HahnSeries.Nonpositive.finiteSupportSubring ∧
        w.negativeIdeal = ⊥ ∧ Function.Bijective w.residueMap)
  ∀ {K : Type v} [Field K] [CharZero K]
    (b c : HahnSeries.Nonpositive ℝ K), b ≠ 0 → c ≠ 0 →
      ((b + c : HahnSeries.Nonpositive ℝ K) : K⟦ℝ⟧).degree ≤
          max (b : K⟦ℝ⟧).degree (c : K⟦ℝ⟧).degree ∧
        ((b * c : HahnSeries.Nonpositive ℝ K) : K⟦ℝ⟧).degree =
          (b : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree ∧
        ((b : K⟦ℝ⟧).degree = ⊥ ↔ b = 0))
  ∀ {K : Type v} [Field K] [CharZero K]
    {p b c : HahnSeries.Nonpositive ℝ K},
      p ∈ HahnSeries.Nonpositive.finiteSupportSubring → p ∣ b * c →
        ∃ p₁ p₂ : HahnSeries.Nonpositive ℝ K,
          p₁ ∈ HahnSeries.Nonpositive.finiteSupportSubring ∧
            p₂ ∈ HahnSeries.Nonpositive.finiteSupportSubring ∧
              p = p₁ * p₂ ∧ p₁ ∣ b ∧ p₂ ∣ c)

/- LM24, Corollary 6.3.9. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    {p : HahnSeries.Nonpositive ℝ K},
      p ∈ HahnSeries.Nonpositive.finiteSupportSubring → IsPrimal p)

/- Berarducci, Definition 6.6. The residual point is strictly negative, and the translated closed
truncation has exactly the residual value. -/
  ∀ {K : Type v} [Field K]
    {b : Berarducci.SeriesWithOrdinalValueAboveOne K} {γ : ℝ},
      γ ∈ Berarducci.residualPointSet b ↔
        γ < 0 ∧
          Berarducci.ordinalValue
              (Berarducci.translatedTruncation (b.1 : K⟦ℝ⟧) γ) = b.residualValue)
  ∀ {K : Type v} [Field K]
    (b : Berarducci.SeriesWithOrdinalValueAboveOne K) (η : ℝ),
      Berarducci.residualPointTail b η =
        Berarducci.residualPointSet b ∩ Set.Ioo η 0)

/- Berarducci, Lemma 6.8. The statement is unchanged; the proof treats residual value one by
isolated support points rather than by the failing limit-index construction in the printed proof. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    (b : Berarducci.SeriesWithOrdinalValueAboveOne K),
      ∀ᶠ η in nhdsWithin (0 : ℝ) (Set.Iio 0),
        (Berarducci.residualPointTail b η).Nonempty ∧
          ∃ htail : (Berarducci.residualPointTail b η).IsPWO,
            htail.orderType = b.principalValue.val ∧
              IsLUB (Berarducci.residualPointTail b η) 0)

/- Berarducci, Lemma 6.9, with the domain of `X(b)` and `v_J^p(b)` made explicit. -/
  ∀ {K : Type v} [Field K] [CharZero K]
    (b : Berarducci.SeriesWithOrdinalValueAboveOne K) (c : Berarducci.Series K)
    {ρ : Ordinal}, Ordinal.IsPrincipal (fun α β ↦ α + β) ρ →
      (∀ᶠ γ in nhdsWithin (0 : ℝ) (Set.Iio 0),
        γ ∈ Berarducci.residualPointSet b →
          NatOrdinal.of ρ ≤
            Berarducci.ordinalValue (Berarducci.translatedTruncation (c : K⟦ℝ⟧) γ)) →
        NatOrdinal.of (ρ * b.principalValue.val) ≤ Berarducci.ordinalValue c)
  ConwayRefinementConjecture.{u} ↔
    ∀ a b c d : Surreal.OmnificInteger.{u}, a * b = c * d →
      ∃ e f g h : Surreal.OmnificInteger.{u},
        a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h)

/- *On Numbers and Games*, Theorem 31, as recalled in LM24, Section 1.1. -/
  ∀ {x : Surreal.{u}},
    Surreal.IsOmnificInteger x ↔
      x.support ⊆ Set.Ici 0 ∧
        x.coeff 0 ∈ Set.range ((↑) : ℤ → ℝ))

/- LM24, Sections 1.1 and 1.5, after the change of variable `t = ω⁻¹`. -/
  ∀ (x : Surreal.{u}),
    x.toFullHahnSeries.supportOrderType = Ordinal.lift.{u + 1, u} x.length)
  ∀ (x : Surreal.{u}), x.toFullHahnSeries.degree = x.supportDegree)

/- LM24, Proposition 2.4.3: every nonzero surreal Archimedean stratum is order-additively
isomorphic to the reals. -/
  ∀ (s : HahnEmbedding.ArchimedeanStrata ℝ Surreal.{u})
    (c : FiniteArchimedeanClass Surreal.{u}), s.stratum c ≃+o ℝ)

/- Universe-bounded LM24, Proposition 2.4.4: every nonzero surreal Archimedean ball has
cofinality at least the cardinal bounding small Conway normal forms. -/
  ∀ (c : FiniteArchimedeanClass Surreal.{u}),
    Surreal.smallSupportCardinal.{u} ≤
      Order.cof ↥(FiniteArchimedeanClass.ball ℝ c))

/- LM24, Definition 8.2.6. Reducedness is defined only for a nonzero series, and the witnessing
Archimedean class may be the zero class. -/
  ∀ {G : Type u} {R : Type v}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Ring R]
    {b : HahnSeries.Nonpositive G R}, HahnSeries.Nonpositive.IsReduced b →
      b ≠ 0 ∧ ∃ c : ArchimedeanClass G,
        (b : R⟦G⟧).support ∩
            ((b - 1 : HahnSeries.Nonpositive G R) : R⟦G⟧).support ⊆
          {x | ArchimedeanClass.mk x = c})

/- The zero Archimedean class is a genuine witness, while mixing zero with a nonzero class is
not reduced. -/
  HahnSeries.Nonpositive.IsReduced Tests.reducedConstant)
  ¬HahnSeries.Nonpositive.IsReduced Tests.nonreducedTwoClass)

/- The finite calculation before LM24, Definition 8.4.2 uses the classes met by the support,
including the zero class. These are not the individual support exponents. -/
  ∀ {G : Type u} {R : Type v}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Ring R]
    (b : HahnSeries.Nonpositive G R) (c : ArchimedeanClass G),
      c ∈ HahnSeries.Nonpositive.supportArchimedeanClasses b ↔
        ∃ g ∈ (b : R⟦G⟧).support, ArchimedeanClass.mk g = c)

/- LM24's finite calculation removes the leading class at each open truncation. The Mathlib
order on classes is opposite to LM24's. This signature checks strict support-class descent. -/
  ∀ {K : Type u} {G : Type u} {R : Type v}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Ring R]
    (b : HahnSeries.Nonpositive G R) (_hb0 : b ≠ 0)
    (horder : (b : R⟦G⟧).order ≠ 0),
      HahnSeries.Nonpositive.supportArchimedeanClasses
          (HahnSeries.Nonpositive.tau (K := K)
            (HahnSeries.Nonpositive.leadingClass b horder) b) ⊂
        HahnSeries.Nonpositive.supportArchimedeanClasses b)

/- The leading reduction in LM24, Proposition 8.2.5 is reduced. This one-step certificate,
together with strict descent, does not assert the closed finite-product formula in Section 8.4. -/
  ∀ {K : Type u} {G : Type u} {R : Type v}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R]
    (s : HahnEmbedding.ArchimedeanStrata K G)
    (b : HahnSeries.Nonpositive G R) (_hb0 : b ≠ 0)
    (horder : (b : R⟦G⟧).order ≠ 0)
    (_htau : HahnSeries.Nonpositive.tau (K := K)
      (HahnSeries.Nonpositive.leadingClass b horder) b ≠ 0),
      HahnSeries.Nonpositive.IsReduced
        (HahnSeries.Nonpositive.rho s (HahnSeries.Nonpositive.leadingClass b horder) b))

/- Nondegenerate separators: the first support contains both zero and a nonzero exponent;
the second support is infinite but meets only one class. -/
  HahnSeries.Nonpositive.supportArchimedeanClasses
      Tests.FiniteClassReduction.twoClassSeries =
    {ArchimedeanClass.mk (-1 : ℝ), ⊤})
  (Berarducci.OneRow.withoutConstant (K := ℝ) : ℝ⟦ℝ⟧).support.Infinite)
  HahnSeries.Nonpositive.supportArchimedeanClasses
      (Berarducci.OneRow.withoutConstant (K := ℝ)) =
    {ArchimedeanClass.mk (-1 : ℝ)})

/- LM24, Proposition 8.3.6(5), residue-one irreducibility transfer. -/
  ∀ {K : Type u} {G : Type u} {R : Type v}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R]
    (s : HahnEmbedding.ArchimedeanStrata K G) (Z : Subring R)
    (b : HahnSeries.truncationIntegerPart G Z)
    (_hb0 : (b : HahnSeries.Nonpositive G R) ≠ 0)
    (horder : ((b : HahnSeries.Nonpositive G R) : R⟦G⟧).order ≠ 0)
    (_htau : HahnSeries.Nonpositive.tauBall (K := K)
      (HahnSeries.Nonpositive.leadingClass
        (b : HahnSeries.Nonpositive G R) horder)
      (b : HahnSeries.Nonpositive G R) = 1)
    (_hirr : Irreducible
      (HahnSeries.Nonpositive.splitTruncation s
        (HahnSeries.Nonpositive.leadingClass
          (b : HahnSeries.Nonpositive G R) horder)
        (b : HahnSeries.Nonpositive G R))),
      Irreducible b)

/- LM24, Proposition 9.2.2 in the cardinal-bounded model used for surreal normal forms. Its
underlying preimage lemma is used with a domain ambient ring and clears scalar denominators before
applying primality in the residue subring. -/
  ∀ {L : Type u} {A : Type v} [Field L] [CommRing A] [Algebra L A]
    {π : A →ₐ[L] L} {S : Subring L} [IsDomain A] {b : A} (hb : π b ∈ S),
      IsPrimal (⟨b, hb⟩ : Subring.residueSubring π S) ↔
        (π b ≠ 0 ∧ IsPrimal (⟨π b, hb⟩ : S) ∧ IsPrimal b) ∨
          (π b = 0 ∧
            IsPrimal
              (⟨b, Subring.le_fracSubring hb⟩ :
                Subring.residueSubring π (Subring.fracSubring S))))
  ∀ {K : Type u} {G : Type u} {R : Type v} {κ : Cardinal.{u}}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R]
    [Fact (Cardinal.aleph0 < κ)] [Fact κ.IsRegular]
    (s : HahnEmbedding.ArchimedeanStrata K G) (Z : Subring R)
    (b : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := G) (R := R) (κ := κ) Z)
    (_hb0 : HahnSeries.CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b ≠ 0)
    (horder : ((HahnSeries.CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b :
      HahnSeries.Nonpositive G R) : R⟦G⟧).order ≠ 0)
    (_hbReduced : HahnSeries.Nonpositive.IsReduced
      (HahnSeries.CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b))
    (_hA2 : LM24.AssumptionA2AtFiniteClass (K := K) κ Z
      (HahnSeries.Nonpositive.leadingClass
        (HahnSeries.CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) horder)),
      IsPrimal b ↔
        IsPrimal (HahnSeries.Nonpositive.splitTruncationCardSuppLT s
          (HahnSeries.Nonpositive.leadingClass
            (HahnSeries.CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) horder)
          (HahnSeries.CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b)
          (HahnSeries.CardSuppLTTruncationIntegerPart.cardSupp_toNonpositiveRingHom_lt Z b)))

end ExactSignatures
