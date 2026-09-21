/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.ReducedPrimality
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.Primality.OrdinaryIntegers

import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ArchimedeanAssumptions

/-!
# Every nonordinary reduced omnific integer is primal

The leading-class transfer of [LM24, Prop. 9.2.2] reduces a nonordinary reduced omnific integer
to a reduced generalised power series with real exponents. Every such series is primal, and every
Archimedean stratum of the surreal exponent group is order-isomorphic to `ℝ` [LM24,
Prop. 2.4.3]. Hence every nonordinary reduced omnific integer is primal, and every irreducible one
is prime.
-/

public noncomputable section

open Cardinal FiniteArchimedeanClass
open scoped HahnSeries NatOrdinal

namespace Surreal.OmnificInteger

universe u

/-- Every nonordinary reduced omnific integer is primal. -/
@[blueprint "thm:reduced-omnific-primal"
  (phase := "Surreal numbers and omnific integers")
  (title := "Primality of reduced omnific integers outside $\\mathbb Z$")
  (statement := /--
    Let $x\in\mathbf{Oz}$ be an omnific integer whose underlying surreal
    number is not equal to any integer.  Write $s$ for its signed nonpositive
    series representation.  Suppose that $s$ is reduced: $s\ne0$ and, for
    some Archimedean class $\sigma$,
    \[
      \operatorname{supp}(s)\cap\operatorname{supp}(s-1)
      \subseteq\{y:[y]=\sigma\}.
    \]
    Then $x$ is primal in $\mathbf{Oz}$.
  -/)
  (proof := /--
    By \ref{thm:signed-normal-form-omnific-integer-equivalence}, $x$
    corresponds to a bounded integer-part series $b$. Since $x$ is not an ordinary integer, the
    underlying series of $b$ is nonzero and has nonzero order; reducedness
    transfers from $s$ to $b$.  At the leading Archimedean class of $b$, the
    surreal exponent group satisfies $(A2)_\sigma$ by
    \ref{fact:surreal-archimedean-ball-cofinality}, and its stratum is
    order-isomorphic to $\mathbb R$ by
    \ref{fact:surreal-archimedean-strata}.  Hence
    \ref{cor:reduced-hahn-integer-part-primal} makes $b$ primal.  Transport
    primality back through the ring equivalence.
  -/)]
theorem isPrimal_of_isReduced
    (x : Surreal.OmnificInteger.{u}) (hxInteger : ¬ IsOrdinaryInteger x)
    (hxReduced : HahnSeries.Nonpositive.IsReduced x.toSignedNonpositiveHahn) :
    IsPrimal x := by
  let b : SignedSmallSupportIntegerPart.{u} := toSignedSmallSupportIntegerPart x
  let hbOrder := boundedSignedHahn_order_ne_zero_of_not_isOrdinaryInteger x hxInteger
  have himage :
      HahnSeries.CardSuppLTTruncationIntegerPart.toNonpositiveRingHom
          Surreal.realIntegerSubring b = x.toSignedNonpositiveHahn := by
    apply Subtype.ext
    rw [HahnSeries.CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom,
      coe_toSignedNonpositiveHahn]
    exact coe_toSignedSmallSupportIntegerPart x
  have hx0 : x ≠ 0 := by
    intro hxzero
    subst x
    apply hxInteger
    rw [isOrdinaryInteger_iff]
    exact ⟨0, rfl⟩
  have hb0 :
      HahnSeries.CardSuppLTTruncationIntegerPart.toNonpositiveRingHom
          Surreal.realIntegerSubring b ≠ 0 := by
    rw [himage]
    intro hxHahn
    apply hx0
    apply Subtype.ext
    apply Surreal.toSignedFullHahnSeries_injective
    have hraw := congrArg (fun q : HahnSeries.Nonpositive Surreal ℝ ↦
      (q : HahnSeries Surreal ℝ)) hxHahn
    rw [coe_toSignedNonpositiveHahn] at hraw
    exact hraw.trans Surreal.toSignedFullHahnSeries_zero.symm
  have hbReduced : HahnSeries.Nonpositive.IsReduced
      (HahnSeries.CardSuppLTTruncationIntegerPart.toNonpositiveRingHom
        Surreal.realIntegerSubring b) := by
    rw [himage]
    exact hxReduced
  let c := HahnSeries.Nonpositive.leadingClass
    (HahnSeries.CardSuppLTTruncationIntegerPart.toNonpositiveRingHom
      Surreal.realIntegerSubring b) hbOrder
  have hbPrimal : IsPrimal b :=
    HahnSeries.Nonpositive.isPrimal_of_isReduced_of_leadingClass_orderIso_real
      Surreal.archimedeanStrata Surreal.realIntegerSubring b hb0 hbOrder hbReduced
        (Surreal.assumptionA2AtFiniteClass Surreal.realIntegerSubring c)
        (Surreal.stratumOrderAddMonoidIsoReal Surreal.archimedeanStrata c)
  let E : Surreal.OmnificInteger.{u} ≃+* SignedSmallSupportIntegerPart.{u} :=
    signedSmallSupportIntegerPartRingEquiv
  have hmap : IsPrimal (E x) := by
    simpa only [E, signedSmallSupportIntegerPartRingEquiv_apply, b] using hbPrimal
  exact (RingEquiv.isPrimal_iff E x).mp hmap

/-- Every irreducible nonordinary reduced omnific integer is prime. -/
theorem prime_of_irreducible_of_isReduced
    (x : Surreal.OmnificInteger.{u}) (hirr : Irreducible x)
    (hxInteger : ¬ IsOrdinaryInteger x)
    (hxReduced : HahnSeries.Nonpositive.IsReduced x.toSignedNonpositiveHahn) :
    Prime x :=
  hirr.prime_of_isPrimal (isPrimal_of_isReduced x hxInteger hxReduced)

end Surreal.OmnificInteger
