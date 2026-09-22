/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Primality.GCDMonoid
public import Mathlib.Algebra.Prime.Defs

import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Factorisation in the series ring

Let `K((ℝ^{≤0}))` be the series ring over a field `K` of characteristic zero and `K(ℝ^{≤0})` its
subring of series with finite support [LM24, Not. 2.1.5], written `K_fin` below. The polynomial
presentation identifies `K((ℝ^{≤0}))` with an arbitrary-variable polynomial ring over `K_fin`.
The GCD-domain structure established in `ConwayRefinement.HahnSeries.Primality.GCDMonoid` therefore
gives Mathlib's `DecompositionMonoid` structure on the series ring. Thus every series is primal,
every
irreducible series is prime, and factorisations into irreducibles are unique up to order and
units.
-/

open Berarducci

universe v

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K] [CharZero K]

/-! ### Pre-Schreier consequences of greatest common divisors -/

/-- `K((ℝ^{≤0}))` is pre-Schreier (Mathlib's `DecompositionMonoid`) because it is a GCD
domain. -/
instance decompositionMonoid : DecompositionMonoid (Series K) := by
  let : GCDMonoid (Series K) := Classical.choice nonemptyGCDMonoid
  infer_instance

/-- Every series is primal in `K((ℝ^{≤0}))`. -/
@[blueprint "thm:hahn-series-primality"
  (phase := "Primality and factorisation for real exponents")
  (title := "Primality of generalised power series")
  (statement := /--
    Let $K$ be a field of characteristic $0$.  Every element of
    $K((\mathbb R^{\le 0}))$ is primal in $K((\mathbb R^{\le 0}))$.
  -/)
  (proof := /--
    By \ref{thm:hahn-series-gcd-domain}, the series ring is a GCD domain.  Every
    GCD domain is pre-Schreier [LM24, Fact 2.5.1], and every element of a
    pre-Schreier domain is primal [LM24, §2.5].
  -/)]
theorem isPrimal (a : Series K) : IsPrimal a :=
  DecompositionMonoid.primal a

/-- Every irreducible series is prime in `K((ℝ^{≤0}))`. -/
@[blueprint "cor:hahn-series-irreducible-is-prime"
  (phase := "Primality and factorisation for real exponents")
  (title := "Irreducible series are prime")
  (statement := /--
    Let $K$ be a field of characteristic $0$.  Every irreducible element of
    $K((\mathbb R^{\le 0}))$ is prime in $K((\mathbb R^{\le 0}))$.
  -/)
  (proof := /--
    Every series is primal by \ref{thm:hahn-series-primality}, and an irreducible
    primal element is prime.
  -/)]
theorem prime_of_irreducible {a : Series K} (ha : Irreducible a) : Prime a :=
  ha.prime_of_isPrimal (isPrimal a)

/-- Unique factorisation in `K((ℝ^{≤0}))`: two factorisations of a series into irreducibles agree
up to order and units, that is, the two multisets of factors are related by association. -/
theorem factorization_unique {f g : Multiset (Series K)} (hf : ∀ x ∈ f, Irreducible x)
    (hg : ∀ x ∈ g, Irreducible x) (hfg : Associated f.prod g.prod) :
    Multiset.Rel Associated f g :=
  prime_factors_unique (fun x hx ↦ prime_of_irreducible (hf x hx))
    (fun x hx ↦ prime_of_irreducible (hg x hx)) hfg

end Berarducci
