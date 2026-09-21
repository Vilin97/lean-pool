/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.PolynomialAlgebra.PolynomialRing
public import Mathlib.Algebra.GCDMonoid.Basic

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.GCDMonoid
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportNormalizedGCD

/-!
# Greatest common divisors in the series ring

The polynomial presentation identifies `K((ℝ^{≤0}))` with an arbitrary-variable polynomial
ring over its finite-support subring `K_fin`. LM24, Fact 2.5.2 makes `K_fin` a GCD domain, and
the multivariate Gauss theorem in
`ConwayRefinement.Algebra.MvPolynomial.GCDMonoid` transfers greatest common divisors
to the polynomial ring. The presentation then transports them to the
series ring.
-/

open HahnSeries HahnSeries.Nonpositive Berarducci MvPolynomial OrdinalGraded

universe v w

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K] [CharZero K]
variable {ι : Type w} {wt : ι → NatOrdinal} {x : ι → PrincipalSubring K}

/-- A polynomial presentation supplied by a particular minimal system and its lifts transports
greatest common divisors from the corresponding polynomial ring to the series ring. -/
theorem GeneratorLifts.nonemptyGCDMonoid
    (hx : IsMinimalSystem (principalGrading K) wt x) (σ : GeneratorLifts wt x) :
    Nonempty (GCDMonoid (Series K)) := by
  letI : Nonempty (NormalizedGCDMonoid (FiniteSupportRing (K := K))) :=
    nonemptyNormalizedGCDMonoid_finiteSupport
  letI : Nonempty (GCDMonoid (MvPolynomial ι (FiniteSupportRing (K := K)))) :=
    MvPolynomial.nonemptyGCDMonoid
  exact MulEquiv.nonemptyGCDMonoid (polynomialRingEquiv hx σ).symm.toMulEquiv

/-- The nonpositive real series ring over a characteristic-zero field is a GCD domain. The result
is stated through `Nonempty` because `GCDMonoid` contains a choice of gcd operation. -/
@[blueprint "thm:hahn-series-gcd-domain"
  (phase := "Primality and factorisation for real exponents")
  (title := "Greatest common divisors in $K((\\mathbb R^{\\le 0}))$")
  (statement := /--
    Let $K$ be a field of characteristic $0$.  The ring
    $K((\mathbb R^{\le 0}))$ of generalised power series with nonpositive real
    exponents is a GCD domain.
  -/)
  (proof := /--
    By \ref{lem:extend-to-minimal-system}, choose a minimal homogeneous generating
    system of $\widehat{\mathrm P}$ together with principal-series representatives
    of its generators. By \ref{thm:hahn-series-polynomial-algebra},
    $K((\mathbb R^{\le 0}))$ is a polynomial ring over the finite-support
    subring $K(\mathbb R^{\le 0})$. By \ref{fact:finite-support-hahn-gcd},
    the coefficient ring is a GCD domain. Normalising each nonzero greatest
    common divisor by the coefficient of $t^{\sup(p)}$ supplies the hypothesis
    required by \ref{lem:multivariate-polynomial-gcd}. Transport the
    resulting gcd operation across the isomorphism.
  -/)
  (highlight)]
theorem nonemptyGCDMonoid : Nonempty (GCDMonoid (Series K)) := by
  obtain ⟨ι, wt, x, hx, ⟨σ⟩⟩ := exists_isMinimalSystem_and_generatorLifts K
  exact σ.nonemptyGCDMonoid hx

end Berarducci
