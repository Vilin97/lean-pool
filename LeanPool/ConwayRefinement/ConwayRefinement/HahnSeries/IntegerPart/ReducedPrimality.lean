/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Primality.Primality
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.CardinalProposition922
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.NonpositiveDomainEquiv
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Divisibility.PrimalPreimage

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.CharZero

/-!
# Primality of reduced Hahn integer-part series

LM24's reduction at the leading Archimedean class transfers primality from a real-exponent Hahn
series to a reduced element of a cardinal-bounded Hahn integer part. Polynomiality of the
real-exponent series ring supplies this primality without a finite-degree hypothesis.
-/

public noncomputable section

open Cardinal FiniteArchimedeanClass
open scoped HahnSeries

namespace HahnSeries.Nonpositive

variable {G K : Type*}
variable [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G] [Field K] [CharZero K]

/-- A nonpositive Hahn series whose exponent group is order-isomorphic to `ℝ` is primal. -/
theorem isPrimal_of_orderIso_real (e : G ≃+o ℝ) (a : Nonpositive G K) : IsPrimal a :=
  (RingEquiv.isPrimal_iff (embDomainRingEquiv e) a).mp
    (Berarducci.isPrimal (embDomainRingEquiv e a))

end HahnSeries.Nonpositive

namespace HahnSeries.Nonpositive

variable {K G R : Type*} {κ : Cardinal}
variable [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module K G] [IsOrderedModule K G]
variable [Field R] [CharZero R] [Fact (ℵ₀ < κ)]

/-- A nonzero reduced bounded Hahn integer-part series is primal under the leading-class
Archimedean hypotheses. -/
@[blueprint "cor:reduced-hahn-integer-part-primal"
  (phase := "Finitely many Archimedean classes")
  (title := "Primality of reduced bounded Hahn integer-part series")
  (statement := /--
    Let $K$ be an Archimedean ordered division ring, $G$ an ordered
    $K$-vector space, $R$ a field of characteristic $0$, $\kappa>\aleph_0$ a
    regular cardinal, and $Z\subseteq R$ a subring.  For every nonzero
    Archimedean class $\tau$ of $G$, fix a complement $H_\tau$ of
    $G_{\prec\tau}$ in $G_{\preceq\tau}$, and write
    $L_\tau:=R((G_{\prec\tau}))_\kappa$.  Let
    $b\in Z+R((G^{<0}))_\kappa$ be reduced, with nonzero underlying series and
    nonzero order, and let $\sigma$ be its leading Archimedean class.  If
    $H_\sigma\simeq\mathbb R$ as ordered additive groups, and either
    $G_{\prec\sigma}$ has cofinality at least $\kappa$ or
    $G_{\prec\sigma}=\{0\}$ and every element of $R$ is a fraction of elements
    of $Z$, then $b$ is primal in $Z+R((G^{<0}))_\kappa$.
  -/)
  (proof := /--
  By \ref{fact:leading-class-primality-transfer}, primality of $b$ is equivalent
  to primality of $\iota_\sigma(T_\sigma b)$ in
  $L_\sigma((H_\sigma^{\le 0}))$.  Transport the exponent group through
  $H_\sigma\simeq\mathbb R$. By \ref{thm:hahn-series-primality}, the
  transported series is primal in
  $L_\sigma((\mathbb R^{\le 0}))$, so the equivalence transfers primality back
  to $b$.
  -/)]
theorem isPrimal_of_isReduced_of_leadingClass_orderIso_real
    [Fact κ.IsRegular]
    (u : HahnEmbedding.ArchimedeanStrata K G) (Z : Subring R)
    (b : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hb0 : CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b ≠ 0)
    (horder : ((CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b :
      Nonpositive G R) : R⟦G⟧).order ≠ 0)
    (hbReduced : IsReduced (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b))
    (hA2 : LM24.AssumptionA2AtFiniteClass (K := K) κ Z
      (leadingClass (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) horder))
    (e : u.stratum
      (leadingClass (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) horder) ≃+o ℝ) :
    IsPrimal b :=
  (isPrimal_iff_isPrimal_splitTruncationCardSuppLT_of_isReduced
    u Z b hb0 horder hbReduced hA2).mpr (isPrimal_of_orderIso_real e _)

end HahnSeries.Nonpositive
