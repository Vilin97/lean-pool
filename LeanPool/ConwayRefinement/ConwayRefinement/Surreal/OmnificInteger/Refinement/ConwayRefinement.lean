/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.LimitTailPrimality
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.CardinalIntegerPart
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.RefinementConjecture
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.RationalTailQuotient

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Divisibility.PrimalPreimage
import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Conway's refinement conjecture for omnific integers

The signed Conway normal form identifies the omnific integers with the cardinal-bounded
generalised-power-series integer part over the integer subring of the reals. Finite support-class
primality and the common-tail theorem prove that this integer part is pre-Schreier. Transporting
through signed normal form gives Conway's four-factor refinement theorem.
-/

open Cardinal FiniteArchimedeanClass
open HahnSeries.CardSuppLTTruncationIntegerPart

universe u

public noncomputable section

namespace Surreal.OmnificInteger

private theorem small_of_card_lt_smallSupportCardinal
    {S : Set (FiniteArchimedeanClass Surreal.{u})}
    (hS : #S < Surreal.smallSupportCardinal.{u}) : Small.{u} S := by
  rw [Cardinal.small_iff_lift_mk_lt_univ, Cardinal.lift_id]
  rw [Surreal.smallSupportCardinal_eq_univ] at hS
  exact hS

/-- Every element of the signed bounded Hahn integer part corresponding to the omnific integers
is primal. -/
@[blueprint "thm:surreal-hahn-integer-part-primality"
  (phase := "Surreal numbers and omnific integers")
  (title := "Primality of the surreal Hahn integer part")
  (statement := /--
    Every element of
    \[
      \mathbb Z+\mathbb R((\mathbf{No}_u^{<0}))_{\kappa_u}
    \]
    is primal, where $\kappa_u$ is the universe cardinal.
  -/)
  (proof := /--
    The two Archimedean hypotheses follow from
    \ref{fact:surreal-archimedean-strata} and
    \ref{fact:surreal-archimedean-ball-cofinality}. Therefore
    \ref{thm:finite-support-classes-primality} handles series whose support
    meets finitely many Archimedean classes. For a small limit family, the
    quotient by its common tail is Cauchy complete by
    \ref{lem:surreal-common-tail-quotient-complete}.  The common tail has
    the required fraction-field property by
    \ref{thm:surreal-common-tail-integer-part-fraction-field}. Finally,
    \ref{thm:limit-tail-primality} proves primality for arbitrary support-class
    order type.
  -/)]
theorem signedSmallSupportIntegerPart_isPrimal
    (a : SignedSmallSupportIntegerPart.{u}) : IsPrimal a := by
  apply isPrimal_of_finite_classes_and_limit_tail_conditions Surreal.realIntegerSubring
  · intro y hy
    apply HahnSeries.Nonpositive.isPrimal_of_supportArchimedeanClasses_finite
      Surreal.realIntegerSubring Surreal.archimedeanStrata
      (fun c ↦ ⟨Surreal.stratumOrderAddMonoidIsoReal Surreal.archimedeanStrata c⟩)
      (Surreal.assumptionA2AtFiniteClass Surreal.realIntegerSubring) y
    rw [supportArchimedeanClasses_toNonpositiveRingHom]
    exact hy
  · intro T hTne hTlimit hTcard
    letI : Small.{u} T := small_of_card_lt_smallSupportCardinal hTcard
    letI : Nonempty T := Set.nonempty_coe_sort.mpr hTne
    exact ⟨Surreal.completeSpace_rationalTailQuotient T hTlimit⟩
  · intro T _hTne hTlimit hTcard
    letI : Small.{u} T := small_of_card_lt_smallSupportCardinal hTcard
    exact Surreal.fracSubring_cardSuppLTTruncationIntegerPart_tailSubmodule_eq_top
      Surreal.realIntegerSubring T hTlimit

/-- The signed bounded Hahn integer part corresponding to the omnific integers is pre-Schreier. -/
theorem signedSmallSupportIntegerPart_decompositionMonoid :
    DecompositionMonoid SignedSmallSupportIntegerPart.{u} :=
  ⟨signedSmallSupportIntegerPart_isPrimal⟩

/-- The omnific-integer subring has the four-factor refinement property. -/
@[blueprint "thm:omnific-integer-refinement-property"
  (phase := "Surreal numbers and omnific integers")
  (title := "Refinement property of $\\mathbf{Oz}_u$")
  (statement := /--
    If $a,b,c,d\in\mathbf{Oz}$ and $ab=cd$, then there are
    $e,f,g,h\in\mathbf{Oz}$ such that
    \[
      a=ef,\qquad b=gh,\qquad c=eg,\qquad d=fh.
    \]
  -/)
  (proof := /--
    By \ref{thm:signed-normal-form-omnific-integer-equivalence},
    $\mathbf{Oz}_u$ is isomorphic to its bounded generalised-power-series
    integer part.
    By \ref{thm:surreal-hahn-integer-part-primality}, that integer part is
    pre-Schreier and therefore has four-factor refinement.  Transport the
    refinement back through signed normal form.
  -/)]
theorem conwayRefinement : ConwayRefinementConjecture.{u} := by
  rw [conwayRefinementConjecture_def, ← hasFourFactorRefinement_def]
  letI : DecompositionMonoid SignedSmallSupportIntegerPart.{u} :=
    signedSmallSupportIntegerPart_decompositionMonoid
  exact signedSmallSupportIntegerPartRingEquiv.toMulEquiv.hasFourFactorRefinement_iff.mpr
    hasFourFactorRefinement_of_decompositionMonoid

end Surreal.OmnificInteger
