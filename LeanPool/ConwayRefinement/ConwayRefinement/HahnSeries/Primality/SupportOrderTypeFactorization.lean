/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Primality.Primality
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.GermLike

import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Unique factorisation under the LM17 support-order alternatives

L'Innocente--Mantova, Theorem 4.8 gives existence of irreducible factorisations for nonzero
series whose support order type is their ordinal value, or is their ordinal value plus one when
that value is greater than one. Polynomiality makes every irreducible series prime, so any two
such factorisations agree up to order and units. This proves LM17, Conjecture 1.6 without carrying
the paper's auxiliary predicate into the current API.

## References

* S. L'Innocente, V. Mantova, *Factorisation of germ-like series*, J. Log. Anal. 9 (2017),
  paper no. 3, cited as [LM17].
-/

universe v

open scoped HahnSeries

public noncomputable section

namespace LM17

open Berarducci

variable {K : Type v} [Field K] [CharZero K]

/-- LM17, Conjecture 1.6: a nonzero series satisfying either support-order alternative in
LM17, Definition 4.1 admits an irreducible factorisation, unique up to order and association of
the factors. -/
@[blueprint "cor:lm17-support-order"
  (phase := "Primality and factorisation for real exponents")
  (title := "Unique factorisation under support-order conditions")
  (statement := /--
    Let $K$ be a field of characteristic $0$ and
    $a\in K((\mathbb R^{\le 0}))$ a non-zero series.  Suppose that
    $\operatorname{ot}(a)=v_J(a)$, or that $v_J(a)>1$ and
    $\operatorname{ot}(a)=v_J(a)+1$.  Then $a$ admits a factorisation into
    irreducibles, unique up to reordering and up to multiplication of the
    factors by non-zero elements of $K$.  These are the two alternatives of
    \cite[Definition~4.1]{LM17}.
  -/)
  (proof := /--
  Under either support-order hypothesis, \cite[Theorem~4.8]{LM17} gives a finite
  factorisation into irreducibles.  By
  \ref{cor:hahn-series-irreducible-is-prime}, every such irreducible is prime.
  Uniqueness of finite prime factorisations then shows that any two multisets of
  factors are related, after reordering, by association.
  -/)]
theorem exists_unique_factorization_of_supportOrderType_eq_ordinalValue_or_add_one
    {a : Series K}
    (ha : (a : K⟦ℝ⟧).supportOrderType = (ordinalValue a).val ∨
      (1 < ordinalValue a ∧
        (a : K⟦ℝ⟧).supportOrderType = (ordinalValue a).val + 1))
    (ha0 : a ≠ 0) :
    (∃ f : Multiset (Series K),
      (∀ b ∈ f, Irreducible b) ∧ Associated f.prod a) ∧
    ∀ f g : Multiset (Series K),
      (∀ b ∈ f, Irreducible b) →
      (∀ b ∈ g, Irreducible b) →
      Associated f.prod a → Associated g.prod a →
      Multiset.Rel Associated f g := by
  have haLM17 : IsGermLike a := isGermLike_iff.mpr ha
  refine ⟨haLM17.exists_factorization ha0, ?_⟩
  intro f g hf hg hfa hga
  exact prime_factors_unique
    (fun b hb ↦ Berarducci.prime_of_irreducible (hf b hb))
    (fun b hb ↦ Berarducci.prime_of_irreducible (hg b hb))
    (hfa.trans hga.symm)

end LM17
