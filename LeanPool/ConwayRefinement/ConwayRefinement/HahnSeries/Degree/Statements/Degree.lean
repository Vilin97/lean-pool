/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Nonpositive
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrderType
public import Mathlib.Basic.Real.Basic

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrderTypeMultiplicativity

/-!
# LM24 degree valuation statement

This module proves LM24, Theorem D with its printed quantifier domain: both input series are
nonzero. The ultrametric inequality and separation at zero are proved directly, while
multiplicativity uses LM24's reduction to Berarducci, Corollary 9.9.

The addition on degrees is Hessenberg addition transported to `NatOrdinal`, with an absorbing
bottom element for the zero series. The source's third clause is retained even though its fixed
input `b` is assumed nonzero. The stronger all-input separation theorem is
`HahnSeries.degree_eq_bot`.
-/

universe v

open scoped HahnSeries

public noncomputable section

namespace HahnSeries.Nonpositive

variable {K : Type v} [Field K] [CharZero K]

/-- The all-input multiplicativity law underlying LM24, Theorem D. The printed theorem assumes
both inputs are nonzero; the zero cases follow from the ring laws. -/
@[blueprint "fact:degree-multiplicativity"
  (phase := "Ordinal value and degree")
  (title := "Multiplicativity of the degree (LM24, Theorem D)")
  (statement := /--
    For $b,c\in\Kser$, $\deg(bc)=\deg(b)\nsum\deg(c)$.
  -/)
  (proof := /--
  Decompose each nonzero series into a principal leading summand and a remainder
  of no larger degree. By
  \ref{fact:weakly-principal-order-type-multiplicativity}, the support order
  types of the two principal summands multiply. Together with the strict degree
  bounds for the remaining products, this shows that the leading term of
  $bc$ has degree $\deg(b)\mathbin\oplus\deg(c)$.  Hence
  $\deg(bc)=\deg(b)\mathbin\oplus\deg(c)$.  The zero cases follow from the
  ring laws.
  -/)]
theorem degree_mul (b c : Nonpositive ℝ K) :
    ((b * c : Nonpositive ℝ K) : K⟦ℝ⟧).degree =
      (b : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree :=
  degree_mul_of_orderTypeMultiplicativeOnWeaklyPrincipal
    orderTypeMultiplicativeOnWeaklyPrincipal b c

/-- LM24, Theorem D: degree is a multiplicative valuation on nonpositive real Hahn series. -/
theorem real_hahn_series_degree_valuation
    (b c : Nonpositive ℝ K) (_hb : b ≠ 0) (_hc : c ≠ 0) :
    ((b + c : Nonpositive ℝ K) : K⟦ℝ⟧).degree ≤
        max (b : K⟦ℝ⟧).degree (c : K⟦ℝ⟧).degree ∧
      ((b * c : Nonpositive ℝ K) : K⟦ℝ⟧).degree =
        (b : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree ∧
      ((b : K⟦ℝ⟧).degree = ⊥ ↔ b = 0) := by
  refine ⟨HahnSeries.degree_add_le _ _, ?_, ?_⟩
  · exact degree_mul b c
  · simp

end HahnSeries.Nonpositive
