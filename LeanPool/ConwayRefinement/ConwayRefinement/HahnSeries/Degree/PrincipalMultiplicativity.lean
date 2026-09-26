/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Multiplicativity
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.NegativeMonomialIdeal
public import Mathlib.RingTheory.Ideal.Prime

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrderTypeMultiplicativity
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Degree.SupportSupremumMultiplicativity
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.ProductValue

/-!
# Multiplication of principal real Hahn series

LM24, Proposition 3.6.1 combines Fact 3.4.1 with Proposition 3.5.1: the product of two principal
series is principal. The first theorem below exposes the two cited Berarducci inputs explicitly.
The second discharges them using their formalized characteristic-zero theorems.

The theorem below directly combines the two cited Berarducci inputs.
-/

universe v

public noncomputable section

namespace HahnSeries.Nonpositive

variable {K : Type v} [Field K]

/-- LM24, Proposition 3.6.1, reduced to the two Berarducci prerequisites used by LM24. -/
theorem IsPrincipal.mul_of_multiplicativity
    {b c : Nonpositive ℝ K}
    (hb : IsPrincipal b) (hc : IsPrincipal c)
    (hOrder : OrderTypeMultiplicativeOnWeaklyPrincipal K)
    (hJ : (negativeMonomialIdeal K).IsPrime) :
    IsPrincipal (b * c) := by
  rw [isPrincipal_iff]
  constructor
  · exact hOrder.isWeaklyPrincipal_mul hb.isWeaklyPrincipal hc.isWeaklyPrincipal
  · rw [supportSup_mul_of_negativeMonomialIdeal_isPrime hJ,
      hb.supportSup_eq_zero, hc.supportSup_eq_zero, add_zero]

/-- LM24, Proposition 3.6.1: the product of two principal real Hahn series is principal. -/
theorem IsPrincipal.mul [CharZero K]
    {b c : Nonpositive ℝ K} (hb : IsPrincipal b) (hc : IsPrincipal c) :
    IsPrincipal (b * c) :=
  hb.mul_of_multiplicativity hc orderTypeMultiplicativeOnWeaklyPrincipal
    Berarducci.negativeMonomialIdeal_isPrime

end HahnSeries.Nonpositive
