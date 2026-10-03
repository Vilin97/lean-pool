/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import Mathlib.RingTheory.LaurentSeries

/-!
# Local derivative estimates for Corvaja--Zannier

The local Wronskian argument is carried out after expanding a rational
function in a Laurent series at a point of the curve.  This file proves the
completion-level estimate that an `r`-th derivative lowers the Laurent-series
order by at most `r`.

The statements use `HahnSeries.orderTop`, rather than `HahnSeries.order`, so
that they remain valid when the derivative vanishes.
-/

@[expose] public section

namespace BGS.CorvajaZannier

open HahnSeries LaurentSeries

variable {K : Type*} [Ring K]

/-- The `r`-th Hasse derivative lowers Laurent-series order by at most `r`.

The `orderTop` formulation also covers the case in which the Hasse derivative
is zero. -/
theorem order_sub_le_orderTop_hasseDeriv (r : ℕ) (f : LaurentSeries K) :
    ((f.order - (r : ℤ) : ℤ) : WithTop ℤ) ≤ (hasseDeriv K r f).orderTop := by
  rw [le_orderTop_iff_forall]
  intro j hj
  have hj' : j < f.order - (r : ℤ) := by
    exact_mod_cast hj
  have hjr : j + (r : ℤ) < f.order := (lt_sub_iff_add_lt).mp hj'
  rw [hasseDeriv_coeff, coeff_eq_zero_of_lt_order hjr, smul_zero]

/-- Every ordinary iterated derivative lowers Laurent-series order by at most
its iteration count.

The `orderTop` formulation also covers the case in which the iterated
derivative is zero. -/
theorem order_sub_le_orderTop_derivative_iterate (r : ℕ) (f : LaurentSeries K) :
    ((f.order - (r : ℤ) : ℤ) : WithTop ℤ) ≤ (((derivative K)^[r]) f).orderTop := by
  rw [derivative_iterate]
  refine (order_sub_le_orderTop_hasseDeriv r f).trans ?_
  exact orderTop_le_orderTop_smul _ _

end BGS.CorvajaZannier
