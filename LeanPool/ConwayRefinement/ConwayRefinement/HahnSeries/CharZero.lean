/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.Algebra.CharZero.Defs

/-!
# Hahn series over a characteristic-zero base

A Hahn series ring inherits characteristic zero from its coefficients, because the natural numbers
embed as constant series. Mathlib carries no such instance.

This is needed to apply results stated for a characteristic-zero coefficient field to a Hahn-series
field. That happens whenever the exponent group is not Archimedean and has to be split into an
Archimedean quotient over a coefficient field that is itself a Hahn-series field.
-/

public section

namespace HahnSeries

instance instCharZero {Γ R : Type*} [LinearOrder Γ] [AddCommMonoid Γ]
    [NonAssocSemiring R] [CharZero R] : CharZero (HahnSeries Γ R) where
  cast_injective m n h := by
    have hm : ((m : ℕ) : R) = ((n : ℕ) : R) := by
      have := congrArg (fun x : HahnSeries Γ R => x.coeff 0) h
      simpa [← single_zero_natCast] using this
    exact Nat.cast_injective hm

end HahnSeries
