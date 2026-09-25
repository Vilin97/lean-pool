/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic.Ring.RingNF

-- Adapted for Lean Pool: relocated imports and simplified supporting infrastructure.

/-!
# The Fermat quotient

For a prime `p` and an integer `x`, the *Fermat quotient* is the rational number
`q_p(x) = (x ^ (p - 1) - 1) / p`. It is an integer exactly when `p ∤ x`, but the
quotient is taken in `ℚ` so that the definition carries no side condition and the
integrality is a theorem about it rather than part of it.

## Main definitions

* `GranvilleMoore.fermatUnit p x`: the power `t_x = x ^ (p - 1)`. When `p ∤ x` this is a
  principal unit at `p`, i.e. `t_x ≡ 1 [ZMOD p]`; that is what makes it the base of the
  Frobenius tower studied later.
* `GranvilleMoore.fermatQuotient p x`: the Fermat quotient `q_p(x) = (t_x - 1) / p`, a
  rational number.
* `GranvilleMoore.frobeniusExponent p k`: the Frobenius exponent
  `e_k = ∑_{r < k} p ^ r`, the exponent with `t_x ^ (e_k) = x ^ (p ^ k) / x`.

## Implementation notes

`fermatUnit` is an `abbrev`: it is notation for `x ^ (p - 1)` and has nothing to say
about itself, so every `pow` lemma in Mathlib applies to it unchanged.

`fermatQuotient` is `ℚ`-valued and unconditional; `(p : ℚ) ≠ 0` is needed only to
cancel the denominator, see `GranvilleMoore.natCast_mul_fermatQuotient`.
-/

public section

namespace GranvilleMoore

open Finset

/-- The unit attached to an integer `x` at `p`: the power `t_x = x ^ (p - 1)`.

For `p` prime with `p ∤ x` this is a principal unit at `p`, congruent to `1` modulo `p`
by Fermat's little theorem. -/
abbrev fermatUnit (p : ℕ) (x : ℤ) : ℤ := x ^ (p - 1)

/-- The Fermat quotient of an integer `x` at `p`:
`q_p(x) = (x ^ (p - 1) - 1) / p`, the quotient being taken in `ℚ`.

For `p` prime with `p ∤ x` this rational number is an integer. -/
@[expose]
def fermatQuotient (p : ℕ) (x : ℤ) : ℚ := ((fermatUnit p x - 1 : ℤ) : ℚ) / (p : ℚ)

/-- The Fermat quotient written out with the numerator cast to `ℚ` termwise. -/
theorem fermatQuotient_eq_div (p : ℕ) (x : ℤ) :
    fermatQuotient p x = ((x : ℚ) ^ (p - 1) - 1) / (p : ℚ) := by
  rw [fermatQuotient]
  push_cast
  ring

/-- Cancelling the denominator in the Fermat quotient: this is the identity
`x ^ (p - 1) = 1 + p * q_p(x)` in `ℚ`, and the only property of `fermatQuotient`
its consumers need. -/
theorem natCast_mul_fermatQuotient {p : ℕ} (hp : p ≠ 0) (x : ℤ) :
    (p : ℚ) * fermatQuotient p x = (x : ℚ) ^ (p - 1) - 1 := by
  rw [fermatQuotient_eq_div, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hp)]

/-- The Fermat quotient of `1` vanishes: `q_p(1) = 0`. -/
@[simp]
theorem fermatQuotient_one (p : ℕ) : fermatQuotient p 1 = 0 := by
  rw [fermatQuotient_eq_div]
  simp

/-- The Frobenius exponent `e_k = ∑_{r < k} p ^ r`, so that `e₀ = 0` and `e₁ = 1`.

It is the exponent for which `(x ^ (p - 1)) ^ e_k = x ^ (p ^ k - 1)`, since
`(p - 1) * e_k = p ^ k - 1`. -/
@[expose] def frobeniusExponent (p k : ℕ) : ℕ := ∑ r ∈ range k, p ^ r

/-- The Frobenius exponent is the truncated geometric sum, which is how Mathlib's
geometric-sum API applies to it. -/
theorem frobeniusExponent_eq_sum (p k : ℕ) :
    frobeniusExponent p k = ∑ r ∈ range k, p ^ r := rfl

/-- The Frobenius exponent of the empty tower vanishes: `e_0 = 0`. -/
@[simp]
theorem frobeniusExponent_zero (p : ℕ) : frobeniusExponent p 0 = 0 := by
  rw [frobeniusExponent_eq_sum, range_zero, sum_empty]

/-- The first Frobenius exponent is `1`: `e_1 = 1`. -/
@[simp]
theorem frobeniusExponent_one (p : ℕ) : frobeniusExponent p 1 = 1 := by
  rw [frobeniusExponent_eq_sum]
  simp

/-- The recursion `e_{k+1} = e_k + p ^ k` defining the Frobenius exponent. -/
theorem frobeniusExponent_succ (p k : ℕ) :
    frobeniusExponent p (k + 1) = frobeniusExponent p k + p ^ k := by
  rw [frobeniusExponent_eq_sum, frobeniusExponent_eq_sum, sum_range_succ]

/-- Peeling the recursion off the bottom instead: `e_{k+1} = 1 + p * e_k`. -/
theorem frobeniusExponent_succ' (p k : ℕ) :
    frobeniusExponent p (k + 1) = 1 + p * frobeniusExponent p k := by
  rw [frobeniusExponent_eq_sum, frobeniusExponent_eq_sum, geom_sum_succ, add_comm]

end GranvilleMoore
